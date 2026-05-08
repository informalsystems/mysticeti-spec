// -*- mode: Bluespec; -*-

/**
 * A state machine for how a DAG can evolve over time.
 * Built to check Mysticeti [1] consensus, but should be generalizable
 * to any DAG-based consensus.
 *
 * [1]: https://arxiv.org/pdf/2310.14821
 *
 * Martin Hutle and Gabriela Moreira, Informal Systems, 2024-2025
 */
module dag_evolution {
  import basicSpells.* from "./spells/basicSpells"

  type BlockReference = { authority: int, round: int, blockID: int }
  type StatementBlock = { reference: BlockReference, parents: Set[BlockReference] }

  type DAG = Set[StatementBlock]

  pure val FAULTY = 1
  pure val CORRECT_NODES = Set(2,3)
  pure val NODES = CORRECT_NODES.union(Set(0,1))

  type NodeState = {
    authority: int,
    dag: DAG,
    backlog: Set[StatementBlock],
    current_round: int,
    incoming_messages: Set[StatementBlock]
  }

  var nodes: int -> NodeState
  /// A map from each authority to its leader rank, for every round (round = list index)
  var leader_ranks: List[int -> int]
  /// The round at which we reach Global Stabilization Time (GST)
  var GST_round: int
  /// The next available blockID
  var next_blockID: int

  /// A node will only add a block to its DAG if all its parents are in the DAG already
  pure def can_add(dag: DAG, block: StatementBlock): bool = {
    pure val b_round = block.reference.round
    if (b_round == 0) {
      true
    } else {
      pure val block_references_from_previous_round = dag
        .filter(b => b.reference.round == b_round - 1)
        .map(b => b.reference)
      and {
        // "A block is valid if (...) within the sequence of past blocks, there are 2f + 1 blocks
        // from the previous round r − 1".
        // For now we only allow blocks in block.parents to be from the previous round r - 1
        block.parents.map(p => p.authority).size() >= 2 * FAULTY + 1 or b_round == 1,
        block.parents.subseteq(block_references_from_previous_round)
      }
    }
  }

  /// Whether a block has received a sufficient number of blocks for a round.
  /// Since we need 2F + 1 supporters on the consensus algorithm, the block needs to have
  /// least that number of blocks to start processing a new round.
  pure def has_enough_blocks(dag: DAG, round: int): bool = {
    dag.filter(b => b.reference.round == round).map(b => b.reference.authority).size() >= 2 * FAULTY + 1
  }

  /// All correct nodes have a block for this round in the DAG
  pure def stabilized(dag: DAG, round: int): bool = {
    CORRECT_NODES.subseteq(
      dag.filter(b => b.reference.round == round).map(b => b.reference.authority)
    )
  }

  /// Add the block to the DAG if possible, otherwise add to the backlog and retry later
  pure def receive_block(node: NodeState, block: StatementBlock): NodeState = {
    if (can_add(node.dag, block)) {
      { ...node, dag: node.dag.union(Set(block)) }
    } else {
      { ...node, backlog: node.backlog.union(Set(block)) }
    }
  }

  /// Receive blocks that couldn't be received before and were stored to the backlog
  pure def consume_backlog(node: NodeState): NodeState = {
    pure val highest_backlog_round = node.backlog.map(b => b.reference.round).fold(0, max)

    // Incrementally add blocks, starting from lowest rounds
    pure val new_dag = range(0, highest_backlog_round + 1).foldl(node.dag, (updated_dag, r) => {
      pure val to_add = node.backlog.filter(b => b.reference.round == r and can_add(updated_dag, b))
      updated_dag.union(to_add)
    })

    { ...node, dag: new_dag, backlog: node.backlog.exclude(new_dag) }
  }

  /// Broadcasts a message with a new block
  pure def send_correct_message(states: int -> NodeState, block: StatementBlock): int -> NodeState = {
    states.keys().fold(states, (acc, authority) => {
      acc.setBy(authority, s => { ...s, incoming_messages: s.incoming_messages.union(Set(block)) })
    })
  }

  /// Whether a node is ready to propose a new block in a new round.
  /// Always true for the first round (zero)
  /// If we reached GST, then we need to check if the DAG is stabilized
  /// Otherwise, we check if the node has enough blocks for the round it is in
  def can_go_to_new_round(node: NodeState): bool = {
    node.current_round == 0 or if (GST) {
      stabilized(node.dag, node.current_round)
    } else {
      has_enough_blocks(node.dag, node.current_round)
    }
  }

  action new_round(auth: int): bool = all {
    pending_nodes == Set(),
    can_go_to_new_round(nodes.get(auth)),
    
    val node = nodes.get(auth)
    all {
      val updated_nodes = nodes.setBy(node.authority, n => { ...n, current_round: node.current_round + 1 })
      val new_block = {
          reference: {
            authority: node.authority,
            round: node.current_round + 1,
            blockID: next_blockID,
          },
          parents: node.dag.filter(b => b.reference.round == node.current_round).map(b => b.reference)
      }
      all {
        elect_leaders(new_block.reference.round),
        nodes' = send_correct_message(updated_nodes, new_block),
        GST_round' = GST_round,
        next_blockID' = next_blockID + 1
      }
    }
  }

  /// A set of possible leader ranks for a round. That is, a maping from authorities to ranks,
  /// where all ranks are different
  pure val possible_leader_ranks =
    NODES.setOfMaps(0.to(NODES.size()-1)).filter(m => m.values().size() == NODES.size())

  action elect_leaders(round) = {
    if (round > leader_ranks.length()) {
      nondet new_leader_ranks = possible_leader_ranks.oneOf()
      leader_ranks' = leader_ranks.append(new_leader_ranks)
    } else {
      // Already elected leaders for this round (saved to leader_ranks[round - 1])
      leader_ranks' = leader_ranks
    }
  }

  val GST = CORRECT_NODES.forall(auth => nodes.get(auth).current_round >= GST_round)

  val pending_nodes = nodes.values().filter(node => {
    node.incoming_messages != Set() or (node.backlog != Set() and consume_backlog(node) != node)
  })

  val nodes_that_can_go_to_new_round = nodes.values().filter(can_go_to_new_round)


  action receive_message(auth: int): bool = all {
    pending_nodes.contains(nodes.get(auth)),

    val node = nodes.get(auth)
    if (node.incoming_messages != Set()) {
        nondet block = node.incoming_messages.oneOf()
        nodes' = nodes
          .set(node.authority, { ...receive_block(node, block), incoming_messages: node.incoming_messages.exclude(Set(block)) })
      } else {
        nodes' = nodes.setBy(node.authority, n => consume_backlog(n))
      },
    leader_ranks' = leader_ranks,
    GST_round' = GST_round,
    next_blockID' = next_blockID
  }


  /// Sends a valid block with new blockID to the destination. When called multiple times for the same 
  /// auth and round blocks with different blockID are set, i.e., node auth equivocates.
  action send_byzantine_block(auth: int, round: int, dest: int): bool = all {
    not(CORRECT_NODES.contains(auth)),
    
    val node_dest = nodes.get(dest)
    // We build a block with set of ancestors tailored to the receiving peer's current dag
    val tailored_block = {
      reference: {
          authority: auth,
          round: round,
          blockID: next_blockID,
        },
        parents: node_dest.dag
          .filter(b => b.reference.round == round - 1)
          .map(b => b.reference),
    }
    all {
      tailored_block.parents.map(p => p.authority).size() >= 2 * FAULTY + 1 or tailored_block.reference.round == 1,
      leader_ranks' = leader_ranks,
      nodes' = nodes.setBy(dest, s => { ...s, incoming_messages: s.incoming_messages.union(Set(tailored_block))}),
      GST_round' = GST_round,
      next_blockID' = next_blockID + 1
    }
  }

  action receive_all_messages(auth: int): bool = all {
    pending_nodes.contains(nodes.get(auth)),

    val node = nodes.get(auth)
    val after_receiving = node.incoming_messages.fold(
      { ...node, incoming_messages: Set() },
      (n, block) => receive_block(n, block)
    )
    nodes' = nodes.set(node.authority, consume_backlog(after_receiving)),
    leader_ranks' = leader_ranks,
    GST_round' = GST_round,
    next_blockID' = next_blockID
  }

  action all_nodes_receive_all_messages: bool = all {
    pending_nodes != Set(),                                                     
    nodes' = nodes.transformValues(node => {
      val after_receiving = node.incoming_messages.fold(                        
        { ...node, incoming_messages: Set() },                                
        (n, block) => receive_block(n, block)                                   
      )                                                                       
      consume_backlog(after_receiving)
    }),                                                                         
    leader_ranks' = leader_ranks,
    GST_round' = GST_round,                                                     
    next_blockID' = next_blockID                                              
  }

  action init_no_GST = all {
    nodes' = NODES.mapBy(n => {
      authority: n,
      dag: Set(),
      backlog: Set(),
      current_round: 0,
      incoming_messages: Set()
    }),
    nondet leader_ranks_0 = possible_leader_ranks.oneOf()
    leader_ranks' = [leader_ranks_0],
    GST_round' = 1000,
    next_blockID' = 0
  }

    action init = all {
    nodes' = NODES.mapBy(n => {
      authority: n,
      dag: Set(),
      backlog: Set(),
      current_round: 0,
      incoming_messages: Set()
    }),
    nondet leader_ranks_0 = possible_leader_ranks.oneOf()
    leader_ranks' = [leader_ranks_0],
    nondet round_GST = 1.to(5).oneOf()
    GST_round' = round_GST,
    next_blockID' = 0
  }

  // 1 (nondet) authority can receive 1 (nondet) incoming message
  action micro_step = {
    nondet authority = NODES.oneOf()
    nondet round = 1.to(leader_ranks.length()).oneOf()
    nondet dest = NODES.oneOf()
    any {
      receive_message(authority),
      new_round(authority),
      send_byzantine_block(authority, round, dest)
    }
  }

  // 1 (nondet) authority can receive all of its incoming messages
  action short_step = {
    nondet authority = NODES.oneOf()
    nondet round = 1.to(leader_ranks.length()).oneOf()
    nondet dest = NODES.oneOf()
    any {
      receive_all_messages(authority),
      new_round(authority),
      send_byzantine_block(authority, round, dest)
    }
  }

  // All authorities receive all of their incoming messages
  action step = {
    nondet authority = NODES.oneOf()
    nondet round = 1.to(leader_ranks.length()).oneOf()
    nondet dest = NODES.oneOf()
    any {
      all_nodes_receive_all_messages,
      new_round(authority),
      send_byzantine_block(authority, round, dest)
    }
  }

  /// Witness to check if we are progressing often enough
  val witness = nodes.values().forall(n => not(n.dag.exists(b => b.reference.round > 5)))
}

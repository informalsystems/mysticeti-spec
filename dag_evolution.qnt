// -*- mode: Bluespec; -*-

module dag_evolution {
  import basicSpells.* from "./spells/basicSpells"

  type BlockReference = { authority: int, round: int, index: int, leader_rank: int }
  type StatementBlock = { reference: BlockReference, parents: Set[BlockReference] }

  type DAG = Set[StatementBlock]

  pure val NUM_NODES = 4
  pure val NUM_FAULTY = 1
  pure val CORRECT = Set(0, 1, 2)
  pure val NODES = CORRECT.union(Set(3))

  type NodeState = {
    authority: int,
    leader_rank: int,
    dag: DAG,
    backlog: Set[StatementBlock],
    current_round: int,
    incoming_messages: Set[StatementBlock]
  }

  var nodes: int -> NodeState
  var GST: bool

  pure def can_add(dag: DAG, block: StatementBlock): bool = {
    pure val b_round = block.reference.round
    if (b_round == 0) {
      true
    } else {
      pure val block_references_from_previous_round = dag.filter(b => b.reference.round == b_round - 1).map(b => b.reference)
      block.parents.subseteq(block_references_from_previous_round)
    }
  }

  pure def has_enough_certificates(dag: DAG, round: int): bool = {
    dag.filter(b => b.reference.round == round).size() >= 2*NUM_FAULTY + 1
  }

  pure def stabilized(dag: DAG, round: int): bool = {
    CORRECT.subseteq(
      dag.filter(b => b.reference.round == round).map(b => b.reference.authority)
    )
  }

  pure def receive_block(node: NodeState, block: StatementBlock): NodeState = {
    if (can_add(node.dag, block)) {
      { ...node, dag: node.dag.union(Set(block)) }
    } else {
      { ...node, backlog: node.backlog.union(Set(block)) }
    }
  }

  pure def consume_backlog(node: NodeState): NodeState = {
    pure val highest_round = node.dag.map(b => b.reference.round).fold(0, (highest, element) => if (element > highest) element else highest)
    pure val new_dag = range(0, highest_round).foldl(node.dag, (updated_dag, r) => {
      pure val to_add = updated_dag.filter(b => b.reference.round == r and can_add(node.dag, b))
      updated_dag.union(to_add)
    })
    {
      ...node,
      dag: new_dag,
      backlog: node.backlog.exclude(new_dag)
    }
  }

  pure def send_correct_message(states: int -> NodeState, block: StatementBlock): int -> NodeState = {
    states.keys().fold(states, (acc, authority) => {
      acc.setBy(authority, s => { ...s, incoming_messages: s.incoming_messages.union(Set(block)) })
    })
  }

  pure def send_byzantine_message(
    states: int -> NodeState,
    block: StatementBlock,
    random: int -> int,
    drops_links: int -> bool,
    drops_all: int -> bool
  ): int -> NodeState = {
    states.keys().fold(states, (acc, auth) => {
      if (drops_all.get(auth)) {
        // drop whole message
        acc        
      } else if (drops_links.get(auth)) {
        // parent list dropped, messages potentially corrupted
        pure val byzblock = {
          reference: { ...block.reference, index: random.get(auth)},
          parents: Set()
        }
        acc.setBy(auth, s => { ...s, incoming_messages: s.incoming_messages.union(Set(byzblock)) })     
      } else {
        // parent list dropped, messages potentially corrupted, 0 means correct
        pure val byzblock = {
          reference: { ...block.reference, index: random.get(auth) },
          parents: block.parents
        }
        acc.setBy(auth, s => { ...s, incoming_messages: s.incoming_messages.union(Set(byzblock)) })     
      }
    })
  }

  def can_go_to_new_round(node: NodeState): bool = {
    node.current_round == 0 or if (GST) {
      stabilized(node.dag, node.current_round)
    } else {
      has_enough_certificates(node.dag, node.current_round)
    }
  }

  action new_round(node: NodeState): bool = all {
    can_go_to_new_round(node),
    val updated_nodes = nodes.setBy(node.authority, n => { ...n, current_round: node.current_round + 1 })
    val new_block = {
        reference: {
          authority: node.authority,
          leader_rank: node.leader_rank,
          round: node.current_round + 1,
          index: 0,
        },
        parents: node.dag.filter(b => b.reference.round == node.current_round).map(b => b.reference)
    }
    if (CORRECT.contains(node.authority))
      nodes' = send_correct_message(updated_nodes, new_block)
    else
      nondet random = NODES.setOfMaps(Set(0,1,2,3)).oneOf() 
      nondet drops_links = NODES.setOfMaps(Set(true,false)).oneOf()
      nondet drops_all = NODES.setOfMaps(Set(true,false)).oneOf()
      nodes' = send_byzantine_message(updated_nodes, new_block, random, drops_links, drops_all)
  }

  action init = all {
    nodes' = NODES.mapBy(n => {
      authority: n,
      leader_rank: n, // TODO pick leader every round
      dag: Set(),
      backlog: Set(),
      current_round: 0,
      incoming_messages: Set()
    }),
    GST' = false,
  }

  val pending_nodes = nodes.values().filter(node => {
    node.incoming_messages != Set() or (node.backlog != Set() and consume_backlog(node) != node)
  })

  val nodes_that_can_go_to_new_round = nodes.values().filter(can_go_to_new_round)

  action step = {
    if (pending_nodes != Set()) all {
      nondet node = pending_nodes.oneOf()
      if (node.incoming_messages != Set()) {
        nondet block = node.incoming_messages.oneOf()
        nodes' = nodes
          .set(node.authority, { ...receive_block(node, block), incoming_messages: node.incoming_messages.exclude(Set(block)) })
      } else {
        nodes' = nodes.setBy(node.authority, n => consume_backlog(n))
      },
      GST' = GST,
    } else if (nodes_that_can_go_to_new_round != Set()) all {
      nondet node = nodes_that_can_go_to_new_round.oneOf()
      new_round(node),
      GST' = GST,
    } else all {
      GST == false,
      nodes' = nodes,
      GST' = true
    }
  }

  val witness = nodes.values().forall(n => not(n.dag.exists(b => b.reference.round > 5)))
}

module dag_evolution {
  import basicSpells.* from "./spells/basicSpells"

  type BlockReference = { authority: int, round: int, index: int }
  type StatementBlock = { reference: BlockReference, parents: Set[BlockReference] }

  type DAG = Set[StatementBlock]

  pure val NUM_OF_PROPOSERS = 4
  pure val FAULTY = 1
  pure val CORRECT = Set(0, 1, 2)

  pure def can_add(dag: DAG, block: StatementBlock): bool = {
    pure val b_round = block.reference.round
    if (b_round == 0) {
      true
    } else {
      pure val block_references_from_previous_round = dag.filter(b => b.reference.round == b_round - 1).map(b => b.reference)
      block.parents.subseteq(block_references_from_previous_round)
    }
  }

  // we can assume that our own block is always included
  pure def has_enough_certificates(dag: DAG, round: int): bool = {
    dag.filter(b => b.reference.round == round).size() >= 2*FAULTY + 1
  }

  pure def stabilized(dag: DAG, round: int): bool = {
    CORRECT.subseteq(
      dag.filter(b => b.reference.round == round).map(b => b.reference.authority)
    )
  }

  type NodeState = {
    authority: int,
    dag: DAG,
    backlog: Set[StatementBlock],
    current_round: int,
    incoming_messages: Set[StatementBlock]
  }

  var nodes: int -> NodeState
  var GST: bool

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
      if (authority == block.reference.authority)
        acc
      else
        acc.setBy(authority, s => { ...s, incoming_messages: s.incoming_messages.union(Set(block)) })
    })
  }

  pure def send_byzantine_message(states: int -> NodeState, blocks: Set[StatementBlock]): int -> NodeState = {
    // TODO: good luck
  }

  action new_round(node: NodeState): bool = all {
    if (GST) {
      stabilized(node.dag, node.current_round)
    } else {
      has_enough_certificates(node.dag, node.current_round)
    },
    val updated_nodes = nodes.setBy(node.authority, n => { ...n, current_round: node.current_round + 1 })
    if (CORRECT.contains(node.authority))
      val new_block = Set().oneOf() // TODO
      nodes' = send_correct_message(updated_nodes, new_block)
        .setBy(node.authority, n => { ...n, dag: node.dag.union(Set(new_block)) }),
    else
      nondet byzantine_blocks = Set().oneOf() // TODO
      nodes' = send_byzantine_message(updated_nodes, byzantine_blocks)
  }

  // action step = any {
  //   consume_backlog,
  //   receive_block,
  // }
}

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

  var dag: DAG
  var backlog: Set[StatementBlock]
  var current_round: int
  var GST: bool

  action receive_block(block: StatementBlock): bool = {
    if (can_add(dag, block)) all {
      dag' = dag.union(Set(block)),
      backlog' = backlog,
    } else all {
      backlog' = backlog.union(Set(block)),
      dag' = dag,
    }
  }

  action consume_backlog: bool = {
    val highest_round = dag.map(b => b.reference.round).fold(0, (highest, element) => if (element > highest) element else highest)
    val new_dag = range(0, highest_round).foldl(dag, (updated_dag, r) => {
      val to_add = updated_dag.filter(b => b.reference.round == r and can_add(dag, b))
      updated_dag.union(to_add)
    })
    all {
      dag' = new_dag,
      backlog' = backlog.exclude(new_dag)
    }
  }

  action new_round: bool = all {
    if (GST) {
      stabilized(dag, current_round)
    } else {
      has_enough_certificates(dag, current_round)
    },
    current_round' = current_round + 1,
    val new_block = {}
    all {
      dag' = dag.union(Set(new_block)),
      messages' = messages.union(Set(new_block))
    }
  }

  // action step = any {
  //   consume_backlog,
  //   receive_block,
  // }
}

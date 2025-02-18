module main {
  import basicSpells.* from "spells/basicSpells"
  import dag_evolution.* from "dag_evolution"
  import mysticeti_c.* from "mysticeti_c"
  import mysticeti_types.to_block_store from "mysticeti_c"

  pure def convert_reference(b) = {
      {
        authority: b.authority,
        round: b.round,
        label: "Generated",
        leader_rank: b.leader_rank,
      }
  }

  val dags_for_consensus = nodes.transformValues(node => {
    node.dag.map(b => {
      // Drop the "index" and add "label"
      reference: b.reference.convert_reference(),
      parents: b.parents.map(convert_reference),
    })
  })

  val inv = {
    val orders = dags_for_consensus.values().map(dag => commit_order(try_decide_all(dag.to_block_store())))
    // Lemma 7
    tuples(orders, orders).forall(((order1, order2)) => order1.length() <= order2.length() implies order1.isPrefixOf(order2))
  }
}

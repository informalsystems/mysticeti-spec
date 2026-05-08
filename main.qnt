// -*- mode: Bluespec; -*-

/**
 * A module to check invariants of the Mysticeti consensus algorithm [1] over an evolving DAG
 *
 * [1]: https://arxiv.org/pdf/2310.14821
 *
 * Gabriela Moreira, Informal Systems, 2025
 */
module main {
  import basicSpells.* from "spells/basicSpells"
  import dag_evolution.* from "dag_evolution"
  import mysticeti_c from "mysticeti_c"
  import mysticeti_types.to_block_store from "mysticeti_c"

  /// Function to convert a reference from the dag_evolution format to the mysticeti_c format
  /// by adding "label" and "blockID"
  def convert_reference(b) = {
      {
        authority: b.authority,
        round: b.round,
        label: "Generated",
        leader_rank: leader_ranks[b.round - 1].get(b.authority),
        blockID: b.blockID
      }
  }

  /// The nodes map with converted references, to be used in mysticeti_c operators
  val dags_for_consensus = nodes.transformValues(node => {
    node.dag.map(b => {
      reference: b.reference.convert_reference(),
      parents: b.parents.map(convert_reference),
    })
  })

  /// Lemma 7. All correct validators commit a consistent sequence of proposer
  /// blocks (i.e., the committed proposer sequence of one correct validator is
  /// a prefix of another’s).
  /// Theorem 1 (Total Order). MYSTICETI-C satisfies the total order property of
  /// Byzantine Atomic Broadcast. Theorem 1 follows directly from Lemma 7.
  val inv = {
    val orders = dags_for_consensus.values().map(dag => {
      mysticeti_c::commit_order(mysticeti_c::try_decide_all(dag.to_block_store()))
    })
    tuples(orders, orders).forall(((order1, order2)) => {
      order1.length() <= order2.length() implies order1.isPrefixOf(order2)
    })
  }

  run equivocationTest = {
  // This test passes for the following configuration:
  //  pure val FAULTY = 1
  //  pure val CORRECT_NODES = Set(2,3)
  //  pure val NODES = CORRECT_NODES.union(Set(0,1))

    val byz_1 = 0
    val byz_2 = 1
    val corr_1 = 2
    val corr_2 = 3

    init_no_GST
      // Correct nodes participate in round 1.
      .then(new_round(corr_1))
      .then(all_nodes_receive_all_messages)
      .then(new_round(corr_2))
      .then(all_nodes_receive_all_messages)
      // All correct nodes should be in round 1
      .expect(CORRECT_NODES.forall(n => nodes.get(n).current_round == 1))
      // Byz node 0 sends equivocating blocks to correct nodes 2 and 3
      // Signature: send_byzantine_block(auth: int, round: int, dest: int)
      .then(send_byzantine_block(byz_1,1,corr_1))
      .then(receive_all_messages(corr_1))
      .then(send_byzantine_block(byz_1,1,corr_2))
      // byz_1 equivocated: corr_1 and corr_2 have different blocks from byz_1 at round 1                                                                   
      .expect({
          val byz_block_1 = nodes.get(corr_1).dag.filter(b => b.reference.authority == byz_1 and b.reference.round == 1)
          val byz_block_2 = nodes.get(corr_2).dag.filter(b => b.reference.authority == byz_1 and b.reference.round == 1)                    
          byz_block_1 != byz_block_2
        })
      // Honest nodes move on to round 2
      // We need to call receive on all nodes because new_round(x) is a broadcast and the
      // precondition for new_round(x) is pending_nodes == Set()
      .then(all_nodes_receive_all_messages)
      .then(new_round(corr_1))
      .then(all_nodes_receive_all_messages)
      .then(new_round(corr_2))
      .then(all_nodes_receive_all_messages)
      // All correct nodes should be in round 2
      .expect(CORRECT_NODES.forall(n => nodes.get(n).current_round == 2))
      // Byz nodes try the equivocating blocks to be accepted sending supporting nodes at round 2
      .then(send_byzantine_block(byz_1,2,corr_1))
      .then(all_nodes_receive_all_messages)
      .then(send_byzantine_block(byz_1,2,corr_2))
      .then(all_nodes_receive_all_messages)
      .then(send_byzantine_block(byz_2,2,corr_1))
      .then(all_nodes_receive_all_messages)
      .then(send_byzantine_block(byz_2,2,corr_2))
      .then(all_nodes_receive_all_messages)
      // Honest nodes move on to round 3
      .then(new_round(corr_1))
      .then(all_nodes_receive_all_messages)
      .then(new_round(corr_2))
      .then(all_nodes_receive_all_messages)
      // All correct nodes should be in round 3
      .expect(CORRECT_NODES.forall(n => nodes.get(n).current_round == 3))
      // Byz nodes forge the certificates needed for deciding at round 1 by sending tailored blocks for round 3.
      .then(send_byzantine_block(byz_1,3,corr_1))
      .then(all_nodes_receive_all_messages)
      .then(send_byzantine_block(byz_1,3,corr_2))
      .then(all_nodes_receive_all_messages)
      .then(send_byzantine_block(byz_2,3,corr_1))
      .then(all_nodes_receive_all_messages)
      .then(send_byzantine_block(byz_2,3,corr_2))
      .then(all_nodes_receive_all_messages)
      // The safety invariant does not hold
      .expect(not(inv))
      // In particular, correct nodes committed different blocks
      .expect({
        val commit_list_corr1: List[BlockReference] = mysticeti_c::commit_order(mysticeti_c::try_decide_all(dags_for_consensus.get(corr_1).to_block_store()))
        val commit_list_corr2: List[BlockReference] = mysticeti_c::commit_order(mysticeti_c::try_decide_all(dags_for_consensus.get(corr_2).to_block_store()))

        val committed_block_1 = commit_list_corr1.select(b => b.authority == byz_1 and b.round == 1)
        val committed_block_2 = commit_list_corr2.select(b => b.authority == byz_1 and b.round == 1)

        committed_block_1 != committed_block_2
      })
  }
}
// -*- mode: Bluespec; -*-

module mysticeti_c {
  import basicSpells.* from "./spells/basicSpells"
  import rareSpells.* from "./spells/rareSpells"

  type Validator = int
  type Round = int

  type ProposerSlot = (Validator, Round)
  type ProposerSlotState = Commit | Skip | Undecided
  type Decision = { status: ProposerSlotState, block: BlockReference, log: Log }
  type BlockWithState = { block: StatementBlock, state: ProposerSlotState }
  type Log = IncompleteWave | DirectDecision | IndirectDecision(BlockReference) | Error | UnableToDecide

  type BlockReference = { authority: int, round: Round, label: str, leader_rank: int }
  type StatementBlock = { reference: BlockReference, includes: Set[BlockReference] }

  type BlockStore = { blocks: Round -> Validator -> StatementBlock, highest_round: Round }

  type DirectDecider = { block_store: BlockStore, wave_length: int, round_offset: int, proposer_offset: int }

  pure val WAVE_LENGTH = 3
  pure val ROUND_OFFSET = 0
  pure val VALIDATORS = Set("A0", "A1", "A2", "A3")
  pure val NUM_OF_PROPOSERS = 4
  pure val FAULTY = 1

  pure val L1a = { authority: 0, round: 0, label: "L1a", leader_rank: 0 }
  pure val L1b = { authority: 1, round: 0, label: "L1b", leader_rank: 1 }
  pure val L1c = { authority: 2, round: 0, label: "L1c", leader_rank: 2 }
  pure val L1d = { authority: 3, round: 0, label: "L1d", leader_rank: 3 }
  pure val L2d = { authority: 0, round: 1, label: "L2d", leader_rank: 3 }
  pure val L2a = { authority: 1, round: 1, label: "L2a", leader_rank: 0 }
  pure val L2b = { authority: 2, round: 1, label: "L2b", leader_rank: 1 }
  pure val L2c = { authority: 3, round: 1, label: "L2c", leader_rank: 2 }
  pure val L3c = { authority: 0, round: 2, label: "L3c", leader_rank: 2 }
  pure val L3d = { authority: 1, round: 2, label: "L3d", leader_rank: 3 }
  pure val L3b = { authority: 3, round: 2, label: "L3b", leader_rank: 1 }
  pure val L4d = { authority: 0, round: 3, label: "L4d", leader_rank: 3 }
  pure val L4a = { authority: 1, round: 3, label: "L4a", leader_rank: 0 }
  pure val L4b = { authority: 2, round: 3, label: "L4b", leader_rank: 1 }
  pure val L4c = { authority: 3, round: 3, label: "L4c", leader_rank: 2 }
  pure val L5c = { authority: 0, round: 4, label: "L5c", leader_rank: 2 }
  pure val L5d = { authority: 1, round: 4, label: "L5d", leader_rank: 3 }
  pure val L5a = { authority: 2, round: 4, label: "L5a", leader_rank: 0 }
  pure val L5b = { authority: 3, round: 4, label: "L5b", leader_rank: 1 }
  pure val L6b = { authority: 0, round: 5, label: "L6b", leader_rank: 1 }
  pure val L6c = { authority: 1, round: 5, label: "L6c", leader_rank: 2 }
  pure val L6d = { authority: 2, round: 5, label: "L6d", leader_rank: 3 }

  pure val DAG = Set(
    { reference: L1a, includes: Set() },
    { reference: L1b, includes: Set() },
    { reference: L1c, includes: Set() },
    { reference: L1d, includes: Set() },
    { reference: L2d, includes: Set(L1a, L1b, L1c) },
    { reference: L2a, includes: Set(L1a, L1b, L1d) },
    { reference: L2b, includes: Set(L1a, L1c, L1d) },
    { reference: L2c, includes: Set(L1a, L1c, L1d) },
    { reference: L3c, includes: Set(L2d, L2a, L2b) },
    { reference: L3d, includes: Set(L2d, L2a, L2c) },
    { reference: L3b, includes: Set(L2d, L2a, L2b, L2c) },
    { reference: L4d, includes: Set(L3c, L3d, L3b) },
    { reference: L4a, includes: Set(L3c, L3d, L3b) },
    { reference: L4b, includes: Set(L3c, L3d, L3b) },
    { reference: L4c, includes: Set(L3c, L3d, L3b) },
    { reference: L5c, includes: Set(L4d, L4b, L4c) },
    { reference: L5d, includes: Set(L4d, L4a, L4b, L4c) },
    { reference: L5a, includes: Set(L4d, L4b, L4c) },
    { reference: L5b, includes: Set(L4d, L4b, L4c) },
    { reference: L6b, includes: Set(L5c, L5d, L5a, L5b) },
    { reference: L6c, includes: Set(L5d, L5a, L5b) },
    { reference: L6d, includes: Set(L5d, L5a, L5b) }
  )

  pure def parents(store: BlockStore, block: StatementBlock): Set[StatementBlock] = {
    pure val potential_parents = store.blocks_by_round(block.reference.round + 1)
    potential_parents.filter(parent => block.includes.contains(parent.reference))
  }

  pure def link(store: BlockStore, later_block: StatementBlock, earlier_block: StatementBlock): bool = {
    val linked_to_later = range(earlier_block.reference.round, later_block.reference.round).foldl(Set(later_block), (parents, r) => {
      val blocks = store.blocks_by_round(r)
      blocks.filter(block => parents.exists(parent => parent.includes.contains(block.reference)))
    })

    linked_to_later.contains(earlier_block)
  }

  pure def direct_decider(block_store: BlockStore, wave_length: int, round_offset: int, proposer_offset: int): DirectDecider = {
    { block_store: block_store, wave_length: wave_length, round_offset: round_offset, proposer_offset: proposer_offset }
  }

  pure def wave_number(d: DirectDecider, round: Round): int = {
    (round - d.round_offset) / d.wave_length
  }

  pure def proposer_round(d: DirectDecider, w: int): int = {
    w * d.wave_length + d.round_offset
  }

  pure def decision_round(d: DirectDecider, w: int): int = {
    w * d.wave_length + d.wave_length - 1 + d.round_offset - 1
  }

  // FIXME: I don't understand what this should be from the paper
  // pure def get_predefined_proposer(d: DirectDecider, w: int): Validator = {
  //   pure val r_proposer = d.proposer_round(w)
  //   VALIDATORS[r_proposer % NUM_OF_PROPOSERS]
  // }

  pure def block_by_reference(d: DirectDecider, reference: BlockReference): StatementBlock = {
    d.block_store.blocks.get(reference.round).get(reference.authority)
  }

  pure def blocks_by_round(b: BlockStore, round: Round): Set[StatementBlock] = {
    b.blocks.getOrElse(round, Map()).values()
  }

  pure def get_proposer_block(d: DirectDecider, w: int): StatementBlock = {
    pure val r_proposer = d.proposer_round(w)
    d.block_store.blocks.get(r_proposer).get(d.proposer_offset)
  }

  pure def get_first_voting_blocks(d: DirectDecider, w: int): Set[StatementBlock] = {
    pure val r_voting = d.proposer_round(w) + 1
    d.block_store.blocks_by_round(r_voting)
  }

  pure def get_decision_blocks(d: DirectDecider, w: int): Set[StatementBlock] = {
    pure val r_decision = d.decision_round(w)
    d.block_store.blocks_by_round(r_decision)
  }

  pure def is_vote(d: DirectDecider, block: StatementBlock, proposer_block: StatementBlock): bool = {
    // The paper describes this as a DFS search starting from block, but from
    // the overall explanation, I can't understand why it is not simply a check
    // for the existence of a link between the blocks
    d.block_store.link(block, proposer_block)
  }

  pure def is_cert(d: DirectDecider, block: StatementBlock, proposer_block: StatementBlock): bool = {
    d.block_store.parents(block).filter(b => d.is_vote(b, proposer_block)).size() >= 2*FAULTY + 1
  }

  pure def skipped_proposer(d: DirectDecider, w: int): bool = {
    pure val r_proposer = d.proposer_round(w)
    // pure val id = d.get_predefined_proposer(w) // mistake on pseudocode here?
    pure val id = (d.proposer_offset, r_proposer)
    pure val blocks = d.get_first_voting_blocks(w)
    // pure val non_supporters = blocks.filter(block => not(d.block_store.parents(block).exists(parent => (parent.reference.authority, parent.reference.round) == id)))
    pure val non_supporters = blocks.filter(block => not(block.includes.exists(child => (child.authority, child.round) == id)))
    non_supporters.size() >= 2*FAULTY + 1
  }

  pure def supported_proposer(d: DirectDecider, w: int): Option[StatementBlock] = {
    pure val b_proposer = q::debug("b_proposer", d.get_proposer_block(w))
    pure val blocks = d.get_decision_blocks(w)
    pure val supporters = blocks.filter(block => d.is_vote(block, b_proposer))
    if (supporters.size() >= 2*FAULTY + 1) {
      Some(b_proposer)
    } else {
      None
    }
  }

  pure def certified_link(d: DirectDecider, b_anchor: StatementBlock, b_proposer: StatementBlock): bool = {
    pure val w = d.wave_number(b_proposer.reference.round)
    pure val blocks = d.get_decision_blocks(w)
    blocks.exists(block => d.is_cert(block, b_proposer) and d.block_store.link(block, b_anchor))
  }

  pure def try_direct_decide(d: DirectDecider, w: int): Decision = {
    pure val status = if (d.skipped_proposer(w)) {
      Skip
    } else {
      pure val b_proposer = d.supported_proposer(w)
      match b_proposer {
        | None => Undecided
        | Some(_) => Commit
      }
    }
    pure val block = d.get_proposer_block(w)
    { status: status, block: block.reference, log: DirectDecision }
  }

  pure def try_indirect_decide(d: DirectDecider, w: int, sequence: List[Decision]): Decision = {
    // The paper uses the decision round in the pseudocode, but the text always mentions r' > r + 2.
    // I couldn't make it work it the decision round, but r' > r + 2 works.
    pure val r_proposer = d.proposer_round(w)
    pure val b_proposer = d.get_proposer_block(w)
    pure val anchors = sequence.select(s => s.block.round == r_proposer + 3).toSet().toList((s1, s2) => intCompare(s1.block.leader_rank, s2.block.leader_rank))

    // FIXME: define and use a `first` operator?
    pure val result = anchors.foldl(None, (res, a) => {
      if (res != None) {
        res
      } else {
        match a.status {
          | Undecided => Some({ status: Undecided, block: b_proposer.reference, log: IndirectDecision(a.block) })
          | Commit => {
            pure val b_anchor = d.block_by_reference(a.block)
            pure val status = if (d.certified_link(b_anchor, b_proposer)) {
              Commit
            } else {
              Skip
            }
            Some({ status: status, block: b_proposer.reference, log: IndirectDecision(b_anchor.reference) })
          }
          | Skip => res
        }
       }
     })

    match result {
      | None => { status: Undecided, block: b_proposer.reference, log: UnableToDecide }
      | Some(s) => s
    }
  }

  pure def try_decide(block_store, sequence, r, l) = {
    pure val i = r % WAVE_LENGTH
    pure val c = direct_decider(block_store, WAVE_LENGTH, i, l)
    pure val w = c.wave_number(r)
    pure val proposer_block = c.get_proposer_block(w)
    if (r > block_store.highest_round - 2) {
      ([{ status: Undecided, block: proposer_block.reference, log: IncompleteWave }].concat(sequence))
    } else {
      if (c.proposer_round(w) != r) {
         sequence
      } else {
        pure val direct_status = c.try_direct_decide(w)
        pure val status = if (direct_status.status == Undecided) {
          c.try_indirect_decide(w, sequence)
        } else {
          direct_status
        }
        ([status].concat(sequence))
      }
    }

    // FIXME: Move this to step so it is only done after all iterations of try_decide
    // if (l == 0) {
    //   pure val result = status_sequence.foldl(([], false), (acc, status) => {
    //     // TODO: write a take while spell or something
    //     if (status.status == Undecided or acc._2) {
    //       (acc._1, true)
    //     } else {
    //       ((acc._1).append(status), false)
    //     }
    //   })

    //   result._1
    // } else {
    //   status_sequence
    // }
  }

  var dag: Set[BlockWithState]
  var result: List[Decision]
  var round_to_process: int
  var validator_to_process: int

  action init = all {
    dag' = DAG.map(block => { block: block, state: Undecided }),
    result' = [],
    round_to_process' = 5,
    validator_to_process' = NUM_OF_PROPOSERS - 1
  }

  action step =
    val block_store = { blocks: DAG.fold(Map(), (m, block) => if (m.has(block.reference.round)) m.setBy(block.reference.round, row => row.put(block.reference.authority, block)) else m.put(block.reference.round, Map(block.reference.authority -> block))), highest_round: 5 }
    val new_result = if (block_store.blocks.get(round_to_process).has(validator_to_process)) {
      try_decide(block_store, result, round_to_process, validator_to_process)
    } else {
      result
    }
    all {
      round_to_process >= 0,
      dag' = DAG.map(block => { block: block, state: find_state(new_result, block.reference).status }),
      result' = new_result,
      round_to_process' = if (validator_to_process == 0) round_to_process - 1 else round_to_process,
      validator_to_process' = if (validator_to_process == 0) NUM_OF_PROPOSERS - 1 else validator_to_process - 1,
    }

  pure def find_state(result: List[Decision], block: BlockReference): Decision = {
    // FIXME: replace with find
    pure val default = { status: Undecided, block: block, log: Error }
    result.foldl(default, (state, res) => {
      if (res.block == block) {
        res
      } else {
        state
      }
    })
  }
}

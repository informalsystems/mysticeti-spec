module mysticeti_c {
  import basicSpells.* from "./spells/basicSpells"

  type Validator = int
  type Round = int

  type ProposerSlot = (Validator, Round) // option?
  type ProposerSlotState = Commit(ProposerSlot) | Skip(int) | Undecided

  type BlockReference = { authority: int, round: Round, label: str }
  type StatementBlock = { reference: BlockReference, includes: Set[BlockReference] }

  type BlockStore = { blocks_by_round: Round -> Set[StatementBlock], highest_round: Round }

  type DirectDecider = { block_store: BlockStore, wave_length: int, round_offset: int, proposer_offset: int }

  pure val WAVE_LENGTH = 3
  pure val ROUND_OFFSET = 0
  pure val VALIDATORS = Set("A0", "A1", "A2", "A3")
  pure val NUM_OF_PROPOSERS = 2

  pure val L1a = { authority: 0, round: 1, label: "L1a" }
  pure val L1b = { authority: 1, round: 1, label: "L1b" }
  pure val L1c = { authority: 2, round: 1, label: "L1c" }
  pure val L1d = { authority: 3, round: 1, label: "L1d" }
  pure val L2a = { authority: 0, round: 2, label: "L2a" }
  pure val L2b = { authority: 1, round: 2, label: "L2b" }
  pure val L2c = { authority: 2, round: 2, label: "L2c" }
  pure val L2d = { authority: 3, round: 2, label: "L2d" }
  pure val L3c = { authority: 0, round: 3, label: "L3c" }
  pure val L3d = { authority: 1, round: 3, label: "L3d" }
  pure val L3b = { authority: 3, round: 3, label: "L3b" }
  pure val L4d = { authority: 0, round: 4, label: "L4d" }
  pure val L4a = { authority: 1, round: 4, label: "L4a" }
  pure val L4b = { authority: 2, round: 4, label: "L4b" }
  pure val L4c = { authority: 3, round: 4, label: "L4c" }
  pure val L5c = { authority: 0, round: 5, label: "L5c" }
  pure val L5d = { authority: 1, round: 5, label: "L5d" }
  pure val L5a = { authority: 2, round: 5, label: "L5a" }
  pure val L5b = { authority: 3, round: 5, label: "L5b" }
  pure val L6b = { authority: 0, round: 6, label: "L6b" }
  pure val L6c = { authority: 1, round: 6, label: "L6c" }
  pure val L6d = { authority: 2, round: 6, label: "L6d" }

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
    pure val potential_parents = store.blocks_by_round.getOrElse(block.reference.round + 1, Set())
    potential_parents.filter(parent => block.includes.contains(parent.reference))
  }

  pure def link(store: BlockStore, later_block: StatementBlock, earlier_block: StatementBlock): bool = {
    val linked_to_later = range(earlier_block.reference.round, later_block.reference.round).foldl(Set(later_block), (parents, r) => {
      val blocks = store.blocks_by_round.get(r)
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
    w * d.wave_length + d.wave_length - 1 + d.round_offset
  }

  // FIXME: I don't understand what this should be from the paper
  // pure def get_predefined_proposer(d: DirectDecider, w: int): Validator = {
  //   pure val r_proposer = d.proposer_round(w)
  //   VALIDATORS[r_proposer % NUM_OF_PROPOSERS]
  // }

  pure def get_proposer_block(d: DirectDecider, w: int): Option[StatementBlock] = {
    pure val r_proposer = d.proposer_round(w)
    pure val id = (d.proposer_offset, r_proposer)
    d.block_store.blocks_by_round.get(r_proposer).find(block => (block.reference.authority, block.reference.round) == id)
  }

  pure def get_first_voting_blocks(d: DirectDecider, w: int): Set[StatementBlock] = {
    pure val r_voting = d.proposer_round(w) + 1
    d.block_store.blocks_by_round.get(r_voting)
  }

  pure def get_decision_blocks(d: DirectDecider, w: int): Set[StatementBlock] = {
    pure val r_decision = d.decision_round(w)
    d.block_store.blocks_by_round.get(r_decision)
  }

  pure def is_vote(d: DirectDecider, block: StatementBlock, proposer_block: StatementBlock): bool = {
    // FIXME: there is something related to ordering here, because we should only certify the first round.
    // perhaps the includes attribute needs to be a list. I'll use link for now because without the order factor, I think this may be the same
    d.block_store.link(proposer_block, block)
    // d.block_store.highest_round.to(proposer_block.reference.round).fold(None, (result, round) => {
    //   d.block_store.blocks_by_round.get(round).find(b => b.includes.contains(proposer_block.reference))
    // })
    // block.includes.contains(proposer_block.reference)
  }

  pure def is_cert(d: DirectDecider, block: StatementBlock, proposer_block: StatementBlock): bool = {
    d.block_store.parents(block).filter(b => d.is_vote(b, proposer_block)).size() >= 2*NUM_OF_PROPOSERS + 1
  }

  pure def skipped_proposer(d: DirectDecider, w: int): bool = {
    pure val r_proposer = d.proposer_round(w)
    // pure val id = d.get_predefined_proposer(w) // mistake on pseudocode here?
    pure val id = (d.proposer_offset, r_proposer)
    pure val blocks = d.get_first_voting_blocks(w)
    pure val non_supporters = blocks.filter(block => not(d.block_store.parents(block).exists(parent => (parent.reference.authority, parent.reference.round) == id)))
    non_supporters.size() >= 2*NUM_OF_PROPOSERS + 1
  }

  pure def supported_proposer(d: DirectDecider, w: int): Option[StatementBlock] = {
    pure val b_proposer = d.get_proposer_block(w)
    match b_proposer {
      | None => None
      | Some(proposed_block) => {
        pure val blocks = d.get_decision_blocks(w)
        pure val supporters = blocks.filter(block => d.is_cert(block, proposed_block))
        if (supporters.size() >= 2*NUM_OF_PROPOSERS + 1) {
          Some(proposed_block)
        } else {
          None
        }
      }
    }
  }

  pure def try_direct_decide(d: DirectDecider, w: int): ProposerSlotState = {
    if (d.skipped_proposer(w)) {
      Skip(w)
    } else {
      pure val b_proposer = d.supported_proposer(w)
      match b_proposer {
        | None => Undecided
        | Some(proposed_block) => Commit((proposed_block.reference.authority, proposed_block.reference.round))
      }
    }
  }

  pure def try_indirect_decide(d: DirectDecider, w: int): ProposerSlotState = {
    // TODO
    Undecided
  }

  pure def try_decide(block_store, r_committed, r_highest) = {
    pure val status_sequence = decreasing_range(r_highest, r_committed + 1).foldl([], (seq, r) => {
      decreasing_range(NUM_OF_PROPOSERS - 1, 0).foldl(seq, (sequence, l) => {
        pure val i = r % WAVE_LENGTH
        pure val c = direct_decider(block_store, WAVE_LENGTH, i, l)
        pure val w = c.wave_number(r)
        if (c.proposer_round(w) != r) {
           sequence
        } else {
          pure val direct_status = c.try_direct_decide(w)
          pure val status = (if (direct_status == Undecided) {
            c.try_indirect_decide(w)
          } else {
            direct_status
          })
          ([status].concat(sequence))
        }
      })
    })

    pure val result = status_sequence.foldl(([], false), (acc, status) => {
      // TODO: write a take while spell or something
      if (status == Undecided or acc._2) {
        (acc._1, true)
      } else {
        ((acc._1).append(status), false)
      }
    })

    result._1
  }

  type BlockWithState = { block: StatementBlock, state: ProposerSlotState }
  var dag: Set[BlockWithState]
  var result: List[ProposerSlotState]

  action init = all {
    dag' = DAG.map(block => { block: block, state: Undecided }),
    result' = [],
  }

  action step =
    val block_store = { blocks_by_round: 0.to(7).mapBy(round => DAG.filter(b => b.reference.round == round)), highest_round: 6 }
    all {
      dag' = DAG.map(block => { block: block, state: Undecided }),
      result' = try_decide(block_store, 0, 6),
    }

  pure def decreasing_range(start: int, end: int): List[int] = {
    range(end, start).foldl([], (acc, i) => {
      List(i).concat(acc)
    })
  }
}

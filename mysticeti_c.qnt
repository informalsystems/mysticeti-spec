// -*- mode: Bluespec; -*-

// This spec assumes wave lenght of three. Since there Quint doesn't allow
// recursion, it would not be trivial to generalize it for any wave length.

module mysticeti_c {
  import basicSpells.* from "./spells/basicSpells"
  import rareSpells.* from "./spells/rareSpells"

  import mysticeti_types.* from "./mysticeti_types"
  import watcher from "./watcher"

  pure val NUM_OF_PROPOSERS = 4
  pure val FAULTY = 1

  pure def should_skip(blocks: BlockStore, proposer_block: StatementBlock): bool = {
    pure val r_proposer = proposer_block.reference.round
    pure val next_round_blocks = blocks.by_round(r_proposer + 1)

    pure val non_supporters = next_round_blocks.filter(block => not(block.parents.exists(parent => parent == proposer_block.reference)))
    non_supporters.size() >= 2*FAULTY + 1
  }

  pure def has_certified_link(blocks: BlockStore, b_anchor: StatementBlock, b_proposer: StatementBlock): bool = {
    // The block has 2F + 1 children that are linked to the anchor
    pure val children_with_link = blocks.children_of(b_proposer).filter(b => blocks.is_link(b_anchor, b))
    // FIXME: This should actually be a certificate "grandparent"

    children_with_link.size() >= 2*FAULTY + 1
  }

  pure def try_direct_decide(blocks: BlockStore, proposer_block: StatementBlock): Decision = {
    // A certificate for a block in round r will be in r + 2, so we fetch the children of the children of the proposer_block
    pure val potential_certificates = blocks.children_of(proposer_block).map(b => blocks.children_of(b)).flatten()

    pure val certificates = potential_certificates.filter(c => {
      // A certificate should have at least 2F + 1 parents that support (link to) the proposer block.
      pure val parents_supporting_proposer = c.parents.filter(b => blocks.by_reference(b).parents.contains(proposer_block.reference))
      parents_supporting_proposer.size() >= 2*FAULTY + 1
    })

    pure val status = if (should_skip(blocks, proposer_block)) {
      Skip
    } else if (certificates.size() >= 2*FAULTY + 1) {
      Commit
    } else {
      Undecided
    }

    { status: status, block: proposer_block.reference, log: watcher::log_direct_decision(blocks, proposer_block, certificates) }
  }

  pure def try_indirect_decide(blocks: BlockStore, sequence: List[Decision], proposer_block: StatementBlock): Decision = {
    // The anchor will always be in the first round of the next wave
    pure val anchor_round = proposer_block.reference.round + 3
    // FIXME: we probably need to consider next rounds as well - blocks that are not there yet are undecided.
    pure val potential_anchors = sequence
      .select(s => s.block.round == anchor_round)
      // Anchors are sorted by their leadership rank
      .sortList((a, b) => a.block.leader_rank < b.block.leader_rank)

    pure val chosen_anchor = potential_anchors.findFirst(decision => {
      decision.status == Undecided or decision.status == Commit
    })

    match chosen_anchor {
      | None => { status: Undecided, block: proposer_block.reference, log: UnableToDecide }
      | Some(anchor) => {
        if (anchor.status == Undecided) {
          // Undecided anchor, undecided block
          { status: Undecided, block: proposer_block.reference, log: IndirectDecision({ anchor: anchor.block.label, edges: Set() }) }
        } else {
          // Anchor marked as commit, we have to check for the existence of a certified link between the anchor and the proposer block
          pure val b_anchor = blocks.by_reference(anchor.block)
          pure val status = if (blocks.has_certified_link(b_anchor, proposer_block)) {
            Commit
          } else {
            Skip
          }

          {
            status: status,
            block: proposer_block.reference,
            log: watcher::log_indirect_decision(blocks, proposer_block, b_anchor),
          }
        }
      }
    }
  }

  pure def try_decide_one(blocks: BlockStore, sequence: List[Decision], round: int, authority: int): List[Decision] = {
    pure val proposer_block = blocks.get(round).get(authority)
    pure val highest_round = blocks.keys().fold(0, (highest, element) => if (element > highest) element else highest)

    if (round > highest_round - 2) {
      // The wave is incomplete, we can not decide
      ([{ status: Undecided, block: proposer_block.reference, log: IncompleteWave }].concat(sequence))
    } else {
      pure val direct_decision = try_direct_decide(blocks, proposer_block)
      pure val decision = if (direct_decision.status != Undecided) {
        direct_decision
      } else {
        try_indirect_decide(blocks, sequence, proposer_block)
      }

      // Add the new decision to the head of the decision sequence
      ([decision].concat(sequence))
    }
  }

  pure def try_decide_all(blocks: BlockStore): List[Decision] = {
    pure val highest_round = blocks.keys().fold(0, (highest, element) => if (element > highest) element else highest)

    // FIXME: we don't have to run all the way to round 0 if there are commited rounds
    decreasingRange(highest_round, 0).foldl([], (sequence, round) => {
      decreasingRange(NUM_OF_PROPOSERS - 1, 0).foldl(sequence, (sequence, proposer) => {
        // There can be more than one block for (round, proposer)

        // We know the proposer index, but this refers to the leader rank. Find the authority for this rank.
        match blocks.getOrElse(round, Map()).values().find(b => b.reference.leader_rank == proposer) {
           | None => sequence
           | Some(block) => {
              try_decide_one(blocks, sequence, block.reference.round, block.reference.authority)
           }
         }
      })
    })
  }

  pure def commit_order(decisions: List[Decision]): List[BlockReference] = {
    decisions
      .takeWhile(decision => decision.status != Undecided)
      .select(decision => decision.status == Commit)
      .listMap(decision => decision.block)
  }
}

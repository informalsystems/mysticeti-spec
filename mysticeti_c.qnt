// -*- mode: Bluespec; -*-

// This spec assumes wave lenght of three. Since there Quint doesn't allow recursion, it would not be trivial to generalize it for any wave length.

module mysticeti_c {
  import basicSpells.* from "./spells/basicSpells"
  import rareSpells.* from "./spells/rareSpells"

  type Validator = int
  type Round = int

  type ProposerSlotState = Commit | Skip | Undecided
  type Decision = { status: ProposerSlotState, block: BlockReference, log: Log }
  type Edge = (str, str)
  type Log = IncompleteWave | DirectDecision(Set[Edge]) | IndirectDecision({ anchor: str, edges: Set[Edge] }) | Error | UnableToDecide

  type BlockReference = { authority: int, round: Round, label: str, leader_rank: int }
  type StatementBlock = { reference: BlockReference, children: Set[BlockReference] }

  type BlockStore = Round -> Validator -> StatementBlock

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
    { reference: L1a, children: Set() },
    { reference: L1b, children: Set() },
    { reference: L1c, children: Set() },
    { reference: L1d, children: Set() },
    { reference: L2d, children: Set(L1a, L1b, L1c) },
    { reference: L2a, children: Set(L1a, L1b, L1d) },
    { reference: L2b, children: Set(L1a, L1c, L1d) },
    { reference: L2c, children: Set(L1a, L1c, L1d) },
    { reference: L3c, children: Set(L2d, L2a, L2b) },
    { reference: L3d, children: Set(L2d, L2a, L2c) },
    { reference: L3b, children: Set(L2d, L2a, L2b, L2c) },
    { reference: L4d, children: Set(L3c, L3d, L3b) },
    { reference: L4a, children: Set(L3c, L3d, L3b) },
    { reference: L4b, children: Set(L3c, L3d, L3b) },
    { reference: L4c, children: Set(L3c, L3d, L3b) },
    { reference: L5c, children: Set(L4d, L4b, L4c) },
    { reference: L5d, children: Set(L4d, L4a, L4b, L4c) },
    { reference: L5a, children: Set(L4d, L4b, L4c) },
    { reference: L5b, children: Set(L4d, L4b, L4c) },
    { reference: L6b, children: Set(L5c, L5d, L5a, L5b) },
    { reference: L6c, children: Set(L5d, L5a, L5b) },
    { reference: L6d, children: Set(L5d, L5a, L5b) }
  )

  pure def parents_of(blocks: BlockStore, block: StatementBlock): Set[StatementBlock] = {
    pure val potential_parents = blocks.by_round(block.reference.round + 1)
    potential_parents.filter(parent => parent.children.contains(block.reference))
  }

  pure def is_link(blocks: BlockStore, later_block: StatementBlock, earlier_block: StatementBlock): bool = {
    val linked_to_earlier = range(earlier_block.reference.round + 1, later_block.reference.round + 1).foldl(Set(earlier_block), (linked_blocks, r) => {
      val r_blocks = blocks.by_round(r)
      linked_blocks.union(r_blocks.filter(block => linked_blocks.exists(b => block.children.contains(b.reference))))
    })

    linked_to_earlier.contains(later_block)
  }

  pure def last(v: List[a]): a = {
    v[v.length() - 1]
  }

  pure def link_edges(blocks: BlockStore, later_block: StatementBlock, earlier_block: StatementBlock): Set[Edge] = {
    val chains = range(earlier_block.reference.round + 1, later_block.reference.round + 1).foldl(Set([earlier_block]), (links, r) => {
      val r_blocks = blocks.by_round(r)
      links.map(l => {
        val linked_blocks = r_blocks.filter(block => block.children.contains(l.last().reference))
        linked_blocks.map(b => l.append(b))
      }).flatten()
    }).filter(c => c.last() == later_block)

    chains.map(c => range(0, c.length() - 1).foldl(Set(), (edges, i) => {
      val child = c[i]
      val parent = c[i + 1]
      edges.union(Set((child.reference.label, parent.reference.label)))
    })).flatten()
  }

  pure def by_reference(blocks: BlockStore, reference: BlockReference): StatementBlock = {
    blocks.get(reference.round).get(reference.authority)
  }

  pure def by_round(blocks: BlockStore, round: Round): Set[StatementBlock] = {
    blocks.getOrElse(round, Map()).values()
  }

  pure def skipped_proposer(blocks: BlockStore, proposer_block: StatementBlock): bool = {
    pure val r_proposer = proposer_block.reference.round
    pure val authority = proposer_block.reference.authority
    pure val id = (authority, r_proposer)
    pure val next_round_blocks = blocks.by_round(r_proposer + 1)

    pure val non_supporters = next_round_blocks.filter(block => not(block.children.exists(child => (child.authority, child.round) == id)))
    non_supporters.size() >= 2*FAULTY + 1
  }

  pure def edge(b1: StatementBlock, b2: StatementBlock): Edge = {
    (b1.reference.label, b2.reference.label)
  }

  pure def certified_link_edges(blocks: BlockStore, b_anchor: StatementBlock, b_proposer: StatementBlock): Set[Edge] = {
    pure val parents_with_link = blocks.parents_of(b_proposer).filter(b => blocks.is_link(b_anchor, b))
    parents_with_link.map(b => {
      Set(edge(b_proposer, b)).union(blocks.link_edges(b_anchor, b))
    }).flatten()
  }

  pure def has_certified_link(blocks: BlockStore, b_anchor: StatementBlock, b_proposer: StatementBlock): bool = {
    // The block has 2F + 1 parents that are linked to the anchor
    pure val parents_with_link = blocks.parents_of(b_proposer).filter(b => blocks.is_link(b_anchor, b))

    parents_with_link.size() >= 2*FAULTY + 1
  }

  pure def try_direct_decide(blocks: BlockStore, proposer_block: StatementBlock): Decision = {
    // A certificate for a block in round r will be in r + 2, so we fetch the parents of the parents of the proposer_block
    pure val potential_certificates = blocks.parents_of(proposer_block).map(b => blocks.parents_of(b)).flatten()

    pure val certificates = potential_certificates.filter(c => {
      // A certificate should have at least 2F + 1 children that support (link to) the proposer block.
      pure val children_supporting_proposer = c.children.filter(b => blocks.by_reference(b).children.contains(proposer_block.reference))
      children_supporting_proposer.size() >= 2*FAULTY + 1
    })

    pure val status = if (skipped_proposer(blocks, proposer_block)) {
      Skip
    } else if (certificates.size() >= 2*FAULTY + 1) {
      Commit
    } else {
      Undecided
    }

    pure val supporting_edges = certificates.map(c => blocks.link_edges(c, proposer_block)).flatten()
    { status: status, block: proposer_block.reference, log: DirectDecision(supporting_edges) }
  }

  pure def try_indirect_decide(blocks: BlockStore, sequence: List[Decision], proposer_block: StatementBlock): Decision = {
    // The anchor will always be in the first round of the next wave
    pure val anchor_round = proposer_block.reference.round + 3
    pure val potential_anchors = sequence
                                   .select(s => s.block.round == anchor_round)
                                   // Anchors are sorted by their leadership rank
                                   .sortList((a, b) => intCompare(a.block.leader_rank, b.block.leader_rank))

    pure val chosen_anchor = potential_anchors.find_first(decision => decision.status == Undecided or decision.status == Commit)

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
            log: IndirectDecision({ anchor: anchor.block.label, edges: blocks.certified_link_edges(b_anchor, proposer_block) }),
          }
        }
      }
    }
  }

  pure def try_decide(blocks: BlockStore, sequence: List[Decision], round: int, authority: int): List[Decision] = {
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

  var blocks: BlockStore
  var result: List[Decision]
  var round_to_process: int
  var validator_to_process: int

  action init = all {
    blocks' = DAG.fold(Map(), (m, block) => if (m.has(block.reference.round)) m.setBy(block.reference.round, row => row.put(block.reference.authority, block)) else m.put(block.reference.round, Map(block.reference.authority -> block))),
    round_to_process' = 5,
    validator_to_process' = NUM_OF_PROPOSERS - 1,
    result' = [],
  }

  action step = all {
    round_to_process >= 0,
    validator_to_process >= 0,
    blocks' = blocks,
    val new_result = match blocks.get(round_to_process).values().find(b => b.reference.leader_rank == validator_to_process) {
      | None => result
      | Some(block) => {
         try_decide(blocks, result, block.reference.round, block.reference.authority)
      }
    }
    result' = new_result,
    round_to_process' = if (validator_to_process == 0) round_to_process - 1 else round_to_process,
    validator_to_process' = if (validator_to_process == 0) NUM_OF_PROPOSERS - 1 else validator_to_process - 1,
  }

  pure def is_direct(l: Log): bool = {
    match l {
      | DirectDecision(_) => true
      | _ => false
    }
  }

  pure def is_indirect(l: Log): bool = {
    match l {
      | IndirectDecision(_) => true
      | _ => false
    }
  }

  pure def anchor(l: Log): Option[str] = {
    match l {
      | IndirectDecision(r) => Some(r.anchor)
      | _ => None
    }
  }

  run paperTest = init.then(24.reps((_) => step)).then(
    val decision_by_block = result.foldl(Map(), (m, decision) => {
      m.put(decision.block.label, decision)
    })
    all {
      // Rounds 5 and 6 are part of an incomplete wave and therefore undecided
      assert(decision_by_block.get("L6d").status == Undecided),
      assert(decision_by_block.get("L6d").log == IncompleteWave),
      // ...
      assert(decision_by_block.get("L5a").status == Undecided),
      assert(decision_by_block.get("L5a").log == IncompleteWave),

      // L4d, L4c and L4b are marked as commit by the direct decision rule
      assert(decision_by_block.get("L4d").status == Commit),
      assert(decision_by_block.get("L4d").log.is_direct()),
      assert(decision_by_block.get("L4c").status == Commit),
      assert(decision_by_block.get("L4c").log.is_direct()),
      assert(decision_by_block.get("L4b").status == Commit),
      assert(decision_by_block.get("L4b").log.is_direct()),

      // L4a is marked as skip by the direct decision rule
      assert(decision_by_block.get("L4a").status == Skip),
      assert(decision_by_block.get("L4a").log.is_direct()),

      // Continuing with L3d, L3c, L3b, and L2d, the direct decision rule
      // categorizes them all as to-commit, similar to L4d, L4c, L4b
      assert(decision_by_block.get("L3d").status == Commit),
      assert(decision_by_block.get("L3d").log.is_direct()),
      assert(decision_by_block.get("L3c").status == Commit),
      assert(decision_by_block.get("L3c").log.is_direct()),
      assert(decision_by_block.get("L3b").status == Commit),
      assert(decision_by_block.get("L3b").log.is_direct()),
      assert(decision_by_block.get("L2d").status == Commit),
      assert(decision_by_block.get("L2d").log.is_direct()),

      // L2c and L2b cannot be classified with direct decision, so indirect
      // decision rule is used. The anchor is L5a, which is undecided.
      // Therefore, the status is undecided.
      assert(decision_by_block.get("L2c").status == Undecided),
      assert(decision_by_block.get("L2c").log.is_indirect()),
      assert(decision_by_block.get("L2c").log.anchor() == Some("L5a")),
      assert(decision_by_block.get("L2b").status == Undecided),
      assert(decision_by_block.get("L2b").log.is_indirect()),
      assert(decision_by_block.get("L2b").log.anchor() == Some("L5a")),

      // L2a is a direct decision on commit
      assert(decision_by_block.get("L2a").status == Commit),
      assert(decision_by_block.get("L2a").log.is_direct()),

      // L1d and L1c need indirect decision, and the anchor is L4b, which is
      // marked as Commit
      assert(decision_by_block.get("L1d").status == Commit),
      assert(decision_by_block.get("L1d").log.is_indirect()),
      assert(decision_by_block.get("L1d").log.anchor() == Some("L4b")),
      assert(decision_by_block.get("L1c").status == Commit),
      assert(decision_by_block.get("L1c").log.is_indirect()),
      assert(decision_by_block.get("L1c").log.anchor() == Some("L4b")),

      // NOTE: description on paper seems wrong here (Appendix A) as it says
      // anchor is L4a.
      // L1b also needs indirect decision with anchor L4b, but
      // there is no certified link between it and the anchor, so it gets marked
      // as Skip
      assert(decision_by_block.get("L1b").status == Skip),
      assert(decision_by_block.get("L1b").log.is_indirect()),
      assert(decision_by_block.get("L1b").log.anchor() == Some("L4b")),

      // L1a is a direct decision on commit
      assert(decision_by_block.get("L1a").status == Commit),
      assert(decision_by_block.get("L1a").log.is_direct()),

      round_to_process' = round_to_process,
      validator_to_process' = validator_to_process,
      blocks' = blocks,
      result' = result,
    })
}

// -*- mode: Bluespec; -*-

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
  type StatementBlock = { reference: BlockReference, includes: Set[BlockReference] }

  type BlockStore = { blocks: Round -> Validator -> StatementBlock, highest_round: Round }
  type DirectDecider = { block_store: BlockStore, proposer_block: StatementBlock }

  // pure val WAVE_LENGTH = 3
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
    potential_parents.filter(parent => parent.includes.contains(block.reference))
  }

  pure def link(store: BlockStore, later_block: StatementBlock, earlier_block: StatementBlock): bool = {
    val linked_to_earlier = range(earlier_block.reference.round + 1, later_block.reference.round + 1).foldl(Set(earlier_block), (linked_blocks, r) => {
      val blocks = store.blocks_by_round(r)
      linked_blocks.union(blocks.filter(block => linked_blocks.exists(b => block.includes.contains(b.reference))))
    })

    linked_to_earlier.contains(later_block)
  }

  pure def last(v: List[a]): a = {
    v[v.length() - 1]
  }

  pure def link_edges(store: BlockStore, later_block: StatementBlock, earlier_block: StatementBlock): Set[Edge] = {
    val chains = range(earlier_block.reference.round + 1, later_block.reference.round + 1).foldl(Set([earlier_block]), (links, r) => {
      val blocks = store.blocks_by_round(r)
      links.map(l => {
        val linked_blocks = blocks.filter(block => block.includes.contains(l.last().reference))
        linked_blocks.map(b => l.append(b))
      }).flatten()
    }).filter(c => c.last() == later_block)

    chains.map(c => range(0, c.length() - 1).foldl(Set(), (edges, i) => {
      val child = c[i]
      val parent = c[i + 1]
      edges.union(Set((child.reference.label, parent.reference.label)))
    })).flatten()
  }

  pure def direct_decider(block_store: BlockStore, round: int, proposer: int): DirectDecider = {
    pure val proposer_block = block_store.blocks.get(round).get(proposer)

    { block_store: block_store, proposer_block: proposer_block }
  }

  pure def block_by_reference(d: DirectDecider, reference: BlockReference): StatementBlock = {
    d.block_store.blocks.get(reference.round).get(reference.authority)
  }

  pure def blocks_by_round(b: BlockStore, round: Round): Set[StatementBlock] = {
    b.blocks.getOrElse(round, Map()).values()
  }

  pure def skipped_proposer(d: DirectDecider): bool = {
    pure val r_proposer = d.proposer_block.reference.round
    pure val authority = d.proposer_block.reference.authority
    pure val id = (authority, r_proposer)
    pure val blocks = d.block_store.blocks_by_round(r_proposer + 1)

    pure val non_supporters = blocks.filter(block => not(block.includes.exists(child => (child.authority, child.round) == id)))
    non_supporters.size() >= 2*FAULTY + 1
  }

  pure def edge(b1: StatementBlock, b2: StatementBlock): Edge = {
    (b1.reference.label, b2.reference.label)
  }

  // I have three parents that are linked to the anchor
  pure def certified_link(d: DirectDecider, b_anchor: StatementBlock, b_proposer: StatementBlock): { patterns: int, edges: Set[Edge] } = {
    pure val parents_with_link = d.block_store.parents(b_proposer).filter(b => d.block_store.link(b_anchor, b))
    pure val edges = parents_with_link.map(b => {
      Set(edge(b_proposer, b)).union(d.block_store.link_edges(b_anchor, b))
    }).flatten()

    { patterns: parents_with_link.size(), edges: edges }
  }

  pure def try_direct_decide(d: DirectDecider): Decision = {
    pure val block = d.proposer_block
    // certificates are in r + 2
    pure val certificates = d.block_store.parents(block).map(b =>
      d.block_store.parents(b).filter(c => c.includes.filter(b2 => d.block_by_reference(b2).includes.contains(block.reference)).size() >= 2*FAULTY + 1)
    ).flatten()
    pure val supporting_edges = certificates.map(c => d.block_store.link_edges(c, block)).flatten()
    pure val status = if (d.skipped_proposer()) {
      Skip
    } else if (certificates.size() >= 2*FAULTY + 1) {
      Commit
    } else {
      Undecided
    }
    { status: status, block: block.reference, log: DirectDecision(supporting_edges) }
  }

  pure def try_indirect_decide(d: DirectDecider, sequence: List[Decision]): Decision = {
    // The paper uses the decision round in the pseudocode, but the text always mentions r' > r + 2.
    // I couldn't make it work it the decision round, but r' > r + 2 works.
    pure val b_proposer = d.proposer_block
    pure val r_proposer = b_proposer.reference.round
    pure val anchors = sequence.select(s => s.block.round == r_proposer + 3).toSet().toList((s1, s2) => intCompare(s1.block.leader_rank, s2.block.leader_rank))

    // FIXME: define and use a `first` operator?
    pure val result = anchors.foldl(None, (res, a) => {
      if (res != None) {
        res
      } else {
        match a.status {
          | Undecided => Some({ status: Undecided, block: b_proposer.reference, log: IndirectDecision({ anchor: a.block.label, edges: Set() }) })
          | Commit => {
            pure val b_anchor = d.block_by_reference(a.block)
            pure val certified_link_result = d.certified_link(b_anchor, b_proposer)
            pure val status = if (certified_link_result.patterns >= 2*FAULTY + 1) {
              Commit
            } else {
              Skip
            }
            Some({ status: status, block: b_proposer.reference, log: IndirectDecision({ anchor: b_anchor.reference.label, edges: certified_link_result.edges }) })
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
    pure val c = direct_decider(block_store, r, l)
    pure val proposer_block = c.proposer_block
    if (r > block_store.highest_round - 2) {
      ([{ status: Undecided, block: proposer_block.reference, log: IncompleteWave }].concat(sequence))
    } else {
      pure val direct_status = c.try_direct_decide()
      pure val status = if (direct_status.status == Undecided) {
        c.try_indirect_decide(sequence)
      } else {
        direct_status
      }
      ([status].concat(sequence))
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

  var block_store: BlockStore
  var result: List[Decision]
  var round_to_process: int
  var validator_to_process: int

  action init = all {
    block_store' = { blocks: DAG.fold(Map(), (m, block) => if (m.has(block.reference.round)) m.setBy(block.reference.round, row => row.put(block.reference.authority, block)) else m.put(block.reference.round, Map(block.reference.authority -> block))), highest_round: 5 },
    round_to_process' = 5,
    validator_to_process' = NUM_OF_PROPOSERS - 1,
    result' = [],
  }

  action step = all {
    round_to_process >= 0,
    validator_to_process >= 0,
    block_store' = block_store,
    val new_result = match block_store.blocks.get(round_to_process).values().find(b => b.reference.leader_rank == validator_to_process) {
      | None => result
      | Some(block) => {
         try_decide(block_store, result, block.reference.round, block.reference.authority)
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
      block_store' = block_store,
      result' = result,
    })
}

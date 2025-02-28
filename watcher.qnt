// -*- mode: Bluespec; -*-

// This is not part of the core protocol. It only gathers information to add it to the trace
module watcher {
  import basicSpells.* from "./spells/basicSpells"
  import mysticeti_types.* from "./mysticeti_types"

  pure def link_edges(blocks: BlockStore, later_block: StatementBlock, earlier_block: StatementBlock): Set[Edge] = {
    val chains = range(earlier_block.reference.round + 1, later_block.reference.round + 1).foldl(Set([earlier_block]), (links, r) => {
      val r_blocks = blocks.by_round(r)
      links.map(l => {
        val linked_blocks = r_blocks.filter(block => block.parents.contains(l.last().reference))
        linked_blocks.map(b => l.append(b))
      }).flatten()
    }).filter(c => c.last() == later_block)

    chains.map(c => range(0, c.length() - 1).foldl(Set(), (edges, i) => {
      val parent = c[i]
      val child = c[i + 1]
      edges.union(Set((parent.reference.label, child.reference.label)))
    })).flatten()
  }

  pure def certified_link_edges(blocks: BlockStore, b_anchor: StatementBlock, b_proposer: StatementBlock): Set[Edge] = {
    pure val children_with_link = blocks.children_of(b_proposer).filter(b => blocks.is_link(b, b_anchor))
    children_with_link.map(b => {
      Set(edge(b_proposer, b)).union(blocks.link_edges(b_anchor, b))
    }).flatten()
  }

  pure def log_direct_decision(blocks: BlockStore, proposer_block: StatementBlock, certificates: Set[StatementBlock]): Log = {
    pure val supporting_edges = certificates.map(c => blocks.link_edges(c, proposer_block)).flatten()
    DirectDecision(supporting_edges)
  }

  pure def log_indirect_decision(blocks: BlockStore, proposer_block: StatementBlock, anchor: StatementBlock): Log = {
    IndirectDecision({
      anchor: anchor.reference.label,
      edges: blocks.certified_link_edges(anchor, proposer_block)
    })
  }
}

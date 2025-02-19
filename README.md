# Mysticeti Consensus - Quint specification

This repository contains an unofficial Quint specification for the Mysticeti-C consensus algorithm based on its [paper](https://arxiv.org/pdf/2310.14821) and public talks. This was written as an exercise and should not be used to inform production-level usage of the protocol.

## Files

Main files:
- `mysticeti_c.qnt` has the core functionality of the algorithm
- `dag_evolution.qnt` describes a state machine for how a DAG can evolve over time, including byzantine behavior. This can be re-used for other DAG-based specifications.
- `main.qnt` connects the two modules above so all nodes try to run `decide_all` at every state while the DAG evolves, and defines properties over the outcomes.

Other files:
- `mysticeti_paper_test.qnt` uses `mysticeti_c.qnt` to reproduce the sequence of decision steps describe by Appendix A on the paper. Serves as evidence that our algorithm specification matches the paper.
- `mysticeti_types.qnt` defines the main data strucutres used for consensus
- `watcher.qnt` implements some logging/tracing-like functionality to enable observing inner parts of the algorithm

## TODO
- [ ] Model equivocation
- [ ] Elect different leaders for different rounds
- [ ] Optimize `decide_all` so it doesn't run all the way to round 0 every time

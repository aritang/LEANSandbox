# EconLEAN — tracking 3 econ Lean libraries

Clones live next to this file (git-ignored). Refresh all three at once:
```bash
cd EconLEAN && for d in EconCSLib matheconlib Econlib; do git -C $d pull -q; git -C $d log -1 --format="$d %h %ad %s" --date=short; done
```

## Snapshot (last checked 2026-10-30)

| | EconCSLib | MathEconLib | Econlib |
|---|---|---|---|
| Repo | gametheoryinlean/EconCSLib | matheconlib/matheconlib | danlyng/Econlib |
| Focus | algorithmic game theory, EC/CS | microtheory foundations | political economy, broad theory |
| Lean | v4.30.0 | v4.35.0 | v4.29.0 |
| Size | 200 files / 52k lines | 171 files / 37k lines | 661 files / 200k lines |
| Commits (last 30d) | 65 (15) | 291 (226) | 2 (1): dropped in big chunks |
| `sorry` | only in `OpenProblem/` (opt-in) | none | none (claims: standard 3 axioms only) |
| Last commit | 10-14 submodular welfare (demand queries) | 10-27 EU assumption docs | 10-19 moment persuasion extremality |

Your sandbox runs v4.34.1, so none of the three matches it exactly. To use one as a dependency, copy its toolchain.

## What each covers
- **EconCSLib**: strategic, extensive, and coalitional games; social choice; fair division; matching; auctions/MD; fixed points, minimax, LP. Its `OpenProblem/` holds statements of open research problems (EFX, prophet inequalities, Tarski query complexity…) left as `sorry`.
- **MathEconLib**: Choice, Auction, BidderProblem, Mechanism (BIC/IR), Matching, SingleParameter, ValueDistribution, Statistics. Small, carefully reviewed steps.
- **Econlib**: Preferences (Debreu utility), Probability (FOSD/SOSD, Strassen), Optimization (Berge, KKT, Topkis, Bellman), GameTheory (Nash via Kakutani, PBE, sequential equilibrium), MD, SocialChoice, GE.

## What to learn from each
- **Reading order for a beginner**: start with `matheconlib/docs/BeginnersManual.md`, then `EconCSLib/EconCSLib/Examples/`, then `Econlib/EconlibExamples/`.
- **Writing proofs that can be trusted**: MathEconLib has axiom audits, `ApiStability.lean`, and tests that pin definitions (e.g. BIC semantics). A good model for getting reliable output from automated proving.
- **Stating a problem before proving it**: EconCSLib's `OpenProblem/` shows how to write the *statement* first and leave the proof as `sorry`.
- **Agent tooling**: EconCSLib has `AGENTS.md` and Econlib has `agent-plugin/`. Both show how others run LLM provers on these libraries.
- **Same concept, three definitions** (worth comparing): Nash equilibrium, mechanism/IC, and preferences. See how each library sets up types and typeclasses.

## Log
- 2026-10-30: cloned all three and recorded the first snapshot.

**No definite elaboration failures found in the requested changes.** No elaboration replacements required. This remains a source review; Lean was not run.

All four renamed call sites are consistent: `Coherence:118`, `Conservative:89,116`, and `LayerAFacts:64`. Neither renamed theorem body retains the `Sq.run` shadowing problem. `runs_exactly`’s substitutions correctly eliminate `w` and `b`.

Witness packaging:

- **[`twoRecv_coherence_witness`]( /Users/ember/dev/fn/build/lanes/fn2/lean-meta/fn2/meta/Fn2/Coherence.lean:327): incomplete.** It now includes G0, trace equivalence, successful execution and the reference result, but still omits `Diamonds`. Observation equality follows from the counter values but is not explicitly packaged. Its “whole premise package” docstring remains too strong.
- **`acceptClose_without_g2` (`Coherence:467`): complete.** `acIdCorr` supplies G1 and the observation edge; the statement includes every remaining hypothesis and negates exactly the conclusion.
- **`drop_exec_breaks` (`Param:111`): complete.** It retains initial relatedness and observation preservation and exhibits disagreement by a permitted client.
- **`liar_*` (`Coherence:220–235`): valid `Respects`-removal tooth.** The explicit independence, non-respect and failed-diamond facts remain separate declarations, rather than one conjunction.

The shorter `IndependentDiamonds` definition is sufficient: **`Diamonds` plus its one-sided enabledness clause implies preservation in the reverse direction**, even without assuming symmetry of `I`. No correction is needed there.
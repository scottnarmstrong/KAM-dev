# Q5 prover handoff (branch inp-p11c-q5, ec3da98b; off inp; offloaded P11C package run by the main orchestrator)


**Files:** new `KAM/Planetary/Quantitative/Zero.lean` (366 lines, all lines <= 100 cols). Branch `inp-p11c-q5`, committed.
No other file touched (KAM.lean not edited; see lint note).

**Declarations (signatures verbatim from P11CSignatures.lean):** `p11c_zeroGood` (def), `zero_case`
(`bpP:p11a:zero-case`; local steps `stepP:p11a:zc-set` = `p11c_zero_good`, `stepP:p11a:zc-tori` =
`p11c_zero_lattice`, `p11c_zero_hasFDeriv`, `p11c_zero_vectorField` and the family assembly in `zero_case`).
`QuantitativeInput`, `QuantitativeFamily` are imported from Quantitative/Interface (Q0), not redefined.
Helpers, all `p11c_zero_*` (grep found no clashes in KAM): isOpen_nbhd, contDiffOn_freq, contDiffAt_scalar,
euclid_iter, diam_pos, patch, dioHyp, cDio_pos, gamma_pos, two_gamma, cDio_eq, small, good_eq, good, hasFDeriv,
vectorField, lattice, image.

**Approach:** `zero_case` builds the family with good = `p11c_zeroGood`, torus = (θ,b), freq = frequencyMap h.
- Good set: bridge `QuantitativeInput` to `P11DioHyp` (patch K=d.K, V=ι⁻¹(actionNbhd K 2ϑ), v=ϑ; wt k = ω;
  smoothness via `KAM.contDiffOn_infty_of_differentiableOn`; amount via `le_index_def`; size via `p11op`;
  close is vacuous since wt = w), then `power_law` with 2γ in place of γ. `p11GammaStar … = 2*gamma` and
  `p11CDio … = d.cDio` proved by unfolding; `(√N·2γ)^ρ < β/4` proved with rpow algebra.
  p11Good identified with p11c_zeroGood via rpow_neg.
- Tori: all lattice-torus clauses (analytic, L2–L6) directly; X_H = (ω(b),0) from HasFDerivAt of
  re∘h∘ι ∘ snd; dio from 2γ ≥ γ; displacement 0; lower/upper trivial; borel/cell_lower/compact_closed
  since the evaluation map is the identity on Phase N (unitCube volume 1, factor 2^-2N ≤ 1).

**Checks:** gate `inp_lake_build.sh <wt> KAM.Planetary.Quantitative.Zero` -> "Build completed successfully"
(no warnings in Zero.lean; the warnings shown belong to WeakMeasure/Stability). `#print axioms
KAM.Planetary.zero_case` -> [propext, Classical.choice, Quot.sound]. No sorry/axiom/maxHeartbeats/EuclideanSpace.
`scripts/lint_sources.sh`: all checks pass except "KAM.lean is out of date; run scripts/gen_root_imports.py",
which only reflects the new module (KAM.lean is generated; orchestrator to regenerate).

**Uncertainties / errata / deviations:** none. Hypothesis `hd : d.Valid` is only used via `hd.1`
(NumericalValid); the source's `tau > N-1` and `beta ≤ 1` are unused here (as in the source). No wrong statement found.
Note the Q5 row asserts Q.good/torus/freq equalities exactly as in the signature; the proof of
`Q.compact` etc. needs no extra premise. Q0's `QuantitativeInput` supplies A1–A4; `M0` bound unused (as in the source).
No design signals (every declaration elaborates at default heartbeats; the file is 366 lines).

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row Q5 (zero_case; QuantitativeInput and Family live in Q0's Interface) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. (a) every declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node mapped to Quantitative/Zero established; an exported lemma named after a node must state that node's literal conclusion; (c) proof soundness, no added premises (the handoff notes hd : d.Valid is used only via hd.1: confirm it is a signature premise); U11a1 power_law and U1 consumed as designed; (d) hygiene: no EuclideanSpace, no reused public helper short name, no root shadow, lines <= 100. Audit ONLY KAM/Planetary/Quantitative/Zero.lean.

# P23-13h independent audit 1

Overall verdict: **PASS WITH NOTES** for `KAM.Planetary.osc_remainder_bound`, the quantitative clause of `bpP:p2:osc-iter`. No blocking mathematical or implementation defect found. The only validation exception is the explicitly permitted stale generated root. This infrastructure package has no frozen anchor or provider to seal; it does not by itself close `osc_iter`, P23-13j, P23-15, or a planetary headline.

## Scope and authority

Audited HEAD `9a7866ee77e93998d33dcdea9919ef454ef8d860`; comparison branch `inp` was `686d56cfb012dd62ac088abd79a6dd17cb22eb98`. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the supplied handoff, track P statement, Revision 3 and Appendix A.3 of P23-LEAN-DESIGN.md, P23-design-audit-1.md, and the relevant blueprint statement/proof at `blueprint-P/parts/p2-averaging.tex:183–196`. Read the relevant carrier definitions and imported frozen definitions and checked their manifest states.

The user's exact report destination overrides the generic brief's MAIN-worktree destination. The handoff's AUDIT FOCUS limits this audit to `KAM/Planetary/Averaging/OscillatorRemainder.lean` (122 lines, one public theorem). `git diff inp...HEAD` contains this file and the inherited 349-line `OscillatorCompositionIntegral.lean` from 13f; the latter was inspected as a consumed interface, not assigned a new independent package verdict. Initial status contained the untracked supplied handoff. No production source was edited.

## Declaration and node fidelity

| Node / obligation | Lean declaration | Verdict | Reason |
|---|---|---|---|
| `bpP:p2:osc-iter` quantitative clause, Appendix A.3, P23-13h | `KAM.Planetary.osc_remainder_bound` (`OscillatorRemainder.lean:37`) | PASS | Entire signature, including all lets and the final bound, is byte-identical to Appendix A.3 and `/root/code/KAM-inp/.drafts/design/P23Signatures.lean`. Exact original premises, binder order, four radii, Rsum, map and remainder; no additional premise or weakened conclusion. |
| `stepP:p2:oi-transfer`, `oi-ratio`, `oi-range` consumption | Same declaration, lines 75–119 | PASS | Supplies the concrete generator data, decomposition and joint continuity; consumes integral and time-one composition estimates on the same flow domain. Preserves the signed geometric denominator. |

A fresh-name scratch copy of the **complete** Appendix A.3 declaration, with no linter option, elaborated with body:

```lean
by
  exact osc_remainder_bound hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
```

The additional `example : type_of% @audit_remainder_bound := @osc_remainder_bound` elaborated. This checks the actual elaborated interface and the exact all-explicit-binders application analogous to the brief's seal probe. No provider/frozen-type probe applies because R3.6 explicitly has no frozen provider assembly. A first scratch generator mistakenly split at a let's `:=`, producing an incomplete probe and syntax errors; it was corrected to extract through the final conclusion before the checks above. This was an auditor scratch error, not a package failure.

`set_option linter.unusedVariables false in` at line 36 is acceptable: it only suppresses unused-variable diagnostics. The unsuppressed fresh declaration passed with warnings for unused lets φ, O, U, u, V and the same type/axioms. It is neither a heartbeat override nor a semantic change.

## Proof and definition audit

No new public `def`, `abbrev`, or `structure` occurs in scope. All local lets are literal intended objects: the existing oscillator step map Ψ, finite sum g, its zero-mode update gp, the actual transformed residual fp, minimum loss product d, weighted finite Rsum, existing generator φ, specified O/U/V domains and normalized size u. The auxiliary Φ is exactly δ/(2πα). No replacement norm, junk value or fallback is introduced.

- Lines 69–85 establish positive d and target strip width, obtain `osc_remainder_decomposition`, `oscGen_class_bound`, and `osc_truncation_tail`, and construct `OscComposeData` at Φ=δ/(2πα). Its fields are source typing/class/bound/width/smallness facts, all discharged here; no remainder or convergence output is assumed.
- Lines 86–97 split on nonemptiness of the target **parameter** set. In the empty branch `oscBound` is a universal assertion over that empty set, so the conclusion is vacuous for any majorants. In the other branch a target point belongs to every larger gj parameter domain. Nonnegative weighted sums imply Mj≥0; positive radius-gap denominators make Rsum≥0 and hence B=2(1+m)Φ(Rsum+δ)/d≥0. There is no extra D-nonemptiness or majorant-positivity premise; J=0 and δ=0 remain admitted.
- Line 98 uses `osc_composition_integral` on the exact integrand family from 13g, with class/bound and joint continuity of v and Dv supplied by that decomposition. The integral bound is (1−θ)⁻¹B.
- Lines 100–107 restrict the class and truncation-tail bound of f−T to O and apply `osc_composition_t` at t=1. The tail bound is (1−θ)⁻¹ exp(−2πKσ)δ. These functions use the actual O-flow, definitionally the signed Ψ. `osc_lie_series` is consumed indirectly by the composition interface (`OscillatorComposition.lean:273`); no extra series assumption is introduced by 13h.
- Lines 108–111 add the class-supported weighted bounds and use the explicit decomposition on V. `add_sub_assoc` gives exactly integral+(f−T)∘Ψ, and positive target strip width justifies transporting coefficient bounds from equality on V.
- Lines 112–119 identify θ=2e(1+m)δ/(2παd) and factors the sum to the exact signed target constant. The equality uses Φ=δ/(2πα), d>0 and α>0; no inequality is silently strengthened. The dependency's smallness estimate provides θ<1 (indeed θ≤e/8), so the inverse factor is the designed positive geometric factor.

The KAM import closure has 85 modules and no provider or frozen theorem module. Its 12 frozen imports are definitions, all manifest state SEALED: actionNbhd, complexStrip, hamiltonianVectorField, hamiltonianVectorFieldℂ, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, omegaZero, symplecticForm, Planetary.Phase, Planetary.fast, Planetary.slow. Thus no DRAFT_SORRY anchor is used. The conclusion's carriers are the existing finite-function complex phase/parameter spaces and weighted Fourier coefficient bound, consistent with period-one normalization barα=2πα.

## Independent validation

All Lean/Lake invocations were sequential with `LEAN_NUM_THREADS=1` and `nice -n 5`; no resource override or cache/library rebuild was requested.

1. Targeted gate:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2313h KAM.Planetary.Averaging.OscillatorRemainder
[inp-gate] slot 2 acquired 12:36:27 for KAM.Planetary.Averaging.OscillatorRemainder
Build completed successfully (9131 jobs).
exit 0
```

2. Exact-type/application and axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2313hAudit.lean
'KAM.Planetary.osc_remainder_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.audit_remainder_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

Only the unused-let warnings described above accompanied the successful probe. There is exactly one new public theorem in scope; no sorryAx or extra axiom appears. The scratch probe was deleted after validation.

3. Kernel replay, one invocation for the sole in-scope module:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorRemainder
replaying KAM.Planetary.Averaging.OscillatorRemainder
exit 0
```

4. Source lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (655 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The nonzero exit is solely the stale generated root expressly allowed by the audit brief. It was not regenerated. No other lint failure was printed.

5. `git diff --check inp...HEAD`: no output, exit 0. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0. Direct target scan finds no sorry/admit/axiom/unsafe/opaque, forbidden ambient carrier, or resource override. The sole option is the scoped linter suppression discussed above. Module header, copyright, public interface imports, docstring and exposed public section are present; 122 lines is below 1500.

## Notes, uncertainties, errata and deviations

No newly suspected pinned-source or blueprint mathematical defect was found. The existing blueprint source-gap sentence at p2:196, “the extension is stated by its (short) list of changes, not rewritten in N,” is paid here at the assigned quantitative assembly boundary using the explicit R3 transfer interfaces; this audit does not reopen upstream source proofs or certify full campaign closure. No pinned-paper erratum is asserted from an unperformed PDF check.

The module docstring says the remainder “lies in the oscillator class”; this file exports the weighted bound only. The separate class result is `osc_fp_class`, intentionally assembled with this bound by P23-13j (R3.6). This wording does not change the theorem or create a missing obligation in 13h.

The only remaining release work is outside this package's assigned scope: the full `osc_iter` conjunction and its independent 13j audit, then the P23-15 consumer checks. No implementation deviation from the signed 13h contract was found.

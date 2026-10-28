# P23-13g independent package audit 1

Overall verdict: **PASS WITH NOTES** for P23-13g's two signed exports. No blocking mathematical or implementation defect found. This is infrastructure for `stepP:p2:oi-transfer`; it does not seal a frozen anchor, establish the full `osc_iter`, prove the final remainder norm estimate, or release P23-15.

## Scope and authority

Audited HEAD: `cebb304fc8375e2541c258a28d47f91e309d51b6`; `inp`: `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`; `inp-p2313b`: `2990ba1bbe1fef94c42f1b224e06c873939a211e`.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the supplied P23-13g handoff and its AUDIT FOCUS, `docs/tracks/P/statement.md`, Revision 3 and Appendix A.3 of `docs/tracks/P/design/P23-LEAN-DESIGN.md`, and `docs/tracks/P/design/P23-design-audit-1.md`. Checked `blueprint-P/parts/p2-averaging.tex:167–196` and the inherited step at `blueprint-N/parts/p6-normal-form.tex:93–106`, plus the actual imported homological, bracket, flow, and Taylor interfaces.

The handoff's narrower scope controls: audit only `KAM/Planetary/Averaging/OscillatorRemainderData*.lean`. There is one matching file, 498 lines. `git diff inp...HEAD --numstat` gives:

```text
498  0  KAM/Planetary/Averaging/OscillatorRemainderData.lean
335  0  KAM/Planetary/Averaging/OscillatorSeriesAlgebra.lean
```

The second file is the inherited P23-13b dependency, not independently re-audited here. The required comparison with `inp-p2313b` gives the same 498-line new remainder file. Its wider branch diff includes unrelated landed infrastructure; those files are outside this audit. The pre-existing untracked handoff was left untouched. The report destination follows the user's explicit worktree-local absolute path, overriding the generic brief's main-worktree destination.

**N1 — Authority availability.** `.drafts/design/P23Signatures.lean` is absent in this checkout. Appendix A.3 contains the exact signed exports and was used directly, without a substitute signature. The integrand definition is literally equal; the theorem declaration up to its proof body is equal after whitespace normalization. This verifies the local authoritative design text, not the hash of an unavailable standalone file.

**N2 — Root lint exception.** Full lint exits 1 solely for the explicitly permitted stale generated `KAM.lean` notice. The generated root was not edited or regenerated.

No frozen theorem/provider is part of this package. Frozen-provider ABI equality and an actual anchor seal are therefore **not applicable**. Instead, a fresh-name copy of the complete Appendix A.3 theorem was elaborated with its body an exact application of the implementation, in the original explicit-binder order; a `type_of%` example also checked the complete type.

## Declaration and node audit

All names below have prefix `KAM.Planetary`; line numbers refer to `OscillatorRemainderData.lean`. Auxiliary declarations have distinct names and support the stated transfer obligations; none replaces an unproved signed result.

| Node / obligation | Declaration, line | Verdict | Reason |
|---|---|---|---|
| `oi-transfer`, concrete integrand | `oscRemIntegrand`, 35 | PASS | Literal `{g+(1-t)xi+t*T,phi}`, with the existing coefficient, packing, truncation and bracket. |
| Weighted majorant monotonicity | `osc_bound_mono`, 44 | PASS | Retains summability and increases only the numerical upper bound. |
| Majorant sign on a nonempty carrier | `osc_bound_nonneg`, 48 | PASS | Evaluates the supplied bound at an actual parameter; does not assume nonemptiness globally. |
| Scalar class algebra | `osc_class_const_mul`, 52 | PASS | Holomorphy and fast-angle periodicity preserved for every complex scalar. |
| Finite weighted addition | `osc_bound_add_sum`, 56 | PASS | Induction over arbitrary `Fin J`; scalar bound is exactly `A+sum b`. Positive strip width supplies the inherited coefficient addition interface. |
| Action projection | `oscActionL`, 77 | PASS | Continuous linear projection to the first action block on the whole phase space. |
| Projection computation | `oscActionL_apply`, 82 | PASS | Definitional equality with `firstBlock w.2`. |
| Chain rule for the integrable Hamiltonian | `fderiv_oscH0`, 84 | PASS | Requires only pointwise differentiability of h at the projected point. |
| Coordinate computation | `firstBlock_zero_fun`, 93 | PASS | Projection of zero, all dimensions. |
| Coordinate computation | `firstBlock_single_cast`, 95 | PASS | First-block unit vector is the corresponding action unit vector. |
| Coordinate computation | `firstBlock_single_nat`, 101 | PASS | Oscillator-block unit vector projects to zero. |
| `oi-transfer`, homological identity | `osc_hom_bracket`, 110 | PASS | Derives `{H0,phi}=xi-T` from `homological_param` on local parameter balls. No homological equation is an input premise. Stronger than the main step's setting: no n/m positivity, smallness or twice-loss assumptions required. |
| Bracket algebra | `pb_lin3`, 210 | PASS | First-slot linearity at a point, with precisely the differentiability needed for the total derivative. No differentiability premise on phi is needed for this algebraic identity. |
| Bracket algebra | `pb_sum`, 219 | PASS | Arbitrary finite sum; pointwise differentiability only. |
| Local bracket congruence | `pb_congr_eventually`, 226 | PASS | Uses neighborhood equality, sufficient for equality of the total derivatives. |
| `osc-bracket`, scalar estimate | `osc_W_le`, 234 | PASS | W bounded by `2*(1+m)*M`; only the angle-ratio sum needs nonnegativity for comparison with `1/exp 1`. Oscillator ratios need only their upper bounds. |
| Scalar majorant transport | `osc_bracket_bound_le`, 245 | PASS | Positive d and nonnegative A,Phi justify multiplying the W inequality. No unguarded sign reversal. |
| `oi-transfer`, remainder data | `osc_remainder_decomposition`, 257 | PASS | Complete Appendix A.3 type, original hypotheses and all lets retained; class, weighted B-bound, both joint continuities, and exact same-flow identity proved. |

## Definitions and hypothesis audit

There are exactly two new definitions, no new abbrev, structure or instance:

- `oscRemIntegrand`: intended literal total bracket expression on every input. The inherited `fderiv` and coefficient integral are total; the theorem uses their analytic interpretation only where class and openness give differentiability and integrability. No conditional branch, choice of a replacement flow, or junk-value proof is introduced.
- `oscActionL`: literal bounded complex-linear action projection on every phase vector; no fallback or restricted-carrier interpretation.

All auxiliary theorem premises express typing, differentiability, class/bounds, elementary numerical comparisons, or a neighborhood equality in a generic congruence lemma. Every such premise is discharged in the concrete theorem. In particular, neither the homological identity nor continuity nor existence of a bounded remainder is assumed in `osc_remainder_decomposition`.

The main type retains the arbitrary action set D, n,m>=1, all four twice-loss margins, alpha>0, K>=0, original divisor and class hypotheses, delta>=0, the original smallness coefficient `16*(1+m)`, and the complete finite decomposition with its actual outer widths. No `D.Nonempty`, `Mj>=0`, norm bound on h, reality, flow or Lie-series hypothesis was added. Zero K, zero delta and J=0 remain admitted by the statement.

## Proof and consumer applicability

1. At each original-domain point, openness of `oscParams` supplies a ball in flat parameter dimension `n+(m+m)`. `homological_param` is instantiated with independent Fourier dimension n, q=1 and Lambda={0}; its fourth and sixth conclusions give the equation and zero-mode residual. K>=0 proves `{0} intersect zBall n K={0}`, including K=0. The chain rule through `oscPackL` and the castAdd/natAdd coordinate split remove oscillator terms of H0. The bracket sign is explicitly computed, giving `{H0,phi}=xi-T` (lines 110–198).
2. For each gj the proof applies `osc_bracket` at its actual larger widths. The four ratios are exactly those of the signed Rsum, not equal-width substitutes (318–325). The zero mode and truncation each have bound delta. For t in [0,1], `norm(1-t)+norm(t)=1`; hence the convex combination contributes one delta, rather than two (397–423).
3. If the smaller parameter set is empty, the weighted conclusion is vacuous. Otherwise an actual parameter in it lies in every gj parameter domain, so the proof derives `Mj j>=0` from each existing bound before multiplying its numerical estimate (390–396). Thus the possible negative-Mj empty-domain case is retained, without an extra source premise.
4. On the open one-loss domain O, bracket holomorphy gives continuity. Polynomial dependence on real t gives joint continuity of v; holomorphic finite-dimensional regularity and neighborhood equality give joint continuity of its full complex phase derivative (363–445). These are proved conclusions, suitable for the later composition-integral consumer.
5. `osc_flowHyp` supplies `H.W` and `H.smallField`. V is included in U, then `H.half` places the starting point in the gauge interior required by Taylor. `flow_a` supplies the entire trajectory on [-1,1] in O. `taylor_poschel` is applied at phase dimension n+m, with `Omega=Omega1=O`, `h=H0`, `f0=g+T` (446–460). This is the same literal domain and field as `oscStepMap`; no flow uniqueness bridge or smaller-domain flow is substituted.
6. The inner homological rewrite is valid on a neighborhood of each flow point in O. `pb_congr_eventually` therefore justifies rewriting a differentiated bracket, rather than relying on equality at a single point (461–478). Taylor and the homological equation at z then give

   `fp z = integral_0^1 v(t)(flow X_phi O t z) dt + f(Psi z)-T(Psi z)`.

   The tail is composed with the same Psi. This establishes exactly the concrete data consumed by the remaining composition/integral packages; it does not itself estimate that composed integral or tail in weighted norm on V.

## Independent checks and exact receipts

All final Lean checks use `LEAN_NUM_THREADS=1`, default elaboration budgets and niceness 5. The targeted build went through the prescribed compile gate:

```text
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2313g KAM.Planetary.Averaging.OscillatorRemainderData
[inp-gate] slot 2 acquired 10:59:59 for KAM.Planetary.Averaging.OscillatorRemainderData
Build completed successfully (9121 jobs).
exit 0
```

The deleted scratch probe `.lake/abi-scratch/P2313gAudit.lean` imported only the production module. It reproduced the Appendix A.3 integrand under `auditOscRemIntegrand` and checked equality by `rfl`. It reproduced the entire signed theorem under `auditSignedRemainder` and used:

```lean
  exact osc_remainder_decomposition hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
example : type_of% @auditSignedRemainder := @osc_remainder_decomposition
```

The probe also ran `#print axioms` for all 16 public theorems in the declaration table:

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2313gAudit.lean
exit 0
```

The exact axiom output was:

```text
'KAM.Planetary.osc_bound_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_bound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_class_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_bound_add_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscActionL_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_oscH0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.firstBlock_zero_fun' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.firstBlock_single_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.firstBlock_single_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_hom_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pb_lin3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pb_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pb_congr_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_W_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_bracket_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_remainder_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` occurred. The fresh copied signature produced only expected unused-let warnings for U and u. The production theorem retains these signature lets and locally disables only `linter.unusedVariables`.

Kernel replay, one invocation covering the module containing all new declarations:

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorRemainderData
replaying KAM.Planetary.Averaging.OscillatorRemainderData
exit 0
```

Full lint:

```text
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (553 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is the brief's permitted generated-root exception. No production file was modified. `git diff --check inp...HEAD` exits 0. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. The scoped file has 498 lines, maximum line length 100, the required module header/docstring/public section and public interface imports, exposed definition bodies, and no forbidden proof escapes or resource overrides. Its only option is the unused-variable linter suppression at line 256.

A recursive source import walk found 75 KAM modules, no provider, and no frozen theorem. The twelve imported frozen definitions are all manifest `SEALED`: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, Planetary/Phase, Planetary/Fast and Planetary/Slow. Their definitions and actual oscillator carriers were checked; there is no DRAFT_SORRY import.

Audit workflow deviation: the first lint was launched while the gated build was pending, before noticing that lint itself starts Lake for ABI checking. A subsequent probe Lake startup also overlapped that lint; it was paused before launching its Lean child. The remaining checks were serialized, and lint and the probe were rerun with explicit single-thread environment. This is an auditor scheduling deviation, not a change to package statements or proof budgets.

## Source/blueprint defects, uncertainties and disposition

No newly suspected pinned-paper erratum or package-introduced mathematical deviation was found; no pinned PDF was fetched or re-audited. This audit uses the named local blueprint/design and actual Lean dependencies, as the AUDIT FOCUS requires.

Retain the inherited blueprint issue already recorded by Revision 3: `blueprint-P/parts/p2-averaging.tex:177` says `sum_i ... <= .../(e(S_0-S))`, although the bracket hypotheses at line 173 only require `S-sigma<S_0`. S0-S can be zero or negative. The correct target-width angle loss is S0-S+sigma. The new proof uses the landed `osc_bracket` and its positive target-width denominators (318–325), so it does not rely on that defective intermediate sentence. This is a pre-existing blueprint defect, not a newly verified paper erratum.

The source gap at `p2-averaging.tex:196` says the oscillator extension is "stated by its (short) list of changes, not rewritten in N." This package pays the homological/explicit-integral-data part only. The original P23-13 F1/full-contract boundary remains until the rest of Revision 3 is proved and audited. No anchor sealing action is recommended from P23-13g alone.

Only this report was added; temporary auditor probes were removed. The pre-existing handoff and all production sources remain unchanged.

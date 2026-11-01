# W-GRAPH-CLOSE handoff

Package: W-GRAPH-CLOSE (track W). Branch `inp-wgclose` (worktree `/root/code/KAM-inp-wpj`, off `inp` with
the SEALED `KAM.Wave.nlw2`). Date: 2026-11-01. Scope: the 10 nodes kept PARTIAL / NOT_STARTED by the D27 audit
`docs/graph/W/reviews/BYPASS-audit-1.md` (branch `inp-wgraph-byp`), findings A, L, S, FLOW, SHELL.

All work is in NEW files; no existing file was edited except the generated root part `KAM/Root/Wave.lean`
(`python3 scripts/gen_root_imports.py`). No `sorry`, `axiom`, heartbeat or recursion override. No file exceeds
1500 lines (largest: `ExportFlowCore.lean`, 310 lines).

## New files

| File | Lines | Content |
|---|---|---|
| `KAM/Wave/Seq/ExportLamFacts.lean` | 177 | `bpW:w0:basis#lambda-facts` |
| `KAM/Wave/Measure/ExportShells.lean` | 127 | `bpW:w7:shell-geom`, `stepW:w7:partition` |
| `KAM/Wave/KamStep/ExportFlowCore.lean` | 310 | per-`t` flow lemmas for `StepCore` (`phiT`, `PsiT`, ...) |
| `KAM/Wave/KamStep/ExportFlow.lean` | 303 | `bpW:w5:flow`, `stepW:w5:f-flow`, `f-par`, `f-der` (source-facing, both cases) |
| `KAM/Wave/KamStep/ExportSolve.lean` | 278 | `bpW:w5:solve` (source-facing, both cases) |
| `KAM/Wave/Algebra/ExportW0n.lean` | 82 | `bpW:w0n:algebra`, `stepW:w0n:weight` |

## Node table

Notation: `U = D(s-2σ, r/2)`, `V = D(s-σ, r)`, `M_F = stepMF (stepCF τ) (stepExpT τ) α σ ε` (non-modified),
`stepMF (stepCFn τ) (stepTn τ) α σ ε` (modified). `φ^t_ξ = H.hyp.core.phiT ξ t` is the time-`t` map of the flow
of `X_{F(ξ)} = ι ∘ stepFieldS (H.hyp.FT ξ)`; `Ψ^t_ξ = H.hyp.core.PsiT ξ t = ∫₀ᵗ stepFieldS(...)(φ^τ ·) dτ`;
`H.hyp.core.phiT ξ 1 = H.hyp.core.Phi ξ` (the `Φ` of `stepTheorem`) by `rfl` (`StepCore.phiT_one`). The
`λ`-norms are encoded as in `stepTheorem`: `∃` a sup bound and a `ξ`-Lipschitz bound whose `λ`-combination is
bounded.

| Node | Lean declaration(s), file:line | Exact statement (Lean) | Status |
|---|---|---|---|
| `bpW:w5:flow` | `KAM.Wave.stepFlowLemma` ExportFlow.lean:66; `KAM.Wave.stepFlowLemmaMod` ExportFlow.lean:189 | For `H : StepHypSrc …` (resp. `StepHypModSrc …`), `[Fact (0<r)]`: `∀ ξ ∈ Π, FlowHyp (smoothField ι Z_ξ) V U M_F (σ/4)`; `M_F ≤ σ/256`; `M_F/(σ/4) ≤ 1/64`; and `∀ t ∈ [-1,1]`: (i) `∀ ξ∈Π, ∀ w∈U, φ^t w ∈ V ∧ φ^t w = w + ι(Ψ^t w)`; `∀ ξ∈Π, DifferentiableOn ℂ Ψ^t U`; `∃ A₀ A₁ ≥ 0, A₀+λA₁ ≤ 2M_F ∧ ∀ ξ ζ ∈ Π, ∀ w ∈ U, ‖Ψ^t_ξ w‖ ≤ A₀ ∧ ‖Ψ^t_ξ w − Ψ^t_ζ w‖ ≤ A₁‖ξ−ζ‖`; (ii) `∀ ξ∈Π, ∀ w ∈ D(s−3σ,r/4), Dφ^t w = id + ι∘DΨ^t w ∧ ‖DΨ^t w‖ ≤ 8M_F/σ`; `(∃ B₀ B₁ ≥ 0, B₀+λB₁ ≤ 16M_F/σ ∧ sup/Lipschitz of DΨ^t on D(s−3σ,r/4)) ∧ 16M_F/σ ≤ η²`; (iii) `∀ ξ∈Π, ∀ w ∈ D(s−5σ,ηr), φ^t w ∈ D(s−4σ,2ηr)` and `D(s−4σ,2ηr) ⊆ D(s−3σ,r/4)`; (iv) `∀ ξ∈Π, ∀ w∈U, StepReal w → StepReal (φ^t w)`; `∀ ξ∈Π, ∀ w∈U, ∀ k : Fin 2 → ℤ, w+τ_k ∈ U ∧ φ^t(w+τ_k) = φ^t w + τ_k` (`τ_k = k₀•τ₀ + k₁•τ₁`) | export |
| `stepW:w5:f-flow` | `KAM.Wave.stepFlow_fFlow` ExportFlow.lean:126; `KAM.Wave.stepFlowMod_fFlow` ExportFlow.lean:249 | `∀ t ∈ [-1,1], ∀ ξ ∈ Π, DifferentiableOn ℂ Ψ^t U ∧ ∀ w ∈ U, φ^t w ∈ V ∧ φ^t w − w = ∫ τ in 0..t, smoothField ι Z_ξ (φ^τ w) ∧ φ^t w = w + ι(Ψ^t w) ∧ ‖Ψ^t w‖ ≤ |t|·M_F` | export |
| `stepW:w5:f-par` | `KAM.Wave.stepFlow_fPar` ExportFlow.lean:147; `KAM.Wave.stepFlowMod_fPar` ExportFlow.lean:270 | `∀ t ∈ [-1,1], ∃ A₀ A₁, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ A₀ + λA₁ ≤ 2M_F ∧ ∀ ξ ζ ∈ Π, ∀ w ∈ U, ‖Ψ^t_ξ w‖ ≤ A₀ ∧ ‖Ψ^t_ξ w − Ψ^t_ζ w‖ ≤ A₁‖ξ−ζ‖` (i.e. `|φ^t − id|^λ_{p_+,r,U} ≤ 2M_F`) | export |
| `stepW:w5:f-der` | `KAM.Wave.stepFlow_fDer` ExportFlow.lean:160; `KAM.Wave.stepFlowMod_fDer` ExportFlow.lean:283 | `∀ t ∈ [-1,1], (∀ ξ∈Π, ∀ w ∈ D(s−3σ,r/4), Dφ^t w = id + ι∘DΨ^t w ∧ ‖DΨ^t w‖ ≤ 8M_F/σ) ∧ (∃ B₀ B₁ ≥ 0, B₀+λB₁ ≤ 16M_F/σ ∧ ∀ ξ ζ ∈ Π, ∀ w ∈ D(s−3σ,r/4), ‖DΨ^t_ξ w‖ ≤ B₀ ∧ ‖DΨ^t_ξ w − DΨ^t_ζ w‖ ≤ B₁‖ξ−ζ‖) ∧ 16M_F/σ ≤ η²` | export |
| `bpW:w7:shell-geom` | `KAM.Wave.shellGeom` ExportShells.lean:108 (also `iUnion_shellSet_eq_box` :63) | `0<q<1`, `0<t₀`, `k : ℕ`: (i) `∀ l l', k ≤ l → k ≤ l' → l ≠ l' → Disjoint R_l R_l'`; `∀ l, MeasurableSet R_l`; `(⋃ (l) (_ : k ≤ l), R_l) = boxIoo 0 t_k`; `∀ l, volume R_l = ofReal ((1−q²) t_l²)`; (ii) `∀ a, 0 < a → a ≤ t_k → volume (R_k \ shellInner q t₀ k a) ≤ ofReal (7 a t_k)`; (iii) `R_k ⊆ {I \| t_{k+1} ≤ ‖I‖}` and `Metric.diam R_k ≤ t_k` | export |
| `stepW:w7:partition` | `KAM.Wave.shellSet_partition` ExportShells.lean:80 | `0<q<1`, `0<t₀`, `k`: `∀ I ∈ (0,t_k)², ∃! l, k ≤ l ∧ I ∈ R_l`; `∀ I ∈ (0,t_k)², ∀ l ≥ k, I ∈ R_l ↔ t_{l+1} ≤ max I₀ I₁ ∧ max I₀ I₁ < t_l`; `∀ l, volume R_l = ofReal (t_l² − t_{l+1}²)`. The reverse inclusion `⋃_{l≥k} R_l ⊆ (0,t_k)²` used inline at `Density.lean:89-93` is `iUnion_shellSet_subset_box` ExportShells.lean:57 | export |
| `bpW:w0n:algebra` | mapping: `KAM.Wave.wave_algebra` Algebra.lean:82 + `KAM.Wave.waveAlgConst_three_halves_sq` CubicHeadline.lean:46; combined export `KAM.Wave.wave_algebra_w0n` ExportW0n.lean:74 | `0 ≤ a`, `1 ≤ s`, `WaveTwoMem a s c`, `WaveTwoMem a s d` ⇒ `((∀ l, Summable fun i => ‖c i‖‖d (l−i)‖) ∧ WaveTwoMem a s (c*d) ∧ ‖c*d‖_{a,s} ≤ waveAlgConst s ‖c‖ ‖d‖) ∧ waveAlgConst (3/2)² = 8(1 + 2 (riemannZeta 3).re)`; `waveAlgConst s = 2^s √(1 + 2 Re ζ(2s))` | mapping confirmed (both cited declarations state the node); combined export added |
| `stepW:w0n:weight` | `KAM.Wave.wave_weight_step` ExportW0n.lean:36 (repackages `wave_weight_ineq` Algebra.lean:48, `waveJap_sub_le` Algebra.lean:36) | `0 ≤ a`, `1 ≤ s`, `l i : ℤ`: `e^{a\|l\|} ≤ e^{a\|i\|} e^{a\|l−i\|}` ∧ `⟨l⟩ ≤ ⟨i⟩ + ⟨l−i⟩` ∧ `w_l ≤ 2^{s−1}(w_i e^{a\|l−i\|} + e^{a\|i\|} w_{l−i})` ∧ `w_l ≤ 2^{s−1}(w_i w_{l−i}/⟨l−i⟩^s + w_i w_{l−i}/⟨i⟩^s)` (`w = waveTwoWeight a s`, `⟨·⟩ = waveJap`) | export. `wave_weight_ineq` states the middle inequality (finding A is right that it is in the route); the first and last clauses of the packet conclusion were inline/unstated, now exported |
| `bpW:w5:solve` | `KAM.Wave.stepSolveLemma` ExportSolve.lean:194; `KAM.Wave.stepSolveLemmaMod` ExportSolve.lean:239; reality via `WaveStepHyp.FT_isRealTaylor` RealStep.lean:138, `StepHypMod.FT_isRealTaylor` RealStep.lean:159 (finding S: the real names), `homNhatTaylor_isReal_gen` | For `H : StepHypSrc …` (resp. `StepHypModSrc …`), `R = H.hyp.core.R ξ`, `F = H.hyp.FT ξ : HomTaylor_gen a p p_+ (s−σ)` (`∈ T_{s−σ}`), `N̂ = homNhatTaylor_gen R`: `∀ ξ ∈ Π`, `IsSmoothing (kamDomain (s−σ) r) (waveStepFun F) (stepField F)` ∧ `IsSmoothing univ (waveStepFun N̂) (stepField N̂)` ∧ `F.isRealTaylor` ∧ `N̂.isRealTaylor` ∧ `∀ w ∈ D(s−σ,r), R(w) + (DN(w)∘…)(ι X_F(w)) = N̂(w) + H.hyp.core.a0 ξ`; `FamBound Π D(s−σ,r) r λ M_F X_F`; `FamBound Π D(s,r) r λ (6ε) X_N̂`; `∃ b₀ b₁ ≥ 0, b₀+λb₁ ≤ 6πε ∧ ‖ω̂_ξ‖ ≤ b₀ ∧ ‖ω̂_ξ − ω̂_ζ‖ ≤ b₁‖ξ−ζ‖`; `∃ c₀ c₁ ≥ 0, c₀+λc₁ ≤ 3ε ∧ ∀ j, (j+2)^{p_+−p}\|Ω̂_j(ξ)\| ≤ c₀ ∧ (j+2)^{p_+−p}\|Ω̂_j(ξ) − Ω̂_j(ζ)\| ≤ c₁‖ξ−ζ‖` | export (one statement per case). New: `N̂ ∈ S_{p_+}(𝒫)` on all of `𝒫` (`stepNhat_isSmoothing_univ` ExportSolve.lean:83), previously only on domains |
| `bpW:w0:basis#lambda-facts` | `KAM.Wave.lamBasis_facts` ExportLamFacts.lean:161 (parts: `lamBasis_bounds` :53, `lamBasis_div_lt_one` :62, `lamBasis_strictMono` :66, `lamFun_strictConvexOn` :85, `lamFun_hasDerivAt` :112, `lamFun_deriv_pos_lt_one` :124, `lamFun_deriv_strictMono` :132, `lamBasis_succ_sub` :138) | `0 < m`: `∀ j, j < λ_j ∧ λ_j < j + √m`; `∀ j, j/λ_j < 1`; `StrictMono λ`; `StrictConvexOn ℝ univ (fun s => √(s²+m))`; `∀ s, HasDerivAt f (s/√(s²+m)) s`; `∀ s > 0, 0 < f'(s) ∧ f'(s) < 1`; `StrictMono (deriv f)` (on all of `ℝ`); `∀ j, λ_{j+1} − λ_j = (2j+1)/(λ_{j+1}+λ_j) ∧ (2j+1)/(λ_{j+1}+λ_j) < 1` | export, all facts including strict convexity (finding L: the cited `lam_pos`, `lam_ge`, `lam_succ_le` are `W6SeqData` names; use these instead) |

## Approach

* Flow: the per-`t` estimates already existed for the abstract `FlowHyp` (`norm_smoothDisp_le`, `flowII_disp`,
  `flowII_disp_sub`, `flowII_deriv`, `flowII_deriv_sub`, `holoFlow_eq_integral`, `holoFlow_smooth_eq`,
  `fderiv_holoFlow_smooth`, `stepFlow_translate`, `stepFlow_real`, `stepImage_mem`). `ExportFlowCore` instantiates
  them for the concrete step flow of any `StepCore` at every `t ∈ [-1,1]` (`StepCore.flow_data`), with the margins
  `M₀ ≤ M_F` (`M_sum`), `M₀/(σ/4) ≤ 1/64`, `ρ = σ/8` (`stepDomain_U_margin`); the integer translation law uses
  `shift_int_law` on `U`. `ExportFlow` states the source-facing results for `StepHypSrc` / `StepHypModSrc` through
  `H.hyp.core`, discharging the reality of `F` by `WaveStepHyp.FT_isRealTaylor` / `StepHypMod.FT_isRealTaylor`.
* Shells: `boxIoo_subset_iUnion_shell` gives `⊆`; the reverse inclusion is `sdiff_subset` plus monotonicity of
  `t_l`; uniqueness from pairwise disjointness; the max characterization by unfolding `boxIoo` with positive entries.
* Solve: `StepCore` fields `F_field`, `F_sub`, `M_sum`, `equation`, `R_field`, `R_sub`, `hε`, with
  `stepNhat_fam`, `stepOmegaHat_bound/_sub`, `stepOmegaTail_bound/_sub`, `stepFun_isSmoothing`. For `N̂` on all
  of `𝒫`: its coefficients are constant in `θ`, so it is the same Taylor polynomial on a strip of any width
  (`homNhatTaylorWide`, same fields, `rfl`), and `stepFun_field` / `stepField_differentiableAt` apply at every point.
* Lambda: strict convexity by the strict Cauchy–Schwarz `xy + m < √(x²+m)√(y²+m)` for `x ≠ y`; `f'` strictly
  increasing from `StrictConvexOn.strictMonoOn_deriv`; the increment identity from `λ_{j+1}² − λ_j² = 2j+1`.

## Checks

* Builds (gate `w_build.sh`, one module per call, in import order), last runs:
  `w_build.sh /root/code/KAM-inp-wpj KAM.Wave.Seq.ExportLamFacts KAM.Wave.Measure.ExportShells
  KAM.Wave.KamStep.ExportFlowCore KAM.Wave.KamStep.ExportFlow KAM.Wave.KamStep.ExportSolve`, then
  `KAM.Wave.Algebra.ExportW0n`, then (after the rename) `KAM.Wave.KamStep.ExportFlowCore KAM.Wave.KamStep.ExportFlow`:
  ```
  ✔ [2147/2147] Built KAM.Wave.Seq.ExportLamFacts (3.0s)
  ✔ [2597/2597] Built KAM.Wave.Measure.ExportShells (2.1s)
  ✔ [3436/3436] Built KAM.Wave.KamStep.ExportFlowCore (8.5s)
  ✔ [3442/3442] Built KAM.Wave.KamStep.ExportFlow (5.3s)
  ✔ [3441/3441] Built KAM.Wave.KamStep.ExportSolve (3.7s)
  ✔ [3277/3277] Built KAM.Wave.Algebra.ExportW0n (2.5s)
  Build completed successfully
  ```
  No warnings in the new files (single-file checks with `w_lean.sh` print nothing).
* `w_lint.sh /root/code/KAM-inp-wpj`: exit 0; tail in the final section below.
* `main_shortname_check.py` on the six modules: exit 0, `short-name check OK (no reused public short name)`
  (a first run flagged `FlowHyp.of_le` against Mathlib's `of_le`; renamed `FlowHyp.weakenFieldBound`).
* `#print axioms` (via `w_lean.sh` on a scratch file): every one of `lamBasis_facts`, `lamFun_strictConvexOn`,
  `shellGeom`, `shellSet_partition`, `iUnion_shellSet_eq_box`, `stepFlowLemma`, `stepFlowLemmaMod`,
  `stepFlow_fFlow`, `stepFlow_fPar`, `stepFlow_fDer`, `stepFlowMod_fFlow`, `stepFlowMod_fPar`, `stepFlowMod_fDer`,
  `stepSolveLemma`, `stepSolveLemmaMod`, `stepNhat_isSmoothing_univ`, `wave_weight_step`, `wave_algebra_w0n`
  depends on axioms: `[propext, Classical.choice, Quot.sound]`.

## Uncertainties and deviations (for the auditor)

1. Flow, "the flow exists on `U`": encoded as `φ^t w ∈ V` plus the integral identity; existence and uniqueness
   of the flow itself are `bpW:w1:flow` (the `FlowHyp` hypotheses are exported as holding, with `M = M_F`).
2. Flow (ii): the operator norms are those of `stepTheorem` clause (v): `‖DΨ^t(w)‖` for
   `DΨ^t(w) : 𝒫^p → 𝒫^{p_+}` (`|Dφ^t − I|_{p→p_+,r}`), with `Dφ^t = I + ι ∘ DΨ^t` stated. Clause (iv), translation:
   stated as `w + τ_k ∈ U` and the law for all `k ∈ ℤ²`; with `−k` this gives `U + τ_k = U`.
3. Shells: the statements assume `0 < t₀` only; the blueprint's `t₀ ≤ 1/2` is not needed (the exports contain the
   blueprint's case). Disjointness in (i) is stated for indices `≥ k` as in the blueprint
   (`shellSet_pairwise_disjoint` gives all pairs).
4. Solve: `F ∈ T_{s−σ}` is the type `HomTaylor_gen a p p_+ (s−σ)`. The parenthetical "(indeed `p'`)" is covered
   in the non-modified case (`p' = p_+`); in the modified case (`p' = p+1`) `N̂ ∈ S_{p+1}` is NOT exported (only
   `S_{p_+}`). In the modified case the `R` of the export is the `StepCore` Taylor polynomial `H.hyp.core.R ξ`
   (of the modified field `X' = D_ρ ∘ X`, typed at `p_+`), as in `stepTheoremMod`; `F` is solved from the `p+1`
   family `H.hyp.R1`. The `Ω̂` clause uses sup and Lipschitz bounds uniform in `j`, which implies the blueprint's
   `sup_j (…) ≤ 3ε` (same encoding as `stepTheorem` (iii)).
5. Lambda: "`f'` strictly increasing" is proved on all of `ℝ` (the blueprint does not name the domain).
6. Generic `StepCore` lemmas in `ExportFlowCore` / `ExportSolve` (`StepCore.flowT_hyp`, `StepCore.solve_*`, …)
   assume the `StepCore` structure; they are helpers. The source-facing statements are `stepFlowLemma*`,
   `stepFlow*_f*`, `stepSolveLemma*` with only the step data `StepHypSrc` / `StepHypModSrc`. The one conditional
   helper with a non-source premise is `StepCore.phiT_real_of_FT_real` (assumes `FT` real); it is discharged in
   the source-facing exports.

## Suspected errata

None in the pinned sources. Graph-reference defects (not source errata), confirming the audit: `bpW:w5:solve`'s
LEAN_REF `KAM.Wave.FT_isRealTaylor` does not exist (use `KAM.Wave.WaveStepHyp.FT_isRealTaylor`,
`KAM.Wave.StepHypMod.FT_isRealTaylor`); lambda-facts' `lam_pos`, `lam_ge`, `lam_succ_le` are `W6SeqData` names
and `lam_le`, `lam_facts` state other facts (use `lamBasis_facts`).

## Final checks (run at the end, foreground)

`/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpj`: exit 0, tail:
```
check_lean_modules: PASS (4059 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```
`python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-wpj
KAM.Wave.Seq.ExportLamFacts KAM.Wave.Measure.ExportShells KAM.Wave.KamStep.ExportFlowCore
KAM.Wave.KamStep.ExportFlow KAM.Wave.KamStep.ExportSolve KAM.Wave.Algebra.ExportW0n`: exit 0,
`short-name check OK (no reused public short name)`.

## W-SOLVE-FIX (closes audit 1, finding F1: `bpW:w5:solve`, modified case, "(indeed `p'`)")

Blueprint `w5-kamstep.tex:355–356`: `N̂ ∈ S_{p_+}(𝒫)` "(indeed `p'`)", with `p' = p+1` in the modified case
(`:335–336`). Fix: `KAM.Wave.stepSolveLemmaMod` is **extended in place**. Its hypothesis (`H : StepHypModSrc …`)
and every previous conjunct are unchanged; two conjuncts are inserted in the `∀ ξ ∈ Π` block right after the
`S_{p_+}(𝒫)` clause. No other file is changed; no consumer of `stepSolveLemmaMod` exists.

### AUDIT FOCUS

* `KAM.Wave.stepSolveLemmaMod`, `KAM/Wave/KamStep/ExportSolve.lean:286`. New conjuncts (lines 295–300), for every
  `ξ ∈ Par`:
  ```lean
  IsSmoothing (p := p) (pb := p + 1) H.ha (stepRho_nn2 H.hp) univ
    (waveStepFun H.ha (homPP H.hp H.hpb) (homNhatTaylor_gen (H.hyp.core.R ξ)))
    (stepField H.ha H.hp (homModPP1 p) (homNhatTaylor_gen (H.hyp.R1 ξ))) ∧
  (∀ w, stepField H.ha H.hp H.hpb (homNhatTaylor_gen (H.hyp.core.R ξ)) w =
    stepRhoK a p pb H.hyp.hc
      (stepField H.ha H.hp (homModPP1 p) (homNhatTaylor_gen (H.hyp.R1 ξ)) w)) ∧
  ```
  The first says `N̂ ∈ S_{p+1}(𝒫)` (holomorphic on all of `𝒫`, with a holomorphic field into the `p+1` weights and
  `DN̂·W = ϖ_{p+1,p}(X, W)` everywhere). The Hamiltonian is **literally the same** `N̂` as in the other clauses,
  `waveStepFun … (homNhatTaylor_gen (H.hyp.core.R ξ))` with `H.hyp.core.R` the reweighted (`p_+`) Taylor family
  that appears in the equation `R + DN·X_F = N̂ + â₀`. Its `p+1` field is the field of `N̂` of the `p+1` Taylor
  element `H.hyp.R1 ξ` (the family from which `F` is solved, W5-MODIFIED, and that the D2 bridge
  `StepOmegaBridge` uses for `ω_+`, `Ω_+`). The second conjunct identifies the two weightings of the field of this
  one Hamiltonian: the `p_+` field (that of the `S_{p_+}` clause and of `|X_N̂|^λ ≤ 6ε`) is `D_ρ` of the `p+1` field.
  It follows from uniqueness of the field (`isSmoothing_unique_apply`, nondegeneracy of `ϖ_{p_+,p}`) and
  `IsSmoothing.rhoK`.
* Helpers (distinct names, same file, namespace `KAM.Wave.StepHypMod`, assume only `H : StepHypMod …` and
  `ξ ∈ Par`; not source-facing on their own):
  `nhat_fun_eq_R1` (`:201`): `waveStepFun … (homNhatTaylor_gen (H.core.R ξ)) =
  waveStepFun … (homNhatTaylor_gen (H.R1 ξ))` as functions on `𝒫` (from `stepFun_nhat_taylorRho`, i.e.
  `homNhat_taylorRho` / `homNhat_reweight`, after `H.core.R ξ = stepTaylorRho …`, `H.R1 ξ = stepTaylorP1 …` by
  `stepTaylorFam_of_mem`, the same identities as `StepHypMod.core_R_eq` / `R1_eq` of `StepOmegaBridge`, inlined so
  that `ExportSolve` does not import that module);
  `nhat_isSmoothing_p1_univ` (`:215`): the first new conjunct for `StepHypMod` (rewrite by `nhat_fun_eq_R1`, then
  `stepNhat_isSmoothing_univ` at `pb := p + 1`);
  `nhat_field_eq_rhoK` (`:223`): the second new conjunct.
* Rule 6: no premise added. `stepRho_nn2 H.hp : 0 ≤ (p+1)+p` and `H.hyp.hc : p_+ ≤ p+1` are proofs (typing data)
  derived from the step data (`hc` from `0 ≤ β`, `2β ≤ p+1−p_+`), not hypotheses.

### Graph record

`bpW:w5:solve` → `KAM.Wave.stepSolveLemma, KAM.Wave.stepSolveLemmaMod` (both now cover the full statement; in the
non-modified case `p' = p_+` and "(indeed `p'`)" is the existing `S_{p_+}(𝒫)` clause). Uncertainty 4 above
("`S_{p+1}` is NOT exported") is superseded by this section.

### Checks

`/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpj KAM.Wave.KamStep.ExportSolve`:
`✔ [3441/3441] Built KAM.Wave.KamStep.ExportSolve (12s)`, `Build completed successfully (3441 jobs).`, no warning
in `ExportSolve.lean`. `wc -l`: 332 lines.

`#print axioms` (scratch file under `.lake/abi-scratch`, via `w_lean.sh`, removed afterwards):
```
'KAM.Wave.stepSolveLemmaMod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypMod.nhat_fun_eq_R1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypMod.nhat_isSmoothing_p1_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypMod.nhat_field_eq_rhoK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSolveLemma' depends on axioms: [propext, Classical.choice, Quot.sound]
```
`python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-wpj
KAM.Wave.KamStep.ExportSolve`: exit 0, `short-name check OK (no reused public short name)`.

`/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpj`: exit 0, tail:
```
check_lean_modules: PASS (4059 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```
`git diff --check` clean; `git diff -- KAM/Frozen manifest KAM.lean README.md` empty.

### Uncertainties, errata, deviations

* Design choice: `stepSolveLemmaMod` was extended rather than complemented, so the existing two-reference LEAN_REF
  list becomes complete. Projections into its `∀ ξ` block shift by two positions (no consumer exists).
* The packet `W-w5a.nodes.md:909` drops "(indeed `p'`)" (audit F1); a packet defect, not a source erratum.
  No suspected errata in pinned sources. No heartbeat or design signals (module builds in ~12 s).

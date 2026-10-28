# Lean design for blueprint-N Parts 6 and 7 (normal form; stability)

Design v2 (Revision 2 after design audit 1, Section 10), 2026-10-28, branch `inp-design-n67` (off `inp` at `40237a3`). Planning evidence, not approved Lean; nothing here
is frozen and these parts have no frozen theorem (no provider; overnight rule D29: no new freezes). Modeled on
`PART145-LEAN-DESIGN.md` (with its two audits) and track K's `PART23-LEAN-DESIGN.md`. Scope: every node of
`docs/graph/N/DEPGRAPH.md` sourced from `blueprint-N/parts/p6-normal-form.tex` (40 nodes) and `p7-stability.tex` (63 nodes),
all `NOT_STARTED`/`EXTERNAL`.

**The signatures.** Every result node of Parts 6, 7 has its exact Lean statement in
`/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean` (untracked; copied verbatim in Appendix A).
- 854 lines, sha256 `c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f` (v1: 790 lines, `f64cf1e3…`).
  `inp_sig_check.sh /root/code/KAM-inp-design-n67 .drafts/scratch/NPart67Signatures.lean` (scratch copy)
  exits 0 with exactly 43 diagnostics, all `declaration uses 'sorry'`; no `set_option`, no `maxHeartbeats`.
- Every `def`/`structure` has its real body; every `theorem ... := sorry` is a prover obligation.
- Section 0 of the file copies `projMode`, `truncate` verbatim from `NPart145Signatures.lean` B.8 (`Weighted/Projections`,
  package W4-7, not yet on `inp`) so that the file elaborates; they are not new declarations and go away on landing.
- Needs only built modules (`KAM.Weighted.{Domains,Norm,Coefficients}`, `KAM.Canonical.{Setting,Flow}`, `KAM.ODE.Basic`,
  `KAM.Strip.RealRestriction`, `KAM.Nekhoroshev.Interfaces.Norms`, frozen defs). The C5-8/9/10 signatures (`ComposeData`,
  `composition_*`, `transform`, `CanonData`, `canonical_map_*`) are cited in the plans, not imported.

## 0. Decisions in brief

1. **Two shared layers.** Part 6 is `KAM/NormalForm/*`, namespace `KAM.NormalForm` (shared N, P: track P derives CP10's
   averaging from the Iterative Lemma with `Λ = {0}`); Part 7 is `KAM/Stability/*`, namespace `KAM.Stability` (shared N, I:
   track I may reuse `energy_core`, `no_exit`, Lemmas 1-2 — prospective reuse, no current blueprint-I citation; Section 8). `NormalForm` imports only `Weighted`, `Canonical`; `Stability` imports
   `NormalForm`, `Weighted`, `Canonical`, `KAM.ODE` and the *leaf* `KAM.Nekhoroshev.Interfaces.Norms` (`euclid`, Part 1
   `norm-compare`; it imports only `KAM.Fourier.Derivative`). No other `KAM.Nekhoroshev.*` import; no provider, no frozen
   theorem anchor, no `DRAFT_SORRY` anchor anywhere.
2. **Carriers.** As Parts 4/5: phase space `(Fin n → ℂ) × (Fin n → ℂ)` angles first; Part 6 takes `D : Set (Fin n → ℂ)`
   (arbitrary, as P needs); Part 7 takes `D : Set (Fin n → ℝ)` and feeds Parts 4-6 the set `cpx D = realInclusion n '' D`
   (so `polyNbhd (cpx D) r = KAM.actionNbhd D r`, `actionNbhd_eq_polyNbhd`). Real phase space `(Fin n → ℝ) × (Fin n → ℝ)`,
   `U_ϱD = realNbhd D ϱ`, `W_ϱ = realStrip D ϱ = univ ×ˢ realNbhd D ϱ`. Max norms (Pi); Euclidean only via `euclid` and
   `dotProduct` (`⬝ᵥ`) in the convexity argument. Never `EuclideanSpace`.
3. **Bounds, not norms.** As Parts 4/5 (`WBound D r s u M`): every "`|u| = δ`" premise is "`WBound … u δ`"; conclusions are in
   terms of the bound. `P_Λ g = g` is coefficient vanishing `∀ I k, k ∉ Λ → coeff g I k = 0`. `|g|_*` is `starNorm` over an
   explicit decomposition `IsDecomp D r s g gj rj sj Mj` (`g = ∑ⱼ gⱼ` as functions, `Fin N`-indexed).
4. **Concrete constructions, not existentials, in the Iterative Lemma.** `homGen` (φ), `homRes` (ξ = `P_Λ T_K f`),
   `iterMap` (Φ = `flow X_φ (Dom (r-ρ)(s-σ)) 1`, the same `flow` as `CanonData.omega`/`ComposeData.omega` with data
   `(r-ρ,s-σ;r,s)`), `iterG` (g₊), `iterF` (f₊ := `H∘Φ - h - g₊`). Item (c)'s identity is then definitional; its content is
   `f₊ ∈ O(r-2ρ,s-2σ)` and the estimate (d). The Normal Form Lemma keeps the blueprint's "there are Ψ, g, f_*".
5. **Direct-divisor form is primary.** The blueprint proves `iterative` from (N1),(N2),`KLr ≤ α/p` and observes
   (`iterative-direct`) that only the divisor bound `(N-dir)` on `V_rD` is used. In Lean the obligations are stated once,
   under the source premise structure `IterHyp` whose field `divisor` *is* `(N-dir)` (`DivisorBound (polyNbhd D r) K Λ h (α/q)`);
   `iterHyp_of_source` derives `IterHyp` from the theorem's own hypotheses through `divisor`. So `bpN:p6:iterative` =
   `iterHyp_of_source` + `iterative_direct_a..e`; `bpN:p6:iterative-direct` = `iterative_direct_a..e`. Both statements are
   exactly the blueprint's (no hypothesis added, `(N-dir)` is a stated source premise of the corollary). Same for
   `homological_direct`/`homological`. Part 11 (`p11:hom`, `n` angles and `n+2k` parameters) consumes the
   parameter-capable core `homological_param` (independent parameter dimension `m`, arbitrary frequency field
   `ω : ℂᵐ → ℂⁿ`); `homological_direct` is its `m = n`, `ω = freq h` specialization (Revision 2, F3).
6. **Real systems via `realH G = Re G ∘ ι` (total).** The blueprint's `G^ℝ` (= `G` on `W_r`, `0` elsewhere) is replaced by
   `Re G ∘ realInclusion₂` everywhere; both agree on the open `W_r`, so the fields `X_{G^ℝ}` agree there, and every statement
   only looks at `W_ϱ ⊆ W_r` (blueprint Remark `p3:totality`). Bonus: `KAM.realHamiltonian h f = realH (h∘snd + f)` by
   unfolding (`realHamiltonian_eq_realH`), the Part 10 bridge. Orbits: `IsOrbit G D ϱ J z :=
   KAM.ODE.IsSolutionIn (hamiltonianVectorField (realH G)) (realStrip D ϱ) J z` (Part 3's `IsSolIn`).
7. **Time bounds by multiplication; `T: D → (0,∞]` by a predicate.** `|t| ≤ sr e^{κ/6}/(5ε)` is `|t|·5ε ≤ sr e^{κ/6}`, which
   encodes `T = ∞` at `ε = 0` with no `EReal`. In `transfer`/`stopped_extension` the time bound is a predicate `adm I t`
   assumed monotone in `|t|`. Sup-type data (`Ω = max ‖ω‖₂`, `sup‖∂_θf‖`) are "any bound `Ω`/`B`" hypotheses; the max is one
   instance, so the statement family has the blueprint's statement as its sharpest member.
8. **Projection without `EuclideanSpace`.** `Π_Λ` is never a definition: `IsOrthProj P` (idempotent, `dotProduct`-symmetric
   linear map) plus `exists_orthProj V` (proof via `LinearMap.BilinForm` orthogonal complement of the dot form, nondegenerate
   on `ℝⁿ`, and `Submodule.linearProjOfIsCompl`). Closeness to resonance `IsCloseToRes` is `∃ w ∈ R_Λ, ‖ω(I) - w‖₂ ≤ δ`
   (= `dist₂(ω, R_Λ) ≤ δ`, attained). `resonant_gradient` concludes `∂_θ g^ℝ ∈ span_ℝ Λ` (`= Π^⊥∂_θg = 0`).
9. **Packages.** 16 prover packages (N6-1..8, S7-1..8), 150-650 lines each except N6-8 (≈950 lines over three modules,
   two sessions), about 7,050 lines, 6 waves; Part 6 waves 3-4 wait
   for C5-8/9/10 and W4-7. Section 7.
10. **Hard rules** (verbatim, binding for every Lean brief):
    1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration failure is a design signal to refactor or split the proof, not something to mask with a larger budget.
    2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules, preserving public import paths as cheap facades.

## 1. Carriers and standing objects

| Object | Lean | Notes |
|---|---|---|
| `Z_K` | `zBall n K = {k \| modeSize k ≤ K}` | the cut-off set of `truncate K` |
| `ω = ∂_I h` (complex) | `freq h I i = fderiv ℂ h I (Pi.single i 1)` | real points: `freq_realInclusion` = frozen `frequencyMap` |
| `k·v` | `dotC k v` | |
| `q = p/(p-1)` | `conjExp p` | statements carry `p`, `1 < p` |
| (N1), (N2), (N-dir) | `IsNonresonant D K α Λ h`, `FreqLipschitz D r L h`, `DivisorBound V K Λ h c` | |
| `g = ∑ gⱼ`, `\|g\|_*` | `IsDecomp D r s g gj rj sj Mj`, `starNorm r s ρ σ rj sj Mj` | `Mⱼ` bound `\|gⱼ\|_{rⱼ,sⱼ}` |
| φ, ξ | `homGen K Λ h f`, `homRes K Λ f = projMode Λ (truncate K f)` | |
| Φ, g₊, f₊ | `iterMap D r s ρ σ K Λ h f`, `iterG K Λ g f`, `iterF D r s ρ σ K Λ h g f` | |
| `u = qδ/(ᾱρσ)` | `iterU α p δ ρ σ` | `ᾱ = 2πα` written out |
| hypotheses of the Iterative Lemma | `IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj` (Prop structure) | source premises only |
| `Φ₀∘⋯∘Φₘ` | `chain Φ m` | |
| `N = ⌊κ/(12 ln 2)⌋` | `nfSteps K s` | `normal-form#data` |
| `D ⊂ ℝⁿ` in `ℂⁿ` | `cpx D` | |
| `U_ϱD`, `W_ϱ` | `realNbhd D ϱ`, `realStrip D ϱ` | `realInclusion₂_mem_Dom_iff` (`s > 0`) |
| `G^ℝ`, orbit | `realH G`, `IsOrbit G D ϱ J z` | |
| `Ψ` on real points | `reMap Ψ` | |
| `∂_θ`, `Q = D²h_ℝ` (real) | `thetaGradR G x`, `hessR hR I ξ η` | `hR = KAM.Nekhoroshev.realPart h` |
| `\|·\|_*` | `IsActionNorm N` | instances `isActionNorm_norm`, `isActionNorm_euclid` |
| `Π`, `R_Λ`, `span Λ` | `IsOrthProj P`, `resSpace Λ`, `resSpan Λ` | `exists_orthProj` |
| δ-close, convex, quasi-convex, `‖Q‖ ≤ M` | `IsCloseToRes`, `IsMConvex`, `IsQuasiConvex`, `HessBound` | Euclidean |
| (RS), `ρ = δ/(4M)`, admissible | `ResSetting D r s Λ h m M g fs Mg η ζ δ`, `resRho δ M`, `IsAdmissible D δ M I₀` | |

Standing structures (Prop): `IsDecomp`, `IterHyp`, `IsActionNorm`, `IsOrthProj`, `ResSetting`. No instances.

## 2. What upstream already provides (cited, not re-planned)

| Need | Upstream declaration (module, status) | Used by |
|---|---|---|
| class, coefficients, bound | `InClass`, `coeff`, `WBound`, `WBound.mono`, `wbound_iff` (`Weighted/Norm`, proved) | all |
| `Dom`, `polyNbhd`, monotonicity, `actionNbhd_eq_polyNbhd` | `Weighted/Domains` (proved) | all |
| `û_k` holomorphic; `∂` on coefficients; series; representation | `coeff_differentiableOn`, `coefficients_deriv`, `coefficients_series`, `coefficients_repr` (`Weighted/Coefficients`, proved) | `homological` (hom-def, hom-eq), `resonant_gradient` |
| sup ≤ weighted | `sup_le_wbound` (`Weighted/SupWeighted`) | `theta_derivative`, `no_exit` (term A) |
| Cauchy in the norm | `cauchy_theta` (`Weighted/Cauchy`) | `theta_derivative` (`s' ↓ 0`), `resonant_gradient` |
| C.1 Cauchy | `general_cauchy` (`Weighted/Parametric`) | `preimage` (contraction) |
| bracket estimate | `wbound_bracket` (`Weighted/Bracket`) | `bracket_g`, it-integrand |
| `P_S`, `T_K`, bounds, tail | `projMode`, `truncate`, `projections`, `truncation_tail` (`Weighted/Projections`, **W4-7, signatures only**) | `homological`, it-terms, `normal_form` |
| bracket, antisymmetry, `{u,v}=Du·X_v`, `RealOn`, `scaledNorm`, `symplFormC` | `Canonical/Setting` (proved) | all |
| `flow`, `flow_a`, `flow_c`, `flow_e` | `Canonical/Flow`, `FlowInverse` (proved) | `iterMap`, reality |
| canonical map (a)-(e) | `CanonData`, `canonical_map_a..e` (`Canonical/CanonicalMap`, **C5-10, signatures**) | `iterative_direct_a,b,e` |
| composition, integral corollary, reality | `ComposeData`, `composition_series`, `composition_integral`, `composition_real` (**C5-8, signatures**) | `iterative_direct_c,d,e` |
| Lie transform | `transform`, `liftRemainder` (**C5-9, signatures**) | it-taylor |
| symplectic form tools | `symplFormC_*`, `det_eq_one_or_neg_one`, `map_hamiltonianJ_comp` (`Canonical/SymplecticForm`, proved) | `telescope`, `conjugation` |
| ODE layer | `KAM.ODE.IsSolutionIn`, `gen_uniqueness`, `gen_maximal`/`IsMaximalSolution`, `gen_continuation_periodic`, `gen_exit`, `ham_smooth(_c1)`, `ham_energy`, `ham_periodic`, `angleShift` (`KAM/ODE/*`, proved) | `real_system`, `transfer`, `stopped_extension`, `exit_ball`, `energy_core` |
| real restriction, `X_H = X_{h+f}∘ι` | K `KAM.real_restriction`, `hamiltonian_real`, `hamiltonian_real_fderiv`, `holomorphic_regularity` (`KAM/Strip/*`) | `real_system`, `conjugation` (`cj-real`) |
| Euclidean norm, comparisons | `KAM.Nekhoroshev.euclid`, `norm_le_euclid`, `modeSize_euclid_compare` (`Interfaces/Norms`, proved) | Part 7 energy, Prop 2 (`√n`) |
| Mathlib | `ContractingWith.exists_fixedPoint` (p7:ext-banach), `taylor_mean_remainder_lagrange` (p7:ext-taylor), `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` (K:ext-mvt), `LinearMap.BilinForm.orthogonal`, `Submodule.linearProjOfIsCompl` (p7:ext-linalg), `Real.add_one_le_exp`, `Real.exp_one_gt_d9`, `Real.log_two_gt_d9` (ext-numerics, ext-num), `HasFDerivAt.comp` (p6:ext-chain) | |

Searched and **not** reused (no parallel representation is introduced): track K/Planetary/Kepler normal-form code works on
`KAM.Strip` single-strip functions without action dependence (`O(r,s)`-style classes do not exist there); `KAM/Planetary`'s
averaging uses its own chart and is not a Lie-transform iteration. Track P's Part 2 will *consume* `KAM.NormalForm`.

## 3. Node tables

### 3.1 Part 6 (`KAM/NormalForm/`)

| Node | Lean | Module |
|---|---|---|
| `ext-numerics`, `ext-chain` | none (Mathlib: `Real.exp_one_gt_d9`, `Real.log_two_gt_d9`, `tsum_geometric_of_lt_one`, `HasFDerivAt.comp`) | — |
| `p6#data` | `zBall`, `freq`, `dotC`, `conjExp` | `Setting` |
| `setting` | `IsNonresonant`, `FreqLipschitz`, `DivisorBound`, `IsDecomp`, `starNorm` | `Setting` |
| `lipschitz` | `lipschitz`, `lipschitz_entries` | `Setting` |
| `divisor` | `divisor` | `Setting` |
| `homological` | `homGenParam`, `homResParam`, `RealOnParam`, `homological_param` (core), `homGen`, `homRes`, bridges `homGen_eq_homGenParam`, `homRes_eq_homResParam`, `realOnParam_iff_realOn`, `homological_direct`, `homological` | `Homological` |
| `bracket-g` | `bracket_g` | `BracketDecomp` |
| `iterative` | `iterMap`, `iterG`, `iterF`, `iterU`, `IterHyp`, `iterHyp_of_source` + `iterative_direct_a..e` | `IterativeMap` (a,b, `iterHyp_of_source`), `IterativeRemainder` (c,d), `IterativeReal` (e), `Iterative` (pure facade, created by N6-7) |
| `iterative-direct` | `iterative_direct_a..e` | as above |
| `telescope` | `chain`, `telescope` | `Telescope` |
| `normal-form`, `normal-form#data` | `nfSteps`, `normal_form` | `Steps` (step sequence, private), `Arith` (numerics), `NormalForm` |
| `nonresonant-case` | `nonresonant_case` | `NormalForm` |
| (off-graph) `action-displacement`, `iterative-special`, `deviations`, `consumers` | none: corollary = `normal_form` (c) + (i); remarks | — |
| all `stepN:p6:*` | none (proof steps; Section 7.1) | — |

### 3.2 Part 7 (`KAM/Stability/`)

| Node | Lean | Module |
|---|---|---|
| `ext-banach`, `ext-taylor`, `ext-num`, `ext-linalg` | Mathlib (Section 2); `ext-linalg` packaged as `exists_orthProj` | — / `Energy` |
| `setting` | `cpx`, `realNbhd`, `realStrip`, `realH`, `IsOrbit`, `reMap`, `thetaGradR`, `hessR`, `isOpen_realNbhd`, `realNbhd_mono`, `realInclusion₂_mem_Dom_iff`, `realHamiltonian_eq_realH`, `freq_realInclusion` | `Setting` |
| `real-system` | `real_system` | `RealSystem` |
| `theta-derivative` | `theta_derivative` | `Gradient` |
| `resonant-gradient` | `resSpan`, `resonant_gradient` | `Gradient` |
| `conjugation` | `conjugation` | `Conjugation` |
| `preimage`, `preimage-nfl` | `preimage`, `preimage_nfl` | `Preimage` |
| `transfer`, `stopped-extension`, `exit-ball` | `IsActionNorm`, `isActionNorm_norm`, `isActionNorm_euclid`, `transfer`, `stopped_extension`, `exit_ball` | `Transfer` (`exit_ball`, `IsActionNorm` in `Setting`) |
| `nonresonant` | `nonresonant` | `Nonresonant` |
| `resonance-data` | `IsOrthProj`, `resSpace`, `IsCloseToRes`, `IsMConvex`, `IsQuasiConvex`, `HessBound` | `Energy` |
| `energy-core` | `energy_core` | `Energy` |
| `s-energy#rs` | `ResSetting`, `resRho`, `IsAdmissible` | `Resonant` |
| `admissible`, `no-exit`, `resonant-lemma2` | `admissible`, `no_exit`, `resonant_lemma2` | `Resonant` |
| (off-graph) `resonant-lemma1` | `resonant_lemma1` (for track I; same package, cheap) | `Resonant` |
| `resonant-prop2` | `resonant_prop2` | `ResonantStability` |
| `factor-e`, `errata`, `dictionary`, `consumers` (remarks, not graph nodes) | none | — |
| all `stepN:p7:*` | none (proof steps; Section 7.1) | — |

## 4. Conventions binding for all modules

- Statements are exactly Appendix A. Binder names may change; hypotheses, carriers and conclusions may not. A needed change
  goes to the orchestrator for a statement audit.
- `ᾱ = 2πα` and `κ = 2πKs` are written out (`2 * Real.pi * α`, `2 * Real.pi * K * s`); never a local notation in statements.
- Widths: `Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2)` etc. literally as in Appendix A, so that `CanonData`/`ComposeData` lemmas
  apply by `rfl` on `omega` (`iterMap`'s flow domain is `Dom n D (r - ρ) (s - σ)` = `CanonData.omega` = `ComposeData.omega`
  for `(r,s,r',s') = (r-ρ,s-σ,r,s)`).
- Two-sided `HasDerivAt` everywhere (Part 3 `IsSolutionIn`); orbit intervals are `OrdConnected` sets containing `0`.
- Reality hypotheses are `RealOn (Dom …) _` for complex functions (`h` as `fun w => h w.2`) and "maps `range realInclusion₂`
  into itself" for maps.
- Every new file: copyright header, `module`, `public import`, module docstring, `@[expose] public noncomputable section` for
  definition files, `public section` otherwise. Files ≤ 1500 lines (target ≤ 600).

## 5. Departures from the literal blueprint text

1. `G^ℝ := Re G ∘ ι` (total) instead of `G` on `W_r`, `0` off it (Decision 6). Same field on `W_r`; nothing else changes.
2. `f₊ := H∘Φ - h - g₊` by definition (Decision 4); the blueprint's formula `f₊ = 𝓡 + (f - T_Kf)∘Φ` becomes a proof step
   (it-decomp) used for (d).
3. Proof order of `iterative`/`iterative-direct` and `homological` inverted (Decision 5). Statements unchanged.
4. Norm equalities `ε = |f|_{r,s}` are bounds `WBound … f ε` (Decision 3); `|t| ≤ T` is multiplied out; `Ω`, sup bounds are
   "any bound" hypotheses (Decision 7). Each is the blueprint statement at its sharpest instance.
5. `P_Λ g = g` and "trigonometric polynomial with frequencies in `Λ ∩ Z_K`" are coefficient vanishing off `Λ ∩ Z_K` (with
   `InClass`, equivalent by `coefficients_repr`).
6. `Π_Λ` is not a definition; `resonant_gradient` concludes membership in `span_ℝ Λ`; `admissible` takes any orthogonal
   projection `P` onto `span Λ` (Decision 8). `δ`-closeness is the attained-distance form.
7. `real_system` (d) states energy conservation explicitly; "Part 3 theorems apply" is the `ContDiffOn ℝ 1` field of (c)
   (exactly the hypothesis of `gen_uniqueness`, `gen_maximal`, `gen_continuation_periodic`).
8. `preimage_nfl` is stated on the *conclusions* of `normal_form` (holomorphy, reality, displacement of the witness Ψ) rather
   than by re-quoting the theorem, since `normal_form` is existential. It adds no hypothesis beyond the corollary's.
9. `nonresonant` (Prop 1) takes `(N1)` as `IsNonresonant (cpx D) K α {0} h` (complex `freq` at the real points of `D`;
   `freq_realInclusion` identifies it with the frozen `frequencyMap`).

## 6. Blueprint issues (none blocking; for the errata ledger)

1. **Lemma 1 and `action-displacement`, `iterative-special` are not graph nodes** (published graph has no
   `bpN:p7:resonant-lemma1`, `bpN:p6:action-displacement`, `bpN:p6:iterative-special`), although Remark `p7:consumers` says
   track I takes Lemma 1. Designed `resonant_lemma1` anyway (off-graph, same package as Lemma 2); the other two are trivial
   corollaries. Ask the graph writer whether track I's import list needs the node.
2. `p6:normal-form` (b) is used by Prop 2 only through `|g|_{r/2,s/6} ≤ |g₀|_{r,s} + 16cε²` (`stepN:p7:p2-cases`); that needs
   `|g₀|_{r/2,s/6} ≤ |g₀|_{r,s}` (monotonicity) and `|g₀| ≤ ε` (`projections`), both available. No issue, noted for the
   prover of S7-8.
3. `p7:resonant-prop2` assumes the **complex** Hessian bound on `V_rD` in the Euclidean operator norm but (RS) needs the
   **real** `HessBound` on `U_rD`; the restriction (`K:real-restriction`, `D²(Re h∘ι) = Re(D²h)`) is an unlisted one-line step
   of `stepN:p7:p2-red`. Not a defect.
4. Statement-level checks found no false statement. Suspected source defects are those already recorded by the blueprint
   (Remark `p7:errata` (1)-(3); `p6:normal-form` sourcegap `e^{Ks/6}` sign); nothing new.

## 7. Modules, import DAG, packages

```
KAM/NormalForm/Setting ── Weighted.{Domains,Norm}, Canonical.Setting
  ├─ Homological ── Weighted.{Coefficients,Projections,SupWeighted}
  ├─ BracketDecomp ── Weighted.Bracket
  ├─ Telescope ── Canonical.SymplecticForm
  ├─ IterativeMap ── Homological, Canonical.CanonicalMap
  ├─ IterativeRemainder ── IterativeMap, BracketDecomp, Canonical.{Composition,CompositionIntegral,Transform}
  ├─ IterativeReal ── IterativeRemainder, Canonical.Composition
  ├─ Iterative (pure facade over the three; created in N6-7, after its imports exist)
  ├─ Arith (pure numerics: Step 0 bounds, (6.1), (6.2), induction constant, displacement constants)
  ├─ Steps (private step sequence nfState i = (gᵢ, fᵢ, Φᵢ), radii rᵢ sᵢ) ── Iterative, Arith
  └─ NormalForm ── Steps, Telescope
KAM/Stability/Setting ── NormalForm.Setting, Weighted.Domains, KAM.ODE.Basic, Strip.RealRestriction, Nekhoroshev.Interfaces.Norms
  ├─ RealSystem ── KAM.ODE.Hamiltonian, Strip.RealRestriction
  ├─ Gradient ── Weighted.{Cauchy,SupWeighted,Coefficients}
  ├─ Conjugation ── RealSystem, Canonical.SymplecticForm
  ├─ Preimage ── Weighted.Parametric (general_cauchy)
  ├─ Transfer ── Conjugation, KAM.ODE.{Maximal,Continuation,Uniqueness,Exit}
  ├─ Energy ── Setting, KAM.ODE.Hamiltonian
  ├─ Resonant ── Energy, Gradient, Transfer (exit_ball)
  ├─ Nonresonant ── NormalForm.NormalForm, Transfer, Preimage, Gradient
  └─ ResonantStability ── NormalForm.NormalForm, Resonant, Transfer, Preimage
```
No cycles; `KAM.Stability.*` never imported by `KAM.NormalForm.*`. Facade files `KAM/NormalForm.lean`, `KAM/Stability.lean`
re-export (generated root import by `scripts/gen_root_imports.py`; do not hand-edit `KAM.lean`).

Every package proves its nodes exactly as in Appendix A. Hard rules (Section 0.10) go into every brief.

| Package | Nodes | Modules | Lines | After | Wave |
|---|---|---|---|---|---|
| N6-1 | p6#data, setting, lipschitz, divisor | `NormalForm/Setting` | 300 | — (Weighted, Canonical.Setting on inp) | 1 |
| N6-3 | bracket-g | `BracketDecomp` | 150 | N6-1 | 1 (after N6-1, same wave if sequential) |
| N6-4 | telescope | `Telescope` | 250 | — | 1 |
| S7-1 | p7 setting, real-system, exit-ball, `IsActionNorm` | `Stability/Setting`, `RealSystem` | 550 | N6-1 (only `freq`, for `freq_realInclusion`) | 1 |
| S7-5 | resonance-data, energy-core, `exists_orthProj` | `Energy` | 500 | S7-1 | 2 |
| S7-2 | theta-derivative, resonant-gradient | `Gradient` | 300 | S7-1 | 2 |
| N6-2 | homological (parameter core + both forms + bridges) | `Homological` | 700 | N6-1, **W4-7** | 2 |
| S7-3 | conjugation, transfer, stopped-extension | `Conjugation`, `Transfer` | 650 | S7-1 | 2 |
| S7-4 | preimage, preimage-nfl | `Preimage` | 400 | S7-1 | 2 |
| S7-6 | s-energy#rs, admissible, no-exit, Lemma 1, Lemma 2 | `Resonant` | 550 | S7-5, S7-2, S7-3, S7-1 | 3 |
| N6-5 | iterative (a),(b), `iterHyp_of_source` | `IterativeMap` | 400 | N6-2, **C5-10** | 3 |
| N6-6 | iterative (c),(d) (imports `IterativeMap`, never the facade) | `IterativeRemainder` | 650 | N6-5, N6-3, **C5-8, C5-9**, W4-7 | 4 |
| N6-7 | iterative (e); facade `Iterative` | `IterativeReal`, `Iterative` | 250 | N6-6 | 4 |
| N6-8 | normal-form, `#data`, nonresonant-case | `Arith`, `Steps`, `NormalForm` | 950 (two sessions: Arith+Steps / NormalForm) | N6-7, N6-4 | 5 |
| S7-7 | nonresonant (Prop 1) | `Nonresonant` | 450 | N6-8, S7-2, S7-3, S7-4 | 6 |
| S7-8 | resonant-prop2 | `ResonantStability` | 550 | N6-8, S7-6, S7-3, S7-4 | 6 |

Total ≈ 7,050 lines, 6 waves (largest package N6-8 ≈ 950 lines split over `Arith`, `Steps`, `NormalForm`; no file > 600 planned). Critical path: (C5-8 → C5-9) → N6-6 → N6-7 → N6-8 → S7-7/S7-8. Track I can start from S7-5/S7-6
(wave 3) without waiting for Part 6; track P from N6-5..N6-7 (Iterative Lemma, `Λ = {0}`).

### 7.1 Proof plans

**N6-1.** `divisor`: for `I ∈ polyNbhd D r` pick `I₀ ∈ D`, `‖I-I₀‖ < r`; `‖dotC k v‖ ≤ modeSize k · ‖v‖` (sum of
`|kᵢ||vᵢ|`, Pi sup norm), reverse triangle; `α - α/p = α/conjExp p` (`field_simp`, `p > 1`). `lipschitz`: segment
`[I₀, I] ⊆ polydisc I₀ r ⊆ polyNbhd D r` (convex), `Convex.norm_image_sub_le_of_norm_fderiv_le` for `freq h` (holomorphic
by `holomorphic_regularity`); entry form via the operator-norm bound `‖A‖ ≤ n max|Aᵢⱼ|` on the Pi sup norm
(`ContinuousLinearMap.opNorm_le_bound`, `Finset.sum_le_card_nsmul`).

**N6-2.** Prove `homological_param` first (all arguments below with `ω` in place of `freq h` and the directional
derivative `∑ᵢ ∂_{θᵢ}φ·ωᵢ` in place of the bracket); then `homGen_eq_homGenParam`, `homRes_eq_homResParam` (`rfl`/`funext`),
`realOnParam_iff_realOn` (`realInclusion₂ n x = (realInclusion n x.1, realInclusion n x.2)`), and `homological_direct` from
the core with `q = conjExp p` (`1 ≤ conjExp p` from `1 < p`), `ω = freq h` (holomorphic by `hh` and `DifferentiableOn.fderiv`
on the open `polyNbhd`), plus `poissonBracket φ (h∘snd) = ∑ⱼ ∂_{θⱼ}φ · ωⱼ`. Details: write `homGen = fourierSeries a` with `aₖ(I) = 𝟙_{Z_K∖Λ}(k) f̂ₖ(I)/(2πi k·ω(I))`; `Z_K` finite
(`Set.Finite` of `modeSize k ≤ K`: bounded integer box); holomorphy of `aₖ` from `coeff_differentiableOn` and
`DifferentiableOn.mul` and `DifferentiableOn.inv` after rewriting `a / b = a * b⁻¹` (`DifferentiableOn.div` has a scalar
domain `s : Set 𝕜` and does not apply on the parameter carrier; divisor nonzero by `hdir`); `coefficients_series` gives class, coefficients and the bound
`q δ/(2πα)` (pointwise `|aₖ| ≤ q|f̂ₖ|/(2πα)` and `hδ`'s summed bound). Equation by coefficients: `coefficients_deriv`
(`dtheta`), multiplication by `θ`-independent `ωⱼ` acts coefficientwise (direct integral computation: `coeff (fun z => c z.2 * u z)
I k = c I * coeff u I k`), `poissonBracket φ (h∘snd) = ∑ⱼ dtheta j φ · ωⱼ` (the `dI φ` terms meet `∂_θ(h∘snd) = 0`), then
`coefficients_repr` (uniqueness of coefficients: two class functions with equal coefficients agree, `KAM.eq_zero_of_torusCoeff_holomorphic`).
`homRes` via `projections` twice (`truncate` then `projMode Λ`). Reality: `conj (coeff f (ι I) k) = coeff f (ι I) (-k)`
(conjugate the torus integral), `Λ = -Λ`, `Z_K` symmetric, finite sum with `ā_k = a_{-k}` is real. `homological` = `divisor` + direct.

**N6-3.** `wbound_bracket` per term with `(u,v;r₀,s₀) = (gⱼ, φ; rⱼ, sⱼ)` and the algebra
`1/e(1/((rⱼ-r+ρ)σ) + 1/((sⱼ-s+σ)ρ)) = 2/(eρσ)·½(ρ/(rⱼ-r+ρ)+σ/(sⱼ-s+σ))`; bilinearity of `poissonBracket` in the first slot
over `Finset.sum` (`fderiv_sum`, holomorphy of each `gⱼ` on `Dom r s`), triangle inequality for `WBound` (add `wbound_add`
helper: coefficients are linear; `Summable.add`).

**N6-4.** Induction on `m`; displacement: telescoping sum with `zᵢ = Φᵢ(zᵢ₊₁)`, finite-sum triangle by a local `Finset` induction on `map_add_le_add` (there is no unqualified `map_sum_le`);
derivatives: `fderiv_comp` at `zᵢ₊₁` (open `U`, `DifferentiableOn.differentiableAt`), form invariance composes;
injectivity `InjOn.comp`.

**N6-5.** Build `CanonData D r s ρ σ (qδ/(2πα)) (homGen …)` from `homological_direct` (`2ρ < r` ⇒ `ρ < r/2`; `Φ/(ρσ) ≤ u ≤ 1/4`).
(a),(b) are `canonical_map_a`..`e` restated (`iterMap` unfolds to the `CanonData` flow by `rfl`); `InjOn` from
`canonical_map_e` (left inverse). `iterU` arithmetic: `Φ/ρ ≤ qδ/(ᾱρ)`, `Φ/(eσ) ≤ qδ/(eᾱσ)`.

**N6-6.** Steps it-taylor .. it-terms: `ComposeData D (r-ρ) (s-σ) r s ρ σ Φ φ` (`η = 2Φ/(ρσ) ≤ 1/2`); `transform` with
`h ↦ h∘snd` (class on `Dom r s` needs only holomorphy on `polyNbhd D r`; its bracket `w = {h, φ} = ξ - T_Kf` has bound
`2δ`) and `f₀ = g + T_Kf`; the integrand `v_t = {g + f_t, φ}` (`f_t = (1-t)ξ + t T_Kf`) bounded by `bracket_g` (decomposition
of `g` extended by one term `f_t`, width `(r,s)`, bound `δ`); continuity of `(t,z) ↦ v_t z`, `D v_t` (affine in `t`).
`composition_integral` gives `|𝓡| ≤ (1-η)⁻¹V`; `truncation_tail` + `WBound.mono` + `composition_series` (last two clauses)
give `|(f - T_Kf)∘Φ| ≤ (1-η)⁻¹e^{-2πKσ}δ`; `iterF = 𝓡 + (f - T_Kf)∘Φ` pointwise on `Dom (r-2ρ)(s-2σ)` (transform identity +
definition); `(1-η)⁻¹ ≤ (1-2u)⁻¹`. Heaviest package: keep `iterF` unfolded only in one lemma (`iterF_eq`), all estimates on
named pieces.

**N6-7.** ω real at real points (`hamiltonian_real_fderiv` / `KAM.real_restriction` for `h` real on the open real slice),
`homological_direct` (c), `canonical_map_b` (second clause), `composition_real` for `H∘Φ`, differences of real functions.

**N6-8.** `Arith`: every displayed inequality of Steps nf-first, nf-case (Cases A/B), nf-N ((6.1), (6.2)), nf-induct
(`128/127 · 0.1915 < 1/4`), nf-concl ((a), (b)), nf-disp (1.17, 8 + 32/(36 ln 2) ≤ 10) as standalone real lemmas
(`norm_num`, `Real.exp_one_gt_d9`, `Real.log_two_gt_d9`, `Real.add_one_le_exp`); **no `nlinarith` over large contexts**.
`Steps`: `nfState : ℕ → (g, f)` by recursion (`gᵢ = iterG …`, `fᵢ₊₁ = iterF …` with `ρᵢ, σᵢ` from `nfSteps`), the decomposition
`gᵢ₋₁ = g₀ + ∑ⱼ(gⱼ - gⱼ₋₁)` as an `IsDecomp` with `Fin i` parts (`rⱼ = rⱼ`, `Mⱼ = εⱼ`; `g₀` on `Dom r s`), and the induction
claim `εᵢ₊₁ ≤ εᵢ/4`; Case B is a separate lemma with losses `(r/4, s/3)`. `NormalForm`: case split (Case B / `N = 0` / `N ≥ 1`),
`telescope` on `Uᵢ = Dom rᵢ sᵢ` (plus the `Φᵢ` maps `Dom rᵢ₊₁ sᵢ₊₁ → Dom (rᵢ-3ρᵢ/2) … ⊆ Dom rᵢ sᵢ`), displacement through
the two `Seminorm`s `‖Π_I ·‖`, `‖Π_θ ·‖`. `nonresonant_case`: `WBound.mono` and `1 ≤ e^{1-κ/6}`.

**S7-1.** `real_system`: `G ∘ realInclusion₂` is `C^∞` on `W_r` (`holomorphic_regularity` + `ContDiffOn.restrict_scalars` +
composition with the real-linear `realInclusion₂`), `Complex.reCLM` composition; (b) is K's `hamiltonian_real_fderiv` on the
open `Dom (cpx D) r s` (real slice `= W_r` by `realInclusion₂_mem_Dom_iff`); periodicity from `InClass.periodic`; (c)
`ham_smooth_c1`, `ham_periodic`; (d) `ham_energy`. `exit_ball`: `gen_exit` on `V = univ ×ˢ {I | N(I - I₀) < ϱ}` (open by
continuity), time reversal `t ↦ z(-t)` for `t₁ < 0`; frontier gives `N = ϱ` (continuity both sides).

**S7-2.** `theta_derivative`: `cauchy_theta` at width `s' < s`, `sup_le_wbound` at real `θ` (`T_{s'} ⊇ ℝⁿ`), `s' ↓ 0` by
`le_of_tendsto` (`tendsto` of `M/(e(s-s'))`); `euclid ≤ ∑ |·|` from `Interfaces/Norms`. `resonant_gradient`: the components
`uᵥ = ∑ⱼ vⱼ ∂_{θⱼ}g` for `v ⊥ span Λ` have zero coefficients (`coefficients_deriv`), hence vanish (`coefficients_repr` at
width `s' < s`); real gradient `thetaGradR (realH g) = Re ∂_θ g ∘ ι` (S7-1 (b)); finite-dimensional double orthogonal
complement (`Submodule.orthogonalBilin`/dot form) gives membership in `span Λ`.

**S7-3.** `conjugation`: real derivative of `reMap Ψ` at real points is the restriction (`HasFDerivAt.restrictScalars`,
real values by `hΨreal`), `YᵀJY = J` from `hΨsympl` restricted, then `YJYᵀ = J` (`det_eq_one_or_neg_one`,
`map_hamiltonianJ_comp`), chain rule `∇H̃ = Yᵀ∇H(Ψ)`. `transfer`: as Steps tr-orbit .. tr-est with `gen_maximal`,
`gen_continuation_periodic` (compact `K = {I | N(I - I_x) ≤ ϱ}`: closed by continuity, bounded since `‖·‖ ≤ N`),
`gen_uniqueness` on `J ∩ (T₋, T₊)` (`OrdConnected`), monotonicity of `adm`. `stopped_extension`: connected component of
`{t ∈ J | z t ∈ W_r}` as `{t ∈ J | ∀ τ ∈ uIcc 0 t, z τ ∈ W_r}`; no-exit by continuity at the endpoint.

**S7-4.** `preimage`: Banach (`ContractingWith.exists_fixedPoint` on the complete closed set `X` with the metric of the gauge
`ν` — use `scaleCLE`-pulled-back norm, i.e. work with `y ↦ W y` coordinates so the Pi sup norm is `ν`); contraction via
`general_cauchy` on the `ν`-ball radius `1/2` (inside `Dom r' s'` by the displayed inequalities) and the mean value inequality
on the convex `X`; real restriction of `DG`. `preimage_nfl`: constants `d_I/ϱ' ≤ 1/64`, `d_θ/σ' ≤ 30/768`.

**S7-5.** `exists_orthProj`: `B = Matrix.toBilin' 1` (dot form), `B.orthogonal V`, `IsCompl V (B.orthogonal V)`
(`LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate`, positivity of the dot form), `Submodule.linearProjOfIsCompl`;
symmetry and idempotence by decomposition. `energy_core`: (a) `ham_energy` + `hHR`; (b) `HasDerivAt` of `t ↦ (1-P)(z t).2`
is `-(1-P) thetaGradR f`, since `(1-P)thetaGradR g = 0`; mean value (`norm_image_sub_le_of_norm_deriv_le_segment'` for
`euclid` via `IsActionNorm`-style seminorm, or componentwise with Cauchy-Schwarz); (c) `taylor_mean_remainder_lagrange` for
`φ(a) = hR(I₀ + aΔ)` (`ContDiffOn ℝ 2` along the segment, `iteratedDerivWithin` = `hessR` by `fderiv_comp`); (d) combine,
`Π` self-adjoint, Cauchy-Schwarz for `dotProduct` (`Matrix.dotProduct_self_...`/`real_inner_le_norm` avoided: prove
`|u⬝ᵥv| ≤ euclid u · euclid v` once in `Energy`).

**S7-6.** As Steps ad-*, ne-*, l2-*: `admissible` by the mean value inequality for `ω` in `euclid` (`HessBound` gives
`euclid (ω(I) - ω(J)) ≤ M euclid(I - J)`: prove a small lemma `freq_euclid_lipschitz` from `HessBound` via
`Convex.norm_image_sub_le_of_norm_fderiv_le` for the `euclid`-normed copy, i.e. componentwise bilinear duality), closeness
witness `w ∈ R_Λ` ⇒ `euclid (P ω) = euclid (P (ω - w)) ≤ euclid (ω - w)` (`P w = 0` for `w ∈ R_Λ = (span Λ)^⊥`); `no_exit`
arithmetic in `Arith`-style standalone lemmas (`1/16 + 5/32 + 1/(12e) < 1/4`, `225/256 · 1/3 > 0.29`); Lemma 2 cone step
`0.3453·2 + 1/4 < 0.941 < 1`.

**S7-7.** Case split `κ ≥ 6` / `< 6`: `normal_form` with `Λ = {0}` (`Λ ∩ Z_K = {0}` ⇒ `g` θ-independent ⇒ `thetaGradR (realH g) = 0`),
`preimage_nfl`, `transfer` with `Nrm = ‖·‖`, `ϱ = 15r/32`, `adm I t := |t|·5ε ≤ sr e^{κ/6}`; (T3) by `exit_ball` + mean value
on `İ = -∂_θf_*` (`real_system` (b), `theta_derivative`); `6/(5e) < 0.442 < 15/32`. Case B with `Ψ = id` (all of (T1)-(T2) trivial).

**S7-8.** As Steps p2-red .. p2-concl: reduction `δ' = mr/8`, `L = √n M` from the complex Hessian bound (`norm_le_euclid`,
`modeSize_euclid_compare`-type `‖v‖₂ ≤ √n‖v‖`) and `lipschitz`; three cases; the restriction of the complex Hessian bound to
`HessBound` on `U_{r/2}` (K's `real_restriction`); `ResSetting` at `(r/2, s̃)`; `resonant_lemma2`; `transfer` with
`Nrm = euclid`, `d = ρ'/4`; `Λ = univ` case C (`f_* = 0`, `η = 0`).

## 8. How the consumers use the API (stable interfaces for Parts 8-12, P, I)

| Consumer | Uses |
|---|---|
| N Part 9 (Theorem 1 blocks; `p9:block-hyp`, `bs-theta`, `bs-res`, `bs-stop`, `bh-lip`, `om-max`) | `nonresonant`, `resonant_prop2`, `stopped_extension`, `lipschitz(_entries)`, `IsNonresonant`, `FreqLipschitz`, `IsCloseToRes`, `IsQuasiConvex`, `cpx`, `realNbhd`, `realStrip`, `IsOrbit`, `freq_realInclusion`, `isActionNorm_euclid` |
| N Part 8 (`p8:cutoffs`, `co-incl`) | `zBall`, `IsNonresonant` (cut-off `Z_{K_a}` ⊆ Euclidean ball), `IsCloseToRes`, `resSpace` |
| N Part 10 (`hypotheses-check`, `hc-f`, `hc-qc`) | `realHamiltonian_eq_realH` (frozen `IsSolutionOn` ↔ `IsOrbit` through K's `ham_reduction`, which needs `DifferentiableAt`: `real_system` (b)), `stopped_extension` with `F = hamiltonianVectorField (realHamiltonian h f)`, then `KAM.Nekhoroshev.ODE.confinement_glue` |
| N Part 11 (partial; `p11:hom`, `nf`, `iterative`, `bracket-g`, `preimage`, `real-system`, `energy-free`, `cj`, `nf-*`) | `homological_param` with `m = n+2k`, `ω (I, x̃) = freq h I` (Part 11 package budgets the fast-coordinate projection/holomorphy bridge and proves its own bracket identity from the directional one); `iterative_direct_*` *patterns* only (Part 11's weighted slow-pair iteration is its own variant), `divisor`, `telescope`, `IsDecomp`/`starNorm`, `preimage`, `conjugation`, `real_system`, `exit_ball` (on the projected fast curve), `resonant_gradient`, `theta_derivative`, `IsCloseToRes`; `energy_core` is *not applied* (p11c L89 repeats only its argument) |
| P Part 2 (averaging) | `IterHyp` with `Λ = {0}`, `iterative_direct_a..e`, `homRes` (`= modeAverage` on `Z_K`). P allows `q = 1`; `IterHyp` has `p > 1`. Wrapper (audit N1): for consumer data `(α, q₀)` take `p = 2`, `α_design = 2α/q₀`; then `α_design / conjExp 2 = α/q₀` and every estimate/smallness condition uses the unchanged ratio `conjExp 2 / α_design = q₀/α`; `homGen`, `iterMap` do not depend on `α, p`, so the map is the same. Never set `p` to a nonexistent conjugate exponent. P's two-scale/oscillator/anisotropic variants remain P's own statements. |
| I (prospective reuse only) | `energy_core`, `IsOrthProj`, `exists_orthProj`, `no_exit`, `resonant_lemma1`, `resonant_lemma2`, `ResSetting` are reusable, but no current `blueprint-I/parts/` file cites a p7 label (I confinement uses the Part 3 torus/barrier/continuation route). Not a verified consumer. |
| N Part 12 | no direct p6/p7 result reference found; no consumer obligation. |

Interfaces Parts 8-10 must not expect: an `EReal` time `T`, a definition of `Π_Λ`, or `|·|` as a value (`wnorm`); all three are
deliberately absent (Decisions 3, 7, 8).

## 9. Risks

### 9.1 Elaboration and design
- Heavy: N6-6 (Lie remainder + integral corollary with continuity of `(t,z) ↦ Dv_t z`), N6-8 (the step sequence and numerics),
  S7-3 (maximal solution plumbing), S7-4 (contraction in a gauge). Per rule 1, a default-heartbeat failure means split by
  estimate (`iterF_eq`, one lemma per displayed inequality of `Arith`), not larger budgets.
- `nfState` recursion carrying functions: keep it a plain `ℕ`-recursion on a pair of functions with radii given by closed
  formulas (`rᵢ = 3r/4 - 2(i-1)ρ`), never dependent types; prove `IsDecomp` for `gᵢ` by induction once.
- `iterF` is defined through `flow`; unfolding it inside estimates is costly: expose `iterF_eq` (it-decomp) and work on its RHS.

### 9.2 Missing Mathlib/upstream API
1. `WBound` additivity (`wbound_add`) and scalar-function multiplication on coefficients (`coeff_mul_snd`): not in Part 4
   signatures; small helpers inside N6-2/N6-3 (Parts 4/5 files are not edited).
2. Cauchy-Schwarz and orthogonal complements for `dotProduct` on `Fin n → ℝ` without `EuclideanSpace`: S7-5 proves the two
   facts it needs.
3. Lagrange Taylor for a `C²` function along a segment in `ℝⁿ`: Mathlib's one-variable `taylor_mean_remainder_lagrange` + chain
   rule; S7-5.

### 9.3 Dependencies outside this design
- W4-7 (`Projections`), C5-8, C5-9, C5-10 are designed (signatures in `NPart145Signatures.lean`) but not on `inp`. If their
  final statements differ from those signatures, N6-2/5/6/7 briefs must be re-checked against the landed declarations
  (especially `ComposeData` field order, `canonical_map_*` widths, `transform` integral form).
- S7-1 relies on K's `hamiltonian_real_fderiv`/`real_restriction` signatures in `KAM/Strip/RealRestriction.lean` (proved).

### 9.4 Errata candidates (reported here, not edited)
- None new; see Section 6 (graph coverage of Lemma 1; unlisted Hessian restriction step in `p2-red`).

## 10. Revision 2 (response to design audit 1, `DESIGN-N67-design-audit-1.md`, verdict FAIL)

All findings are resolved in `NPart67Signatures.lean` (now 854 lines; re-elaborated once through
`inp_sig_check.sh` on a scratch copy: exit 0, exactly 43 warnings, all `declaration uses 'sorry'`, no errors) and in this
document. Appendix A is regenerated from the new file. No proofs were written; no frozen file was touched.

- **F1 (BLOCKING) — fixed.** `IsActionNorm` gains `map_zero : N 0 = 0` and `smul : ∀ (c : ℝ) a, N (c • a) = |c| * N a`
  (exactly the audit's structure), so it describes an actual norm dominating the max norm; the shifted norm `‖·‖ + 1`
  is no longer admissible and `exit_ball` (statement unchanged, = the audit's corrected signature) is true: at `τ = 0` the
  value is `N 0 = 0 < ϱ`, so IVT on `uIcc 0 t₁` gives the first boundary time. `isActionNorm_norm`, `isActionNorm_euclid`
  remain obligations (both instances satisfy the new fields: `norm_smul`, `euclid` homogeneity). S7-1's plan adds these two
  fields; `transfer`, `stopped_extension` statements unchanged.
- **F2 (MAJOR) — fixed.** `normal_form` gains, between (a) and (b), the exact-correction clause
  `(nfSteps K s = 0 ∨ iterU α p ε (r/8) (s/6) < exp(-κ/6)) → EqOn g (homRes K Λ f) (Dom n D (r/2) (s/6))`
  (the blueprint's "`g = g₀` if `N = 0` or in the second case", p6 L167, packet `bpN:p6:normal-form` L890), stated on the
  domain only. Case B is tested with the carried bound `ε` (`iterU` at `ρ = r/8`, `σ = s/6`, Step 0's widths), which is the
  literal blueprint case at the sharp norm instance and matches the step construction. N6-8's `Steps` must expose
  `g = homRes` in both branches.
- **F3 (MAJOR) — fixed.** New parameter-capable core in `Homological`: `homGenParam`, `homResParam`, `RealOnParam`
  (`RealOn` is square-only, so a `ℂⁿ × ℂᵐ` reality predicate is needed), `homological_param` (the audit's statement with
  `RealOnParam`), and bridges `homGen_eq_homGenParam`, `homRes_eq_homResParam`, `realOnParam_iff_realOn`. Part 6's
  `homological_direct` (statement unchanged) is the `m = n`, `ω = freq h`, `q = conjExp p` specialization. Ownership: N6-2
  (+150 lines). Part 11 applies `homological_param` with `m = n + 2k`, `ω(I,x̃) = freq h I`; its fast-coordinate
  projection/holomorphy bridge is budgeted in the Part 11 package. No new premise beyond consumer source data.
- **N1 — documented** (Section 8, P row): `q = 1` by the rescaling `p = 2`, `α_design = 2α/q₀`.
- **N2 — fixed** (Section 7): `iterHyp_of_source` lives in `IterativeMap` (N6-5); the facade `Iterative` is created in
  N6-7; N6-6 imports `IterativeMap`; S7-6 lists S7-3; summaries reconciled (6 waves, N6-8 ≈ 950 lines over three files).
- **N3 — fixed** (Sections 0.1, 8): track I and Part 12 marked prospective/no consumer; Part 11 does not apply
  `energy_core`.
- **N4 — convention stated.** `telescope`'s `IsOpen (U (i+1))` premise is the domain convention "holomorphic on an open
  set"; every normal-form `Uᵢ` is an open `Dom` set (`isOpen_Dom`). Not an extra geometric assumption on any consumer;
  the blueprint's "subsets ... holomorphic" is read as holomorphic on open neighborhoods.
- **N5 — fixed** (Section 7.1): `map_sum_le` replaced by a local finite-sum induction on `map_add_le_add`;
  `DifferentiableOn.div` replaced by `DifferentiableOn.mul` + `DifferentiableOn.inv`.

Suspected errata in pinned sources: none new. Deviations introduced by this revision: `RealOnParam` (a new predicate,
agreeing with `RealOn` at `m = n` by a stated bridge); Case B tested with the carried bound `ε` rather than the exact norm.

## Appendix A. The signatures

Verbatim copy of `/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean` (sha256 above).

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Frozen.Defs.RealHamiltonian
public import KAM.Frozen.Nekhoroshev.Defs.RealPart
public import KAM.Strip.RealRestriction
public import KAM.Weighted.Domains
public import KAM.Weighted.Norm
public import KAM.Weighted.Coefficients
public import KAM.Canonical.Setting
public import KAM.Canonical.Flow
public import KAM.ODE.Basic
public import KAM.Nekhoroshev.Interfaces.Norms

/-!
# Signatures of blueprint-N Parts 6 and 7 (design draft)

Exact Lean statements of every result node of `blueprint-N/parts/p6-normal-form.tex` and
`p7-stability.tex` (published graph `docs/graph/N/DEPGRAPH.md`). Every theorem body is `sorry`; every
`def`/`structure` has its real body. Design evidence, not approved Lean. Sections follow the modules of
`docs/tracks/N/design/PART67-LEAN-DESIGN.md`:

* 0. upstream stubs: the three definitions of `KAM/Weighted/Projections.lean` (W4-8, not yet on `inp`),
  copied VERBATIM from `NPart145Signatures.lean` B.8 so that this file elaborates; delete on landing;
* A. `KAM/NormalForm/*` (Part 6, namespace `KAM.NormalForm`, shared by tracks N and P);
* B. `KAM/Stability/*` (Part 7, namespace `KAM.Stability`, shared by tracks N and I).
-/

@[expose] public noncomputable section

open Set Metric
open scoped NNReal

/-! ## 0. Upstream stubs (`KAM/Weighted/Projections.lean`, package W4-8; verbatim) -/

namespace KAM.Weighted

variable {n m : ℕ}

/-- `P_S u = ∑_{k ∈ S} û_k χ_k`. -/
def projMode (S : Set (Fin n → ℤ)) (u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) :
    (Fin n → ℂ) × (Fin m → ℂ) → ℂ :=
  fun z => ∑' k, S.indicator (fun k => coeff u z.2 k * KAM.character k z.1) k

/-- `T_K u = P_{|k|₁ ≤ K} u`. -/
def truncate (K : ℝ) (u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) : (Fin n → ℂ) × (Fin m → ℂ) → ℂ :=
  projMode {k | KAM.Fourier.modeSize k ≤ K} u

end KAM.Weighted

/-! ## A. Part 6: homological equation, Iterative Lemma, Normal Form Lemma (`KAM/NormalForm/*`) -/

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

/-! ### A.1 Setting (`bpN:p6:setting`, `bpN:p6#data`; `NormalForm/Setting.lean`) -/

/-- `Z_K = {k : |k|₁ ≤ K}` (the `ℓ¹` ball; the cut-off set of `truncate K`). -/
def zBall (n : ℕ) (K : ℝ) : Set (Fin n → ℤ) := {k | KAM.Fourier.modeSize k ≤ K}

/-- The complex frequency `ω(I) = ∂_I h(I) ∈ ℂⁿ` (`ωᵢ = Dh(I)eᵢ`). -/
def freq (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℂ) : Fin n → ℂ := fun i => fderiv ℂ h I (Pi.single i 1)

/-- `k · v = ∑ kᵢ vᵢ` for `k ∈ ℤⁿ`, `v ∈ ℂⁿ`. -/
def dotC (k : Fin n → ℤ) (v : Fin n → ℂ) : ℂ := ∑ i, (k i : ℂ) * v i

/-- The Hölder conjugate `q = p/(p-1)`. -/
def conjExp (p : ℝ) : ℝ := p / (p - 1)

/-- `(N1)`: `(α, K)`-nonresonant modulo `Λ` on `D`. -/
def IsNonresonant (D : Set (Fin n → ℂ)) (K α : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ I ∈ D, ∀ k ∈ zBall n K \ Λ, α ≤ ‖dotC k (freq h I)‖

/-- `(N2)`: the frequency Lipschitz bound (max norms) from points of `D` into `V_r D`. -/
def FreqLipschitz (D : Set (Fin n → ℂ)) (r L : ℝ) (h : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ I₀ ∈ D, ∀ I ∈ polyNbhd D r, ‖I - I₀‖ < r → ‖freq h I - freq h I₀‖ ≤ L * ‖I - I₀‖

/-- `(N-dir)` (and the conclusion of `divisor`): `|k · ω(I)| ≥ c` on `V` for `k ∈ Z_K \ Λ`. -/
def DivisorBound (V : Set (Fin n → ℂ)) (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (c : ℝ) : Prop :=
  ∀ I ∈ V, ∀ k ∈ zBall n K \ Λ, c ≤ ‖dotC k (freq h I)‖

/-- A finite decomposition `g = ∑ⱼ gⱼ`, `gⱼ ∈ O(rⱼ, sⱼ)`, `|gⱼ|_{rⱼ,sⱼ} ≤ Mⱼ`, `rⱼ ≥ r`, `sⱼ ≥ s`
(Definition `bpN:p6:setting`; the bounds `Mⱼ` stand for the norms). -/
structure IsDecomp (D : Set (Fin n → ℂ)) (r s : ℝ) (g : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) {N : ℕ}
    (gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (rj sj Mj : Fin N → ℝ) : Prop where
  eq_sum : g = fun z => ∑ j, gj j z
  r_le : ∀ j, r ≤ rj j
  s_le : ∀ j, s ≤ sj j
  inClass : ∀ j, InClass D (rj j) (sj j) (gj j)
  bound : ∀ j, WBound D (rj j) (sj j) (gj j) (Mj j)

/-- `|g|_* = ∑ⱼ ½(ρ/(rⱼ-r+ρ) + σ/(sⱼ-s+σ)) Mⱼ` (depends on the decomposition). -/
def starNorm (r s ρ σ : ℝ) {N : ℕ} (rj sj Mj : Fin N → ℝ) : ℝ :=
  ∑ j, (1 / 2) * (ρ / (rj j - r + ρ) + σ / (sj j - s + σ)) * Mj j

/-- `bpN:p6:lipschitz`: an operator-norm bound `L` on `Dω` over `V_r D` gives `(N2)`. -/
theorem lipschitz {D : Set (Fin n → ℂ)} {r L : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hD2 : ∀ I ∈ polyNbhd D r, ‖fderiv ℂ (freq h) I‖ ≤ L) : FreqLipschitz D r L h := sorry

/-- `bpN:p6:lipschitz`, entry form: `|∂ᵢ∂ⱼh| ≤ M_C` on `V_r D` gives `(N2)` with `L = n M_C`. -/
theorem lipschitz_entries {D : Set (Fin n → ℂ)} {r Mc : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hD2 : ∀ I ∈ polyNbhd D r, ∀ i j : Fin n,
      ‖fderiv ℂ (fun J => fderiv ℂ h J (Pi.single j 1)) I (Pi.single i 1)‖ ≤ Mc) :
    FreqLipschitz D r (n * Mc) h := sorry

/-- `bpN:p6:divisor`: `(N1)`, `(N2)`, `KLr ≤ α/p` give `|k·ω| ≥ α - KLr ≥ α/q` on `V_r D`. -/
theorem divisor {D : Set (Fin n → ℂ)} {r K α L p : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} (hp : 1 < p) (hα : 0 < α) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hnr : IsNonresonant D K α Λ h) (hlip : FreqLipschitz D r L h) (hrad : K * L * r ≤ α / p) :
    DivisorBound (polyNbhd D r) K Λ h (α - K * L * r) ∧
    DivisorBound (polyNbhd D r) K Λ h (α / conjExp p) := sorry

/-! ### A.2 The homological equation (`bpN:p6:homological`; `NormalForm/Homological.lean`) -/

/-- The generating function `φ = ∑_{k ∈ Z_K \ Λ} f̂ₖ(I)/(2πi k·ω(I)) χₖ(θ)`. -/
def homGen (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) → ℂ :=
  fun z => ∑' k, (zBall n K \ Λ).indicator (fun k =>
    coeff f z.2 k / (2 * (Real.pi : ℂ) * Complex.I * dotC k (freq h z.2)) * KAM.character k z.1) k

/-- The resonant part `ξ = P_Λ T_K f`. -/
def homRes (K : ℝ) (Λ : Set (Fin n → ℤ)) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) :
    (Fin n → ℂ) × (Fin n → ℂ) → ℂ :=
  projMode Λ (truncate K f)

/-! Parameter-capable core (Revision 2, audit F3): `n` angles, `m` parameters, an arbitrary
holomorphic frequency field `ω : ℂᵐ → ℂⁿ`; the bracket identity is stated as the directional
derivative `∑ᵢ ∂_{θᵢ}φ · ωᵢ`. Part 6 specializes `m = n`, `ω = freq h`; Part 11 takes
`ω (I, x̃) = freq h I`. -/

/-- `φ = ∑_{k ∈ Z_K \ Λ} f̂ₖ(y)/(2πi k·ω(y)) χₖ(θ)` with an independent parameter carrier. -/
def homGenParam {m : ℕ} (K : ℝ) (Λ : Set (Fin n → ℤ)) (ω : (Fin m → ℂ) → Fin n → ℂ)
    (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) : (Fin n → ℂ) × (Fin m → ℂ) → ℂ :=
  fun z => ∑' k, (zBall n K \ Λ).indicator (fun k =>
    coeff f z.2 k / (2 * (Real.pi : ℂ) * Complex.I * dotC k (ω z.2)) * KAM.character k z.1) k

/-- `ξ = P_Λ T_K f` with an independent parameter carrier. -/
def homResParam {m : ℕ} (K : ℝ) (Λ : Set (Fin n → ℤ)) (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) :
    (Fin n → ℂ) × (Fin m → ℂ) → ℂ :=
  projMode Λ (truncate K f)

/-- Reality on the real points of `U ⊆ ℂⁿ × ℂᵐ` (the `m ≠ n` analogue of `RealOn`). -/
def RealOnParam {m : ℕ} (U : Set ((Fin n → ℂ) × (Fin m → ℂ)))
    (u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) : Prop :=
  ∀ x : (Fin n → ℝ) × (Fin m → ℝ), (KAM.realInclusion n x.1, KAM.realInclusion m x.2) ∈ U →
    (u (KAM.realInclusion n x.1, KAM.realInclusion m x.2)).im = 0

/-- Bridge: for `m = n` the two reality predicates agree. -/
theorem realOnParam_iff_realOn (U : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : RealOnParam U u ↔ RealOn U u := sorry

/-- The homological solve with independent angle/parameter dimensions (core of
`homological_direct`; consumed by `bpN:p11:hom`). -/
theorem homological_param {m : ℕ} {D : Set (Fin m → ℂ)} {r s K α q δ : ℝ}
    {Λ : Set (Fin n → ℤ)} {ω : (Fin m → ℂ) → Fin n → ℂ} {f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hq : 1 ≤ q) (hα : 0 < α) (hs : 0 < s) (hK : 0 ≤ K)
    (hω : DifferentiableOn ℂ ω (polyNbhd D r))
    (hdir : ∀ I ∈ polyNbhd D r, ∀ k ∈ zBall n K \ Λ, α / q ≤ ‖dotC k (ω I)‖)
    (hf : InClass D r s f) (hδ : WBound D r s f δ) :
    InClass D r s (homGenParam K Λ ω f) ∧ InClass D r s (homResParam K Λ f) ∧
    (∀ I ∈ polyNbhd D r, ∀ k, k ∉ zBall n K \ Λ → coeff (homGenParam K Λ ω f) I k = 0) ∧
    (∀ z ∈ Dom n D r s,
      (∑ i, fderiv ℂ (homGenParam K Λ ω f) z (Pi.single i 1, 0) * ω z.2 i) +
        homResParam K Λ f z = truncate K f z) ∧
    (∀ I ∈ polyNbhd D r, ∀ k ∈ Λ, coeff (homGenParam K Λ ω f) I k = 0) ∧
    (∀ z ∈ Dom n D r s, homResParam K Λ f z = projMode (Λ ∩ zBall n K) f z) ∧
    WBound D r s (homResParam K Λ f) δ ∧ WBound D r s (truncate K f) δ ∧
    WBound D r s (homGenParam K Λ ω f) (q * δ / (2 * Real.pi * α)) ∧
    ((∀ k ∈ Λ, -k ∈ Λ) → RealOnParam (Dom n D r s) f →
      (∀ I : Fin m → ℝ, KAM.realInclusion m I ∈ polyNbhd D r →
        ∀ i, (ω (KAM.realInclusion m I) i).im = 0) →
      RealOnParam (Dom n D r s) (homGenParam K Λ ω f) ∧
        RealOnParam (Dom n D r s) (homResParam K Λ f)) :=
  sorry

/-- Bridge: the canonical generator is the `m = n`, `ω = freq h` specialization. -/
theorem homGen_eq_homGenParam (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : homGen K Λ h f = homGenParam K Λ (freq h) f := sorry

/-- Bridge: the canonical resonant part is the `m = n` specialization. -/
theorem homRes_eq_homResParam (K : ℝ) (Λ : Set (Fin n → ℤ))
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : homRes K Λ f = homResParam K Λ f := sorry

/-- `bpN:p6:homological` under `(N-dir)` (the form all proofs use; `bpN:p6:iterative-direct`). -/
theorem homological_direct {D : Set (Fin n → ℂ)} {r s K α p δ : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hp : 1 < p) (hα : 0 < α)
    (hs : 0 < s) (hK : 0 ≤ K) (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hdir : DivisorBound (polyNbhd D r) K Λ h (α / conjExp p))
    (hf : InClass D r s f) (hδ : WBound D r s f δ) :
    -- finite sums of characters of degree `≤ K`, in the class
    InClass D r s (homGen K Λ h f) ∧ InClass D r s (homRes K Λ f) ∧
    (∀ I ∈ polyNbhd D r, ∀ k, k ∉ zBall n K \ Λ → coeff (homGen K Λ h f) I k = 0) ∧
    -- (a)
    (∀ z ∈ Dom n D r s, poissonBracket (homGen K Λ h f) (fun w => h w.2) z + homRes K Λ f z =
      truncate K f z) ∧
    (∀ I ∈ polyNbhd D r, ∀ k ∈ Λ, coeff (homGen K Λ h f) I k = 0) ∧
    (∀ z ∈ Dom n D r s, homRes K Λ f z = projMode (Λ ∩ zBall n K) f z) ∧
    -- (b)
    WBound D r s (homRes K Λ f) δ ∧ WBound D r s (truncate K f) δ ∧
    WBound D r s (homGen K Λ h f) (conjExp p * δ / (2 * Real.pi * α)) ∧
    -- (c)
    ((∀ k ∈ Λ, -k ∈ Λ) → RealOn (Dom n D r s) f →
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd D r →
        ∀ i, (freq h (KAM.realInclusion n I) i).im = 0) →
      RealOn (Dom n D r s) (homGen K Λ h f) ∧ RealOn (Dom n D r s) (homRes K Λ f)) := sorry

/-- `bpN:p6:homological` (source hypotheses `(N1)`, `(N2)`, `KLr ≤ α/p`); from the direct form and
`divisor`. -/
theorem homological {D : Set (Fin n → ℂ)} {r s K α L p δ : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hp : 1 < p) (hα : 0 < α)
    (hs : 0 < s) (hK : 0 ≤ K) (hL : 0 ≤ L) (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hnr : IsNonresonant D K α Λ h) (hlip : FreqLipschitz D r L h) (hrad : K * L * r ≤ α / p)
    (hf : InClass D r s f) (hδ : WBound D r s f δ) :
    InClass D r s (homGen K Λ h f) ∧ InClass D r s (homRes K Λ f) ∧
    (∀ I ∈ polyNbhd D r, ∀ k, k ∉ zBall n K \ Λ → coeff (homGen K Λ h f) I k = 0) ∧
    (∀ z ∈ Dom n D r s, poissonBracket (homGen K Λ h f) (fun w => h w.2) z + homRes K Λ f z =
      truncate K f z) ∧
    (∀ I ∈ polyNbhd D r, ∀ k ∈ Λ, coeff (homGen K Λ h f) I k = 0) ∧
    (∀ z ∈ Dom n D r s, homRes K Λ f z = projMode (Λ ∩ zBall n K) f z) ∧
    WBound D r s (homRes K Λ f) δ ∧ WBound D r s (truncate K f) δ ∧
    WBound D r s (homGen K Λ h f) (conjExp p * δ / (2 * Real.pi * α)) ∧
    ((∀ k ∈ Λ, -k ∈ Λ) → RealOn (Dom n D r s) f →
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd D r →
        ∀ i, (freq h (KAM.realInclusion n I) i).im = 0) →
      RealOn (Dom n D r s) (homGen K Λ h f) ∧ RealOn (Dom n D r s) (homRes K Λ f)) := sorry

/-! ### A.3 Bracket with a decomposed `g` (`bpN:p6:bracket-g`; `NormalForm/BracketDecomp.lean`) -/

theorem bracket_g {D : Set (Fin n → ℂ)} {r s ρ σ Φ : ℝ} {g φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {N : ℕ} {gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {rj sj Mj : Fin N → ℝ}
    (hg : IsDecomp D r s g gj rj sj Mj) (hφ : InClass D r s φ) (hbφ : WBound D r s φ Φ)
    (hρ : 0 < ρ) (hρr : ρ < r) (hσ : 0 < σ) (hσs : σ < s) :
    InClass D (r - ρ) (s - σ) (poissonBracket g φ) ∧
    WBound D (r - ρ) (s - σ) (poissonBracket g φ)
      (2 / (Real.exp 1 * ρ * σ) * starNorm r s ρ σ rj sj Mj * Φ) ∧
    WBound D (r - ρ) (s - σ) (poissonBracket g φ) (2 / (ρ * σ) * starNorm r s ρ σ rj sj Mj * Φ) := sorry

/-! ### A.4 The Iterative Lemma (`bpN:p6:iterative`, `bpN:p6:iterative-direct`;
`NormalForm/IterativeMap.lean`, `IterativeRemainder.lean`, `IterativeReal.lean`, `Iterative.lean`) -/

/-- The time-one map `Φ = X¹_φ` of the generating function, flow domain `𝒟_{r-ρ,s-σ}` (the
`omega` of both `CanonData D r s ρ σ _ φ` and `ComposeData D (r-ρ) (s-σ) r s ρ σ _ φ`). -/
def iterMap (D : Set (Fin n → ℂ)) (r s ρ σ K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  flow (KAM.hamiltonianVectorFieldℂ (homGen K Λ h f)) (Dom n D (r - ρ) (s - σ)) 1

/-- `g₊ = g + P_Λ T_K f`. -/
def iterG (K : ℝ) (Λ : Set (Fin n → ℤ)) (g f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) :
    (Fin n → ℂ) × (Fin n → ℂ) → ℂ :=
  fun z => g z + homRes K Λ f z

/-- `f₊ = H ∘ Φ - h - g₊` (so item (c)'s identity is definitional; its content is (d)). -/
def iterF (D : Set (Fin n → ℂ)) (r s ρ σ K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (g f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) → ℂ :=
  fun z => (fun w => h w.2 + g w + f w) (iterMap D r s ρ σ K Λ h f z) - h z.2 - iterG K Λ g f z

/-- The source premises of the Iterative Lemma in direct-divisor form (`bpN:p6:iterative-direct`):
`s > 0`, `0 < ρ`, `2ρ < r`, `0 < σ`, `2σ < s`, `h` holomorphic on `V_r D`, `(N-dir)` with `α/q`,
`g` decomposed, `f ∈ O(r,s)`, `|f| ≤ δ ≤ ᾱρσ/(4q)`. -/
structure IterHyp (D : Set (Fin n → ℂ)) (r s ρ σ K α p δ : ℝ) (Λ : Set (Fin n → ℤ))
    (h : (Fin n → ℂ) → ℂ) (g f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) {N : ℕ}
    (gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (rj sj Mj : Fin N → ℝ) : Prop where
  hp : 1 < p
  hα : 0 < α
  hK : 0 ≤ K
  hs : 0 < s
  hρ : 0 < ρ
  hρr : 2 * ρ < r
  hσ : 0 < σ
  hσs : 2 * σ < s
  h_holo : DifferentiableOn ℂ h (polyNbhd D r)
  divisor : DivisorBound (polyNbhd D r) K Λ h (α / conjExp p)
  decomp : IsDecomp D r s g gj rj sj Mj
  f_class : InClass D r s f
  f_bound : WBound D r s f δ
  δ_nonneg : 0 ≤ δ
  δ_small : δ ≤ 2 * Real.pi * α * ρ * σ / (4 * conjExp p)

/-- `u = qδ/(ᾱρσ)`. -/
def iterU (α p δ ρ σ : ℝ) : ℝ := conjExp p * δ / (2 * Real.pi * α * ρ * σ)

section Iterative

variable {D : Set (Fin n → ℂ)} {r s ρ σ K α p δ : ℝ} {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ}
  {g f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {N : ℕ} {gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {rj sj Mj : Fin N → ℝ}

/-- `bpN:p6:iterative-direct` (a): holomorphic on `𝒟_{r-3ρ/2,s-3σ/2}` into `𝒟_{r-ρ,s-σ}`, canonical,
integer translations, injective on `𝒟_{r-2ρ,s-2σ}` with left inverse `X⁻¹_φ`. -/
theorem iterative_direct_a (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) :
    DifferentiableOn ℂ (iterMap D r s ρ σ K Λ h f) (Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2)) ∧
    MapsTo (iterMap D r s ρ σ K Λ h f) (Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2))
      (Dom n D (r - ρ) (s - σ)) ∧
    (∀ z ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2), ∀ v w,
      symplFormC (fderiv ℂ (iterMap D r s ρ σ K Λ h f) z v)
        (fderiv ℂ (iterMap D r s ρ σ K Λ h f) z w) = symplFormC v w) ∧
    (∀ k : Fin n → ℤ, ∀ z ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2),
      iterMap D r s ρ σ K Λ h f (z.1 + (fun i => (k i : ℂ)), z.2) =
        iterMap D r s ρ σ K Λ h f z + ((fun i => (k i : ℂ)), 0)) ∧
    InjOn (iterMap D r s ρ σ K Λ h f) (Dom n D (r - 2 * ρ) (s - 2 * σ)) ∧
    ∀ z ∈ Dom n D (r - 2 * ρ) (s - 2 * σ),
      flow (KAM.hamiltonianVectorFieldℂ (homGen K Λ h f)) (Dom n D (r - ρ) (s - σ)) (-1)
        (iterMap D r s ρ σ K Λ h f z) = z := sorry

/-- `bpN:p6:iterative-direct` (b): displacement. -/
theorem iterative_direct_b (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) :
    (∀ z ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2),
      scaledNorm ρ σ (iterMap D r s ρ σ K Λ h f z - z) ≤ iterU α p δ ρ σ ∧
      ‖(iterMap D r s ρ σ K Λ h f z).1 - z.1‖ ≤ conjExp p * δ / (2 * Real.pi * α * ρ) ∧
      ‖(iterMap D r s ρ σ K Λ h f z).2 - z.2‖ ≤
        conjExp p * δ / (Real.exp 1 * (2 * Real.pi * α) * σ)) ∧
    ∀ z ∈ Dom n D (r - 2 * ρ) (s - 2 * σ), ∀ v,
      scaledNorm ρ σ (fderiv ℂ (iterMap D r s ρ σ K Λ h f) z v - v) ≤
        2 * iterU α p δ ρ σ * scaledNorm ρ σ v := sorry

/-- `bpN:p6:iterative-direct` (c): `H ∘ Φ = h + g₊ + f₊`, `g₊ = g + P_Λ T_K f`, `|g₊ - g| ≤ δ`,
`f₊ ∈ O(r-2ρ,s-2σ)`. -/
theorem iterative_direct_c (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) :
    (∀ z ∈ Dom n D (r - 2 * ρ) (s - 2 * σ),
      (fun w => h w.2 + g w + f w) (iterMap D r s ρ σ K Λ h f z) =
        h z.2 + iterG K Λ g f z + iterF D r s ρ σ K Λ h g f z) ∧
    InClass D r s (homRes K Λ f) ∧ WBound D r s (homRes K Λ f) δ ∧
    InClass D (r - 2 * ρ) (s - 2 * σ) (iterF D r s ρ σ K Λ h g f) := sorry

/-- `bpN:p6:iterative-direct` (d): the estimate of `f₊`. -/
theorem iterative_direct_d (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) :
    WBound D (r - 2 * ρ) (s - 2 * σ) (iterF D r s ρ σ K Λ h g f)
      ((1 - 2 * iterU α p δ ρ σ)⁻¹ *
        (2 * conjExp p / (Real.exp 1 * (2 * Real.pi * α) * ρ * σ) *
            (starNorm r s ρ σ rj sj Mj + δ) + Real.exp (-(2 * Real.pi * K * σ))) * δ) := sorry

/-- `bpN:p6:iterative-direct` (e): reality. -/
theorem iterative_direct_e (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj)
    (hΛ : ∀ k ∈ Λ, -k ∈ Λ) (hhr : RealOn (Dom n D r s) (fun w => h w.2))
    (hgr : RealOn (Dom n D r s) g) (hfr : RealOn (Dom n D r s) f) :
    RealOn (Dom n D r s) (homGen K Λ h f) ∧ RealOn (Dom n D r s) (iterG K Λ g f) ∧
    RealOn (Dom n D (r - 2 * ρ) (s - 2 * σ)) (iterF D r s ρ σ K Λ h g f) ∧
    ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2) →
      iterMap D r s ρ σ K Λ h f (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n) := sorry

end Iterative

/-- The source hypotheses `(N1)`, `(N2)`, `KLr ≤ α/p` give the direct-form premise (`divisor`):
this is how `bpN:p6:iterative` is obtained from `IterHyp`. -/
theorem iterHyp_of_source {D : Set (Fin n → ℂ)} {r s ρ σ K α L p δ : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} {g f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {N : ℕ}
    {gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {rj sj Mj : Fin N → ℝ}
    (hp : 1 < p) (hα : 0 < α) (hK : 0 ≤ K) (hL : 0 ≤ L) (hs : 0 < s) (hρ : 0 < ρ) (hρr : 2 * ρ < r)
    (hσ : 0 < σ) (hσs : 2 * σ < s) (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hnr : IsNonresonant D K α Λ h) (hlip : FreqLipschitz D r L h) (hrad : K * L * r ≤ α / p)
    (hg : IsDecomp D r s g gj rj sj Mj) (hf : InClass D r s f) (hfb : WBound D r s f δ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 2 * Real.pi * α * ρ * σ / (4 * conjExp p)) :
    IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj := sorry

/-! ### A.5 Telescoping (`bpN:p6:telescope`; `NormalForm/Telescope.lean`) -/

/-- `Ψₘ = Φ₀ ∘ Φ₁ ∘ ⋯ ∘ Φₘ`. -/
def chain {E : Type*} (Φ : ℕ → E → E) : ℕ → E → E
  | 0 => Φ 0
  | m + 1 => chain Φ m ∘ Φ (m + 1)

theorem telescope {U : ℕ → Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {Φ : ℕ → (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {m : ℕ}
    (hU : ∀ i ≤ m, U (i + 1) ⊆ U i) (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i)) :
    MapsTo (chain Φ m) (U (m + 1)) (U 0) ∧
    (∀ (μ : Seminorm ℂ ((Fin n → ℂ) × (Fin n → ℂ))) (d : ℕ → ℝ),
      (∀ i ≤ m, ∀ z ∈ U (i + 1), μ (Φ i z - z) ≤ d i) →
      ∀ z ∈ U (m + 1), μ (chain Φ m z - z) ≤ ∑ i ∈ Finset.range (m + 1), d i) ∧
    ((∀ i ≤ m, IsOpen (U (i + 1))) → (∀ i ≤ m, DifferentiableOn ℂ (Φ i) (U (i + 1))) →
      (∀ i ≤ m, ∀ z ∈ U (i + 1), ∀ v w,
        symplFormC (fderiv ℂ (Φ i) z v) (fderiv ℂ (Φ i) z w) = symplFormC v w) →
      DifferentiableOn ℂ (chain Φ m) (U (m + 1)) ∧
      ∀ z ∈ U (m + 1), ∀ v w,
        symplFormC (fderiv ℂ (chain Φ m) z v) (fderiv ℂ (chain Φ m) z w) = symplFormC v w) ∧
    ((∀ i ≤ m, InjOn (Φ i) (U (i + 1))) → InjOn (chain Φ m) (U (m + 1))) := sorry

/-! ### A.6 The Normal Form Lemma (`bpN:p6:normal-form`, `normal-form#data`;
`NormalForm/Steps.lean` (the step sequence), `NormalForm/Arith.lean`, `NormalForm/NormalForm.lean`) -/

/-- `bpN:p6:normal-form#data`: the number of steps `N = ⌊κ/(12 ln 2)⌋`, `κ = 2πKs`. -/
def nfSteps (K s : ℝ) : ℕ := ⌊2 * Real.pi * K * s / (12 * Real.log 2)⌋₊

/-- `bpN:p6:normal-form`. -/
theorem normal_form {D : Set (Fin n → ℂ)} {r s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hp : 1 < p) (hα : 0 < α)
    (hK : 0 < K) (hL : 0 ≤ L) (hr : 0 < r) (hs : 0 < s) (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hnr : IsNonresonant D K α Λ h) (hlip : FreqLipschitz D r L h) (hrad : K * L * r ≤ α / p)
    (hf : InClass D r s f) (hfb : WBound D r s f ε) (hε0 : 0 ≤ ε)
    (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K)) (hii : 6 ≤ 2 * Real.pi * K * s) :
    ∃ (Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
      (g fs : (Fin n → ℂ) × (Fin n → ℂ) → ℂ),
      -- the map
      DifferentiableOn ℂ Ψ (Dom n D (r / 2) (s / 6)) ∧ InjOn Ψ (Dom n D (r / 2) (s / 6)) ∧
      MapsTo Ψ (Dom n D (r / 2) (s / 6)) (Dom n D r s) ∧
      (∀ z ∈ Dom n D (r / 2) (s / 6), ∀ v w,
        symplFormC (fderiv ℂ Ψ z v) (fderiv ℂ Ψ z w) = symplFormC v w) ∧
      (∀ k : Fin n → ℤ, ∀ z ∈ Dom n D (r / 2) (s / 6),
        Ψ (z.1 + (fun i => (k i : ℂ)), z.2) = Ψ z + ((fun i => (k i : ℂ)), 0)) ∧
      -- the normal form
      InClass D (r / 2) (s / 6) g ∧ InClass D (r / 2) (s / 6) fs ∧
      (∀ I ∈ polyNbhd D (r / 2), ∀ k, k ∉ Λ ∩ zBall n K → coeff g I k = 0) ∧
      (∀ z ∈ Dom n D (r / 2) (s / 6), (fun w => h w.2 + f w) (Ψ z) = h z.2 + g z + fs z) ∧
      -- (a)
      WBound D (r / 2) (s / 6) (fun z => g z - homRes K Λ f z)
        (16 * (2 * conjExp p * K / (α * r)) * ε ^ 2) ∧
      -- exact correction `g = g₀` in the zero-step case and in Case B
      ((nfSteps K s = 0 ∨
          iterU α p ε (r / 8) (s / 6) < Real.exp (-(2 * Real.pi * K * s) / 6)) →
        EqOn g (homRes K Λ f) (Dom n D (r / 2) (s / 6))) ∧
      -- (b)
      WBound D (r / 2) (s / 6) fs (Real.exp (-(2 * Real.pi * K * s) / 6) * ε) ∧
      -- (c)
      (∀ z ∈ Dom n D (r / 2) (s / 6), ‖(Ψ z).2 - z.2‖ ≤ conjExp p * K * ε / α ∧
        ‖(Ψ z).1 - z.1‖ ≤ 10 * conjExp p * ε / (2 * Real.pi * α * r)) ∧
      -- (d)
      ((∀ k ∈ Λ, -k ∈ Λ) → RealOn (Dom n D r s) (fun w => h w.2) → RealOn (Dom n D r s) f →
        RealOn (Dom n D (r / 2) (s / 6)) g ∧ RealOn (Dom n D (r / 2) (s / 6)) fs ∧
        ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n D (r / 2) (s / 6) →
          Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n)) := sorry

/-- `bpN:p6:nonresonant-case`: `Ψ = id`, `g = 0`, `f_* = f` for `κ < 6`, `|f_*| ≤ e·e^{-κ/6} ε`. -/
theorem nonresonant_case {D : Set (Fin n → ℂ)} {r s K ε : ℝ} {h : (Fin n → ℂ) → ℂ}
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hfb : WBound D r s f ε) (hκ : 2 * Real.pi * K * s < 6) :
    (∀ z, (fun w => h w.2 + f w) (id z) = h z.2 + 0 + f z) ∧
    WBound D r s f (Real.exp 1 * Real.exp (-(2 * Real.pi * K * s) / 6) * ε) := sorry

end KAM.NormalForm

/-! ## B. Part 7: stability estimates (`KAM/Stability/*`) -/

namespace KAM.Stability

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {n : ℕ}

/-! ### B.1 Real neighbourhoods, real systems, orbits (`bpN:p7:setting`; `Stability/Setting.lean`) -/

/-- `D ⊆ ℝⁿ` viewed in `ℂⁿ` (the `D` of Parts 4-6). -/
def cpx (D : Set (Fin n → ℝ)) : Set (Fin n → ℂ) := KAM.realInclusion n '' D

/-- `U_ϱ D = {I ∈ ℝⁿ : ∃ J ∈ D, |I - J| < ϱ}` (max norm). -/
def realNbhd (D : Set (Fin n → ℝ)) (ϱ : ℝ) : Set (Fin n → ℝ) := {I | ∃ J ∈ D, ‖I - J‖ < ϱ}

/-- `W_ϱ = ℝⁿ × U_ϱ D`. -/
def realStrip (D : Set (Fin n → ℝ)) (ϱ : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  univ ×ˢ realNbhd D ϱ

/-- The real Hamiltonian `G^ℝ = Re G ∘ ι` (total; equals `G` on `W_r` for `G ∈ O(r,s)^ℝ`). -/
def realH (G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (x : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (G (KAM.realInclusion₂ n x)).re

/-- A `G`-orbit in `W_ϱ` on `J`. -/
def IsOrbit (G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (D : Set (Fin n → ℝ)) (ϱ : ℝ) (J : Set ℝ)
    (z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)) : Prop :=
  KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorField (realH G)) (realStrip D ϱ) J z

/-- The real part of a map of `ℂ²ⁿ`, as a map of `ℝ²ⁿ`. -/
def reMap (Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (x : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => ((Ψ (KAM.realInclusion₂ n x)).1 i).re, fun i => ((Ψ (KAM.realInclusion₂ n x)).2 i).re)

/-- Real `θ`-gradient `∂_θ G(x)` of a real function. -/
def thetaGradR (G : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (x : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℝ :=
  fun i => fderiv ℝ G x (Pi.single i 1, 0)

/-- The real Hessian `Q(I)[ξ, η] = D²h_ℝ(I)[ξ, η]`. -/
def hessR (hR : (Fin n → ℝ) → ℝ) (I ξ η : Fin n → ℝ) : ℝ := fderiv ℝ (fderiv ℝ hR) I ξ η

theorem isOpen_realNbhd (D : Set (Fin n → ℝ)) (ϱ : ℝ) : IsOpen (realNbhd D ϱ) := sorry

theorem realNbhd_mono (D : Set (Fin n → ℝ)) {ϱ ϱ' : ℝ} (h : ϱ' ≤ ϱ) :
    realNbhd D ϱ' ⊆ realNbhd D ϱ := sorry

/-- `W_r = 𝒟_{r,s} ∩ ℝ²ⁿ` (for `s > 0`). -/
theorem realInclusion₂_mem_Dom_iff (D : Set (Fin n → ℝ)) {r s : ℝ} (hs : 0 < s)
    (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    KAM.realInclusion₂ n x ∈ Dom n (cpx D) r s ↔ x ∈ realStrip D r := sorry

/-- The frozen Hamiltonian is the real Hamiltonian of `h + f` (Part 10 bridge). -/
theorem realHamiltonian_eq_realH (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) :
    KAM.realHamiltonian h f = realH (fun w => h w.2 + f w) := sorry

/-- The Part 6 complex frequency at real points is the frozen frequency map (Parts 9-10 bridge). -/
theorem freq_realInclusion {D : Set (Fin n → ℝ)} {r : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r))
    (hreal : ∀ I ∈ realNbhd D r, (h (KAM.realInclusion n I)).im = 0) {I : Fin n → ℝ}
    (hI : I ∈ realNbhd D r) :
    freq h (KAM.realInclusion n I) = KAM.realInclusion n (KAM.frequencyMap h I) := sorry

/-! ### B.2 Holomorphic real systems (`bpN:p7:real-system`; `Stability/RealSystem.lean`) -/

theorem real_system {D : Set (Fin n → ℝ)} {r s : ℝ} {G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hs : 0 < s) (hG : InClass (cpx D) r s G) (hGr : RealOn (Dom n (cpx D) r s) G) :
    -- (a)
    (∀ k : ℕ, ContDiffOn ℝ k (realH G) (realStrip D r)) ∧
    (∀ k : Fin n → ℤ, ∀ x ∈ realStrip D r, realH G (x + KAM.ODE.angleShift k) = realH G x) ∧
    -- (b)
    (∀ x ∈ realStrip D r, DifferentiableAt ℝ (realH G) x ∧
      KAM.realInclusion₂ n (KAM.hamiltonianVectorField (realH G) x) =
        KAM.hamiltonianVectorFieldℂ G (KAM.realInclusion₂ n x)) ∧
    -- (c)
    ContDiffOn ℝ 1 (KAM.hamiltonianVectorField (realH G)) (realStrip D r) ∧
    (∀ k : Fin n → ℤ, ∀ x ∈ realStrip D r, KAM.hamiltonianVectorField (realH G)
      (x + KAM.ODE.angleShift k) = KAM.hamiltonianVectorField (realH G) x) ∧
    -- (d) energy conservation (the other Part 3 results need only (c))
    ∀ ϱ, 0 < ϱ → ϱ ≤ r → ∀ J : Set ℝ, J.OrdConnected → ∀ z, IsOrbit G D ϱ J z →
      ∀ t ∈ J, ∀ t' ∈ J, realH G (z t) = realH G (z t') := sorry

/-! ### B.3 Derivative bound, resonant gradients (`bpN:p7:theta-derivative`, `resonant-gradient`;
`Stability/Gradient.lean`) -/

theorem theta_derivative {D : Set (Fin n → ℝ)} {ϱ s M : ℝ} {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hs : 0 < s) (hu : InClass (cpx D) ϱ s u) (hb : WBound (cpx D) ϱ s u M) :
    (∀ θ : Fin n → ℝ, ∀ I ∈ realNbhd D ϱ,
      ∑ j, ‖dtheta j u (KAM.realInclusion₂ n (θ, I))‖ ≤ M / (Real.exp 1 * s) ∧
      KAM.Nekhoroshev.euclid (fun j => dtheta j u (KAM.realInclusion₂ n (θ, I))) ≤
        M / (Real.exp 1 * s)) ∧
    ∀ x ∈ Dom n (cpx D) ϱ s, ‖u x‖ ≤ M := sorry

/-- `span_ℝ Λ ⊆ ℝⁿ`. -/
def resSpan (Λ : Set (Fin n → ℤ)) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ ((fun k i => (k i : ℝ)) '' Λ)

/-- `bpN:p7:resonant-gradient`: `P_Λ g = g` (coefficients vanish off `Λ`) gives
`∂_θ g^ℝ ∈ span Λ` (i.e. `Π^⊥ ∂_θ g = 0`) on `W_r`. -/
theorem resonant_gradient {D : Set (Fin n → ℝ)} {r s M : ℝ} {Λ : Set (Fin n → ℤ)}
    {g : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hs : 0 < s) (hg : InClass (cpx D) r s g)
    (hgr : RealOn (Dom n (cpx D) r s) g) (hb : WBound (cpx D) r s g M)
    (hΛ : ∀ I ∈ polyNbhd (cpx D) r, ∀ k, k ∉ Λ → coeff g I k = 0) :
    ∀ x ∈ realStrip D r, thetaGradR (realH g) x ∈ resSpan Λ := sorry

/-! ### B.4 Transfer through a symplectic change of variables (`bpN:p7:conjugation`, `preimage`,
`preimage-nfl`, `transfer`, `stopped-extension`, `exit-ball`; `Stability/Conjugation.lean`,
`Preimage.lean`, `Transfer.lean`) -/

theorem conjugation {D : Set (Fin n → ℝ)} {r s r' s' : ℝ}
    {H H' : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hs : 0 < s) (hs' : 0 < s')
    (hH : InClass (cpx D) r s H) (hHr : RealOn (Dom n (cpx D) r s) H)
    (hH' : InClass (cpx D) r' s' H') (hH'r : RealOn (Dom n (cpx D) r' s') H')
    (hΨ : DifferentiableOn ℂ Ψ (Dom n (cpx D) r' s'))
    (hΨmap : MapsTo Ψ (Dom n (cpx D) r' s') (Dom n (cpx D) r s))
    (hΨreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n (cpx D) r' s' →
      Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    (hΨsympl : ∀ z ∈ Dom n (cpx D) r' s', ∀ v w,
      symplFormC (fderiv ℂ Ψ z v) (fderiv ℂ Ψ z w) = symplFormC v w)
    (hconj : ∀ z ∈ Dom n (cpx D) r' s', H' z = H (Ψ z))
    {J : Set ℝ} {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hz : IsOrbit H' D r' J z) :
    IsOrbit H D r J (fun t => reMap Ψ (z t)) := sorry

theorem preimage {D : Set (Fin n → ℝ)} {r' s' dθ dI ϱ' σ' : ℝ}
    {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hΨ : DifferentiableOn ℂ Ψ (Dom n (cpx D) r' s'))
    (hΨreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n (cpx D) r' s' →
      Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    (hθ : ∀ z ∈ Dom n (cpx D) r' s', ‖(Ψ z).1 - z.1‖ ≤ dθ)
    (hI : ∀ z ∈ Dom n (cpx D) r' s', ‖(Ψ z).2 - z.2‖ ≤ dI)
    (hϱ' : 0 < ϱ') (hϱr : ϱ' ≤ r') (hσ' : 0 < σ') (hσs : σ' ≤ 2 * s')
    (hκ : max (dθ / σ') (dI / ϱ') ≤ 1 / 4) :
    ∀ y : (Fin n → ℝ) × (Fin n → ℝ), y.2 ∈ D → ∃ x ∈ realStrip D r',
      Ψ (KAM.realInclusion₂ n x) = KAM.realInclusion₂ n y ∧ ‖x.1 - y.1‖ ≤ dθ ∧ ‖x.2 - y.2‖ ≤ dI :=
  sorry

/-- `bpN:p7:preimage-nfl`: for any `Ψ` with the conclusions of `normal_form` (hypothesis (i), `κ ≥ 6`,
reality), every `y ∈ ℝⁿ × D` has a real preimage in `W_{r/2}`. Stated on the conclusions so that it is
applied to the witness of `normal_form`. -/
theorem preimage_nfl {D : Set (Fin n → ℝ)} {r s K α p ε : ℝ}
    {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hp : 1 < p) (hα : 0 < α)
    (hK : 0 < K) (hr : 0 < r) (hs : 0 < s) (hε0 : 0 ≤ ε)
    (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K)) (hii : 6 ≤ 2 * Real.pi * K * s)
    (hΨ : DifferentiableOn ℂ Ψ (Dom n (cpx D) (r / 2) (s / 6)))
    (hΨreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n (cpx D) (r / 2) (s / 6) →
      Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    (hdisp : ∀ z ∈ Dom n (cpx D) (r / 2) (s / 6), ‖(Ψ z).2 - z.2‖ ≤ conjExp p * K * ε / α ∧
      ‖(Ψ z).1 - z.1‖ ≤ 10 * conjExp p * ε / (2 * Real.pi * α * r)) :
    ∀ y : (Fin n → ℝ) × (Fin n → ℝ), y.2 ∈ D → ∃ x ∈ realStrip D (r / 2),
      Ψ (KAM.realInclusion₂ n x) = KAM.realInclusion₂ n y ∧
      ‖x.2 - y.2‖ ≤ conjExp p * K * ε / α ∧ conjExp p * K * ε / α ≤ r / 2 ^ 7 := sorry

/-- A norm `|·|_*` on `ℝⁿ` dominating the max norm (the two instances used: `‖·‖`, `euclid`). -/
structure IsActionNorm (N : (Fin n → ℝ) → ℝ) : Prop where
  continuous : Continuous N
  map_zero : N 0 = 0
  add_le : ∀ a b, N (a + b) ≤ N a + N b
  neg : ∀ a, N (-a) = N a
  smul : ∀ (c : ℝ) a, N (c • a) = |c| * N a
  norm_le : ∀ a, ‖a‖ ≤ N a

theorem isActionNorm_norm : IsActionNorm (fun a : Fin n → ℝ => ‖a‖) := sorry

theorem isActionNorm_euclid : IsActionNorm (fun a : Fin n → ℝ => KAM.Nekhoroshev.euclid a) := sorry

/-- `bpN:p7:transfer`. The time bound `T : D → (0, ∞]` is the predicate `adm I t` ("`|t| ≤ T(I)`"),
which must be symmetric-monotone in `|t|`. -/
theorem transfer {D : Set (Fin n → ℝ)} {r s r' s' d ϱ : ℝ} {Nrm : (Fin n → ℝ) → ℝ}
    {adm : (Fin n → ℝ) → ℝ → Prop} {H H' : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hs : 0 < s) (hs' : 0 < s')
    (hN : IsActionNorm Nrm) (hadm : ∀ I t t', |t'| ≤ |t| → adm I t → adm I t')
    (hH : InClass (cpx D) r s H) (hHr : RealOn (Dom n (cpx D) r s) H)
    (hH' : InClass (cpx D) r' s' H') (hH'r : RealOn (Dom n (cpx D) r' s') H')
    (hΨ : DifferentiableOn ℂ Ψ (Dom n (cpx D) r' s'))
    (hΨmap : MapsTo Ψ (Dom n (cpx D) r' s') (Dom n (cpx D) r s))
    (hΨreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n (cpx D) r' s' →
      Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    (hΨsympl : ∀ z ∈ Dom n (cpx D) r' s', ∀ v w,
      symplFormC (fderiv ℂ Ψ z v) (fderiv ℂ Ψ z w) = symplFormC v w)
    (hconj : ∀ z ∈ Dom n (cpx D) r' s', H' z = H (Ψ z))
    -- (T1)
    (hT1 : ∀ x ∈ realStrip D r', Nrm ((reMap Ψ x).2 - x.2) ≤ d)
    -- (T2)
    (hT2 : ∀ y : (Fin n → ℝ) × (Fin n → ℝ), y.2 ∈ D → ∃ x ∈ realStrip D r', reMap Ψ x = y)
    -- (T3)
    (hϱ : 0 < ϱ) (hdϱ : d + ϱ < r')
    (hT3 : ∀ Iy ∈ D, ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z', IsOrbit H' D r' J z' →
      Nrm ((z' 0).2 - Iy) ≤ d → ∀ t ∈ J, adm Iy t → Nrm ((z' t).2 - (z' 0).2) ≤ ϱ) :
    ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit H D r J z → (z 0).2 ∈ D →
      ∀ t ∈ J, adm (z 0).2 t → Nrm ((z t).2 - (z 0).2) ≤ ϱ + 2 * d := sorry

/-- `bpN:p7:stopped-extension`. -/
theorem stopped_extension {D : Set (Fin n → ℝ)} {r ϱ : ℝ} {Nrm : (Fin n → ℝ) → ℝ}
    {adm : ℝ → Prop} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hN : IsActionNorm Nrm) (hϱ : 0 < ϱ)
    (hϱr : ϱ < r) (hadm : ∀ t t', |t'| ≤ |t| → adm t → adm t')
    (hconf : ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit H D r J z → (z 0).2 ∈ D →
      ∀ t ∈ J, adm t → Nrm ((z t).2 - (z 0).2) ≤ ϱ)
    {F : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hF : ∀ x ∈ realStrip D r, F x = KAM.hamiltonianVectorField (realH H) x)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : ∀ t ∈ J, HasDerivAt z (F (z t)) t) (hz0 : (z 0).2 ∈ D) :
    ∀ t ∈ J, adm t → Nrm ((z t).2 - (z 0).2) ≤ ϱ ∧ z t ∈ realStrip D r := sorry

/-- `bpN:p7:exit-ball`. -/
theorem exit_ball {Nrm : (Fin n → ℝ) → ℝ} (hN : IsActionNorm Nrm) {J : Set ℝ} (hJ : J.OrdConnected)
    (h0 : (0 : ℝ) ∈ J) {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hz : ContinuousOn z J) {ϱ : ℝ}
    (hϱ : 0 < ϱ) {t₁ : ℝ} (ht₁ : t₁ ∈ J) (hexit : ϱ < Nrm ((z t₁).2 - (z 0).2)) :
    ∃ tstar ∈ J, tstar ∈ uIcc 0 t₁ ∧ Nrm ((z tstar).2 - (z 0).2) = ϱ ∧
      ∀ τ ∈ uIcc 0 tstar, Nrm ((z τ).2 - (z 0).2) ≤ ϱ := sorry

/-! ### B.5 Proposition 1 (`bpN:p7:nonresonant`; `Stability/Nonresonant.lean`) -/

/-- `bpN:p7:nonresonant`. `|t| ≤ T_nr = (sr/5ε) e^{κ/6}` is written `|t| · 5ε ≤ sr e^{κ/6}`
(so `T_nr = ∞` for `ε = 0`). -/
theorem nonresonant (hn : 1 ≤ n) {D : Set (Fin n → ℝ)} {r s K α L p ε : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hp : 1 < p) (hr : 0 < r)
    (hs : 0 < s) (hK : 0 < K) (hα : 0 < α) (hL : 0 ≤ L)
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r))
    (hhr : RealOn (Dom n (cpx D) r s) (fun w => h w.2))
    (hf : InClass (cpx D) r s f) (hfr : RealOn (Dom n (cpx D) r s) f)
    (hfb : WBound (cpx D) r s f ε) (hε0 : 0 ≤ ε)
    -- (i)
    (hnr : IsNonresonant (cpx D) K α {0} h)
    -- (ii)
    (hlip : FreqLipschitz (cpx D) r L h) (hrad : K * L * r ≤ α / p)
    -- (iii)
    (hiii : ε ≤ α * r / (2 ^ 7 * conjExp p * K)) :
    ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit (fun w => h w.2 + f w) D r J z →
      (z 0).2 ∈ D → ∀ t ∈ J, |t| * (5 * ε) ≤ s * r * Real.exp (2 * Real.pi * K * s / 6) →
        ‖(z t).2 - (z 0).2‖ ≤ r / 2 := sorry

/-! ### B.6 The energy argument (`bpN:p7:resonance-data`, `energy-core`; `Stability/Energy.lean`) -/

/-- An orthogonal projection of `(ℝⁿ, ⟨·,·⟩)` (`dotProduct`), as a linear map. -/
structure IsOrthProj (P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) : Prop where
  idem : ∀ v, P (P v) = P v
  symm : ∀ u v, P u ⬝ᵥ v = u ⬝ᵥ P v

/-- The orthogonal projection onto any subspace exists (no `EuclideanSpace`: via the dot-product
bilinear form). -/
theorem exists_orthProj (V : Submodule ℝ (Fin n → ℝ)) :
    ∃ P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ), IsOrthProj P ∧ (∀ v, P v ∈ V) ∧ ∀ v ∈ V, P v = v := sorry

/-- `R_Λ = {ω : k·ω = 0 ∀ k ∈ Λ}`. -/
def resSpace (Λ : Set (Fin n → ℤ)) : Set (Fin n → ℝ) := {w | ∀ k ∈ Λ, ∑ i, (k i : ℝ) * w i = 0}

/-- `D` is `δ`-close to exact `Λ`-resonances: `dist₂(ω(I), R_Λ) ≤ δ` on `D` (`= ‖Π_Λ ω(I)‖₂`). -/
def IsCloseToRes (D : Set (Fin n → ℝ)) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) (δ : ℝ) : Prop :=
  ∀ I ∈ D, ∃ w ∈ resSpace Λ, KAM.Nekhoroshev.euclid (KAM.frequencyMap h I - w) ≤ δ

/-- `m`-convex on `U`. -/
def IsMConvex (U : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (m : ℝ) : Prop :=
  ∀ I ∈ U, ∀ ξ, m * KAM.Nekhoroshev.euclid ξ ^ 2 ≤ hessR (KAM.Nekhoroshev.realPart h) I ξ ξ

/-- `ℓ,m`-quasi-convex on `U` (never full positive definiteness). -/
def IsQuasiConvex (U : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (ℓ m : ℝ) : Prop :=
  ∀ I ∈ U, ∀ ξ, ℓ * KAM.Nekhoroshev.euclid ξ < |KAM.frequencyMap h I ⬝ᵥ ξ| ∨
    m * KAM.Nekhoroshev.euclid ξ ^ 2 ≤ hessR (KAM.Nekhoroshev.realPart h) I ξ ξ

/-- `‖Q(I)‖_{2→2} ≤ M` on `U`. -/
def HessBound (U : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (M : ℝ) : Prop :=
  ∀ I ∈ U, ∀ ξ η, |hessR (KAM.Nekhoroshev.realPart h) I ξ η| ≤
    M * KAM.Nekhoroshev.euclid ξ * KAM.Nekhoroshev.euclid η

/-- `bpN:p7:energy-core` (reusable core; track I, Part 11). -/
theorem energy_core {U : Set (Fin n → ℝ)} (hU : IsOpen U) {hR : (Fin n → ℝ) → ℝ}
    {g f HR : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hhR : ContDiffOn ℝ 2 hR U)
    (hg : ContDiffOn ℝ 1 g (univ ×ˢ U)) (hf : ContDiffOn ℝ 1 f (univ ×ˢ U))
    (hHR : ∀ x ∈ (univ : Set (Fin n → ℝ)) ×ˢ U, HR x = hR x.2 + g x + f x)
    {P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hP : IsOrthProj P)
    (hgP : ∀ x ∈ (univ : Set (Fin n → ℝ)) ×ˢ U, P (thetaGradR g x) = thetaGradR g x)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorField HR) (univ ×ˢ U) J z) {t₁ : ℝ}
    (ht₁ : t₁ ∈ J) (hseg : ∀ a ∈ Icc (0 : ℝ) 1, (z 0).2 + a • ((z t₁).2 - (z 0).2) ∈ U) :
    -- (a)
    hR (z t₁).2 - hR (z 0).2 = -((g (z t₁) + f (z t₁)) - (g (z 0) + f (z 0))) ∧
    -- (b)
    (∀ B, (∀ τ ∈ uIcc 0 t₁, KAM.Nekhoroshev.euclid (thetaGradR f (z τ)) ≤ B) →
      KAM.Nekhoroshev.euclid (((z t₁).2 - (z 0).2) - P ((z t₁).2 - (z 0).2)) ≤ |t₁| * B) ∧
    -- (c)
    (∃ a ∈ Ioo (0 : ℝ) 1, hR (z t₁).2 - hR (z 0).2 -
        (fun i => fderiv ℝ hR (z 0).2 (Pi.single i 1)) ⬝ᵥ ((z t₁).2 - (z 0).2) =
      1 / 2 * hessR hR ((z 0).2 + a • ((z t₁).2 - (z 0).2)) ((z t₁).2 - (z 0).2)
        ((z t₁).2 - (z 0).2)) ∧
    -- (d)
    (∀ m, (∀ a ∈ Icc (0 : ℝ) 1, m * KAM.Nekhoroshev.euclid ((z t₁).2 - (z 0).2) ^ 2 ≤
        hessR hR ((z 0).2 + a • ((z t₁).2 - (z 0).2)) ((z t₁).2 - (z 0).2) ((z t₁).2 - (z 0).2)) →
      m / 2 * KAM.Nekhoroshev.euclid ((z t₁).2 - (z 0).2) ^ 2 ≤
        |(g (z t₁) + f (z t₁)) - (g (z 0) + f (z 0))| +
        KAM.Nekhoroshev.euclid (P (fun i => fderiv ℝ hR (z 0).2 (Pi.single i 1))) *
          KAM.Nekhoroshev.euclid ((z t₁).2 - (z 0).2) +
        KAM.Nekhoroshev.euclid (fun i => fderiv ℝ hR (z 0).2 (Pi.single i 1)) *
          KAM.Nekhoroshev.euclid (((z t₁).2 - (z 0).2) - P ((z t₁).2 - (z 0).2))) := sorry

/-! ### B.7 The resonant setting, Lemma 2 (`bpN:p7:s-energy#rs`, `admissible`, `no-exit`,
`resonant-lemma2`; `Stability/Resonant.lean`) -/

/-- `bpN:p7:s-energy#rs`: the resonant setting (RS); `Mg`, `η` bound `|g|`, `|f_*|`. -/
structure ResSetting (D : Set (Fin n → ℝ)) (r s : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (m M : ℝ) (g fs : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (Mg η ζ δ : ℝ) : Prop where
  hn : 1 ≤ n
  hr : 0 < r
  hs : 0 < s
  h_holo : DifferentiableOn ℂ h (polyNbhd (cpx D) r)
  h_real : RealOn (Dom n (cpx D) r s) (fun w => h w.2)
  hm : 0 < m
  hmM : m ≤ M
  hess : HessBound (realNbhd D r) h M
  g_class : InClass (cpx D) r s g
  g_real : RealOn (Dom n (cpx D) r s) g
  g_bound : WBound (cpx D) r s g Mg
  g_res : ∀ I ∈ polyNbhd (cpx D) r, ∀ k, k ∉ Λ → coeff g I k = 0
  fs_class : InClass (cpx D) r s fs
  fs_real : RealOn (Dom n (cpx D) r s) fs
  fs_bound : WBound (cpx D) r s fs η
  η_nonneg : 0 ≤ η
  ζ_ge : Mg + η ≤ ζ
  hδ : 0 < δ
  close : IsCloseToRes D Λ h δ
  δ_le : δ ≤ m * r / 4
  ζ_le : ζ ≤ m * r ^ 2 / 32

/-- `ρ = δ/(4M)`. -/
def resRho (δ M : ℝ) : ℝ := δ / (4 * M)

/-- Admissible initial action: `‖I₀ - J₀‖₂ < ρ` for some `J₀ ∈ D`. -/
def IsAdmissible (D : Set (Fin n → ℝ)) (δ M : ℝ) (I₀ : Fin n → ℝ) : Prop :=
  ∃ J₀ ∈ D, KAM.Nekhoroshev.euclid (I₀ - J₀) < resRho δ M

section Resonant

variable {D : Set (Fin n → ℝ)} {r s : ℝ} {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {m M : ℝ}
  {g fs : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {Mg η ζ δ : ℝ}

/-- `bpN:p7:admissible`. (The orthogonal projection `Π_Λ` is any `P` given by `exists_orthProj`.) -/
theorem admissible (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ)
    {P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hP : IsOrthProj P) (hPV : ∀ v, P v ∈ resSpan Λ)
    (hPid : ∀ v ∈ resSpan Λ, P v = v) {I₀ : Fin n → ℝ} (hI₀ : IsAdmissible D δ M I₀) :
    (∀ I, KAM.Nekhoroshev.euclid (I - I₀) ≤ r - resRho δ M → I ∈ realNbhd D r) ∧
    (∀ I, KAM.Nekhoroshev.euclid (I - I₀) ≤ r - resRho δ M →
      KAM.Nekhoroshev.euclid (P (KAM.frequencyMap h I)) ≤
        5 / 4 * δ + M * KAM.Nekhoroshev.euclid (I - I₀)) ∧
    KAM.Nekhoroshev.euclid (P (KAM.frequencyMap h I₀)) ≤ 5 / 4 * δ := sorry

/-- `bpN:p7:no-exit`: (i)-(iii) cannot hold together. -/
theorem no_exit (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ) {J : Set ℝ} (hJ : J.OrdConnected)
    (h0 : (0 : ℝ) ∈ J) {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : IsOrbit (fun w => h w.2 + g w + fs w) D r J z) (hadm : IsAdmissible D δ M (z 0).2)
    {t₁ : ℝ} (ht₁ : t₁ ∈ J) (ht₁0 : t₁ ≠ 0)
    (hi : (∀ τ ∈ uIcc 0 t₁, KAM.Nekhoroshev.euclid ((z τ).2 - (z 0).2) ≤ r - resRho δ M) ∧
      KAM.Nekhoroshev.euclid ((z t₁).2 - (z 0).2) = r - resRho δ M)
    (hii : ∀ a ∈ Icc (0 : ℝ) 1, m * KAM.Nekhoroshev.euclid ((z t₁).2 - (z 0).2) ^ 2 ≤
      hessR (KAM.Nekhoroshev.realPart h) ((z 0).2 + a • ((z t₁).2 - (z 0).2))
        ((z t₁).2 - (z 0).2) ((z t₁).2 - (z 0).2))
    (hiii : |t₁| * KAM.Nekhoroshev.euclid (KAM.frequencyMap h (z 0).2) * η ≤ s * m * r ^ 2 / 12) :
    False := sorry

/-- `bpN:p7:resonant-lemma1` (Lemma 1; off the published graph, consumed by track I only). -/
theorem resonant_lemma1 (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ)
    (hconv : IsMConvex (realNbhd D r) h m) :
    ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit (fun w => h w.2 + g w + fs w) D r J z →
      IsAdmissible D δ M (z 0).2 → ∀ t ∈ J,
        |t| * (12 * KAM.Nekhoroshev.euclid (KAM.frequencyMap h (z 0).2) * η) ≤ s * m * r ^ 2 →
          KAM.Nekhoroshev.euclid ((z t).2 - (z 0).2) ≤ r - resRho δ M := sorry

/-- `bpN:p7:resonant-lemma2`; `Ω` is any bound of `‖ω‖₂` on the ball (the max is one). -/
theorem resonant_lemma2 (hRS : ResSetting D r s Λ h m M g fs Mg η ζ δ) {ℓ : ℝ}
    (hqc : IsQuasiConvex (realNbhd D r) h ℓ m) (hR1 : r ≤ 2 * ℓ / m) (hR2 : M * r ≤ ℓ / 4)
    {I₀ : Fin n → ℝ} (hI₀ : IsAdmissible D δ M I₀) {Ω : ℝ}
    (hΩ : ∀ I, KAM.Nekhoroshev.euclid (I - I₀) ≤ r - resRho δ M →
      KAM.Nekhoroshev.euclid (KAM.frequencyMap h I) ≤ Ω) :
    ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit (fun w => h w.2 + g w + fs w) D r J z →
      (z 0).2 = I₀ → ∀ t ∈ J, |t| * (12 * Ω * η) ≤ s * m * r ^ 2 →
        KAM.Nekhoroshev.euclid ((z t).2 - I₀) ≤ r - resRho δ M := sorry

end Resonant

/-! ### B.8 Proposition 2, the Resonant Stability Lemma (`bpN:p7:resonant-prop2`;
`Stability/ResonantStability.lean`) -/

/-- `bpN:p7:resonant-prop2`. `Ω(I₀)` is any bound of `‖ω‖₂` on `{‖I - I₀‖₂ ≤ r/2}`; `|t| ≤ T(I₀)` is
`|t| · 288 Ω ε ≤ s m r² e^{κ/6}`. Complex Hessian bound in the Euclidean operator norm on `V_r D`. -/
theorem resonant_prop2 (hn : 1 ≤ n) {D : Set (Fin n → ℝ)} {r s K α p m M ℓ δ ε : ℝ}
    {Λ : AddSubgroup (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hp : 1 < p) (hp32 : p ≤ 3 / 2) (hr : 0 < r) (hs : 0 < s) (hK : 0 < K) (hα : 0 < α)
    (hm : 0 < m) (hmM : m ≤ M) (hℓ : 0 < ℓ) (hδ : 0 < δ)
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r))
    (hhr : RealOn (Dom n (cpx D) r s) (fun w => h w.2))
    (hHess : ∀ I ∈ polyNbhd (cpx D) r, ∀ v : Fin n → ℂ,
      KAM.Nekhoroshev.euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤
        M * KAM.Nekhoroshev.euclid v)
    (hqc : IsQuasiConvex (realNbhd D r) h ℓ m)
    (hf : InClass (cpx D) r s f) (hfr : RealOn (Dom n (cpx D) r s) f)
    (hfb : WBound (cpx D) r s f ε) (hε0 : 0 ≤ ε)
    -- (a)
    (hnr : IsNonresonant (cpx D) K α (Λ : Set (Fin n → ℤ)) h)
    (hclose : IsCloseToRes D (Λ : Set (Fin n → ℤ)) h δ)
    -- (b)
    (hεb : ε ≤ p / conjExp p * (m * r ^ 2 / 2 ^ 7)) (hδb : δ ≤ m * r / 8)
    -- (c)
    (hc1 : r ≤ α / (p * Real.sqrt n * M * K)) (hc2 : r ≤ 4 * ℓ / m) (hc3 : M * r ≤ ℓ / 2) :
    ∀ I₀ ∈ D, ∀ Ω : ℝ, (∀ I, KAM.Nekhoroshev.euclid (I - I₀) ≤ r / 2 →
        KAM.Nekhoroshev.euclid (KAM.frequencyMap h I) ≤ Ω) →
      ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit (fun w => h w.2 + f w) D r J z →
        (z 0).2 = I₀ →
        ∀ t ∈ J, ((Λ : Set (Fin n → ℤ)) = univ ∨
            |t| * (288 * Ω * ε) ≤ s * m * r ^ 2 * Real.exp (2 * Real.pi * K * s / 6)) →
          KAM.Nekhoroshev.euclid ((z t).2 - I₀) ≤ r / 2 ∧ ‖(z t).2 - I₀‖ ≤ r := sorry

end KAM.Stability
```

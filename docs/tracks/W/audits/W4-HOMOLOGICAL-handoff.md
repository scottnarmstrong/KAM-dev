# Handoff: W4-HOMOLOGICAL (branch `inp-wpj`)

Blueprint: `blueprint-W/parts/w4-homological.tex` (current `inp` version, with the accepted W4-E5 Riesz gap
repair). Status: **every statement of the W4 package is proved** in the representative model below:
Lemma 1 (i)–(iv) (including reality and the equation for all `(z, \bar z)`), Lemma 2 and bound (4), and the
guarded Fréchet derivative `DN·X_F = −L_N F` of `bpW:w4:lie` (iv). Remaining: only remarks without statements.
Everything compiles under the gate, has no `sorry`, no new axiom, no heartbeat override, all files are under
710 lines, no line over 100 characters. Note: `Lie.lean`'s sequence-level `homLieN` was renamed `homLieSeq`
(it clashed with `homLieN` of `LemmaOneEquation` when both were imported).

## Model (read first)

* **Normal spaces.** `HomL2 = ℓ²_ℂ` (index `j ≥ 1`) is the common model of every `ℓ^N_{a,q}`: a normal vector
  `z` is represented by `ẑ_j = ω_{a,q}(j+2) z_j`. The variables `z, \bar z ∈ ℓ^N_{a,p}` are given by their
  representatives; the gradients `c^±` (in `ℓ^N_{a,p+1}`) by their representatives. `HomL2`/`HomOp` are
  `abbrev`s in `Schur.lean`.
* **𝓛 and 𝓑.** `HomOp = HomL2 →L HomL2` is the model of `𝓛` by weighted matrices (blueprint step
  *Representatives* of `bpW:w4:schur`: same norm). `Λ : 𝓛 → 𝓑` is `homLamCLM` (`ΛM = D M̂`, `D_j =
  1/(ω_{a,p}(j+2) ω_{a,p+1}(j+2))`), `‖M‖_bil = ‖ΛM‖`, dual norm `‖c‖_* = ‖D ĉ‖` (`homDualNorm`). The
  Hadamard map on `𝓑` (`schur` (ii)) is the Hadamard map on `HomOp`, and it commutes with `Λ`
  (`homHadamardOp_lam`), so no Riesz transfer is needed in this model. Matrix entries of the represented
  operator: `homNormalEntry`.
* **Taylor class.** `HomTaylor a p s` (components `a0, b, cp, cm, P, P', Q, Qt`, holomorphic, `1`-periodic and
  bounded on `T_s`; `P, P'` symmetric and `Qt` the entrywise transpose of `Q`, on `T_s`), the value `homRval`,
  the gradients `homRz, homRzb, homRu, homRv, homRy, homRtheta`, the norm `homXnorm r` (`|X_R|_r`) and the
  domain `HomDomain s r` (`‖u‖+‖v‖ < r`).

## Files (all `KAM/Wave/Homological/`, namespace `KAM.Wave`)

Part 1 (previous session): `LatticeCount`, `Lattice`, `LatticeBW` (`lattice`), `Melnikov`, `Divisors`,
`DivisorsConcrete` (`melnikov`, `divisors`), `Wave` (`wave` (i)), `Solve`, `SolveLinear` (`solve` (i),(ii),(iv),
`fourier-ops` (i)).

Part 1 (this session): `SolveDeriv`, `HolomorphicBanach` (`solve` (iii), `fourier-ops` (ii): the derivative of a
holomorphic *Banach-valued* map is holomorphic, without separability; track K only has the second countable
case), `WaveReindex` (`wave` (ii)), `Extract` (`extract`), `Schur` (`schur` (i),(iii)), `Index` (pairing,
multipliers), `Lie` (`lie` (i),(ii) and the guard (G) at sequence level; `homLieSeq`).

Part 2:

| file | content | main declarations |
|---|---|---|
| `NormalOps` | `ops`, `schur` (ii) | `homLamCLM`, `norm_homLamCLM_apply_le`, `homHadamardOp_lam`, `norm_homLam_hadamard_le`, `homDualNorm`, `norm_le_of_pairing_le` |
| `NormalPol` | polarization | `homPairL2`, `homPairL2_symm_of_entries`, `norm_le_of_quadratic` |
| `Taylor` | `taylor` | `HomTaylor`, `homRz`, `homRtheta`, `homXnorm`, `HomDomain`, `homNorm_le_uv` (`bpW:w4:zu`) |
| `ComponentsBasic`, `ComponentsFirst`, `AngleSupport`, `ComponentsAngle`, `ComponentsAngleQ` | `components` | `homComp_first` (i), `homComp_angle` (ii) |
| `CohEq` | scalar cohomological equation | `homCohEq_scalar` |
| `LemmaOneMult`, `LemmaOneF` | division operators, `F ∈ 𝒯_{s-σ}` | `HomMultBounds`, `homMultBounds_of`, `homSolveTaylor` |
| `SolveImage`, `SolveImageSub` | image bounds of the solve | `homSolve_image_partial_bound`, `homSolve_image_sub_bound`, … |
| `LemmaOneAssembly`, `LemmaOneBounds` | `lemma1` (iii) | `homXnorm_le_of_components`, `homF_compBounds`, `homLemma1_fieldBound` |
| `LemmaOneFin`, `LemmaOneEq`, `LemmaOneEqFam`, `LemmaOneEquation` | `lemma1` (ii) | `homEq_a … homEq_Q`, `homLemma1_equation` |
| `NhatTaylor` | `lemma1` (i),(iv) | `homNhatTaylor`, `homNhatTaylor_val`, `homNhat_coeff_bounds`, `homNhat_fieldBound`, `homLemma1_zero_modes` |
| `TaylorSub`, `LemmaOneLip`, `LemmaOneLipDiff`, `LemmaOneLipBounds` | Lipschitz in `ξ` | `HomTaylor.sub`, `HomMultLip`, `homMultLip_of`, `homF_sub_compBounds` |
| `Lemma1` | assembly, `lemma2` | `homLemma1_lipschitz`, `homNhat_lipschitz`, `homLemma2` |
| `LieDeriv` | `lie` (iv) | `homNfun`, `homNfun_hasFDerivAt`, `homLemma_lie_iv`, `homGuard_of_cond`, `not_homGuard_of_lt` |
| `LemmaOneAll` | `lemma1` (ii), all `z` | `homLemma1_equation_all` (continuity + truncations) |
| `RealSolve`, `RealF` | `lemma1` (i), reality | `HomTaylor.IsReal`, `homSolveTaylor_isReal`, `homNhatTaylor_isReal` |

Blueprint Lemma 1: (i) `homSolveTaylor` + `homLemma1_zero_modes`; (ii) `homLemma1_equation`; (iii)
`homLemma1_fieldBound`, `homLemma1_lipschitz`; (iv) `homNhat_coeff_bounds`, `homNhat_fieldBound`,
`homNhat_lipschitz`. Lemma 2 and bound (4): `homLemma2` (with `homKS_lt_29`: `3C₁ < 108`) and `waveBW_le`.

## Deviations and caveats (read before audit)

* **Lemma 1 (ii) for all `(z, \bar z)`**: `homLemma1_equation_all` (needs `|Ω_j| ≤ K₀ (j+2)`, from the frequency
  hypotheses `homOmega_le`); it is deduced from the finitely supported case `homLemma1_equation` by continuity of
  both sides in `(z, \bar z) ∈ HomL2 × HomL2` and the truncations `P_N z → z`. `L_N F` is `homLieN` (with
  `homPairOmega` for `⟨F_z, Ωz⟩₀`), `N̂` is `homNhat` (true coordinates).
* **Guarded derivative** (`LieDeriv`): the phase carrier is `HomPhase = ℂ² × ℂ² × HomL2 × HomL2` (the weighted
  `lp` carrier of `KAM/Wave/Seq`; normal variables by their representatives). Under `HomGuard a p γ` the form
  `N_Ω` is the bounded bilinear map `homNOmegaCLM`, `N = homNfun` has the derivative `homDN` (`DN(w)(Θ,Y,Z,\bar Z)
  = ⟨ω,Y⟩ + N_Ω(Z,\bar z) + N_Ω(z,\bar Z)`), and `homLemma_lie_iv` gives `DN(w)·X_F(w) = −L_N F(w)` for the
  field `X_F = (·, −(1/2π)F_θ, −iF_{\bar z}, iF_z)` with the normal components embedded in `ℓ^N_{a,p}`
  (`homEmbed`, `ĉ_j ↦ ĉ_j/(j+2)`); equality with the weak bracket is `homWeakBracket_eq_neg_lieN` (`Lie.lean`).
  `homGuard_of_cond` (for `a, p ≥ 0`: `a > 0 ∨ p ≥ 1/2 ⟹ ∃γ, (G)`) and `not_homGuard_of_lt` (`a = 0`, `p < 1/2`
  fails) give the characterisation of (G); `homGuard_one_one` the wave value `γ = e^{-6}/3`.
* **Reality** is `HomTaylor.IsReal` (at real `θ`: `a, b` real, `c^- = \overline{c^+}`, `P' = \overline P`,
  `Q^T = \overline Q` in the entries of the represented operators; weights are real). `F` and `N̂` real if `R` is
  (`homSolveTaylor_isReal`, `homNhatTaylor_isReal`), by `homSolve_conj_real` and the divisor parities
  (`homMultA0_conj`, `homMultDp_conj`, `homDP_conj`, `homDQ_conj`, …).
* **Lipschitz statements** are for the *difference* Taylor Hamiltonian `F(ξ).sub F(ζ)`: the hypothesis
  `|X_{R(ξ)} − X_{R(ζ)}|_r ≤ ε^L d` is `HomFieldBound … (εL * d) (R₁.sub R₂)` (fields are linear in the components).
  The parameter dependence enters through `HomMultBounds` at `ξ`, `ζ` and `HomMultLip` (`homMultLip_of`).
* `N̂`'s field is the field of the Taylor Hamiltonian `homNhatTaylor R` (constant components), identified with the
  blueprint `N̂` by `homNhatTaylor_val`.
* The Hadamard maps are used in the weighted-matrix model; `symP`, `symP'`, `transQ` are fields of `HomTaylor` on
  `T_s` only.

## Not done

* Only remarks without formal statements: `bpW:w4:from-w3`, `bpW:w4:to-w5`, the `weights` remark, and
  `bpW:w4:k0` (superseded by W7, "used by no later result").

## Checks

* Every module built with `/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpj <Module>` in import order
  (final run after the line wrapping; last line `Build completed successfully`); single-file checks with
  `w_lean.sh`.
* `w_lint.sh /root/code/KAM-inp-wpj`: exit 0; tail `check_lean_modules: PASS (3602 Lean files, 0 comparator
  configurations)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (177 frozen declarations of KAM; ...)`. `KAM/Root/Wave.lean`
  regenerated by `scripts/gen_root_imports.py`.
* `#print axioms`: `[propext, Classical.choice, Quot.sound]` for `homLemma1_equation`, `homLemma1_fieldBound`,
  `homLemma1_lipschitz`, `homNhat_fieldBound`, `homNhat_lipschitz`, `homNhat_coeff_bounds`,
  `homLemma1_zero_modes`, `homLemma2`, `homComp_first`, `homComp_angle`, `homMultLip_of`, `homMultBounds_of`,
  `homCohEq_scalar`, `norm_le_of_quadratic`, `homF_compBounds`, `homXnorm_le_of_components`, `homSolveTaylor`,
  `homNhatTaylor_val`, `homEq_Q`, `homLemma_lie_iv`, `homNfun_hasFDerivAt`, `homGuard_of_cond`, `not_homGuard_of_lt`, `homLemma1_equation_all`, `homSolveTaylor_isReal`, `homNhatTaylor_isReal`, and for all part-1 declarations listed in the earlier handoff.

## Suspected errata / blueprint observations

* `lemma1` proof, step *Assembly*: the constant is `C₁ = 7 + 10K_S`; `3C₁ < 108` needs `K_S < 2.9`
  (`K_S < 2.82` as in the blueprint; `homKS_lt_29` proves `< 2.9`).
* `components` (ii): the bilinear bounds are not bounds on the operator norms of `∂_θ P`; the proof must (and does)
  pass through `Λ` (`D ∂P̂`), with the symmetry of `Λ∂P̂` coming from the entry symmetry of `P`.
* Track K `[SecondCountableTopology]` hypotheses (Regularity, Averages, AnalyticSeries) do not cover non-separable
  operator targets; see `HolomorphicBanach`.

## Design signals

No heartbeat failures in final code. One elaboration trap: passing `fun hm k => lemma (hm.Q k)` with `hm`'s type left to
unification (field-notation on a metavariable) made `homLipField_dQ` time out; stating the commutation facts as named
lemmas (`homLam_comm_homTQ`, …) fixed it.

## p_plus refactor (bpW:w5:w4-general)

**Audit target commit: `82d8325d`** ("W4 p_plus refactor (names): ..."; supersedes `945977b7`, which had the `_succ` corollaries).

W4 is now parametrized by the smoothing exponent `p_+` (Lean: `pb`, hypotheses `hp : 0 ≤ p`, `hpb : p ≤ pb`):
* New parameter: `HomTaylor a p pb s`, `homNormalEntry a p pb`, `homLamD a p pb` (hence `homLamDiag/homLamCLM/homPairRep/
  homDualNorm` with weight condition `homPP : 0 ≤ p + pb`), `homNormEntryCLM a p pb`, `homEmbed a p pb hpb`
  (`ĉ_j ↦ ĉ_j ω_p/ω_{p_+}`), and everything built on them (`HomFieldBound`, `homXnorm`, `homSolveTaylor`, `homLieN`, …).
  The unchanged parts (`homLemma2`, lattice, divisors, `homGuard_of_cond`, `one_le_homWt`) do not take `pb`.
* Tail hypothesis: `HomFreqHyp` now has `j^{1/2}|Ω̃_j| ≤ M₀`, `j^{1/2}|Ω_j(ξ)-Ω_j(ζ)| ≤ M_Ω|ξ-ζ|` (`bpW:w5:freq`).
  The original (tail weight `j`) is `HomFreqHyp1`, with `HomFreqHyp1.toHyp : HomFreqHyp1 … → HomFreqHyp …`
  (same constants). `homFreqHyp1_wave` is the old wave statement; `homFreqHyp_wave` gives the weak one.
* Statement changes forced by `p_+`: Lemma 1 (iv) coefficient bound reads
  `(j+2)^{p_+-p} ‖(homNormalEntry …) j j‖ ≤ ε` (`homNhat_coeff_bounds`, `homDiagonal_bound`);
  `homLie_pairing_summable` has `F ∈ ℓ_{a,p_+}` and hypothesis `1 ≤ p + p_+` (pairing pair `(p-1, p_+)`);
  `homLemma1_equation_all` has the extra hypothesis `1 ≤ p + p_+` (`homWt_mul_ge`, `norm_homLamD_mul_le`,
  needed for `‖D_jΩ_j‖ ≤ K₀`). The field bounds, Lipschitz bounds, Lemma 2 and constants are unchanged.
* **Old names keep old statements.** Every declaration whose statement mentions `p_+` was renamed with the
  suffix `_gen` (e.g. `HomTaylor_gen a p pb s`, `homLemma1_fieldBound_gen`, `homLemma_lie_iv_gen`,
  `homNormalEntry_gen a p pb`); the general ones take `hpb : p ≤ pb`. In `KAM/Wave/Homological/PPlusOne.lean`
  the original names denote the original (`p_+ = p+1`) objects again: definitions are `abbrev`s at `pb := p+1`
  (`HomTaylor`, `homNormalEntry`, `homLamD`, `homLamDiag`, `homLamCLM`, `homPairRep`, `homDualNorm`, `homRz` …,
  `homRtheta`, `homXnorm`, `HomFieldBound`, `HomTaylor.sub`, `HomTaylor.IsReal`, `homRval`, `homLieN`, `homNhat`,
  `homPairOmega`, `homSolveTaylor`, `homNhatTaylor`, `homEmbed`, `homNormEntryCLM`) and the theorems have their
  original statements, each proved by its `_gen` version (all headline results: `homLemma1_fieldBound`,
  `homLemma1_lipschitz`, `homLemma1_equation`, `homLemma1_equation_all`, `homLemma1_zero_modes`,
  `homNhat_coeff_bounds` (original `(j+2)|…| ≤ ε` form), `homNhat_fieldBound`, `homNhat_lipschitz`,
  `homNhatTaylor_val`, `homComp_first`, `homComp_angle`, `homF_compBounds`, `homXnorm_le_of_components`,
  `homLemma_lie_iv`, `homLie_pairing_summable`, `homSolveTaylor_isReal`, `homNhatTaylor_isReal`,
  `homDiagonal_bound`, `norm_homLamD_mul_le`, `norm_homLamCLM_apply_le`, `homHadamardOp_lam`,
  `norm_homLam_hadamard_le`, `homEq_Q`, `homLam_comm_homTQ`, `homLipField_dQ`, `homF_sub_compBounds`).
  Declarations whose statement does not mention `p_+` (e.g. `homLemma2`, `homGuard_of_cond`, `homKS_lt_29`)
  were not renamed. **Exception, stated plainly:** the 72 internal helper names listed below (changed
  statements, not mentioned in any handoff) have *no* old-name version: only the `_gen` name exists, so no old
  name changed meaning silently. They are: `HomCompBounds`, `HomTaylor.ext_of`, `continuous_homPairRep_op`, `continuous_homPairRep_right`, `continuous_homRtheta`, `continuous_homRval`, `continuous_homRz`, `continuous_homRzb`, `homAngle_Q`, `homAngle_a`, `homAngle_b`, `homAngle_z`, `homAngle_zb`, `homDiagW`, `homDualNorm_le`, `homEmbedCoef`, `homEq_P`, `homEq_P'`, `homEq_cm`, `homEq_cp`, `homFieldBound_nonneg`, `homLamCLM_apply`, `homLamDiag_apply`, `homLamDiag_comm_homTdm`, `homLamDiag_comm_homTdp`, `homLam_comm_hadamard`, `homLam_comm_homTP`, `homLam_comm_homTP'`, `homLam_entry_eq`, `homLam_entry_symm`, `homLipField_dP`, `homLipField_dP'`, `homLipField_dcm`, `homLipField_dcp`, `homNOmega_embed`, `homNOmega_le`, `homNhatTaylor_sub`, `homNormEntryCLM_apply`, `homNormalEntry_hadamard`, `homNormalEntry_partial`, `homNormalEntry_partial_symm`, `homNormalEntry_sub`, `homPairOmega_Rz`, `homPairOmega_Rzb`, `homPairOmega_eq_clm`, `homPairOmega_fin`, `homPairOmega_op_fin`, `homPairRep_eq`, `homPairRep_eq'`, `homPairRep_fin`, `homPairRep_op_fin`, `homPartial_sub_comp`, `homRtheta_fin`, `homRtheta_y`, `homRtheta_z`, `homRtheta_zb`, `homRtheta_zzb`, `homRval_fin`, `homRz_eq`, `homRzb_eq`, `homSent`, `homSolveTaylor_Q`, `homSolve_entry_symm`, `homSolve_hadamard_entry`, `homXnorm_nonneg`, `homXnorm_parts`, `kamEntry_homLamCLM`, `norm_homEmbedCoef_le`, `norm_homLamD_le`, `norm_homLamDiag_le`, `norm_homPairRep_le`, `norm_homPairRep_op_le`.
* Checks: all W4 modules and `PPlusOne` build (rebuilt in import order after the rename) (`w_build.sh`); `w_lint.sh` exit 0;
  `#print axioms` of `homLemma1_fieldBound`, `homLemma1_lipschitz`, `homLemma1_equation_all`, `homLemma_lie_iv`,
  `homNhat_coeff_bounds`, `homSolveTaylor_isReal`, `homFreqHyp_wave`, `homLemma2`: propext, Classical.choice, Quot.sound.

**Short-name renames (commit `7de5b4e0`, "W4 names: ...").** The audit launcher's short-name check now passes
(`main_shortname_check.py` on all `KAM.Wave.Homological.*`: "no reused public short name"). Renamed:
`IsHomComp.sub → IsHomComp.homSub` (in `TaylorSub.lean`), `conj_character_real → homConj_character_real`,
`coth_le_one_add_inv → wave_coth_le_one_add_inv`, `HomTaylor_gen.sub → HomTaylor_gen.homSub` (and the old-name abbrev
`HomTaylor.sub → HomTaylor.homSub`), `HomTaylor_gen.IsReal → HomTaylor_gen.isRealTaylor` (`HomTaylor.IsReal →
HomTaylor.isRealTaylor`), `HomHadamardBound.nonneg → HomHadamardBound.homNonneg`, `HomFreqHyp.nonneg`/`HomFreqHyp1.nonneg
→ consts_nonneg`. **The W4 audit should target this commit (`7de5b4e0`), which supersedes `82d8325d`.** The old-name
statements are unchanged in content; only these auxiliary identifiers changed.

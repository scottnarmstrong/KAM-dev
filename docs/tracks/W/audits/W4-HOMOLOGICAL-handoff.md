# Handoff: W4-HOMOLOGICAL (branch `inp-wpj`)

Blueprint: `blueprint-W/parts/w4-homological.tex` (current `inp` version, with the accepted W4-E5 Riesz gap
repair). Status: **Lemma 1 (i)–(iv) and Lemma 2 are proved in the representative model below, with the
deviations listed**; not done: the guarded Fréchet derivative of `N` (Lie (iv)), the extension of the equation
(ii) from finitely supported to all `(z, \bar z)`, reality in (i), and the remarks `from-w3`/`to-w5` (no
statements). Everything compiles under the gate, has no `sorry`, no new axiom, no heartbeat override, all
files are under 700 lines, no line over 100 characters.

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
multipliers), `Lie` (`lie` (i),(ii) and the guard (G) at sequence level).

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

Blueprint Lemma 1: (i) `homSolveTaylor` + `homLemma1_zero_modes`; (ii) `homLemma1_equation`; (iii)
`homLemma1_fieldBound`, `homLemma1_lipschitz`; (iv) `homNhat_coeff_bounds`, `homNhat_fieldBound`,
`homNhat_lipschitz`. Lemma 2 and bound (4): `homLemma2` (with `homKS_lt_29`: `3C₁ < 108`) and `waveBW_le`.

## Deviations and caveats (read before audit)

* **Equation (ii) for finitely supported `z, \bar z`** (`∀ j ∉ S, z j = 0`, `S` finite). The blueprint states it for
  all `z` and extends by density; the density step (continuity of both sides, `truncLp`) is not formalized.
  `L_N F` is `homLieN` (with `homPairOmega` for `⟨F_z, Ωz⟩₀`), `N̂` is `homNhat` (true coordinates), and the
  statement is `L_N F + N̂ = R − â₀`.
* **Lipschitz statements** are stated for the *difference* Taylor Hamiltonian `F(ξ).sub F(ζ)`: the hypothesis
  `|X_{R(ξ)} − X_{R(ζ)}|_r ≤ ε^L d` is `HomFieldBound … (εL * d) (R₁.sub R₂)`; the fields are linear in the
  components, so `X_{R₁.sub R₂} = X_{R₁} − X_{R₂}`. The parameter dependence enters through
  `HomMultBounds` at `ξ` and `ζ` and `HomMultLip` (derived from `(H_α)`, `homMultLip_of`).
* **Reality** in (i) (`F` and `N̂` real if `R` real) is not formalized (the class has no reality predicate).
* `N̂`'s field is the field of the Taylor Hamiltonian `homNhatTaylor R` (constant components), identified with the
  blueprint `N̂` by `homNhatTaylor_val`.
* The Hadamard maps are used with the weighted-matrix model; `P`, `Q^T` etc. keep the entrywise relations
  (`symP`, `transQ`) as fields of `HomTaylor`, on `T_s` only (not on all of `ℂ²`).
* In `Lie.lean`, items (iii) and the Fréchet derivative of (iv) (the identity `DN·X_F = −L_N F` under (G)) are
  not stated separately; (iii) is used inside `homLemma1_equation` through the entrywise equations.

## Not done

* `bpW:w4:lie` (iv) Fréchet derivative of `N` under the guard (needs a Banach model of `ℓ^N`), and the "iff"
  characterisation of (G).
* Extension of (ii) to all `(z, \bar z)`; reality; `bpW:w4:from-w3`, `bpW:w4:to-w5` (remarks about interfaces, no
  formal statements); `bpW:w4:k0` (superseded by W7); the `weights` remark (no statement).

## Checks

* Every module built with `/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpj <Module>` in import order
  (final run after the line wrapping; last line `Build completed successfully`); single-file checks with
  `w_lean.sh`.
* `w_lint.sh /root/code/KAM-inp-wpj`: exit 0; tail `check_lean_modules: PASS (3598 Lean files, 0 comparator
  configurations)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (177 frozen declarations of KAM; ...)`. `KAM/Root/Wave.lean`
  regenerated by `scripts/gen_root_imports.py`.
* `#print axioms`: `[propext, Classical.choice, Quot.sound]` for `homLemma1_equation`, `homLemma1_fieldBound`,
  `homLemma1_lipschitz`, `homNhat_fieldBound`, `homNhat_lipschitz`, `homNhat_coeff_bounds`,
  `homLemma1_zero_modes`, `homLemma2`, `homComp_first`, `homComp_angle`, `homMultLip_of`, `homMultBounds_of`,
  `homCohEq_scalar`, `norm_le_of_quadratic`, `homF_compBounds`, `homXnorm_le_of_components`, `homSolveTaylor`,
  `homNhatTaylor_val`, `homEq_Q`, and for all part-1 declarations listed in the earlier handoff.

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

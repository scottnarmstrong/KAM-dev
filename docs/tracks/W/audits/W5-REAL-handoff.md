# Handoff: W5-REAL (branch `inp-w5r`, worktree `/root/code/KAM-inp-wpq`)

Blueprint: `blueprint-W/parts/w5-kamstep.tex`, labels `bpW:w5:step` (i), (ii), `bpW:w5:new-ham` (ii),
(iii), `bpW:w5:flow` (iv), `bpW:w5:flow-calc` (iii), `bpW:w5:taylor` (i) ("`R` is real").
Task: the three clauses the W5 step theorem omits (W5-STEP handoff, Session 5, "Deviations / open"),
as separate theorems in new files `KAM/Wave/KamStep/Real*.lean`.
**Status: (1), (2), (3) all done**, for `StepHyp` (non-modified case) and for `StepHypMod` (modified
case). No existing file was edited except the generated `KAM/Root/Wave.lean`
(`scripts/gen_root_imports.py`). No `sorry`, `axiom`, heartbeat or recursion override. Largest new
file 225 lines. Every new module elaborates at default heartbeats in a few seconds.

Commits: `f237686b` (2), `3ca7924b` (1), `92dcca5b` (3), `dc7bebd5` (docstring wraps, root
regeneration), plus the commit of this handoff.

## Files (all new, namespace `KAM.Wave`)

| file | lines | item |
|---|---|---|
| `KAM/Wave/KamStep/RealSmoothOnto.lean` | 225 | (2) `DΦ(w)` maps `𝒫^{p_+}` onto `𝒫^{p_+}` |
| `KAM/Wave/KamStep/RealFlowPicard.lean` | 148 | (1) the flow of a real field is real |
| `KAM/Wave/KamStep/RealTaylorOf.lean` | 213 | (1) `R = stepTaylorOf …` is real (W4 sense) |
| `KAM/Wave/KamStep/RealTaylorFun.lean` | 179 | (1) a real Taylor Hamiltonian and its field are real at real points |
| `KAM/Wave/KamStep/RealStep.lean` | 186 | (1) headline: `Φ` real, `P_+` real |
| `KAM/Wave/KamStep/RealNField.lean` | 167 | (3) `X_N`, Riesz representation of `DN` |
| `KAM/Wave/KamStep/RealWeakConj.lean` | 181 | (3) weak conjugacy in field form |
| `KAM/Root/Wave.lean` | +7 | generated |

## Model (read this first)

`StepPhase r` is `KamPhase` with the norm `|·|_{p,r}`; normal coordinates are stored as
representatives (`ω_{a,q}(j+2)` times the true coordinate). `𝒫 = 𝒫^p` is `StepPhase r` in the
`p`-representatives. `𝒫^{p_+}` is `StepPhase r` read in the `p_+`-representatives, and its inclusion
into `𝒫` is `ι = stepEmbedCLM a p pb hpb r` (diagonal, real coefficients
`ω_{a,p}(j+2)/ω_{a,pb}(j+2)`; `stepEmbedCLM_injective`). So "`W ∈ 𝒫^{p_+}`" is "`W = ι W'`". This is
the model already used by the landed flow (`smoothField (stepEmbedCLM …) (stepFieldS …)`).
A point is real (`StepReal`, landed in `RealCalc.lean`) iff all its coordinates are real; since the
weights are real this is the same in representatives and in true coordinates.
`Φ = H.core.Phi ξ`, `P_+ = H.core.Pplus ξ`, `X_{P_+} = H.core.Xplus ξ`, `ω_+ = H.core.omegaPlus ξ`,
`Ω_+ = H.core.OmegaPlus ξ` are the objects of the landed `stepTheorem_of_eps0_pos` / `StepCore`.

## AUDIT FOCUS

### (1) Reality: `KAM/Wave/KamStep/RealStep.lean:167` (`StepHyp`), `:178` (`StepHypMod`)

```lean
theorem stepTheorem_reality
    (H : StepHyp a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)] :
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), StepReal (StepPhase.toK w) →
      StepReal (StepPhase.toK (H.core.Phi ξ w))) ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), StepReal (StepPhase.toK w) →
      (H.core.Pplus ξ w).im = 0)
```
`stepTheoremMod_reality` is the same statement for `H : StepHypMod … β …`.
Companion: `kamDomain_star_mem` (`RealStep.lean:47`): `D(s,r)` is invariant under conjugation of all
coordinates (the other half of "`P_+` is real" in `bpW:w5:class`; `D_+ = stepDomain … = kamDomain …`).

Proof route (check these):
* `stepTaylorOf_isRealTaylor` (`RealTaylorOf.lean:198`): `P` real at real points ⇒ `R` real in W4's
  sense `HomTaylor_gen.isRealTaylor` (all five clauses: `a, b` real, `c^- = \overline{c^+}`,
  `P' = \overline P`, `Q^T = \overline Q` in true entries). Key lemma `stepBilin_iota_conj`
  (`:102`): for the bilinear form `(c,c') ↦ ϖ(DX(w₀)c, c')`, real on real vectors
  (`stepSymp_dfield_im'`, landed), conjugation exchanges the values on `ι_z e_j` and `ι_{\bar z} e_j`.
* `F` real: `StepHyp.FT_isRealTaylor` (`RealStep.lean:134`) is W4-COMPLETE's unconditional
  `homLemma1Complete_real_gen` (CompleteZeroReal.lean:79); `StepHypMod.FT_isRealTaylor` (`:155`) is
  `homModSolveTaylor_isReal` (ModifiedReal.lean:130) on the `p+1` Taylor family `R1`.
* `stepFun_real` (`RealTaylorFun.lean:89`): a real Taylor Hamiltonian is real at real points
  (`\bar z = \overline z`; conjugation maps each term to its partner; the `Q`-term to itself via
  `transQ`). `stepField_real` (`:163`): its field is real at real points (`DT(w)c = ϖ(X_T(w),c)`
  real for real `c` by `fderiv_im_of_real`, and real coordinate directions detect each coordinate,
  `stepReal_of_symp`).
* `holoFlow_real_of_field_real` (`RealFlowPicard.lean:64`): abstract; real points = common zeros of
  real-linear functionals; every Picard iterate is real, and the limit is real. `stepFlow_real`
  (`:131`) is the concrete flow of `X_F` on `D(s-2σ, r/2)`.
* `P_+` real: from `H ∘ Φ = N_+ + P_+ + â₀` (landed `StepCore.conj_eq`): `N(Φw)` and `N_+(w)` real
  (`stepNfun_real`, real frequencies), `P(Φw)` real (`hreal`, `Φw ∈ D(s,r)`), `â₀ = [a]` real
  (`StepCore.a0_im`).

Conditional helpers (rule 6): `StepCore.phi_real_of_FT_real` (`RealStep.lean:100`),
`StepCore.Pplus_real_of_FT_real` (`:110`) assume `∀ ξ ∈ Par, (FT ξ).isRealTaylor`, because the
abstract `StepCore` does not record how `FT` was obtained. They are used only through
`stepTheorem_reality` / `stepTheoremMod_reality`, which discharge that premise from W4.

### (2) `DΦ(w)(𝒫^{p_+}) = 𝒫^{p_+}`: `KAM/Wave/KamStep/RealSmoothOnto.lean:199`, `:213`

```lean
theorem stepTheorem_dPhi_smooth_onto
    (H : StepHyp a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)]
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    (∀ W' : StepPhase r, ∃ W'' : StepPhase r,
      fderiv ℂ (H.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'') ∧
    (∀ W'' : StepPhase r, ∃ W' : StepPhase r,
      fderiv ℂ (H.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'')
```
(into, and onto). `stepTheoremMod_dPhi_smooth_onto` is the same for `StepHypMod`. The flow-level
statements (`bpW:w5:flow-calc` (iii), on `D(s-3σ, r/4)`, any `|t| ≤ 1`) are
`stepFlow_dPhi_smooth_mapsTo` (`:112`) and `stepFlow_dPhi_smooth_onto` (`:135`). Proof:
`Dφ^t = I + ι ∘ DΨ^t` (landed `fderiv_holoFlow_smooth`), `‖DΨ^t(w)‖ ≤ M_F/(σ/8) < 1`
(`flowII_deriv`), and `I + DΨ^t(w) ∘ ι` is invertible on `𝒫^{p_+}` (Neumann series,
`fderiv_holoFlow_smooth_onto`, `:60`). Invertibility of `DΦ(w)` on `𝒫` was already landed
(`isUnit_fderiv_holoFlow`).

### (3) `X_N`, Riesz representation, field-form weak conjugacy

`KAM/Wave/KamStep/RealNField.lean:65`
```lean
def stepXN (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (ω : Fin 2 → ℝ)
    (w : KamPhase) : KamPhase :=
  (fun i => (2 * Real.pi : ℂ)⁻¹ * (ω i : ℂ), 0, stepXNdiag (a := a) (p := p) hΩ w.2.2.2,
    -stepXNdiag (a := a) (p := p) hΩ w.2.2.1)
```
`X_N(w') = (ω/2π, 0, Ωv', -Ωu')` in the `(p-1)`-representatives: `stepXNdiag` multiplies the
`p`-representative by `stepXNcoef a p Ω j = Ω_j ω_{a,p-1}(j+2)/ω_{a,p}(j+2) = Ω_j/(j+2)`
(`homWt_pred_div`), bounded by `K₀` (`norm_stepXNcoef_le`). Check: this is the
`(p-1)`-representative of the true coordinate `Ω_j v'_j`.

`KAM/Wave/KamStep/RealNField.lean:105` (Riesz representation, `bpW:w5:new-ham` step `n-conj`)
```lean
theorem stepDN_eq_symp_XN (ha : 0 ≤ a) (hpb : p ≤ pb) (hqq : 0 ≤ (p - 1) + pb)
    (hG : HomGuard a p γ) (hK0 : 0 ≤ K0) (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2))
    (ω : Fin 2 → ℝ) (w W : KamPhase) :
    (homDN hG hK0 hΩ ω (stepToHom w)).comp stepToHom (kamHomEmbed a p pb hpb W) =
      stepSymp (q := p - 1) (q' := pb) ha hqq (stepXN (a := a) (p := p) hΩ ω w) W
```
`DN(w')(ι W) = ϖ_{p-1,p_+}(X_N(w'), W)` for all `w' ∈ 𝒫`, `W ∈ 𝒫^{p_+}`; `ϖ_{q,q'}` is the landed
`stepSymp` (pairing of a `q`-representative with a `q'`-representative; `q+q' ≥ 0` needed).
`stepSymp_embed_eq` (`:157`): `ϖ_{p,p}(ι X, ι W) = ϖ_{p-1,p_+}(ι_{p_+→p-1} X, W)` (both are the true
pairing, `stepPair_embed_eq_true`).

`KAM/Wave/KamStep/RealWeakConj.lean:137` (`StepHyp`), `:160` (`StepHypMod`)
```lean
theorem stepTheorem_weakConj_field
    (H : StepHyp a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)]
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    (∀ W' : StepPhase r, ∃ W'' : StepPhase r,
      fderiv ℂ (H.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'') ∧
    (∀ W' W'' : StepPhase r, fderiv ℂ (H.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'' →
      stepSymp (q := p - 1) (q' := pb) H.ha H.core.hqq1
          (stepXN (a := a) (p := p) (homOmega_le H.freq hξ) (ω ξ)
              (StepPhase.toK (H.core.Phi ξ w)) +
            kamHomEmbed a (p - 1) pb H.core.hpm (X ξ (StepPhase.toK (H.core.Phi ξ w))))
          (StepPhase.toK W'') =
        stepSymp (q := p - 1) (q' := pb) H.ha H.core.hqq1
          (stepXN (a := a) (p := p) (H.core.omegaPlus_bound hξ) (H.core.omegaPlus ξ)
              (StepPhase.toK w) +
            kamHomEmbed a (p - 1) pb H.core.hpm (StepPhase.toK (H.core.Xplus ξ w)))
          (StepPhase.toK W'))
```
This is `ϖ(X_H(Φw), DΦ(w)W) = ϖ(X_{N_+}(w) + X_{P_+}(w), W)` for `W = ι W' ∈ 𝒫^{p_+}`, with
`DΦ(w) W = ι W''` (exists by the first conjunct; unique by `stepEmbedCLM_injective`),
`X_H = X_N + X_P` in `𝒫^{p-1}` (`X_P` enters through `ι_{p_+→p-1}`), `ϖ = ϖ_{p-1,p_+}`.
`H.core.hqq1 : 0 ≤ (p-1)+pb` and `H.core.hpm : p-1 ≤ pb` are derived from `StepHyp` (`hp1`, `hpb`).
In `stepTheoremMod_weakConj_field` the field of `P` is `H.X' = D_ρ ∘ X` (the `p_+`-representative of
`X_P`, as in `StepHypMod.core`). Proof (`StepCore.weakConj_field`, `:79`): landed derivative form
`StepCore.weakConj` at `W = ι W'`; `DN_+(w) = DN(w) + DN̂(w)` (`StepCore.dNplus_eq`, `:54`, from
`N + N̂ = N_+` and uniqueness of derivatives); `stepDN_eq_symp_XN` for `N` at `Φw` and for `N_+` at
`w`; `stepSymp_embed_eq` for the bounded fields.

## Not done

Nothing of (1)–(3) is open. Not attempted (outside this package): replacing the existing
`stepTheorem_of_eps0_pos` conjunction by one containing the new clauses (the existing KamStep files
were not to be edited; the new theorems are stated against the same objects `H.core.*`, so a later
`StepCore` refactor can add them as conjuncts).

## Deviations (none is a blueprint defect)

* Premises: the theorems take exactly `StepHyp` / `StepHypMod` (and `ξ ∈ Π`, `w ∈ D_+`). They inherit
  the existing `StepHyp` deviation `0 < ε₀` (W5-STEP handoff), used through `H.core`. No new premise.
* "`P_+` real" is stated as "real at the real points of `D_+`" (the convention of the landed `hreal`);
  the conjugation invariance of the domain is the separate lemma `kamDomain_star_mem`.
* `𝒫^{p_+}` is modelled as the range of `ι` (see Model); the weight `p-1` pairing is `stepSymp` with
  `q = p-1`, `q' = p_+`; the "extension of `ϖ` to `𝒫^{p-1} × 𝒫^{p_+}`" is this pairing, and
  `stepSymp_embed_eq` shows it agrees with `ϖ_{p,p}` on `𝒫^{p_+} × 𝒫^{p_+}`.
* `stepDN_eq_symp_XN` is stated for all `w' ∈ 𝒫` (no domain restriction is needed).

## Suspected errata

None found in `w5-kamstep.tex` for these clauses.

## Checks

Gate builds (each `/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpq <M>`):
`KAM.Wave.KamStep.StepTheorem`, `…StepTheoremMod`, `…RealSmoothOnto`, `…RealFlowPicard`,
`…RealTaylorOf`, `…RealTaylorFun`, `KAM.Wave.Homological.CompleteZeroReal`,
`KAM.Wave.Homological.ModifiedReal`, `…RealStep`, `…RealNField`, `…RealWeakConj` (last, after the
docstring wraps): tail `Build completed successfully (3436 jobs).` No warning in any `Real*.lean`
(checked per file with `w_lean.sh`).

`python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-wpq`
on the seven new modules (module names and file paths): `short-name check OK (no reused public short name)`.

`/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpq`: **exit 1**, tail:
```
Lean lines over 100 characters:
/root/code/KAM-inp-wpq/KAM/Wave/KamStep/StepClauses.lean:40:107
/root/code/KAM-inp-wpq/KAM/Wave/KamStep/StepFlowClauses.lean:39:107
/root/code/KAM-inp-wpq/KAM/Wave/KamStep/StepHypMod.lean:208:101
/root/code/KAM-inp-wpq/KAM/Wave/KamStep/StepReweightTaylor.lean:19:101
/root/code/KAM-inp-wpq/KAM/Wave/KamStep/StepTheorem.lean:49:107  (and :119 :129 :136 :155 :166)
/root/code/KAM-inp-wpq/KAM/Wave/KamStep/StepTheoremMod.lean:35:101  (and :47 :54 :73 :84)
check_lean_modules: PASS (3835 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; …)
```
The only failures are 15 over-long lines in **pre-existing** KamStep files of the base branch
(commits `c48d2f50`, `657f4b71`, `9a0768bc`), which this package was told not to edit (another
prover is refactoring StepHyp/StepTheorem). None of the new `Real*.lean` files has a line over 100
characters. Wrapping those 15 lines (whitespace only) makes the lint pass; it belongs to the owner
of those files.

`#print axioms` (all `[propext, Classical.choice, Quot.sound]`): `stepTheorem_reality`,
`stepTheoremMod_reality`, `stepTheorem_dPhi_smooth_onto`, `stepTheoremMod_dPhi_smooth_onto`,
`stepDN_eq_symp_XN`, `stepTheorem_weakConj_field`, `stepTheoremMod_weakConj_field`,
`stepTaylorOf_isRealTaylor`, `stepField_real`, `holoFlow_real_of_field_real`,
`stepEmbedCLM_injective`, `kamDomain_star_mem`.

## Design signals

None. All new modules elaborate in seconds at default heartbeats. One first-draft `exact` of a
defeq-heavy identity (`StepCore.weakConj_field`, unifying `stepToKCLM`/`stepEmbedCLM` applications
against `stepDN_eq_symp_XN` with metavariable arguments) hit the default heartbeat limit; giving the
arguments explicitly and rewriting with `comp_apply`, `stepToKCLM_apply`, `stepEmbedCLM_apply` fixed
it (no budget change).

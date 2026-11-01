/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.ClockGraphCert
public import KAM.Application.GraphCheck
public import KAM.Certificate.Positivity
public import KAM.Certificate.Torsion.Models

/-!
# The clock-triangular graph checks

`Bool` checks of every certificate-side input of the clock-triangular graph adapter
(`ClockGraphCert.lean`), with soundness:

* **clocks** (`checkClock c i a`): `0 < a` and, for every `l ≠ i`, the certificate's expression
  `c.ham` is affine in the action `I_l` with slope `a`: `actionSlope l c.ham = some a`, a
  syntactic computation (`actionSlope`: actions contribute their own slope, a constant factor
  scales it, every other constructor needs operands independent of `I_l`). Sound by
  `eval_add_action`: `H(z + t e_{I_l}) = H(z) + a t`, so `∂_{I_l} H = a` wherever `H` is
  holomorphic (`checkClock_sound`). It covers the Moon Hamiltonians (`soHamExpr`,
  `soRotHamExprScaled c`, `κ · lockHamExpr`) and the toy T2.
* **free diagonal, real torus** (`checkClockGraphReal c i mono`): the margin `disp < mono ρ∞`
  and `sup_{x ∈ ℝⁿ} |∂_i U_i(x)| ≤ 1 - mono` (the unconverted derivative model
  `angleDerivModel` at weight `1`, as `checkAngleGraphReal` but for the one diagonal entry),
  hence `∂_i K_{θ,i} = 1 + ∂_i U_i ≥ mono`.
* **free diagonal, SOS** (`checkClockGraph c i mono mono₀ sos`): the margin and a paid SOS lower
  bound `Re ∂_i K_{θ,i} ≥ mono` on the real torus (`checkRealLowerBound`, residual measured in
  the strip weight) of the `(i, i)` entry of the `DK` models (`clockDiagModel`). For `n = 2`,
  `i = 0` these are the first two conjuncts of the spin–orbit check `checkSoGraph`
  (`soGraphMonoModel g` is `clockDiagModel 2 g.base.emb g.base.weight g.base.piEnc 0`).

`CertifiedTorus.exists_clockGraph_of_checks`: the clock-triangular graph adapter with every
certificate-side input a passing `Bool` check.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Application

open KAM KAM.Certificate CertArith

variable {n : ℕ}

/-! ### The clock slope of a Hamiltonian expression -/

/-- `some q` for the constant expression `q`, `none` otherwise. -/
def hamConstVal? : HamExpr n → Option ℚ
  | .const q => some q
  | _ => none

/-- `some 0` if both operands are independent of the action (slope `0`), `none` otherwise. -/
def slopeZero₂ (a b : Option ℚ) : Option ℚ :=
  if a = some 0 ∧ b = some 0 then some 0 else none

/-- `some 0` if the operand is independent of the action (slope `0`), `none` otherwise. -/
def slopeZero₁ (a : Option ℚ) : Option ℚ :=
  if a = some 0 then some 0 else none

/-- **The slope of `e` in the action `I_l`**: `some s` certifies that `e` is affine in `I_l` with
slope `s` (`eval_add_action`). Actions contribute `1` or `0`, sums add, a constant left factor
scales; every other constructor requires operands of slope `0`. -/
def actionSlope (l : Fin n) : HamExpr n → Option ℚ
  | .const _ => some 0
  | .pi => some 0
  | .action j => some (if j = l then 1 else 0)
  | .cosMode _ => some 0
  | .sinMode _ => some 0
  | .add a b =>
    match actionSlope l a, actionSlope l b with
    | some sa, some sb => some (sa + sb)
    | _, _ => none
  | .mul a b =>
    match hamConstVal? a, actionSlope l b with
    | some q, some sb => some (q * sb)
    | _, _ => slopeZero₂ (actionSlope l a) (actionSlope l b)
  | .div a b => slopeZero₂ (actionSlope l a) (actionSlope l b)
  | .pow a _ => slopeZero₁ (actionSlope l a)
  | .exp a => slopeZero₁ (actionSlope l a)
  | .sin a => slopeZero₁ (actionSlope l a)
  | .cos a => slopeZero₁ (actionSlope l a)
  | .sqrt a => slopeZero₁ (actionSlope l a)

theorem eval_of_hamConstVal? {e : HamExpr n} {q : ℚ} (h : hamConstVal? e = some q)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) : e.eval z = q := by
  cases e <;> simp [hamConstVal?] at h
  subst h
  rfl

theorem eq_zero_of_slopeZero₂ {a b : Option ℚ} {s : ℚ} (h : slopeZero₂ a b = some s) :
    a = some 0 ∧ b = some 0 ∧ s = 0 := by
  unfold slopeZero₂ at h
  split_ifs at h with h0
  · exact ⟨h0.1, h0.2, (Option.some_inj.1 h).symm⟩

theorem eq_zero_of_slopeZero₁ {a : Option ℚ} {s : ℚ} (h : slopeZero₁ a = some s) :
    a = some 0 ∧ s = 0 := by
  unfold slopeZero₁ at h
  split_ifs at h with h0
  · exact ⟨h0, (Option.some_inj.1 h).symm⟩

/-- **Soundness of the slope**: `actionSlope l e = some s` gives
`e(θ, I + t e_l) = e(θ, I) + s t` for all complex `t`. -/
theorem eval_add_action {l : Fin n} {e : HamExpr n} {s : ℚ} (h : actionSlope l e = some s)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) (t : ℂ) :
    e.eval (z.1, z.2 + t • Pi.single l 1) = e.eval z + s * t := by
  induction e generalizing s with
  | const q =>
    simp only [actionSlope, Option.some_inj] at h
    subst h; simp [HamExpr.eval]
  | pi =>
    simp only [actionSlope, Option.some_inj] at h
    subst h; simp [HamExpr.eval]
  | action j =>
    simp only [actionSlope, Option.some_inj] at h
    subst h
    by_cases hj : j = l
    · subst hj; simp [HamExpr.eval]
    · simp [HamExpr.eval, hj]
  | cosMode k =>
    simp only [actionSlope, Option.some_inj] at h
    subst h; simp [HamExpr.eval]
  | sinMode k =>
    simp only [actionSlope, Option.some_inj] at h
    subst h; simp [HamExpr.eval]
  | add a b iha ihb =>
    simp only [actionSlope] at h
    cases ha : actionSlope l a <;> cases hb : actionSlope l b <;> simp [ha, hb] at h
    subst h
    simp only [HamExpr.eval, iha ha, ihb hb]
    push_cast; ring
  | mul a b iha ihb =>
    simp only [actionSlope] at h
    cases hq : hamConstVal? a with
    | none =>
      simp only [hq] at h
      obtain ⟨h1, h2, rfl⟩ := eq_zero_of_slopeZero₂ h
      simp [HamExpr.eval, iha h1, ihb h2]
    | some q =>
      cases hb : actionSlope l b with
      | none =>
        simp only [hq, hb] at h
        obtain ⟨-, h2, -⟩ := eq_zero_of_slopeZero₂ h
        exact absurd h2 (by simp)
      | some sb =>
        simp only [hq, hb, Option.some_inj] at h
        subst h
        simp only [HamExpr.eval, eval_of_hamConstVal? hq, ihb hb]
        push_cast; ring
  | div a b iha ihb =>
    simp only [actionSlope] at h
    obtain ⟨h1, h2, rfl⟩ := eq_zero_of_slopeZero₂ h
    simp [HamExpr.eval, iha h1, ihb h2]
  | pow a m iha =>
    simp only [actionSlope] at h
    obtain ⟨h1, rfl⟩ := eq_zero_of_slopeZero₁ h
    simp [HamExpr.eval, iha h1]
  | exp a iha =>
    simp only [actionSlope] at h
    obtain ⟨h1, rfl⟩ := eq_zero_of_slopeZero₁ h
    simp [HamExpr.eval, iha h1]
  | sin a iha =>
    simp only [actionSlope] at h
    obtain ⟨h1, rfl⟩ := eq_zero_of_slopeZero₁ h
    simp [HamExpr.eval, iha h1]
  | cos a iha =>
    simp only [actionSlope] at h
    obtain ⟨h1, rfl⟩ := eq_zero_of_slopeZero₁ h
    simp [HamExpr.eval, iha h1]
  | sqrt a iha =>
    simp only [actionSlope] at h
    obtain ⟨h1, rfl⟩ := eq_zero_of_slopeZero₁ h
    simp [HamExpr.eval, iha h1]

/-- An affine function of `t` along `v` has derivative `s` in the direction `v` wherever it is
differentiable. -/
theorem fderiv_apply_eq_of_affine {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {z v : (Fin n → ℂ) × (Fin n → ℂ)} {s : ℂ} (hd : DifferentiableAt ℂ H z)
    (haff : ∀ t : ℂ, H (z + t • v) = H z + s * t) : fderiv ℂ H z v = s := by
  have hline : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hd' : HasFDerivAt H (fderiv ℂ H z) (z + (0 : ℂ) • v) := by
    simpa using hd.hasFDerivAt
  have h1 : HasDerivAt (fun t : ℂ => H (z + t • v)) (fderiv ℂ H z v) 0 :=
    hd'.comp_hasDerivAt (x := (0 : ℂ)) hline
  have h2 : HasDerivAt (fun t : ℂ => H (z + t • v)) s 0 := by
    rw [show (fun t : ℂ => H (z + t • v)) = fun t => H z + s * t from funext haff]
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul s).const_add (H z)
  exact h1.unique h2

variable {α : Type} [CertArith α]

/-- **The clock check**: `0 < a`, and `c.ham` is affine with slope `a` in every action `I_l`,
`l ≠ i`. -/
def checkClock (c : TorusCertificate n α) (i : Fin n) (a : ℚ) : Bool :=
  decide (0 < a) &&
    (List.finRange n).all fun l => decide (l = i) || decide (actionSlope l c.ham = some a)

omit [CertArith α] in
/-- **Soundness of the clock check**: `∂_{I_l} H ≡ a` on the certified domain for `l ≠ i`. -/
theorem checkClock_sound {c : TorusCertificate n α} (hH : IsRealHolo c.D c.H) {i : Fin n}
    {a : ℚ} (h : checkClock c i a = true) :
    (0 : ℝ) < a ∧ ∀ l, l ≠ i → ∀ z ∈ c.D, fderiv ℂ c.H z (phaseBasis (.inr l)) = a := by
  simp only [checkClock, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies, Bool.or_eq_true] at h
  obtain ⟨ha, hl⟩ := h
  refine ⟨by exact_mod_cast ha, fun l hli z hz => ?_⟩
  have hs : actionSlope l c.ham = some a := (hl l).resolve_left hli
  refine fderiv_apply_eq_of_affine
    (hH.holo.differentiableAt (hH.isOpen.mem_nhds hz)) fun t => ?_
  have e : z + t • phaseBasis (.inr l) = (z.1, z.2 + t • Pi.single l 1) := by
    rw [phaseBasis_inr]; ext <;> simp
  rw [e]
  exact eval_add_action hs z t

/-! ### The free diagonal -/

/-- The model of `∂_i K_{θ,i}`: entry `(i, i)` of the `DK` models, converted to degree `0` (for
`n = 2`, `i = 0`, the spin–orbit `soGraphMonoModel`). -/
def clockDiagModel (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (pe : PiEnclosure α) (i : ℕ) :
    CertModel α :=
  CertModel.toDeg W pe 0 (modelMatrixEntry (dkModels n K W pe) i i)

/-- **The SOS diagonal check** (the spin–orbit form): the margin `disp < mono ρ∞` and the SOS
lower bound `Re ∂_i K_{θ,i} ≥ mono` on the real torus, with SOS witness `sos` and centre `mono₀`
(`checkRealLowerBound`; its residual is measured in the strip weight). -/
def checkClockGraph (c : TorusCertificate n α) (i : Fin n) (mono mono₀ : ℚ) (sos : CertPoly α) :
    Bool :=
  decide (c.params.disp < mono * c.params.rhoInf) &&
    checkRealLowerBound c.weight c.cfgLow (clockDiagModel n c.emb c.weight c.piEnc i.val) mono₀
      mono sos

/-- **The real-torus diagonal check**: the margin `disp < mono ρ∞` and
`sup_{x ∈ ℝⁿ} |∂_i U_i(x)| ≤ 1 - mono` (the unconverted derivative model at weight `1`: for
`U_i = (2π)^d Σ_k c_k e^{2πi k·θ}` the bound is `(2π)^{d+1} Σ_k |k_i| |c_k|`, rounded up). -/
def checkClockGraphReal (c : TorusCertificate n α) (i : Fin n) (mono : ℚ) : Bool :=
  decide (c.params.disp < mono * c.params.rhoInf) &&
    ble ((angleDerivModel n c.emb c.weight i.val i.val).supBound
      KAM.CertificateSharp.Hybrid.realWeight) (ofRatDown (1 - mono))

variable [LawfulCertArith α] {c : TorusCertificate n α}

/-- **Soundness of the SOS diagonal check.** -/
theorem checkClockGraph_sound (hs : checkStatic c = true) {i : Fin n} {mono mono₀ : ℚ}
    {sos : CertPoly α} (h : checkClockGraph c i mono mono₀ sos = true) :
    ClockMono c i mono ∧ (c.params.disp : ℝ) < mono * c.params.rhoInf := by
  have S := checkStatic_sound hs
  simp only [checkClockGraph, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hm, hlow⟩ := h
  have hM : (clockDiagModel n c.emb c.weight c.piEnc i.val).Encloses n c.weight.rho
      fun θ => (fderiv ℂ c.K θ (Pi.single i 1)).1 i :=
    ((dkModels_encloses (n := n) S.hW S.hpe c.emb (.inl i) i).toDeg S.hW S.hpe 0).of_eq_fun
      fun θ => by rw [KAM.Torus.tangentMat_apply, KAM.Torus.sumVec_apply, Sum.elim_inl]; rfl
  exact ⟨fun x => checkRealLowerBound_sound S.hW _ hM hlow x, by exact_mod_cast hm⟩

/-- **Soundness of the real-torus diagonal check.** -/
theorem checkClockGraphReal_sound (hs : checkStatic c = true) {i : Fin n} {mono : ℚ}
    (h : checkClockGraphReal c i mono = true) :
    ClockMono c i mono ∧ (c.params.disp : ℝ) < mono * c.params.rhoInf := by
  have S := checkStatic_sound hs
  simp only [checkClockGraphReal, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hm, hb⟩ := h
  have hE : (angleDerivModel n c.emb c.weight i.val i.val).Encloses n c.weight.rho
      fun θ => fderiv ℂ (c.emb.angleAt n i.val) θ (Pi.single i 1) :=
    (CertModel.Encloses.ofDeriv S.hW i _ (realCompPoly n c.emb.angle[i.val]?)).of_eq_fun
      fun θ => (fderiv_realComp_apply n _ _ θ _).symm
  refine ⟨fun x => ?_, by exact_mod_cast hm⟩
  have hn := KAM.CertificateSharp.Hybrid.CertModel.norm_le_supBound_real
    (CertWeight.rho_pos S.hW) hE x
  have hle : ‖fderiv ℂ (c.emb.angleAt n i.val) (realInclusion n x) (Pi.single i 1)‖ ≤
      1 - (mono : ℝ) := by
    refine hn.trans ((LawfulCertArith.ble_sound _ _ hb).trans ?_)
    have := LawfulCertArith.ofRatDown_le (α := α) (1 - mono)
    push_cast at this
    exact this
  have e : (fderiv ℂ c.K (realInclusion n x) (Pi.single i 1)).1 i =
      1 + fderiv ℂ (c.emb.angleAt n i.val) (realInclusion n x) (Pi.single i 1) := by
    rw [TorusCertificate.K, fderiv_eval_fst_apply]
    simp
  rw [e, Complex.add_re, Complex.one_re]
  have := (Complex.abs_re_le_norm
    (fderiv ℂ (c.emb.angleAt n i.val) (realInclusion n x) (Pi.single i 1))).trans hle
  linarith [(abs_le.1 this).1]

/-- **The clock-triangular graph adapter, fully checked**: a certified torus (any certifier) with
passing `checkStatic`, `checkHamBounds`, `checkClock c i a` and one of the diagonal checks
(`checkClockGraphReal c i mono`, or the SOS `checkClockGraph c i mono mono₀ sos`), and a
Diophantine `ω*`, has an exact torus with `s∞ ω*_l = a` (`l ≠ i`) whose real restriction is a real
model torus of `realHam c.H` and a clock-triangular analytic graph over the angles with free
diagonal `∂_i A_i ≥ mono - disp/ρ∞ > 0`. -/
theorem _root_.KAM.Certificate.CertifiedTorus.exists_clockGraph_of_checks
    {ωstar : Fin n → ℝ} (hT : CertifiedTorus c ωstar) (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) {i : Fin n} {a : ℚ} (hclk : checkClock c i a = true)
    {γ τ : ℝ} (hγ : 0 < γ) (hdio : IsDiophantine γ τ ωstar) {mono : ℚ}
    (hg : checkClockGraphReal c i mono = true ∨
      ∃ (mono₀ : ℚ) (sos : CertPoly α), checkClockGraph c i mono mono₀ sos = true) :
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
      CertifiedTorusAt c ωstar Kinf sinf ∧
      IsRealModelTorus (realHam c.H) (sinf • ωstar) c.params.E0 (realRestriction Kinf) ∧
      (∀ l, l ≠ i → sinf * ωstar l = a) ∧ ∃ cc : Fin n → ℝ,
      IsClockAngleGraph (realRestriction Kinf) i cc
        ((mono : ℝ) - (c.params.disp : ℝ) / c.params.rhoInf) := by
  have hH := isRealHolo_of_checkHamBounds hs hh
  obtain ⟨ha, hclock⟩ := checkClock_sound hH hclk
  have hg' : ClockMono c i mono ∧ (c.params.disp : ℝ) < mono * c.params.rhoInf := by
    rcases hg with hg | ⟨_, _, hg⟩
    · exact checkClockGraphReal_sound hs hg
    · exact checkClockGraph_sound hs hg
  exact hT.exists_clockGraph hs hH ha hclock hγ hdio hg'.1 hg'.2

end KAM.Application

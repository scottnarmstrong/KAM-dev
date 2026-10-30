/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.StepBQ
public import KAM.Sharp2.RouteB.Sched
public import KAM.Certificate.Sound.Ham

/-!
# Exact rational mirror of a run of route B

Every number of a run of route B (`KAM.Sharp2.RouteB.NumB`) is a rational at rational data, for
`τ ∈ ℕ`: the schedule `δ_s = δ₀ a^{-s}`, `r_s`, the full bites `min r_s 1`, the Rüssmann-Cauchy
factor `(τ+1)^{τ+1}/τ^τ`, and every power. So the test is the Lean definition over `ℚ`.

* `NumBQ`, with `NumBQ.toNum n : NumB n`; the lists `c`, `c'`, `cbar` are read with the tail
  constants as defaults, so that `NumB.Wf.sd` (positivity at every index) is checkable;
* `NumBQ.inp n s : StepBQ`, with `toB_inp : (Q.inp n s).toB = (Q.toNum n).inp s`;
* `NumBQ.x`, `rate`, `wt`, `ballSum`, `freqSum`: the mirrors of `NumB.xS`, `rate`, `wt`,
  `ballSum`, `freqSum` (`cast_*`);
* `NumBQ.okB`: the Boolean form of `routeBOk`, and `okB_sound`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Sharp2 KAM.Sharp2.RouteB

/-- The rational numbers of a run of route B, with a natural exponent `τ`. -/
structure NumBQ where
  τ : ℕ
  ρ : ℚ
  ρinf : ℚ
  γb : ℚ
  M1 : ℚ
  M2 : ℚ
  cTh : ℚ
  cDTh : ℚ
  sK : ℚ
  sLt : ℚ
  sB : ℚ
  sN : ℚ
  sNt : ℚ
  sT : ℚ
  ts : ℚ
  bF : ℚ
  θ : ℚ
  θξ : ℚ
  θΩ : ℚ
  q : ℚ
  θN : ℚ
  θω : ℚ
  a : ℚ
  ybar : ℚ
  kp : ℕ
  c : List ℚ
  c' : List ℚ
  cbar : List ℚ
  ctail : ℚ
  cbtail : ℚ
  selfcons : Bool
  lam0 : ℚ
  lamW0 : ℚ
  ePer0 : ℚ
  iso : Bool
  Θ : ℚ
  y0 : ℚ
  Mh2 : ℚ

namespace NumBQ

variable (Q : NumBQ) (n : ℕ)

/-- The real numbers of the run, in dimension `n`. -/
noncomputable def toNum : NumB n :=
  { τ := Q.τ, ρ := Q.ρ, ρinf := Q.ρinf, γb := Q.γb, M1 := Q.M1, M2 := Q.M2, cTh := Q.cTh,
    cDTh := Q.cDTh, sK := Q.sK, sLt := Q.sLt, sB := Q.sB, sN := Q.sN, sNt := Q.sNt, sT := Q.sT,
    ts := Q.ts, bF := Q.bF, θ := Q.θ, θξ := Q.θξ, θΩ := Q.θΩ, q := Q.q, θN := Q.θN,
    θω := Q.θω, a := Q.a, ybar := Q.ybar, kp := Q.kp,
    c := fun s => ((Q.c.getD s Q.ctail : ℚ) : ℝ), c' := fun s => ((Q.c'.getD s Q.ctail : ℚ) : ℝ),
    cbar := fun s => ((Q.cbar.getD s Q.cbtail : ℚ) : ℝ), ctail := Q.ctail, cbtail := Q.cbtail,
    selfcons := Q.selfcons, lam0 := Q.lam0, lamW0 := Q.lamW0, ePer0 := Q.ePer0, iso := Q.iso,
    Θ := Q.Θ, y0 := Q.y0, Mh2 := Q.Mh2 }

/-- `δ₀ = min {1, (ρ - ρ∞)(a - 1)/(3a)}`. -/
def δ0 : ℚ := min 1 ((Q.ρ - Q.ρinf) * (Q.a - 1) / (3 * Q.a))
/-- `δ_s = δ₀ a^{-s}`. -/
def δ (s : ℕ) : ℚ := Q.δ0 / Q.a ^ s
/-- `r_s = ρ - 3δ₀(1 - a^{-s})/(1 - a^{-1})`. -/
def r (s : ℕ) : ℚ := Q.ρ - 3 * Q.δ0 * (1 - Q.a⁻¹ ^ s) / (1 - Q.a⁻¹)
/-- The full bite `min r_s 1`. -/
def bfull (s : ℕ) : ℚ := min (Q.r s) 1
/-- The split `τ/(τ+1)`. -/
def split : ℚ := (Q.τ : ℚ) / ((Q.τ : ℚ) + 1)
/-- The Rüssmann-Cauchy factor `(τ+1)^{τ+1}/τ^τ`. -/
def rcf : ℚ := ((Q.τ : ℚ) + 1) ^ (Q.τ + 1) / (Q.τ : ℚ) ^ Q.τ

/-- The inputs of stage `s` (the tail record from `kp` on). -/
def inp (s : ℕ) : StepBQ :=
  { n := n, κ := Q.τ, M1 := Q.M1, M2 := Q.M2, cTh := Q.cTh, cDTh := Q.cDTh, sK := Q.sK,
    sLt := Q.sLt, sB := Q.sB, sN := Q.sN, sNt := Q.sNt, sT := Q.sT, ts := Q.ts, bF := Q.bF,
    c := if s < Q.kp then Q.c.getD s Q.ctail else Q.ctail,
    c1 := (if s < Q.kp then Q.c'.getD s Q.ctail else Q.ctail) * Q.rcf,
    cavg := if s < Q.kp then Q.cbar.getD s Q.cbtail * (Q.δ s / Q.bfull s) ^ Q.τ
      else Q.cbtail * (Q.δ Q.kp / Q.bfull Q.kp) ^ Q.τ,
    θ := Q.θ, θξ := Q.θξ, θΩ := Q.θΩ, q := Q.q, θN := Q.θN, θω := Q.θω, a := Q.a,
    lam := if s = 0 then Q.lam0 else 1, γb := Q.γb, δ := Q.δ (min s Q.kp),
    selfcons := Q.selfcons, stage0 := decide (s = 0), ePer := Q.ePer0, iso := Q.iso, Θ := Q.Θ,
    y0 := Q.y0, Mh2 := Q.Mh2, lamW := if s = 0 then Q.lamW0 else 1 }

/-- `Q_s`. -/
def Qs (s : ℕ) : ℚ := (Q.inp n s).sQ

/-- The normalized errors: `x_{s+1} = a^{τ+1} Q_s x_s²`. -/
def x (Xs : ℚ) : ℕ → ℚ
  | 0 => Xs
  | s + 1 => Q.a ^ (Q.τ + 1) * Q.Qs n s * x Xs s ^ 2

/-- The seven cap rates. -/
def rate (s : ℕ) : Fin 7 → ℚ :=
  ![n * (Q.inp n s).sCDK, 2 * n * (Q.inp n s).sCDK, (Q.inp n s).sCBb, (Q.inp n s).sCNb,
    (Q.inp n s).sCNbT, (Q.inp n s).sCab, (Q.inp n s).sCnu]

/-- Their weights. -/
def wt (s : ℕ) : Fin 7 → ℚ := ![1, 1, 1, 1, 1, 1, Q.γb * Q.δ (min s Q.kp) ^ (Q.τ + 1)]

/-- The ball sum (J4). -/
def ballSum (Xs : ℚ) : ℚ :=
  KAM.Certificate.sumRangeQ Q.kp (fun s => (Q.inp n s).sCDK * Q.δ s * Q.x n Xs s) +
    (Q.inp n Q.kp).sCDK * Q.δ Q.kp * Q.x n Xs Q.kp / (1 - Q.ybar)

/-- The frequency sum. -/
def freqSum (Xs : ℚ) : ℚ :=
  KAM.Certificate.sumRangeQ Q.kp
      (fun s => (Q.inp n s).sCnu * (Q.γb * Q.δ s ^ (Q.τ + 1)) * Q.x n Xs s) +
    (Q.inp n Q.kp).sCnu * (Q.γb * Q.δ Q.kp ^ (Q.τ + 1)) * Q.x n Xs Q.kp / (1 - Q.ybar)

/-- `routeBOk` over `ℚ`. -/
def okB (σ m₀ : Fin 7 → ℚ) (β Xs : ℚ) : Bool :=
  decide (0 ≤ Xs) &&
    (List.range Q.kp).all (fun s => (Q.inp n s).condB (Q.x n Xs s)) &&
    (Q.inp n Q.kp).condB (Q.x n Xs Q.kp) &&
    decide (Q.a ^ (Q.τ + 1) * Q.Qs n Q.kp * Q.x n Xs Q.kp ≤ Q.ybar) &&
    (List.finRange 7).all (fun i => decide (m₀ i +
      KAM.Certificate.sumRangeQ Q.kp (fun s => Q.rate n s i * Q.wt s i * Q.x n Xs s) +
      Q.rate n Q.kp i * Q.wt Q.kp i * Q.x n Xs Q.kp / (1 - Q.ybar) ≤ σ i)) &&
    decide (Q.ballSum n Xs < β)

/-! ### The casts -/

variable {Q n}

theorem cast_δ0 : (Q.toNum n).δ0 = (Q.δ0 : ℝ) := by
  simp only [NumB.δ0, bite0R, δ0, toNum]; push_cast; rfl

theorem cast_δ (s : ℕ) : (Q.toNum n).δ s = (Q.δ s : ℝ) := by
  simp only [NumB.δ, biteSR, bite0R, δ, δ0, toNum]; push_cast; rfl

theorem cast_r (s : ℕ) : (Q.toNum n).r s = (Q.r s : ℝ) := by
  simp only [NumB.r, stripSR, bite0R, r, δ0, toNum]; push_cast; rfl

theorem cast_bfull (s : ℕ) : (Q.toNum n).bfull s = (Q.bfull s : ℝ) := by
  simp only [NumB.bfull, bfull, cast_r]; push_cast; rfl

theorem cast_τ : (Q.toNum n).τ = ((Q.τ : ℕ) : ℝ) := rfl

theorem cast_split : (Q.toNum n).split = (Q.split : ℝ) := by
  simp only [NumB.split, split, toNum]; push_cast; rfl

theorem cast_rcf : (Q.toNum n).rcf = (Q.rcf : ℝ) := by
  have e : ((Q.τ : ℝ) + 1) = ((Q.τ + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [NumB.rcf, rcf, toNum]
  rw [e, Real.rpow_natCast, Real.rpow_natCast]
  push_cast; rfl

theorem toB_inp (s : ℕ) : (Q.inp n s).toB = (Q.toNum n).inp s := by
  simp only [StepBQ.toB, inp, NumB.inp, cast_rcf, cast_δ, cast_bfull, cast_τ]
  simp only [toNum, Real.rpow_natCast]
  push_cast [apply_ite (Rat.cast : ℚ → ℝ)]
  rfl

theorem consts_eq (s : ℕ) : stepConstsB ((Q.toNum n).inp s) = stepConstsB (Q.inp n s).toB := by
  rw [toB_inp]

theorem cast_Qs (s : ℕ) : (Q.toNum n).Qs s = (Q.Qs n s : ℝ) := by
  show (stepConstsB ((Q.toNum n).inp s)).Q = _
  rw [consts_eq]
  exact StepBQ.cast_sQ

theorem cast_x (Xs : ℚ) (s : ℕ) : (Q.toNum n).xS Xs s = (Q.x n Xs s : ℝ) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    show (Q.toNum n).a ^ ((Q.toNum n).τ + 1) * (Q.toNum n).Qs s * (Q.toNum n).xS Xs s ^ 2 = _
    have e : ((Q.τ : ℝ) + 1) = ((Q.τ + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [ih, cast_Qs, cast_τ, e, Real.rpow_natCast]
    simp only [x, toNum]
    push_cast
    rfl

theorem cast_CDK (s : ℕ) : (stepConstsB ((Q.toNum n).inp s)).CDK = ((Q.inp n s).sCDK : ℝ) := by
  rw [consts_eq]; exact StepBQ.cast_sCDK

theorem cast_Cnu (s : ℕ) : (stepConstsB ((Q.toNum n).inp s)).Cnu = ((Q.inp n s).sCnu : ℝ) := by
  rw [consts_eq]; exact StepBQ.cast_sCnu

theorem cast_rate (s : ℕ) (i : Fin 7) : (Q.toNum n).rate s i = (Q.rate n s i : ℝ) := by
  have e1 : (stepConstsB ((Q.toNum n).inp s)).CBb = ((Q.inp n s).sCBb : ℝ) := by
    rw [consts_eq]; exact StepBQ.cast_sCBb
  have e2 : (stepConstsB ((Q.toNum n).inp s)).CNb = ((Q.inp n s).sCNb : ℝ) := by
    rw [consts_eq]; exact StepBQ.cast_sCNb
  have e3 : (stepConstsB ((Q.toNum n).inp s)).CNbT = ((Q.inp n s).sCNbT : ℝ) := by
    rw [consts_eq]; exact StepBQ.cast_sCNbT
  have e4 : (stepConstsB ((Q.toNum n).inp s)).Cab = ((Q.inp n s).sCab : ℝ) := by
    rw [consts_eq]; exact StepBQ.cast_sCab
  fin_cases i <;> simp [NumB.rate, rate, cast_CDK, cast_Cnu, e1, e2, e3, e4]

theorem cast_wt (s : ℕ) (i : Fin 7) : (Q.toNum n).wt s i = (Q.wt s i : ℝ) := by
  have e : ((Q.τ : ℝ) + 1) = ((Q.τ + 1 : ℕ) : ℝ) := by push_cast; ring
  have h6 : (Q.toNum n).γb * (Q.toNum n).δ (min s (Q.toNum n).kp) ^ ((Q.toNum n).τ + 1) =
      ((Q.γb * Q.δ (min s Q.kp) ^ (Q.τ + 1) : ℚ) : ℝ) := by
    rw [cast_δ, cast_τ, e, Real.rpow_natCast]; push_cast; rfl
  fin_cases i <;> simp [NumB.wt, wt, h6]

theorem cast_ballSum (Xs : ℚ) : (Q.toNum n).ballSum Xs = (Q.ballSum n Xs : ℝ) := by
  simp only [NumB.ballSum, ballSum, KAM.Certificate.sumRangeQ_eq, cast_CDK, cast_δ, cast_x]
  push_cast
  rfl

theorem cast_freqSum (Xs : ℚ) : (Q.toNum n).freqSum Xs = (Q.freqSum n Xs : ℝ) := by
  have e : ((Q.τ : ℝ) + 1) = ((Q.τ + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [NumB.freqSum, freqSum, KAM.Certificate.sumRangeQ_eq, cast_Cnu, cast_δ, cast_x,
    cast_τ, e, Real.rpow_natCast]
  push_cast
  rfl

/-- **The test `okB` gives `routeBOk`.** -/
theorem okB_sound (hN : (Q.toNum n).Wf) {σ m₀ : Fin 7 → ℚ} {β Xs : ℚ}
    (h : Q.okB n σ m₀ β Xs = true) :
    routeBOk (Q.toNum n) (fun i => (σ i : ℝ)) (fun i => (m₀ i : ℝ)) β Xs := by
  simp only [okB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.mem_finRange, true_implies] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have cond : ∀ s, (Q.inp n s).condB (Q.x n Xs s) = true →
      stepCondB ((Q.toNum n).inp s) ((Q.toNum n).xS Xs s) := fun s hs => by
    rw [cast_x, ← toB_inp]
    exact StepBQ.condB_sound hs
  have hkp : (Q.toNum n).kp = Q.kp := rfl
  refine ⟨by exact_mod_cast h1, fun s hs => cond s (h2 s hs), fun X hX hle => ?_, ?_,
    fun i => ?_, ?_⟩
  · exact stepCondB_anti (hN.inp_ok _) hX hle (cond _ h3)
  · have e : ((Q.τ : ℝ) + 1) = ((Q.τ + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [cast_Qs, cast_x, hkp]
    show (Q.a : ℝ) ^ ((Q.τ : ℝ) + 1) * _ * _ ≤ (Q.ybar : ℝ)
    rw [e, Real.rpow_natCast]
    exact_mod_cast h4
  · have := (Rat.cast_le (K := ℝ)).mpr (h5 i)
    push_cast [KAM.Certificate.sumRangeQ_eq] at this
    have hy : (Q.toNum n).ybar = (Q.ybar : ℝ) := rfl
    simp only [cast_rate, cast_wt, cast_x, hkp, hy]
    exact this
  · rw [cast_ballSum]; exact_mod_cast h6

end NumBQ

end KAM.CertificateSharp.V2

end

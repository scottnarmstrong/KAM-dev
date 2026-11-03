/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusStep.Smoke

/-!
# A single Bool checker for one-generator torus certificates (track B, B4-TCHECK)

`TorusStepCert n` is pure data (Fourier–Taylor polynomials, a Lie-sum length, rational radii and
bounds). `checkTorusStep` is a total computable `Bool` conjunction of every non-binder premise of
`torusStep_confinement`, evaluated in exact `ℚ`; `checkTorusStep_sound` extracts the premises and
applies B4-TSTEP. Lists are read with `getD i 0`; the fact `π ≤ πub` is replaced by the rational
check `ftPiUB ≤ πub`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

/-- Certificate data for one torus generator `χ` (no `Prop` fields; all numbers are rational). -/
structure TorusStepCert (n : ℕ) where
  /-- the physical Hamiltonian -/
  H : FTPoly
  /-- the generator -/
  χ : FTPoly
  /-- the normal form, in the actions only -/
  Nact : FTPoly
  /-- the remainder -/
  P : FTPoly
  /-- the Lie-sum length -/
  L : ℕ
  /-- strip width of the chart domain -/
  σ : ℚ
  /-- polydisc radius of the chart domain -/
  ρ : ℚ
  /-- small-field action scale -/
  σ' : ℚ
  /-- small-field angle scale -/
  ρ' : ℚ
  /-- Cauchy width -/
  δc : ℚ
  /-- smallness of the generator field -/
  ε : ℚ
  /-- slack in the action ball -/
  εb : ℚ
  /-- time horizon -/
  T : ℚ
  /-- rational upper bound for `π` -/
  πub : ℚ
  /-- strip constant bounding `1/(1 - 2 πub σ)` -/
  lam : ℚ
  /-- initial action bounds -/
  a : List ℚ
  /-- action-ball bounds -/
  b : List ℚ
  /-- drift rates -/
  η : List ℚ
  /-- coordinate radii of the oscillator ball -/
  r : List ℚ

/-- The majorant `B = ftSupBound (ad_χ^L H) πub λ ρ` of the certificate. -/
def TorusStepCert.torusBmaj {n : ℕ} (c : TorusStepCert n) : ℚ :=
  ftSupBound (ftAdPow c.χ c.L c.H) c.πub c.lam (List.replicate n c.ρ)

/-- The Bool checker: every non-binder premise of `torusStep_confinement`, in exact `ℚ`. -/
def checkTorusStep {n : ℕ} (c : TorusStepCert n) : Bool :=
  ftFitsCheck n c.H && (ftFitsCheck n c.χ && (ftFitsCheck n c.P && (ftActOnly c.Nact &&
  (decide (1 ≤ c.L) && (ftEqCheck (ftLieSum c.χ c.H c.L) (ftAdd c.Nact c.P) &&
  (decide (0 < c.σ') && (decide (0 < c.ρ') && (decide (0 < c.δc) && (decide (0 ≤ c.ε) &&
  (decide (c.ε ≤ 1 / 2) && (decide (ftPiUB ≤ c.πub) && (decide (2 * c.πub * c.σ < 1) &&
  (decide (1 / (1 - 2 * c.πub * c.σ) ≤ c.lam) && (decide (0 < c.εb) && (decide (0 ≤ c.T) &&
  (decide (c.σ' < c.σ) && (decide (c.δc + c.σ' / 2 < c.σ) &&
  (List.range n).all fun i =>
    decide (ftSupBound (ftDJ i c.χ) c.πub c.lam (List.replicate n c.ρ) ≤ c.ε * c.σ')
    && (decide (ftSupBound (ftDφ i c.χ) c.πub c.lam (List.replicate n c.ρ) ≤ c.ε * c.ρ')
    && (decide (c.b.getD i 0 ≤ c.r.getD i 0)
    && (decide (c.b.getD i 0 + c.εb + c.ρ' ≤ c.ρ)
    && (decide (c.r.getD i 0 + c.δc + c.ρ' / 2 < c.ρ)
    && (decide (0 ≤ c.η.getD i 0)
    && (decide (ftAngleDriftBound c.P i c.πub c.b + c.torusBmaj / ((c.L.factorial : ℚ) * c.δc) ≤
      c.η.getD i 0)
    && decide (c.a.getD i 0 + c.T * c.η.getD i 0 < c.b.getD i 0))))))))))))))))))))))))

theorem checkTorusStep_sound {n : ℕ} (c : TorusStepCert n) (hc : checkTorusStep c = true)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j : Fin n, |w₀.2 j| ≤ (c.a.getD j 0 : ℝ)) :
    ∃ T₁ : ℝ, (c.T : ℝ) < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      z 0 = torusChart c.χ (c.σ : ℝ) (c.ρ : ℝ) w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR c.H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = torusChart c.χ (c.σ : ℝ) (c.ρ : ℝ) w₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR c.H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ (c.T : ℝ) →
        torusChart c.χ (c.σ : ℝ) (c.ρ : ℝ) (torusChartInv c.χ (c.σ : ℝ) (c.ρ : ℝ) (z t)) = z t ∧
        ∀ j : Fin n,
          |(torusChartInv c.χ (c.σ : ℝ) (c.ρ : ℝ) (z t)).2 j - w₀.2 j| ≤
              (c.η.getD j 0 : ℝ) * |t| ∧
          |(torusChartInv c.χ (c.σ : ℝ) (c.ρ : ℝ) (z t)).2 j| ≤
            (c.a.getD j 0 : ℝ) + (c.η.getD j 0 : ℝ) * (c.T : ℝ) := by
  unfold checkTorusStep at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨hH, hχ, hP, hA, hL, hid, hσ', hρ', hδc, hε0, hε, hπ, hx, hlam, hεb, hT, hσσ', hσc,
    hall⟩ := hc
  have hρl : ∀ i : Fin n, (((List.replicate n c.ρ).getD i 0 : ℚ) : ℝ) = ((c.ρ : ℚ) : ℝ) := by
    intro i; simp [List.getD_eq_getElem?_getD, i.2]
  have hK : ∀ i : Fin n, _ := fun i => hall i i.2
  have hπR : Real.pi ≤ ((c.πub : ℚ) : ℝ) :=
    pi_le_ftPiUB.trans (Rat.cast_le.2 hπ)
  refine torusStep_confinement (ftFits_of_check hH) (ftFits_of_check hχ) (ftFits_of_check hP)
    hA hL hid (σ := (c.σ : ℝ)) (ρ := (c.ρ : ℝ)) (σ' := (c.σ' : ℝ)) (ρ' := (c.ρ' : ℝ))
    (δc := (c.δc : ℝ)) (ε := (c.ε : ℝ)) (by exact_mod_cast hσ') (by exact_mod_cast hρ')
    (by exact_mod_cast hδc) (by exact_mod_cast hε0)
    (by have := (Rat.cast_le (K := ℝ)).2 hε; push_cast at this; exact this) hπR
    (by exact_mod_cast hx)
    (by have := (Rat.cast_le (K := ℝ)).2 hlam; push_cast at this; exact this)
    (List.replicate n c.ρ) hρl
    (fun i => by exact_mod_cast (hK i).1) (fun i => by exact_mod_cast (hK i).2.1)
    (fun j => (c.a.getD j 0 : ℝ)) (fun j => (c.b.getD j 0 : ℝ)) (fun j => (c.η.getD j 0 : ℝ))
    (c.εb : ℝ) (c.T : ℝ) (by exact_mod_cast hεb) (by exact_mod_cast hT) c.b (fun i => rfl)
    (fun i => (c.r.getD i 0 : ℝ))
    (fun i => by exact_mod_cast (hK i).2.2.1) (by exact_mod_cast hσσ')
    (fun i => by exact_mod_cast (hK i).2.2.2.1) (by exact_mod_cast hσc)
    (fun i => by exact_mod_cast (hK i).2.2.2.2.1) (fun i => by exact_mod_cast (hK i).2.2.2.2.2.1)
    (fun j => by
      have := (Rat.cast_le (K := ℝ)).2 (hK j).2.2.2.2.2.2.1
      simpa [TorusStepCert.torusBmaj] using this)
    (fun j => by exact_mod_cast (hK j).2.2.2.2.2.2.2) w₀ hw₀

/-! ### Smoke test: the integrable certificate of B4-TSTEP -/

/-- `n = 1`, `H = Nact = J₀²/2`, `χ = 0`, `P = 0`, `L = 1`. -/
def torusSmokeCert : TorusStepCert 1 where
  H := torusSmokeH
  χ := []
  Nact := torusSmokeH
  P := []
  L := 1
  σ := 1 / 10
  ρ := 5
  σ' := 1 / 20
  ρ' := 1
  δc := 1 / 20
  ε := 0
  εb := 1
  T := 1
  πub := ftPiUB
  lam := 3
  a := [0]
  b := [1]
  η := [0]
  r := [2]

theorem torusSmokeCert_check : checkTorusStep torusSmokeCert = true := by decide +kernel

/-- The smoke certificate is accepted and yields the zero-drift confinement statement. -/
theorem torusSmokeCert_zeroDrift (w₀ : (Fin 1 → ℝ) × (Fin 1 → ℝ))
    (hw₀ : ∀ j, |w₀.2 j| ≤ 0) :
    ∃ z : ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ), ∀ t : ℝ, |t| ≤ 1 → ∀ j,
      |(torusChartInv ([] : FTPoly) (1 / 10 : ℝ) (5 : ℝ) (z t)).2 j - w₀.2 j| ≤ 0 := by
  obtain ⟨T₁, -, z, -, -, -, hb⟩ := checkTorusStep_sound torusSmokeCert torusSmokeCert_check w₀
    (fun j => by simpa [torusSmokeCert] using hw₀ j)
  refine ⟨z, fun t ht j => ?_⟩
  have := ((hb t (by simpa [torusSmokeCert] using ht)).2 j).1
  simpa [torusSmokeCert] using this

end KAM.EffectiveStability

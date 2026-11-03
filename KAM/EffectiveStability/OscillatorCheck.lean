/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorStep

/-!
# A single Bool checker for one-generator certificates (track B, B2-CHECK)

`OscStepCertK K n` is pure data (polynomials, a Lie-sum length, rational radii and bounds).
`checkOscStep` is a total computable `Bool` conjunction of every non-binder premise of
`oscillatorStep_confinement`, evaluated in exact `ℚ`; `checkOscStep_sound` extracts the premises
and applies B2-STEP. Lists are read with `getD i 0`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set CartPoly

variable {K : Type} [CertCoeff K]

/-- Certificate data for one generator `χ` (no `Prop` fields; all numbers are rational). -/
structure OscStepCertK (K : Type) (n : ℕ) where
  /-- the physical Hamiltonian -/
  H : CartPolyK K
  /-- the generator -/
  χ : CartPolyK K
  /-- the normal form, in the `q`-variables only -/
  Nact : CartPolyK K
  /-- the remainder -/
  P : CartPolyK K
  /-- the Lie-sum length -/
  L : ℕ
  /-- chart-domain polydisc radius -/
  ρ : ℚ
  /-- gauge width -/
  δ : ℚ
  /-- Cauchy width -/
  δc : ℚ
  /-- smallness of the generator field -/
  ε : ℚ
  /-- slack in the action ball -/
  εb : ℚ
  /-- time horizon -/
  T : ℚ
  /-- initial action bounds -/
  a : List ℚ
  /-- action-ball bounds -/
  b : List ℚ
  /-- drift rates -/
  η : List ℚ
  /-- coordinate radii of the oscillator ball -/
  r : List ℚ

/-- The `ℚ`-coefficient certificates (the original name). -/
abbrev OscStepCert (n : ℕ) := OscStepCertK ℚ n

/-- Boolean version of `CartFits`: all exponents past index `n` are zero. -/
def cartFitsB (n : ℕ) (P : CartPolyK K) : Bool :=
  P.all fun m => (m.a.drop n).all (· == 0) && (m.b.drop n).all (· == 0)

private theorem getD_zero_of_drop {l : List ℕ} {n : ℕ} (h : (l.drop n).all (· == 0) = true)
    {k : ℕ} (hk : n ≤ k) : l.getD k 0 = 0 := by
  by_cases hlen : k < l.length
  · have hm : l[k] ∈ l.drop n := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [List.mem_iff_getElem]
      exact ⟨j, by simp; omega, by simp⟩
    have := List.all_eq_true.1 h _ hm
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen] using this
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 hlen)]

omit [CertCoeff K] in
theorem cartFitsB_sound {n : ℕ} {P : CartPolyK K} (h : cartFitsB n P = true) : CartFits n P := by
  intro m hm k hk
  have := List.all_eq_true.1 h m hm
  simp only [Bool.and_eq_true] at this
  exact ⟨getD_zero_of_drop this.1 hk, getD_zero_of_drop this.2 hk⟩

/-- The majorant `B = cartSupBound (ad_χ^L H) ρ` of the certificate. -/
def OscStepCertK.Bmaj {n : ℕ} (c : OscStepCertK K n) : ℚ :=
  cartSupBound (cartAdPow c.χ c.L c.H) (List.replicate n c.ρ) (List.replicate n c.ρ)

/-- The Bool checker: every non-binder premise of `oscillatorStep_confinement`, in exact `ℚ`. -/
def checkOscStep {n : ℕ} (c : OscStepCertK K n) : Bool :=
  cartFitsB n c.H && cartFitsB n c.χ && cartFitsB n c.Nact && cartFitsB n c.P &&
  cartActOnly c.Nact && decide (1 ≤ c.L) &&
  cartEqCheck (cartLieSum c.χ c.H c.L) (cartAdd (cartActSubst c.Nact) c.P) &&
  decide (0 < c.δ) && decide (0 < c.δc) && decide (0 ≤ c.ε) && decide (c.ε ≤ 1 / 2) &&
  decide (0 < c.εb) && decide (0 ≤ c.T) &&
  (List.range n).all fun i =>
    decide (cartSupBound (cartDq i c.χ) (List.replicate n c.ρ) (List.replicate n c.ρ) ≤ c.ε * c.δ)
    && decide (cartSupBound (cartDp i c.χ) (List.replicate n c.ρ) (List.replicate n c.ρ) ≤
      c.ε * c.δ)
    && decide (0 ≤ c.r.getD i 0)
    && decide (2 * (c.b.getD i 0 + c.εb) ≤ c.r.getD i 0 ^ 2)
    && decide (c.r.getD i 0 + c.δ < c.ρ)
    && decide (c.r.getD i 0 + c.δc + c.δ / 2 < c.ρ)
    && decide (0 ≤ c.η.getD i 0)
    && decide (cartSupBound (cartBracket (cartAction i) c.P) c.r c.r ≤
      c.η.getD i 0 - 2 * c.r.getD i 0 * c.Bmaj / ((c.L.factorial : ℚ) * c.δc))
    && decide (c.a.getD i 0 + c.T * c.η.getD i 0 < c.b.getD i 0)

theorem checkOscStep_sound {n : ℕ} [Algebra K ℝ] [Algebra K ℂ]
    [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ]
    (c : OscStepCertK K n) (hc : checkOscStep c = true)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ))
    (hw₀ : ∀ j : Fin n, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ (c.a.getD j 0 : ℝ)) :
    ∃ T₁ : ℝ, (c.T : ℝ) < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      z 0 = stepChart c.χ (c.ρ : ℝ) w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval c.H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = stepChart c.χ (c.ρ : ℝ) w₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval c.H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ (c.T : ℝ) →
        stepChart c.χ (c.ρ : ℝ) (stepChartInv c.χ (c.ρ : ℝ) (z t)) = z t ∧
        ∀ j : Fin n,
          |KAM.Planetary.oscillatorAction (stepChartInv c.χ (c.ρ : ℝ) (z t)).2
              (stepChartInv c.χ (c.ρ : ℝ) (z t)).1 j -
            KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ (c.η.getD j 0 : ℝ) * |t| ∧
          KAM.Planetary.oscillatorAction (stepChartInv c.χ (c.ρ : ℝ) (z t)).2
            (stepChartInv c.χ (c.ρ : ℝ) (z t)).1 j ≤
              (c.a.getD j 0 : ℝ) + (c.η.getD j 0 : ℝ) * (c.T : ℝ) := by
  unfold checkOscStep at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hH, hχ⟩, hN⟩, hP⟩, hA⟩, hL⟩, hid⟩, hδ⟩, hδc⟩, hε0⟩, hε⟩, hεb⟩, hT⟩,
    hall⟩ := hc
  have hρl : ∀ i : Fin n, (((List.replicate n c.ρ).getD i 0 : ℚ) : ℝ) = ((c.ρ : ℚ) : ℝ) := by
    intro i; simp [List.getD_eq_getElem?_getD, i.2]
  have hK : ∀ i : Fin n, _ := fun i => hall i i.2
  have hq := fun i : Fin n => (hK i).1.1.1.1.1.1.1.1
  have hp := fun i : Fin n => (hK i).1.1.1.1.1.1.1.2
  have hr0 := fun i : Fin n => (hK i).1.1.1.1.1.1.2
  have hd1 := fun i : Fin n => (hK i).1.1.1.1.1.2
  have hd2 := fun i : Fin n => (hK i).1.1.1.1.2
  have hd3 := fun i : Fin n => (hK i).1.1.1.2
  have hη := fun i : Fin n => (hK i).1.1.2
  have hdr := fun i : Fin n => (hK i).1.2
  have hmg := fun i : Fin n => (hK i).2
  exact oscillatorStep_confinement (cartFitsB_sound hH) (cartFitsB_sound hχ)
    (cartFitsB_sound hN) (cartFitsB_sound hP) hA hL hid (ρ := (c.ρ : ℝ)) (δ := (c.δ : ℝ))
    (δc := (c.δc : ℝ)) (ε := (c.ε : ℝ)) (by exact_mod_cast hδ) (by exact_mod_cast hδc)
    (by exact_mod_cast hε0)
    (by have := (Rat.cast_le (K := ℝ)).2 hε; push_cast at this; exact this)
    (List.replicate n c.ρ) hρl
    (fun i => by exact_mod_cast (hq i)) (fun i => by exact_mod_cast (hp i))
    (fun j => (c.a.getD j 0 : ℝ)) (fun j => (c.b.getD j 0 : ℝ)) (fun j => (c.η.getD j 0 : ℝ))
    (c.εb : ℝ) (c.T : ℝ) (by exact_mod_cast hεb) (by exact_mod_cast hT) c.r
    (fun i => (c.r.getD i 0 : ℝ)) (fun i => rfl)
    (fun i => by exact_mod_cast hr0 i) (fun i => by exact_mod_cast hd1 i)
    (fun i => by exact_mod_cast hd2 i) (fun i => by exact_mod_cast hd3 i)
    (fun i => by exact_mod_cast hη i)
    (fun j => by
      have := hdr j
      have h2 : ((cartSupBound (cartBracket (cartAction j) c.P) c.r c.r : ℚ) : ℝ) ≤
          (((c.η.getD j 0 - 2 * c.r.getD j 0 * c.Bmaj / ((c.L.factorial : ℚ) * c.δc) : ℚ)) : ℝ) :=
        Rat.cast_le.2 this
      simpa [OscStepCertK.Bmaj] using h2)
    (fun j => by exact_mod_cast hmg j) w₀ hw₀

/-! ### Smoke test: the harmonic oscillator certificate of B2-STEP -/

/-- `n = 1`, `H = I₀`, `χ = 0`, `Nact = q₀`, `P = 0`, `L = 1`. -/
def harmonicCert : OscStepCert 1 where
  H := cartAction 0
  χ := []
  Nact := cartQVar 0
  P := []
  L := 1
  ρ := 5
  δ := 1
  δc := 1
  ε := 0
  εb := 1
  T := 1
  a := [0]
  b := [1]
  η := [0]
  r := [2]

theorem harmonicCert_check : checkOscStep harmonicCert = true := by decide +kernel

/-- The harmonic certificate is accepted and yields the zero-drift confinement statement. -/
theorem harmonicCert_zeroDrift (w₀ : (Fin 1 → ℝ) × (Fin 1 → ℝ))
    (hw₀ : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ 0) :
    ∃ z : ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ), ∀ t : ℝ, |t| ≤ 1 → ∀ j,
      |KAM.Planetary.oscillatorAction (stepChartInv ([] : CartPoly) (5 : ℝ) (z t)).2
          (stepChartInv ([] : CartPoly) (5 : ℝ) (z t)).1 j -
        KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ 0 := by
  obtain ⟨T₁, -, z, -, -, -, hb⟩ := checkOscStep_sound harmonicCert harmonicCert_check w₀
    (fun j => by simpa [harmonicCert] using hw₀ j)
  refine ⟨z, fun t ht j => ?_⟩
  have := ((hb t (by simpa [harmonicCert] using ht)).2 j).1
  simpa [harmonicCert] using this

end KAM.EffectiveStability

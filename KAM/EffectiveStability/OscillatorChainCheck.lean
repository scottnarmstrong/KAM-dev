/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorChain
public import KAM.EffectiveStability.OscillatorCheck

/-!
# A single Bool checker for `m`-generator certificates (track B, B2-CHECKCHAIN)

`OscChainCertK K n` is pure data (polynomials, the list of `OscStepK K`s, rational widths and
bounds).
`checkOscChain` is a total computable `Bool` conjunction of every non-binder premise of
`oscillatorChain_confinement`, evaluated in exact `ℚ`; `checkOscChain_sound` extracts the premises
and applies B2-MULTI. Lists are read with `getD i 0`; ranges `i < n` are `List.range n`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set CartPoly

variable {K : Type} [CertCoeff K]

/-- Certificate data for a chain of generators (no `Prop` fields; all numbers are rational). -/
structure OscChainCertK (K : Type) (n : ℕ) where
  /-- the physical Hamiltonian -/
  H : CartPolyK K
  /-- the normal form, in the `q`-variables only -/
  Nact : CartPolyK K
  /-- the remainder -/
  P : CartPolyK K
  /-- the normalization steps, outermost first -/
  steps : List (OscStepK K)
  /-- Cauchy width -/
  δc : ℚ
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
abbrev OscChainCert (n : ℕ) := OscChainCertK ℚ n

/-- Boolean version of `OscStepOK`. -/
def oscStepOKB (n : ℕ) (s : OscStepK K) : Bool :=
  decide (0 < s.δ) && decide (0 ≤ s.ε) && decide (s.ε ≤ 1 / 2) && decide (1 ≤ s.order) &&
  cartFitsB n s.gen && cartFitsB n s.out &&
  (List.range n).all fun i =>
    decide (cartSupBound (cartDq i s.gen) (List.replicate n s.ρ) (List.replicate n s.ρ) ≤
      s.ε * s.δ) &&
    decide (cartSupBound (cartDp i s.gen) (List.replicate n s.ρ) (List.replicate n s.ρ) ≤
      s.ε * s.δ)

theorem oscStepOKB_sound {n : ℕ} {s : OscStepK K} (h : oscStepOKB n s = true) : OscStepOK n s := by
  unfold oscStepOKB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, cartFitsB_sound h5, cartFitsB_sound h6,
    fun i => (h7 i i.2).1, fun i => (h7 i i.2).2⟩

/-- Boolean version of `OscChainOK` (using the `cartEqCheck` disjunct of `OscLieOK`). -/
def oscChainOKB (n : ℕ) (Nact P : CartPolyK K) : List (OscStepK K) → CartPolyK K → Bool
  | [], Q => cartEqCheck Q (cartAdd (cartActSubst Nact) P)
  | s :: l, Q => oscStepOKB n s && cartEqCheck (cartLieSum s.gen Q s.order) s.out &&
      oscChainOKB n Nact P l s.out

theorem oscChainOKB_sound {n : ℕ} {Nact P : CartPolyK K} :
    ∀ (l : List (OscStepK K)) (Q : CartPolyK K), oscChainOKB n Nact P l Q = true →
      OscChainOK n Nact P l Q
  | [], _, h => h
  | s :: l, Q, h => by
    simp only [oscChainOKB, Bool.and_eq_true] at h
    exact ⟨oscStepOKB_sound h.1.1, Or.inr h.1.2, oscChainOKB_sound l _ h.2⟩

/-- Boolean version of `OscDomOK`, with rational radii `r` read by `getD`. -/
def oscDomOKB (n : ℕ) (r : List ℚ) (δc : ℚ) : List (OscStepK K) → Bool
  | [] => true
  | s :: l => ((List.range n).all fun i =>
      decide (r.getD i 0 + oscTail l + s.δ < s.ρ) &&
      decide (r.getD i 0 + δc + oscTail l + s.δ / 2 < s.ρ)) && oscDomOKB n r δc l

omit [CertCoeff K] in
theorem oscDomOKB_sound {n : ℕ} {r : List ℚ} {δc : ℚ} :
    ∀ l : List (OscStepK K), oscDomOKB n r δc l = true →
      OscDomOK n (fun i : Fin n => ((r.getD i 0 : ℚ) : ℝ)) (δc : ℝ) l
  | [], _ => trivial
  | s :: l, h => by
    simp only [oscDomOKB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
    refine ⟨fun i => ?_, fun i => ?_, oscDomOKB_sound l h.2⟩
    · have := (Rat.cast_lt (K := ℝ)).2 (h.1 i i.2).1
      push_cast at this; exact this
    · have := (Rat.cast_lt (K := ℝ)).2 (h.1 i i.2).2
      push_cast at this; exact this

/-- The Bool checker: every non-binder premise of `oscillatorChain_confinement`, in exact `ℚ`. -/
def checkOscChain {n : ℕ} (c : OscChainCertK K n) : Bool :=
  cartFitsB n c.H && cartFitsB n c.Nact && cartFitsB n c.P && cartActOnly c.Nact &&
  oscChainOKB n c.Nact c.P c.steps c.H && oscDomOKB n c.r c.δc c.steps &&
  decide (0 < c.δc) && decide (0 < c.εb) && decide (0 ≤ c.T) &&
  (List.range n).all fun i =>
    decide (0 ≤ c.r.getD i 0) && decide (2 * (c.b.getD i 0 + c.εb) ≤ c.r.getD i 0 ^ 2) &&
    decide (0 ≤ c.η.getD i 0) &&
    decide (cartSupBound (cartBracket (cartAction i) c.P) c.r c.r ≤
      c.η.getD i 0 - 2 * c.r.getD i 0 * oscChainBound n c.steps c.H / c.δc) &&
    decide (c.a.getD i 0 + c.T * c.η.getD i 0 < c.b.getD i 0)

theorem checkOscChain_sound {n : ℕ} [Algebra K ℝ] [Algebra K ℂ]
    [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ]
    (c : OscChainCertK K n) (hc : checkOscChain c = true)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ))
    (hw₀ : ∀ j : Fin n, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ (c.a.getD j 0 : ℝ)) :
    ∃ T₁ : ℝ, (c.T : ℝ) < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      z 0 = oscChainMap c.steps w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval c.H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = oscChainMap c.steps w₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval c.H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ (c.T : ℝ) →
        oscChainMap c.steps (oscChainInv c.steps (z t)) = z t ∧
        ∀ j : Fin n,
          |KAM.Planetary.oscillatorAction (oscChainInv c.steps (z t)).2
              (oscChainInv c.steps (z t)).1 j -
            KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ (c.η.getD j 0 : ℝ) * |t| ∧
          KAM.Planetary.oscillatorAction (oscChainInv c.steps (z t)).2
            (oscChainInv c.steps (z t)).1 j ≤
              (c.a.getD j 0 : ℝ) + (c.η.getD j 0 : ℝ) * (c.T : ℝ) := by
  unfold checkOscChain at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hH, hN⟩, hP⟩, hA⟩, hok⟩, hdom⟩, hδc⟩, hεb⟩, hT⟩, hall⟩ := hc
  have hK : ∀ i : Fin n, _ := fun i => hall i i.2
  have hr0 := fun i : Fin n => (hK i).1.1.1.1
  have hd1 := fun i : Fin n => (hK i).1.1.1.2
  have hη := fun i : Fin n => (hK i).1.1.2
  have hdr := fun i : Fin n => (hK i).1.2
  have hmg := fun i : Fin n => (hK i).2
  exact oscillatorChain_confinement (cartFitsB_sound hH) (cartFitsB_sound hN)
    (cartFitsB_sound hP) hA (oscChainOKB_sound _ _ hok) (δc := (c.δc : ℝ))
    (by exact_mod_cast hδc)
    (fun j => (c.a.getD j 0 : ℝ)) (fun j => (c.b.getD j 0 : ℝ)) (fun j => (c.η.getD j 0 : ℝ))
    (c.εb : ℝ) (c.T : ℝ) (by exact_mod_cast hεb) (by exact_mod_cast hT) c.r
    (fun i => (c.r.getD i 0 : ℝ)) (fun i => rfl)
    (fun i => by exact_mod_cast hr0 i) (fun i => by exact_mod_cast hd1 i)
    (oscDomOKB_sound _ hdom) (fun i => by exact_mod_cast hη i)
    (fun j => by
      have h2 := (Rat.cast_le (K := ℝ)).2 (hdr j)
      push_cast at h2 ⊢
      exact h2)
    (fun j => by exact_mod_cast hmg j) w₀ hw₀

/-! ### Smoke test: two zero generators on the harmonic oscillator -/

/-- `n = 1`, `H = I₀`, `Nact = q₀`, `P = 0`, two zero generators with `Q₁ = Q₂ = I₀`. -/
def harmonicChainCert : OscChainCert 1 where
  H := cartAction 0
  Nact := cartQVar 0
  P := []
  steps := [⟨[], cartAction 0, 1, 5, 1, 0⟩, ⟨[], cartAction 0, 1, 5, 1, 0⟩]
  δc := 1
  εb := 1
  T := 1
  a := [0]
  b := [1]
  η := [0]
  r := [2]

theorem harmonicChainCert_check : checkOscChain harmonicChainCert = true := by decide +kernel

/-- The harmonic two-step certificate is accepted and yields zero action drift. -/
theorem harmonicChainCert_zeroDrift (w₀ : (Fin 1 → ℝ) × (Fin 1 → ℝ))
    (hw₀ : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ 0) :
    ∃ z : ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ), ∀ t : ℝ, |t| ≤ 1 → ∀ j,
      |KAM.Planetary.oscillatorAction (oscChainInv harmonicChainCert.steps (z t)).2
          (oscChainInv harmonicChainCert.steps (z t)).1 j -
        KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ 0 := by
  obtain ⟨T₁, -, z, -, -, -, hb⟩ := checkOscChain_sound harmonicChainCert
    harmonicChainCert_check w₀ (fun j => by simpa [harmonicChainCert] using hw₀ j)
  refine ⟨z, fun t ht j => ?_⟩
  have := ((hb t (by simpa [harmonicChainCert] using ht)).2 j).1
  simpa [harmonicChainCert] using this

end KAM.EffectiveStability

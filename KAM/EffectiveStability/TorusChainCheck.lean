/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChain.Smoke
public import KAM.EffectiveStability.TorusCheck

/-!
# A single Bool checker for `m`-generator torus certificates (track B, B4-TCHECKCHAIN)

`TorusChainCert n` is pure data (polynomials, the list of `TChStep`s, rational widths and bounds).
`checkTorusChain` is a total computable `Bool` conjunction of every non-binder premise of
`torusChain_confinement`, evaluated in exact `ℚ`; `checkTorusChain_sound` extracts the premises and
applies B4-TMULTI. Lists are read with `getD i 0`; ranges `i < n` are `List.range n`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

/-- Certificate data for a chain of torus generators (no `Prop` fields; all numbers rational). -/
structure TorusChainCert (n : ℕ) where
  /-- the physical Hamiltonian -/
  H : FTPoly
  /-- the normal form, in the actions only -/
  Nact : FTPoly
  /-- the remainder -/
  P : FTPoly
  /-- the normalization steps, outermost first -/
  steps : List TChStep
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

/-- Boolean version of `TChStepOK`. -/
def tchStepOKB (n : ℕ) (s : TChStep) : Bool :=
  decide (0 < s.σ') && decide (0 < s.ρ') && decide (s.σ' < s.σ) && decide (0 ≤ s.ε) &&
  decide (s.ε ≤ 1 / 2) && decide (1 ≤ s.order) && ftFitsCheck n s.gen && ftFitsCheck n s.out &&
  decide (2 * ftPiUB * s.σ < 1) && decide (1 / (1 - 2 * ftPiUB * s.σ) ≤ s.lam) &&
  (List.range n).all fun i =>
    decide (ftSupBound (ftDJ i s.gen) ftPiUB s.lam (List.replicate n s.ρ) ≤ s.ε * s.σ') &&
    decide (ftSupBound (ftDφ i s.gen) ftPiUB s.lam (List.replicate n s.ρ) ≤ s.ε * s.ρ')

theorem tchStepOKB_sound {n : ℕ} {s : TChStep} (h : tchStepOKB n s = true) : TChStepOK n s := by
  unfold tchStepOKB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, ftFits_of_check h7, ftFits_of_check h8, h9, h10,
    fun i => (h11 i i.2).1, fun i => (h11 i i.2).2⟩

/-- Boolean version of `TChChainOK`. -/
def tchChainOKB (n : ℕ) (Nact P : FTPoly) : List TChStep → FTPoly → Bool
  | [], Q => ftEqCheck Q (ftAdd Nact P)
  | s :: l, Q => tchStepOKB n s && ftEqCheck (ftLieSum s.gen Q s.order) s.out &&
      tchChainOKB n Nact P l s.out

theorem tchChainOKB_sound {n : ℕ} {Nact P : FTPoly} :
    ∀ (l : List TChStep) (Q : FTPoly), tchChainOKB n Nact P l Q = true →
      TChChainOK n Nact P l Q
  | [], _, h => h
  | s :: l, Q, h => by
    simp only [tchChainOKB, Bool.and_eq_true] at h
    exact ⟨tchStepOKB_sound h.1.1, h.1.2, tchChainOKB_sound l _ h.2⟩

/-- Boolean version of `TChDomOK`, with rational radii `b`, `r` read by `getD`. -/
def tchDomOKB (n : ℕ) (b r : List ℚ) (εb δc : ℚ) : List TChStep → Bool
  | [] => true
  | s :: l => ((List.range n).all fun i =>
      decide (b.getD i 0 + εb + tchTailJ l + s.ρ' ≤ s.ρ) &&
      decide (r.getD i 0 + δc + tchTailJ l + s.ρ' / 2 < s.ρ)) &&
    decide (δc + tchTailA l + s.σ' / 2 < s.σ) && tchDomOKB n b r εb δc l

theorem tchDomOKB_sound {n : ℕ} {b r : List ℚ} {εb δc : ℚ} :
    ∀ l : List TChStep, tchDomOKB n b r εb δc l = true →
      TChDomOK n (fun i : Fin n => ((b.getD i 0 : ℚ) : ℝ)) (fun i : Fin n => ((r.getD i 0 : ℚ) : ℝ))
        (εb : ℝ) (δc : ℝ) l
  | [], _ => trivial
  | s :: l, h => by
    simp only [tchDomOKB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨fun i => ?_, ?_, fun i => ?_, tchDomOKB_sound l h3⟩
    · have := (Rat.cast_le (K := ℝ)).2 (h1 i i.2).1
      push_cast at this; exact this
    · have := (Rat.cast_lt (K := ℝ)).2 h2
      push_cast at this; exact this
    · have := (Rat.cast_lt (K := ℝ)).2 (h1 i i.2).2
      push_cast at this; exact this

/-- The Bool checker: every non-binder premise of `torusChain_confinement`, in exact `ℚ`. -/
def checkTorusChain {n : ℕ} (c : TorusChainCert n) : Bool :=
  ftFitsCheck n c.H && ftFitsCheck n c.P && ftActOnly c.Nact &&
  tchChainOKB n c.Nact c.P c.steps c.H && tchDomOKB n c.b c.r c.εb c.δc c.steps &&
  decide (0 < c.δc) && decide (0 < c.εb) && decide (0 ≤ c.T) &&
  (List.range n).all fun i =>
    decide (c.b.getD i 0 ≤ c.r.getD i 0) && decide (0 ≤ c.η.getD i 0) &&
    decide (ftAngleDriftBound c.P i ftPiUB c.b + tchChainBound n c.steps c.H / c.δc ≤
      c.η.getD i 0) &&
    decide (c.a.getD i 0 + c.T * c.η.getD i 0 < c.b.getD i 0)

theorem checkTorusChain_sound {n : ℕ} (c : TorusChainCert n) (hc : checkTorusChain c = true)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j : Fin n, |w₀.2 j| ≤ (c.a.getD j 0 : ℝ)) :
    ∃ T₁ : ℝ, (c.T : ℝ) < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      z 0 = tchChainMap c.steps w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR c.H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = tchChainMap c.steps w₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR c.H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ (c.T : ℝ) →
        tchChainMap c.steps (tchChainInv c.steps (z t)) = z t ∧
        ∀ j : Fin n,
          |(tchChainInv c.steps (z t)).2 j - w₀.2 j| ≤ (c.η.getD j 0 : ℝ) * |t| ∧
          |(tchChainInv c.steps (z t)).2 j| ≤
            (c.a.getD j 0 : ℝ) + (c.η.getD j 0 : ℝ) * (c.T : ℝ) := by
  unfold checkTorusChain at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hH, hP⟩, hA⟩, hok⟩, hdom⟩, hδc⟩, hεb⟩, hT⟩, hall⟩ := hc
  have hK : ∀ i : Fin n, _ := fun i => hall i i.2
  exact torusChain_confinement (ftFits_of_check hH) (ftFits_of_check hP) hA
    (tchChainOKB_sound _ _ hok) (δc := (c.δc : ℝ)) (by exact_mod_cast hδc)
    (fun j => (c.a.getD j 0 : ℝ)) (fun j => (c.b.getD j 0 : ℝ)) (fun j => (c.η.getD j 0 : ℝ))
    (c.εb : ℝ) (c.T : ℝ) (by exact_mod_cast hεb) (by exact_mod_cast hT) c.b (fun i => rfl)
    (fun i => (c.r.getD i 0 : ℝ)) (fun i => by exact_mod_cast (hK i).1.1.1)
    (tchDomOKB_sound _ hdom) (fun i => by exact_mod_cast (hK i).1.1.2)
    (fun j => by
      have h2 := (Rat.cast_le (K := ℝ)).2 (hK j).1.2
      push_cast at h2 ⊢
      exact h2)
    (fun j => by exact_mod_cast (hK j).2) w₀ hw₀

/-! ### Smoke test: two zero generators on the integrable Hamiltonian -/

/-- `n = 1`, `H = Nact = J₀²/2`, `P = 0`, two zero generators with outputs `Q₁ = Q₂ = H`. -/
def torusChainSmokeCert : TorusChainCert 1 where
  H := torusSmokeH
  Nact := torusSmokeH
  P := []
  steps := [tchSmokeStep, tchSmokeStep]
  δc := 1 / 20
  εb := 1
  T := 1
  a := [0]
  b := [1]
  η := [0]
  r := [2]

theorem torusChainSmokeCert_check : checkTorusChain torusChainSmokeCert = true := by
  decide +kernel

/-- The two-step certificate is accepted and yields zero action drift. -/
theorem torusChainSmokeCert_zeroDrift (w₀ : (Fin 1 → ℝ) × (Fin 1 → ℝ))
    (hw₀ : ∀ j, |w₀.2 j| ≤ 0) :
    ∃ z : ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ), ∀ t : ℝ, |t| ≤ 1 → ∀ j,
      |(tchChainInv torusChainSmokeCert.steps (z t)).2 j - w₀.2 j| ≤ 0 := by
  obtain ⟨T₁, -, z, -, -, -, hb⟩ := checkTorusChain_sound torusChainSmokeCert
    torusChainSmokeCert_check w₀ (fun j => by simpa [torusChainSmokeCert] using hw₀ j)
  refine ⟨z, fun t ht j => ?_⟩
  have := ((hb t (by simpa [torusChainSmokeCert] using ht)).2 j).1
  simpa [torusChainSmokeCert] using this

end KAM.EffectiveStability

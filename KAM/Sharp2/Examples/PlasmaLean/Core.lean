/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Examples.MirrorQ
public import KAM.Sharp2.RouteA.G1
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The cA-like data of PlasmaLean's example

`CALike` collects the explicit bounds on a Hamiltonian `h` and an approximate torus `K` of the norm
set "cA-like" of the design (§10.1): `M = 3`, the ball `μ = 1/160`, `‖DK‖ ≤ 3.1`, `‖G⁻¹‖ ≤ 2` (row
sums), `‖⟨T⟩⁻¹‖ ≤ 1/0.22 = 50/11` (row sums), `‖T‖ ≤ 19.84` on `T_{ρ-δ₀}`, on the strip `ρ = 1/50`.
The transposes need no hypothesis: `frame_bounds` gives their conservative values
`‖Lᵀ‖ ≤ 12.4`, `‖N‖ ≤ 6.2`, `‖Nᵀ‖ ≤ 24.8`.

`CAVar` holds what is free in a run: the caps, `ϑ`, the small-divisor constants and the prefix.
`CAVar.numA` is the run, with literal real fields, and `CAVar.numQ` its rational mirror.
`cALike_core` is `g1_branch_A` at these data: the only inputs are the rational test `ok`, the
small-divisor certificate, and `CALike`.
-/

@[expose] public section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Sharp2.Examples

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2.RouteA

/-- The explicit bounds of the cA-like norm set on `h`, `K`, `ω`. -/
structure CALike (𝔅 : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ))) (h : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ)
    (K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (ω : Fin 2 → ℝ) : Prop where
  isOpen : IsOpen 𝔅
  transl : ∀ z ∈ 𝔅, ∀ k : Fin 2 → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅
  holo : DifferentiableOn ℂ h 𝔅
  periodic : ∀ z ∈ 𝔅, ∀ k : Fin 2 → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z
  real : ∀ θ I : Fin 2 → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
    (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0
  bounds : ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ 3 ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ 3 ∧
    ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ 3 ∧
    ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ 3
  torus_holo : DifferentiableOn ℂ K (complexStrip 2 (1 / 50))
  primary : IsPrimaryOnStrip K (1 / 50)
  torus_real : IsRealOnReals K
  ball : ∀ θ ∈ complexStrip 2 (1 / 50), Metric.ball (K θ) (1 / 160) ⊆ 𝔅
  deriv_le : ∀ θ ∈ complexStrip 2 (1 / 50), ‖fderiv ℂ K θ‖ ≤ 31 / 10
  gram : ∀ θ ∈ complexStrip 2 (1 / 50), IsUnit (gramMatrix K θ).det ∧
    ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ 2
  twist_unit : IsUnit (torsionAverage h K ω).det
  twist_le : ∀ i, ∑ j, ‖(torsionAverage h K ω)⁻¹ i j‖ ≤ 50 / 11
  torsion_le : ∀ θ ∈ complexStrip 2 (1 / 50 - 333 / 100000), ‖torsion h K ω θ‖ ≤ 496 / 25

/-- The free numbers of a run at the cA-like data. -/
structure CAVar where
  sB : ℚ
  sT : ℚ
  sLt : ℚ
  sN : ℚ
  sNt : ℚ
  t : ℚ
  th : ℚ
  c : ℕ → ℚ
  cbar : ℕ → ℚ
  ctail : ℚ
  kp : ℕ

/-- The conservative initial values of the refined data: `‖Lᵀ‖ ≤ 12.4`, `‖N‖ ≤ 6.2`,
`‖Nᵀ‖ ≤ 24.8`, `‖T‖ ≤ 19.84`. -/
noncomputable def caInit : InitA := ⟨62 / 5, 31 / 5, 124 / 5, 496 / 25⟩

/-- The rational initial cap values. -/
def caM0 : Fin 8 → ℚ := ![0, 31 / 10, 2, 50 / 11, 62 / 5, 31 / 5, 124 / 5, 496 / 25]

namespace CAVar

variable (V : CAVar)

/-- The rational numbers of the run. -/
def numQ : NumQ :=
  { n := 2, ρ := 1 / 50, ρinf := 1 / 50000, M1 := 3, M2 := 3, sK := 993 / 320, sB := V.sB,
    sT := V.sT, sLt := V.sLt, sN := V.sN, sNt := V.sNt, t := V.t, th := V.th, γb := 687 / 5000,
    c := V.c, cbar := V.cbar, ctail := V.ctail, kp := V.kp }

/-- The numbers of the run. -/
noncomputable def numA : NumA :=
  { n := 2, τ := 1, ρ := 1 / 50, ρinf := 1 / 50000, M1 := 3, M2 := 3, sK := 993 / 320, sB := V.sB,
    sT := V.sT, sLt := V.sLt, sN := V.sN, sNt := V.sNt, t := V.t, th := V.th, γb := 687 / 5000,
    c := fun s => V.c s, cbar := fun s => V.cbar s, ctail := V.ctail, kp := V.kp }

theorem numQ_toA : V.numQ.toA = V.numA := by
  simp [numQ, numA, NumQ.toA]

/-- The rational caps. -/
def cap : Fin 8 → ℚ := ![1 / 320, 993 / 320, V.sB, V.sT, V.sLt, V.sN, V.sNt, V.t]

theorem capV_eq : V.numA.capV ((1 / 160) / 2) = fun i => (V.cap i : ℝ) := by
  funext i
  fin_cases i <;> norm_num [NumA.capV, numA, cap]

theorem initV_eq : initV caInit (31 / 10 + 1 / 160) (2 + 1 / 160) (50 / 11 + 1 / 160) (1 / 160) =
    fun i => (caM0 i : ℝ) := by
  funext i
  fin_cases i <;> norm_num [initV, caInit, caM0]

/-- Well-formedness. -/
theorem wf (hB : 0 < V.sB) (hT : 0 < V.sT) (hLt : 0 ≤ V.sLt) (hN : 0 ≤ V.sN) (hNt : 0 ≤ V.sNt)
    (ht : 0 ≤ V.t) (hth0 : 0 < V.th) (hth1 : V.th < 1) (hc : ∀ s, 0 ≤ V.c s)
    (hcb : ∀ s, 0 ≤ V.cbar s) (hct : 0 ≤ V.ctail) : V.numA.Wf where
  two_le := le_rfl
  τ_ge := le_rfl
  ρinf_pos := by norm_num [numA]
  ρinf_lt := by norm_num [numA]
  M1 := by norm_num [numA]
  M2 := by norm_num [numA]
  sK := by norm_num [numA]
  sB := by
    show (0 : ℝ) < V.sB
    exact_mod_cast hB
  sT := by
    show (0 : ℝ) < V.sT
    exact_mod_cast hT
  sLt := by
    show (0 : ℝ) ≤ V.sLt
    exact_mod_cast hLt
  sN := by
    show (0 : ℝ) ≤ V.sN
    exact_mod_cast hN
  sNt := by
    show (0 : ℝ) ≤ V.sNt
    exact_mod_cast hNt
  t := by
    show (0 : ℝ) ≤ V.t
    exact_mod_cast ht
  th0 := by
    show (0 : ℝ) < V.th
    exact_mod_cast hth0
  th1 := by
    show (V.th : ℝ) < 1
    exact_mod_cast hth1
  γb := by norm_num [numA]
  c := fun s => by
    show (0 : ℝ) ≤ V.c s
    exact_mod_cast hc s
  cbar := fun s => by
    show (0 : ℝ) ≤ V.cbar s
    exact_mod_cast hcb s
  ctail := by
    show (0 : ℝ) ≤ V.ctail
    exact_mod_cast hct
  Θ := le_rfl
  HY := le_rfl
  Mh2 := le_rfl

theorem delta0_eq : Engine.delta0 3 V.numA.ρ V.numA.ρinf = 333 / 100000 := by
  norm_num [Engine.delta0, numA]

theorem numA_δ (s : ℕ) : V.numA.δ s = (2 : ℝ)⁻¹ ^ s * (333 / 100000) := by
  show Engine.deltaSeq 3 V.numA.ρ V.numA.ρinf s = _
  simp only [Engine.deltaSeq, V.delta0_eq]

theorem numA_r (s : ℕ) :
    V.numA.r s = 1 / 50 - 2 * 3 * (333 / 100000) * (1 - (2 : ℝ)⁻¹ ^ s) := by
  show Engine.rSeq 3 V.numA.ρ V.numA.ρinf s = _
  simp only [Engine.rSeq, V.delta0_eq]
  rfl

theorem rho_pow : V.numA.ρ ^ (2 * V.numA.τ) = (1 / 50) ^ 2 := by
  show (1 / 50 : ℝ) ^ (2 * (1 : ℝ)) = _
  norm_num

/-- The closeness constant of route A, in rational form. -/
theorem c2A_eq {Xs : ℚ} : c2A V.numA (Xs : ℝ) =
    (1 / 50) ^ 2 * (V.numQ.sumD Xs : ℝ) / ((Xs : ℝ) * (333 / 100000) ^ 4) := by
  have h1 := V.numQ.cast_sumD Xs
  rw [V.numQ_toA] at h1
  unfold c2A
  rw [V.rho_pow, h1, V.delta0_eq, show 4 * V.numA.τ = ((4 : ℕ) : ℝ) by
    show 4 * (1 : ℝ) = _
    norm_num, Real.rpow_natCast]

end CAVar

open CAVar in
/-- **The core theorem at the cA-like data.** The rational test `ok` at `X⋆ > 0`, the small-divisor
certificate on a set `Ω ∋ ω`, the Diophantine pair `(γ, 1)` and the bounds `CALike` give the
invariant torus, for `e < X⋆ γ⁴ δ₀⁴`, where `δ₀ = 333/100000`. -/
theorem cALike_core (V : CAVar) (hV : V.numA.Wf) {Xs : ℚ} (hXs : 0 < Xs)
    (hok : V.numQ.ok V.cap caM0 Xs = true) {𝔅 : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ))}
    {h : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)}
    {ω : Fin 2 → ℝ} {Ω : Set (Fin 2 → ℝ)} {γ e : ℝ} (hO : CALike 𝔅 h K ω) (hω : ω ∈ Ω)
    (hCt : V.numA.Cert γ Ω) (hγ : 0 < γ) (hγb : γ ≤ 687 / 5000) (hdio : IsDiophantine γ 1 ω)
    (hE : ∀ θ ∈ complexStrip 2 (1 / 50), ‖invarianceError h K ω θ‖ ≤ e)
    (hsm : e / (γ ^ 4 * (333 / 100000) ^ 4) < Xs) :
    ∃ Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip 2 (1 / 50000)) ∧ IsPrimaryOnStrip Kinf (1 / 50000) ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), Metric.ball (Kinf θ) (1 / 320) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), ‖fderiv ℂ Kinf θ‖ ≤ 31 / 10 + 1 / 320) ∧
      ∀ θ ∈ complexStrip 2 (1 / 50000), ‖Kinf θ - K θ‖ ≤
        (V.numQ.sumD Xs : ℝ) / ((Xs : ℝ) * (333 / 100000) ^ 4 * γ ^ 2) * e := by
  have hρ0 : (0 : ℝ) < 1 / 50 := by norm_num
  have hXpos : (0 : ℝ) < Xs := by exact_mod_cast hXs
  have h00 : (0 : Fin 2 → ℂ) ∈ complexStrip 2 (1 / 50) := fun i => by simp
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hOk := NumQ.ok_sound hok
  rw [V.numQ_toA, show (fun i => (caM0 i : ℝ)) = _ from initV_eq.symm,
    show (fun i => (V.cap i : ℝ)) = _ from V.capV_eq.symm] at hOk
  have hSv : Standing 2 1 3 (31 / 10 + 1 / 160) (2 + 1 / 160) (50 / 11 + 1 / 160) 𝔅 h ω γ :=
    { toParams := ⟨le_rfl, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      isOpen := hO.isOpen
      transl_mem := hO.transl
      holo := hO.holo
      periodic := hO.periodic
      real := hO.real
      bounds := fun z hz => (hO.bounds z hz).2
      gamma_pos := hγ
      dio := hdio }
  have hK𝔅 : ∀ θ ∈ complexStrip 2 (1 / 50), K θ ∈ 𝔅 := fun θ hθ =>
    hO.ball θ hθ (Metric.mem_ball_self (by norm_num))
  have hGn : ∀ θ ∈ complexStrip 2 (1 / 50), ‖(gramMatrix K θ)⁻¹‖ ≤ 2 := fun θ hθ =>
    norm_le_of_rowSum_le le_rfl (hO.gram θ hθ).2
  have hfb : ∀ θ ∈ complexStrip 2 (1 / 50), _ := fun θ hθ =>
    frame_bounds hSv (hK𝔅 θ hθ) (hO.deriv_le θ hθ) (hO.gram θ hθ).1 (hGn θ hθ) ω
  have hδ0 : V.numA.δ 0 = 333 / 100000 := by
    show Engine.deltaSeq 3 V.numA.ρ V.numA.ρinf 0 = _
    simp [Engine.deltaSeq, V.delta0_eq]
  have hRef : RefHypA V.numA caInit 𝔅 h K ω :=
    { dX := fun z hz => (hO.bounds z hz).2.2.1
      d2X := fun z hz => (hO.bounds z hz).2.2.2
      tangentT := fun θ hθ => (hfb θ hθ).2.1.trans_eq (by norm_num [caInit])
      normal := fun θ hθ => (hfb θ hθ).2.2.1.trans_eq (by norm_num [caInit])
      normalT := fun θ hθ => (hfb θ hθ).2.2.2.2.1.trans_eq (by norm_num [caInit])
      tors := fun θ hθ => hO.torsion_le θ (by
        have e1 : V.numA.ρ - V.numA.δ 0 = 1 / 50 - 333 / 100000 := by rw [hδ0]; rfl
        rw [← e1]
        exact hθ) }
  have hsm' : e / (γ ^ 4 * Engine.delta0 3 V.numA.ρ V.numA.ρinf ^ (2 * (2 * V.numA.τ))) < Xs := by
    rw [V.delta0_eq, show 2 * (2 * V.numA.τ) = ((4 : ℕ) : ℝ) by
      show 2 * (2 * (1 : ℝ)) = _
      norm_num, Real.rpow_natCast]
    exact hsm
  obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := g1_branch_A (N := V.numA) (M := 3)
    (σK := 31 / 10 + 1 / 160) (σB := 2 + 1 / 160) (σT := 50 / 11 + 1 / 160) (μ := 1 / 160)
    (γbar := 687 / 5000) (Xs := Xs) (I := caInit) hV rfl rfl (by norm_num [numA]) (by norm_num)
    (by norm_num) rfl (by norm_num [numA]) hOk hXpos hO.isOpen hO.transl hO.holo hO.periodic hO.real
    hO.bounds hO.torus_holo hO.primary hO.torus_real
    hO.ball (fun θ hθ => (hO.deriv_le θ hθ).trans_eq (by norm_num))
    (fun θ hθ => ⟨(hO.gram θ hθ).1, fun i => ((hO.gram θ hθ).2 i).trans_eq (by norm_num)⟩)
    hO.twist_unit (fun i => (hO.twist_le i).trans_eq (by norm_num)) hRef hω hCt hγ hγb hdio he0 hE
    hsm'
  refine ⟨Kinf, h1, h2, h3, h4, ?_, ?_, ?_⟩
  · intro θ hθ
    have := h5 θ hθ
    rwa [show (1 / 160 / 2 : ℝ) = 1 / 320 by norm_num] at this
  · intro θ hθ
    exact (h6 θ hθ).trans_eq (by norm_num)
  · intro θ hθ
    refine (h7 θ hθ).trans_eq ?_
    rw [V.rho_pow, V.c2A_eq]
    field_simp

end KAM.Sharp2.Examples

end

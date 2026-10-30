/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Mono
public import KAM.Sharp2.RouteA.Ref.Step
public import KAM.Sharp2.RouteA.Scheme
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lever L8′ of route A: the scheme

`schemeR`: the states are the tori, compared with the initial torus `K₀`; the cap values are the
budgets of `AdmR`. `Budget` is the arithmetic of Lemma `bp:p2s2:torsion-ref`:
`b_T + 2b_F ≤ β_T = (σ̂_T - m_T)/(σ̂_T m_T)`, and the same sum, with the initial `H`, below the cap
`t` of `|T|`. `schemeR_isNewton` proves (N1), (N2): at the entry to a stage, `AdmR.entry` gives the
bounds of `T` and `⟨T⟩⁻¹`, and `step_core` is the step.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Sharp2.RouteA.Ref

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2

/-- The scheme with the torsion against the initial torus `K₀`. -/
def schemeR (N : NumA) (𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ)))
    (h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ) (ω : Fin N.n → ℝ) (μ : ℝ)
    (K₀ : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) :
    SchemeA N.n 7 ((Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) where
  tor := fun K => K
  par := fun _ => 0
  Adm := fun s ε m K => AdmR 𝔅 h ω K₀ (N.r s) (N.r s - N.δ s) (μ - m 0) ε (m 1) (m 2) (m 3) (m 4)
    (m 5) (m 6) K
  step := fun s K => newtonMap h K ω (N.r s - 2 * N.δ s)

/-- The budgets of the torsion: `m_T` bounds `⟨T₀⟩⁻¹`, `iH` bounds `T₀`, the cap of `𝒯_ab` is
`bT`, and `bF` is the local bound. -/
structure Budget (N : NumA) (mT iH bF bT : ℝ) : Prop where
  mT_pos : 0 < mT
  mT_lt : mT < N.sT
  beta : bT + 2 * bF ≤ (N.sT - mT) / (N.sT * mT)
  sup : iH + bT + 2 * bF ≤ N.t

variable {N : NumA} {τ M : ℝ} {𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))}
  {h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ} {ω : Fin N.n → ℝ} {γ : ℝ}
  {Ω : Set (Fin N.n → ℝ)}

/-- The strips of the torsion are nested. -/
theorem strip_sub (hN : N.Wf) (s : ℕ) :
    complexStrip N.n (N.r s - N.δ s) ⊆ complexStrip N.n (N.r 0 - N.δ 0) := by
  refine Triangular.strip_mono ?_
  induction s with
  | zero => exact le_rfl
  | succ s ih =>
    have := hN.δ_pos s
    rw [NumA.r_succ, NumA.δ_succ]
    linarith

theorem cont_torsion {m : ℕ} {σK σB σT : ℝ} {𝔅 : Set ((Fin m → ℂ) × (Fin m → ℂ))}
    {h : (Fin m → ℂ) × (Fin m → ℂ) → ℂ} {ω : Fin m → ℝ} {r β ε mK mB mLt mN mNt : ℝ}
    {K : (Fin m → ℂ) → (Fin m → ℂ) × (Fin m → ℂ)}
    (hS : Standing m τ M σK σB σT 𝔅 h ω γ) (hK : Adm0 𝔅 h ω r β ε mK mB mLt mN mNt K) :
    Continuous (fun x : Fin m → ℝ => torsion h K ω (fun i => (x i : ℂ))) :=
  FrameAux.continuous_torsion_real hK.r_pos
    (PerturbationAux.differentiableOn_torsion_of hS hK.holo hK.mem fun θ hθ => (hK.gram θ hθ).1)

/-- (N1), (N2) of the scheme with the torsion against the initial torus. -/
theorem schemeR_isNewton (hN : N.Wf) (hfix : N.iso = false) (hΘ : N.Θ = 0)
    (hS : Standing N.n τ M N.sK N.sB N.sT 𝔅 h ω γ)
    (hd1 : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ N.M1)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ N.M2)
    (hγb : γ ≤ N.γb) (hω : ω ∈ Ω) (hC : N.Cert γ Ω) {μ b bT bF iH mT : ℝ} (hb : b < μ)
    {K₀ : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)}
    (hR : RefT h K₀ ω (N.r 0 - N.δ 0) bF iH mT) (hB : Budget N mT iH bF bT) :
    (schemeR N 𝔅 h ω μ K₀).IsNewton (2 * N.τ) 3 N.ρ N.ρinf γ N.stageR jR
      (fun s x => N.CondR bF s x) (N.capR b bT) where
  adm := fun {s ε m x} hx => by
    have hx' : AdmR 𝔅 h ω K₀ (N.r s) (N.r s - N.δ s) (μ - m 0) ε (m 1) (m 2) (m 3) (m 4) (m 5)
      (m 6) x := hx
    exact ⟨hx'.ε_nonneg, hx'.holo, hx'.primary, hx'.real⟩
  step := by
    intro s ε m K hx hcond hcap
    have hA : AdmR 𝔅 h ω K₀ (N.r s) (N.r s - N.δ s) (μ - m 0) ε (m 1) (m 2) (m 3) (m 4) (m 5)
      (m 6) K := hx
    set p := N.inp s with hp
    have hpos : p.Pos := hN.pos s
    have hδ := hN.δ_pos s
    have hfixp : p.iso = false := hfix
    have hγ := hS.gamma_pos
    obtain ⟨hc, b', cb, hcb, hbr, hca⟩ := hC.at hN s
    set X := ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + 1)) with hX
    set E := ε / (γ ^ 2 * N.δ s ^ (2 * N.τ)) with hE
    have hX0 : 0 ≤ X := div_nonneg hA.ε_nonneg (by positivity)
    have e1 : ∀ c : ℝ, c * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))) = c * X := fun c => by
      rw [Nat.cast_one, mul_div_assoc]
    have e0 : ∀ c : ℝ, c * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((0 : ℕ) : ℝ))) = c * E := fun c => by
      rw [Nat.cast_zero, add_zero, mul_div_assoc]
    have c0 : m 0 + p.CDK * E ≤ b := by
      have := hcap 0
      rwa [show (N.stageR s).rate 0 = p.CDK from rfl,
        show ((jR 0 : ℕ) : ℝ) = ((0 : ℕ) : ℝ) from rfl,
        show deltaSeq 3 N.ρ N.ρinf s = N.δ s from rfl, e0] at this
    have cj : ∀ (i : Fin 7) (c : ℝ), (N.stageR s).rate i = c → jR i = 1 →
        m i + c * X ≤ N.capR b bT i := by
      intro i c hc1 hj
      have := hcap i
      rwa [hc1, hj, show deltaSeq 3 N.ρ N.ρinf s = N.δ s from rfl, e1] at this
    have c1 : m 1 + (N.n : ℝ) * p.CDK * X ≤ N.sK := cj 1 _ rfl rfl
    have c2 : m 2 + p.CB * p.CDK * X ≤ N.sB := cj 2 _ rfl rfl
    have c3 : m 3 + p.rAb * X ≤ bT := cj 3 _ rfl rfl
    have c4 : m 4 + 2 * (N.n : ℝ) * p.CDK * X ≤ N.sLt := cj 4 _ rfl rfl
    have c5 : m 5 + p.CNd * p.CDK * X ≤ N.sN := cj 5 _ rfl rfl
    have c6 : m 6 + p.CNtd * p.CDK * X ≤ N.sNt := cj 6 _ rfl rfl
    have hβ : p.CDK * E < μ - m 0 := by linarith
    have hn0 : (0 : ℝ) ≤ N.n := Nat.cast_nonneg _
    have hDK0 := hpos.CDK
    have hm1 : m 1 ≤ N.sK := le_of_add_le_of_nonneg_left c1 (by positivity)
    have hm2 : m 2 ≤ N.sB :=
      le_of_add_le_of_nonneg_left c2 (mul_nonneg (mul_nonneg hpos.CB hDK0) hX0)
    have hm3 : m 3 ≤ bT := le_of_add_le_of_nonneg_left c3 (mul_nonneg hpos.rAb hX0)
    have hm4 : m 4 ≤ N.sLt := le_of_add_le_of_nonneg_left c4 (by positivity)
    have hm5 : m 5 ≤ N.sN :=
      le_of_add_le_of_nonneg_left c5 (mul_nonneg (mul_nonneg hpos.CNd hDK0) hX0)
    have hm6 : m 6 ≤ N.sNt :=
      le_of_add_le_of_nonneg_left c6 (mul_nonneg (mul_nonneg hpos.CNtd hDK0) hX0)
    have h3δ := hN.lam_δ_lt s
    have hδD := hN.δ_le_dS s
    obtain ⟨hεδ, -, -, -⟩ := hcond.base.facts hpos hγ hγb hδ hδD hA.ε_nonneg
    have hc2 : SDConst N.n N.τ γ (N.δ s / 2) (N.cS (s + 1)) Ω := by
      have := (hC.at hN (s + 1)).1
      rwa [NumA.δ_succ] at this
    have hbL : N.bLocS s = p.bLoc0 (N.cS (s + 1)) := by simp [NumA.bLocS, StepInA.bLoc, hfixp, ← hp]
    have hloc : ∀ θ ∈ complexStrip N.n (N.r s - N.δ s),
        ‖torsion h K ω θ - torsionAB h K θ‖ ≤ bF := fun θ hθ => by
      have h1 := local_bound hpos rfl hS hd1 hγb hω (hA.toAdm0.mono hm1 hm2 hm4 hm5 hm6) hδ hδD
        (by linarith) hεδ hc2 θ hθ
      refine h1.trans ?_
      have h2 := hcond.loc
      rw [hbL] at h2
      exact h2
    have hrT : 0 < N.r s - N.δ s := by linarith
    have hAd : AdmA 𝔅 h ω (N.r s) (N.r s - N.δ s) (μ - m 0) ε (m 1) (m 2) N.sT (m 4) (m 5) (m 6) N.t
        K := hA.entry hR (strip_sub hN s) (cont_torsion hS hA.toAdm0) hrT hloc hB.mT_pos hB.mT_lt
      (by have := hB.beta; linarith) (by have := hB.sup; linarith)
    obtain ⟨hA', -, hclose, hab⟩ := step_core (p := p) (n := N.n) (ω := ω) hpos hfix hΘ rfl hS hd1
      hd2 hγb hω hAd hδ hδD h3δ hc hcb hbr hca hcond.base hβ c1 c2 c4 c5 c6
    have hrAb : p.rAb = p.CDab * p.CDK := by simp [StepInA.rAb, hfixp]
    refine ⟨?_, fun θ hθ => ?_, ?_⟩
    · show AdmR 𝔅 h ω K₀ (N.r (s + 1)) (N.r (s + 1) - N.δ (s + 1))
        (μ - (m 0 + (N.stageR s).rate 0 * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((0 : ℕ) : ℝ)))))
        (p.CE * ε ^ 2 / (γ ^ 4 * N.δ s ^ (2 * (2 * N.τ))))
        (m 1 + (N.n : ℝ) * p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 2 + p.CB * p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 3 + p.rAb * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 4 + 2 * (N.n : ℝ) * p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 5 + p.CNd * p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (m 6 + p.CNtd * p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + ((1 : ℕ) : ℝ))))
        (newtonMap h K ω (N.r s - 2 * N.δ s))
      rw [e0 ((N.stageR s).rate 0), e1, e1, e1, e1, e1, e1, NumA.r_succ, NumA.δ_succ,
        show μ - (m 0 + (N.stageR s).rate 0 * E) = μ - m 0 - p.CDK * E by
          rw [show (N.stageR s).rate 0 = p.CDK from rfl]; ring]
      refine ⟨hA', fun θ hθ => ?_⟩
      have hθ3 : θ ∈ complexStrip N.n (N.r s - 3 * N.δ s) :=
        Triangular.strip_mono (by linarith) hθ
      have hθ1 : θ ∈ complexStrip N.n (N.r s - N.δ s) :=
        Triangular.strip_mono (by linarith) hθ3
      have e : torsionAB h (newtonMap h K ω (N.r s - 2 * N.δ s)) θ - torsionAB h K₀ θ =
          (torsionAB h K θ - torsionAB h K₀ θ) +
            (torsionAB h (newtonMap h K ω (N.r s - 2 * N.δ s)) θ - torsionAB h K θ) := by abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add (hA.tab θ hθ1) ?_)
      rw [hrAb, mul_assoc]
      exact hab θ hθ3
    · have hθ' : θ ∈ complexStrip N.n (N.r s - 3 * N.δ s) := by
        rw [← NumA.r_succ]; exact hθ
      obtain ⟨h1, h2⟩ := hclose θ hθ'
      refine ⟨?_, ?_⟩
      · show ‖newtonMap h K ω (N.r s - 2 * N.δ s) θ - K θ‖ ≤
          p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ))
        rw [mul_div_assoc]
        exact h1
      · show ‖fderiv ℂ (newtonMap h K ω (N.r s - 2 * N.δ s)) θ - fderiv ℂ K θ‖ ≤
          (N.n : ℝ) * p.CDK * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ + 1))
        rw [mul_div_assoc]
        exact h2
    · show |(0 : ℝ) - 0| ≤ 0 * ε / (γ ^ 2 * N.δ s ^ (2 * N.τ))
      simp

end KAM.Sharp2.RouteA.Ref

end

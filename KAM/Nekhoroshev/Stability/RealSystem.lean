/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Stability.Setting
public import KAM.Canonical.Setting
public import KAM.ODE.Hamiltonian
public import KAM.Strip.Bridges
public import KAM.Strip.Periodic

/-!
# Holomorphic real systems (`bpN:p7:real-system`)

For `G ∈ O(r,s)` real on the real points of `𝒟_{r,s}`, the total real Hamiltonian
`realH G = Re G ∘ ι` is `C^∞` on `W_r`, `ℤⁿ`-periodic in the angles, its Hamiltonian field is the
restriction of the complex field, `X_{G^ℝ}` is `C¹` and periodic, and `G^ℝ` is conserved along
orbits in `W_ϱ`, `ϱ ≤ r`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace KAM.Stability

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

private theorem isOpen_realStrip (D : Set (Fin n → ℝ)) (ϱ : ℝ) : IsOpen (realStrip D ϱ) :=
  isOpen_univ.prod (isOpen_realNbhd D ϱ)

private theorem realStrip_mono (D : Set (Fin n → ℝ)) {ϱ ϱ' : ℝ} (h : ϱ' ≤ ϱ) :
    realStrip D ϱ' ⊆ realStrip D ϱ :=
  prod_mono subset_rfl (realNbhd_mono D h)

private theorem realH_contDiffOn {D : Set (Fin n → ℝ)} {r s : ℝ} {G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hs : 0 < s) (hG : InClass (cpx D) r s G) :
    ContDiffOn ℝ ∞ (realH G) (realStrip D r) := by
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional (isOpen_Dom (n := n) (cpx D) r s)
    hG.differentiableOn
  have h1 : ContDiffOn ℝ ∞ G (Dom n (cpx D) r s) := hreg.2.2.1.restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ∞ (fun x => G (KAM.realInclusion₂ n x)) (realStrip D r) :=
    h1.comp (KAM.realInclusion₂ n).contDiff.contDiffOn fun x hx =>
      (realInclusion₂_mem_Dom_iff D hs x).2 hx
  exact Complex.reCLM.contDiff.comp_contDiffOn h2

private theorem realH_periodic {D : Set (Fin n → ℝ)} {r s : ℝ} {G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hs : 0 < s) (hG : InClass (cpx D) r s G) (k : Fin n → ℤ) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realStrip D r) : realH G (x + KAM.ODE.angleShift k) = realH G x := by
  have hxD : KAM.realInclusion₂ n x ∈ Dom n (cpx D) r s := (realInclusion₂_mem_Dom_iff D hs x).2 hx
  have hθ : KAM.realInclusion n x.1 ∈ KAM.complexStrip n s := hxD.1
  have hp : ∀ (i : Fin n) (θ : Fin n → ℂ), θ ∈ KAM.complexStrip n s →
      (fun θ => G (θ, KAM.realInclusion n x.2)) (θ + Pi.single i 1) =
        (fun θ => G (θ, KAM.realInclusion n x.2)) θ := fun i θ hθ' =>
    hG.periodic i (θ, KAM.realInclusion n x.2) ⟨hθ', hxD.2⟩
  have h := KAM.periodic_int_shift (u := fun θ => G (θ, KAM.realInclusion n x.2)) hp k hθ
  have e : KAM.realInclusion₂ n (x + KAM.ODE.angleShift k) =
      (KAM.realInclusion n x.1 + fun i => (k i : ℂ), KAM.realInclusion n x.2) := by
    ext i <;> simp [KAM.ODE.angleShift]
  unfold realH
  rw [e]
  exact congrArg Complex.re h

theorem real_system {D : Set (Fin n → ℝ)} {r s : ℝ} {G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hs : 0 < s) (hG : InClass (cpx D) r s G) (hGr : RealOn (Dom n (cpx D) r s) G) :
    -- (a)
    (∀ k : ℕ, ContDiffOn ℝ k (realH G) (realStrip D r)) ∧
    (∀ k : Fin n → ℤ, ∀ x ∈ realStrip D r, realH G (x + KAM.ODE.angleShift k) = realH G x) ∧
    -- (b)
    (∀ x ∈ realStrip D r, DifferentiableAt ℝ (realH G) x ∧
      KAM.realInclusion₂ n (KAM.hamiltonianVectorField (realH G) x) =
        KAM.hamiltonianVectorFieldℂ G (KAM.realInclusion₂ n x)) ∧
    -- (c)
    ContDiffOn ℝ 1 (KAM.hamiltonianVectorField (realH G)) (realStrip D r) ∧
    (∀ k : Fin n → ℤ, ∀ x ∈ realStrip D r, KAM.hamiltonianVectorField (realH G)
      (x + KAM.ODE.angleShift k) = KAM.hamiltonianVectorField (realH G) x) ∧
    -- (d) energy conservation (the other Part 3 results need only (c))
    ∀ ϱ, 0 < ϱ → ϱ ≤ r → ∀ J : Set ℝ, J.OrdConnected → ∀ z, IsOrbit G D ϱ J z →
      ∀ t ∈ J, ∀ t' ∈ J, realH G (z t) = realH G (z t') := by
  have hsm := realH_contDiffOn hs hG
  have hper := fun k x hx => realH_periodic hs hG k (x := x) hx
  have hb : ∀ x ∈ realStrip D r, DifferentiableAt ℝ (realH G) x ∧
      KAM.realInclusion₂ n (KAM.hamiltonianVectorField (realH G) x) =
        KAM.hamiltonianVectorFieldℂ G (KAM.realInclusion₂ n x) := fun x hx => by
    have hxD : KAM.realInclusion₂ n x ∈ Dom n (cpx D) r s :=
      (realInclusion₂_mem_Dom_iff D hs x).2 hx
    have hreal : ∀ y : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n y ∈ Dom n (cpx D) r s →
        (G (KAM.realInclusion₂ n y)).im = 0 := fun y hy => hGr y hy
    exact ⟨(KAM.hamiltonian_real_fderiv (isOpen_Dom _ _ _) hG.differentiableOn hreal hxD
        (Filter.Eventually.of_forall fun y => rfl)).1,
      KAM.hamiltonianVectorField_eq_of_real (isOpen_Dom _ _ _) hG.differentiableOn hreal hxD
        (Filter.Eventually.of_forall fun y => rfl)⟩
  have hW : IsOpen (realStrip D r) := isOpen_realStrip D r
  have hWk : ∀ k : Fin n → ℤ,
      (fun x => x + KAM.ODE.angleShift k) '' realStrip D r = realStrip D r := by
    intro k
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_univ _, by simpa [KAM.ODE.angleShift] using hx.2⟩
    · intro hy
      refine ⟨y - KAM.ODE.angleShift k, ⟨mem_univ _, by simpa [KAM.ODE.angleShift] using hy.2⟩, ?_⟩
      simp
  have h2 : ContDiffOn ℝ 2 (realH G) (realStrip D r) :=
    hsm.of_le (by exact WithTop.coe_le_coe.2 le_top)
  refine ⟨fun k => hsm.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)), hper, hb,
    KAM.ODE.ham_smooth_c1 hW h2,
    (KAM.ODE.ham_periodic hW hWk hper).1, ?_⟩
  intro ϱ _ hϱr J hJ z hz
  refine KAM.ODE.ham_energy hJ fun t ht => ?_
  exact ⟨(hb _ (realStrip_mono D hϱr (hz t ht).1)).1, (hz t ht).2⟩

end KAM.Stability

end

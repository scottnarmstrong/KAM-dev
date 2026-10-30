/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Engine.Scheme
public import KAM.Apost.Limit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The limit of the abstract Newton scheme (blueprint `bp:p2s:engine-limit`)

The limit torus `K_∞` is the pointwise limit of `tor x_s` on `T_{ρ∞}` (`tor x₀` elsewhere) and
`p_∞` the limit of `par x_s`. The proof reuses the generic limit lemmas of `KAM.Apost.Limit`
(`lim_k`, `lim_dk`, `lim_holo`, `lim_primary`, `lim_close`).
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Sharp.Engine

variable {n k : ℕ} {α : Type*}

open Classical in
/-- `K_∞ = lim_s tor x_s` on `T_{ρ∞}`, `tor x₀` elsewhere. -/
def Scheme.limTor (S : Scheme n k α) (lam ρ ρinf : ℝ) (x₀ : α) :
    (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  fun θ => if θ ∈ complexStrip n ρinf then
    limUnder atTop (fun s => S.tor (S.iter lam ρ ρinf x₀ s) θ) else S.tor x₀ θ

/-- `p_∞ = lim_s par x_s`. -/
def Scheme.limPar (S : Scheme n k α) (lam ρ ρinf : ℝ) (x₀ : α) : ℝ :=
  limUnder atTop (fun s => S.par (S.iter lam ρ ρinf x₀ s))

section Helpers

variable {S : Scheme n k α} {c : Consts k} {γ ρ ρinf e : ℝ}

/-- Summability of `d_s`, `n d_s/δ_s` and of the parameter increments, with the sums of `d_s` and of
the parameter increments. -/
theorem Scheme.IsNewton.summable_terms (hS : S.IsNewton c γ) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e)
    (hE : (2 : ℝ) ^ (2 * c.a) * c.CE * e / (γ ^ 4 * delta0 c.lam ρ ρinf ^ (2 * c.a)) ≤ 1) :
    Summable (c.d ρ ρinf γ e) ∧
      ∑' s, c.d ρ ρinf γ e s ≤ 2 * c.CD * e / (γ ^ 2 * delta0 c.lam ρ ρinf ^ c.a) ∧
      Summable (fun s => n * c.d ρ ρinf γ e s / deltaSeq c.lam ρ ρinf s) ∧
      Summable (fun s => c.Cp * c.eps ρ ρinf γ e s / (γ ^ 2 * deltaSeq c.lam ρ ρinf s ^ c.a)) ∧
      ∑' s, c.Cp * c.eps ρ ρinf γ e s / (γ ^ 2 * deltaSeq c.lam ρ ρinf s ^ c.a) ≤
        2 * c.Cp * e / (γ ^ 2 * delta0 c.lam ρ ρinf ^ c.a) := by
  have hlam := hS.lam_pos
  have ha := hS.two_le_a
  obtain ⟨-, hdsum, hdtsum⟩ := term_sum hS.CE_nonneg hlam hρ hγ he hE hS.CD_nonneg
    (i := c.a) (by linarith) (by linarith)
  obtain ⟨-, hpsum, hptsum⟩ := term_sum hS.CE_nonneg hlam hρ hγ he hE hS.Cp_nonneg
    (i := c.a) (by linarith) (by linarith)
  obtain ⟨-, hksum, -⟩ := term_sum hS.CE_nonneg hlam hρ hγ he hE
    (Left.mul_nonneg (Nat.cast_nonneg n) hS.CD_nonneg) (i := c.a + 1) (by linarith)
    (by linarith)
  refine ⟨hdsum, hdtsum, ?_, hpsum, hptsum⟩
  refine hksum.congr fun s => ?_
  have hδ := deltaSeq_pos hlam hρ s
  have h1 : deltaSeq c.lam ρ ρinf s ^ (c.a + 1) = deltaSeq c.lam ρ ρinf s ^ c.a *
      deltaSeq c.lam ρ ρinf s := Real.rpow_add_one hδ.ne' _
  have hp := Real.rpow_pos_of_pos hδ c.a
  show n * c.CD * epsSeq c.CE c.a c.lam ρ ρinf γ e s /
      (γ ^ 2 * deltaSeq c.lam ρ ρinf s ^ (c.a + 1)) =
    n * (c.CD * epsSeq c.CE c.a c.lam ρ ρinf γ e s /
      (γ ^ 2 * deltaSeq c.lam ρ ρinf s ^ c.a)) / deltaSeq c.lam ρ ρinf s
  rw [h1]
  field_simp

/-- `ε_s → 0`. -/
theorem Scheme.IsNewton.eps_tendsto (hS : S.IsNewton c γ) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e)
    (hE : (2 : ℝ) ^ (2 * c.a) * c.CE * e / (γ ^ 4 * delta0 c.lam ρ ρinf ^ (2 * c.a)) ≤ 1) :
    Tendsto (fun s => c.eps ρ ρinf γ e s) atTop (𝓝 0) := by
  have := (epsSeq_sum hS.CE_nonneg hS.lam_pos hρ hγ he hE (i := 0) le_rfl
    (by linarith [hS.two_le_a])).1.tendsto_atTop_zero
  have h2 : Tendsto (fun s => epsSeq c.CE c.a c.lam ρ ρinf γ e s) atTop (𝓝 0) := by
    simpa using this
  exact h2

/-- The scalar parameter converges, with the stated bound. -/
theorem converge_par {f : ℕ → ℝ} {u : ℕ → ℝ} {B : ℝ} (hu : Summable u)
    (hd : ∀ s, |f (s + 1) - f s| ≤ u s) (hB : ∑' s, u s ≤ B) :
    ∃ p, Tendsto f atTop (𝓝 p) ∧ |p - f 0| ≤ B := by
  have hpd : ∀ s, dist (f s) (f (s + 1)) ≤ u s := fun s => by
    rw [Real.dist_eq, abs_sub_comm]; exact hd s
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_summable_dist (Summable.of_nonneg_of_le (fun s => dist_nonneg) hpd hu))
  refine ⟨p, hp, ?_⟩
  have hpb := dist_le_tsum_of_dist_le_of_tendsto₀ _ hpd hu hp
  rw [← Real.dist_eq, dist_comm]
  exact hpb.trans hB

end Helpers

/-- Blueprint `bp:p2s:engine-limit`. -/
theorem Scheme.limit {S : Scheme n k α} {c : Consts k} {γ : ℝ} (hS : S.IsNewton c γ)
    {ρ ρinf β₀ e : ℝ} {m₀ : Fin k → ℝ} {x₀ : α} (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (h0 : S.Adm ρ β₀ e m₀ x₀)
    (hE : (2 : ℝ) ^ (2 * c.a) * c.CE * e / (γ ^ 4 * delta0 c.lam ρ ρinf ^ (2 * c.a)) ≤ 1)
    (hst : c.cstep * e / (γ ^ 4 * delta0 c.lam ρ ρinf ^ (2 * c.a)) ≤ 1)
    (hball : 2 * c.CD * e / (γ ^ 2 * delta0 c.lam ρ ρinf ^ c.a) ≤ β₀ / 4)
    (hcap : ∀ i, m₀ i + 2 * c.rate i * e / (γ ^ 2 * delta0 c.lam ρ ρinf ^ (c.a + c.j i)) ≤
      c.cap i) :
    TendstoUniformlyOn (fun s => S.tor (S.iter c.lam ρ ρinf x₀ s)) (S.limTor c.lam ρ ρinf x₀)
        atTop (complexStrip n ρinf) ∧
      TendstoUniformlyOn (fun s θ => fderiv ℂ (S.tor (S.iter c.lam ρ ρinf x₀ s)) θ)
        (fderiv ℂ (S.limTor c.lam ρ ρinf x₀)) atTop (complexStrip n ρinf) ∧
      DifferentiableOn ℂ (S.limTor c.lam ρ ρinf x₀) (complexStrip n ρinf) ∧
      IsPrimaryOnStrip (S.limTor c.lam ρ ρinf x₀) ρinf ∧ IsRealOnReals (S.limTor c.lam ρ ρinf x₀) ∧
      (∀ θ ∈ complexStrip n ρinf, ‖S.limTor c.lam ρ ρinf x₀ θ - S.tor x₀ θ‖ ≤
        2 * c.CD * e / (γ ^ 2 * delta0 c.lam ρ ρinf ^ c.a)) ∧
      Tendsto (fun s => S.par (S.iter c.lam ρ ρinf x₀ s)) atTop
        (𝓝 (S.limPar c.lam ρ ρinf x₀)) ∧
      |S.limPar c.lam ρ ρinf x₀ - S.par x₀| ≤ 2 * c.Cp * e / (γ ^ 2 * delta0 c.lam ρ ρinf ^ c.a) ∧
      Tendsto (fun s => c.eps ρ ρinf γ e s) atTop (𝓝 0) := by
  have hlam := hS.lam_pos
  have he : 0 ≤ e := (hS.adm h0).1
  have hit := Scheme.iterate hS hρinf hρ hγ h0 hE hst hball hcap
  have hsch := schedule hlam hρinf hρ
  have hsub : ∀ s, complexStrip n ρinf ⊆ complexStrip n (rSeq c.lam ρ ρinf s) := fun s =>
    KAM.Apost.Triangular.strip_mono (hsch.2.2.2.2.1 s).le
  obtain ⟨hdsum, hdtsum, hdk, hpsum, hptsum⟩ := hS.summable_terms hρ hγ he hE
  have hdiff : ∀ s, ∀ θ ∈ complexStrip n ρinf,
      ‖S.tor (S.iter c.lam ρ ρinf x₀ (s + 1)) θ - S.tor (S.iter c.lam ρ ρinf x₀ s) θ‖ ≤
        c.d ρ ρinf γ e s := fun s θ hθ =>
    ((hit s).2.2.2.1 θ (hsub (s + 1) hθ)).1
  have hddiff : ∀ s, ∀ θ ∈ complexStrip n ρinf,
      ‖fderiv ℂ (S.tor (S.iter c.lam ρ ρinf x₀ (s + 1))) θ -
          fderiv ℂ (S.tor (S.iter c.lam ρ ρinf x₀ s)) θ‖ ≤
        n * c.d ρ ρinf γ e s / deltaSeq c.lam ρ ρinf s := fun s θ hθ =>
    ((hit s).2.2.2.1 θ (hsub (s + 1) hθ)).2
  have hhol : ∀ s, DifferentiableOn ℂ (S.tor (S.iter c.lam ρ ρinf x₀ s)) (complexStrip n ρinf) :=
    fun s => (hS.adm (hit s).1).2.1.mono (hsub s)
  have hprim : ∀ s, IsPrimaryOnStrip (S.tor (S.iter c.lam ρ ρinf x₀ s)) ρinf :=
    fun s θ hθ kk => (hS.adm (hit s).1).2.2.1 θ (hsub s hθ) kk
  have hreal : ∀ s, IsRealOnReals (S.tor (S.iter c.lam ρ ρinf x₀ s)) :=
    fun s => (hS.adm (hit s).1).2.2.2
  obtain ⟨hconv, hpt, hLG⟩ := KAM.Apost.lim_k
    (Ks := fun s => S.tor (S.iter c.lam ρ ρinf x₀ s))
    hdsum hdiff (L := S.limTor c.lam ρ ρinf x₀)
    (fun θ hθ => by simp only [Scheme.limTor, hθ, ite_true])
  obtain ⟨Λ, hΛ⟩ := KAM.Apost.lim_dk
    (Ks := fun s => S.tor (S.iter c.lam ρ ρinf x₀ s))
    hdk hddiff
  obtain ⟨hholo, hconvd⟩ := KAM.Apost.lim_holo
    (Ks := fun s => S.tor (S.iter c.lam ρ ρinf x₀ s))
    hhol hpt hΛ
  obtain ⟨hpr, hrr⟩ := KAM.Apost.lim_primary
    (Ks := fun s => S.tor (S.iter c.lam ρ ρinf x₀ s))
    hρinf hpt hprim hreal
  have hclose : ∀ θ ∈ complexStrip n ρinf, ‖S.limTor c.lam ρ ρinf x₀ θ - S.tor x₀ θ‖ ≤
      2 * c.CD * e / (γ ^ 2 * delta0 c.lam ρ ρinf ^ c.a) := fun θ hθ =>
    ((KAM.Apost.lim_close
    (Ks := fun s => S.tor (S.iter c.lam ρ ρinf x₀ s))
    hdsum hdiff hLG) θ hθ).trans hdtsum
  obtain ⟨p, hp, hpb⟩ := converge_par
    (f := fun s => S.par (S.iter c.lam ρ ρinf x₀ s)) hpsum
    (fun s => (hit s).2.2.2.2.1) hptsum
  have hlimP : S.limPar c.lam ρ ρinf x₀ = p := hp.limUnder_eq
  rw [hlimP]
  exact ⟨hconv, hconvd, hholo, hpr, hrr, hclose, hp, hpb, hS.eps_tendsto hρ hγ he hE⟩

end KAM.Sharp.Engine

end

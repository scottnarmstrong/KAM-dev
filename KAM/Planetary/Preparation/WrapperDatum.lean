/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedData
public import KAM.Planetary.Preparation.HoloAssembly
public import KAM.Planetary.Quantitative.Zero
public import KAM.Planetary.Quantitative.AssemblyK6
public import KAM.Planetary.Quantitative.KamInputNodes

/-!
# The datum `𝔡_ε` of the KAM input (P11A-P10, `bpP:p11:data-star` admissibility)

`p11WrDatum D b` is the KAM datum `(μ̄, b, K_ε, 1/4, σ/72, M_*, M_0^*, C_1, τ_D, 1/2)` of Remark
data-star.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
namespace KAM.Planetary

section Datum

variable {n : ℕ}

/-- The KAM datum of Remark data-star with amount `b`. -/
def p11WrDatum (D : P11Physical n) (b : ℝ) : QuantitativeData (n+n) where
  mu := (p11PatchData D).mu
  rho := 2
  tau := (p11SecularData D).tau
  vartheta := 1/4
  s := (p11SecularData D).sigma/72
  beta := b
  M := (2 : ℝ)^((p11PatchData D).mu+1)*(2*(p11SecularData D).L+1)^2
  M0 := p11M0 n (p11PatchData D).mu (p11SecularData D).L
  C1 := 2*(p11SecularData D).L+1
  epsLoss := 1/2
  K := p11PreparedBox n

theorem p11WrDatum_valid {D : P11Physical n} (hC : P11SecularSpec D (p11SecularData D))
    (hK : IsCompact (p11PreparedBox n)) (hvol : volume (p11PreparedBox n) = 1) {b : ℝ}
    (hb : 0 < b) (hbM : b ≤ min 1 (p11WrDatum D b).M) : (p11WrDatum D b).Valid := by
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast D.n_ge
  have hmu : 1 ≤ (p11PatchData D).mu := by
    have := (p11_patch D).choose_spec
    obtain ⟨-, -, -, -, -, -, -, -, -, hm, -⟩ := this
    exact hm
  have hC' := hC
  obtain ⟨-, -, -, hτ, -⟩ := hC'
  obtain ⟨-, -, hL1, -, -, hσ0, hσ1, -, -, -⟩ := fast_consts hC
  have hnm : ((n : ℝ)*(p11PatchData D).mu) ≤ (p11SecularData D).tau := by
    rw [hτ]; exact le_max_left _ _
  have h2n : (2 : ℝ)*n ≤ (p11SecularData D).tau := by
    rw [hτ]; exact le_max_right _ _
  have hmu' : (1 : ℝ) ≤ (p11PatchData D).mu := by exact_mod_cast hmu
  have hn2 : 2 ≤ n := D.n_ge
  refine ⟨⟨?_, hmu, Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb, ?_, hK, ?_, ?_⟩, ?_, ?_⟩
  · show 1 ≤ n + n
    omega
  · show ((n+n : ℕ) : ℝ) * (p11PatchData D).mu / (2 : ℕ) - 1 < _
    have e : ((n+n:ℕ):ℝ)*((p11PatchData D).mu:ℝ)/((2:ℕ):ℝ) = n*(p11PatchData D).mu := by
      push_cast; ring
    rw [e]; show _ < (p11SecularData D).tau; linarith
  · show 0 ≤ (p11SecularData D).tau
    have : 0 ≤ (n:ℝ)*(p11PatchData D).mu := by positivity
    linarith
  · show (0 : ℝ) < 1/4; norm_num
  · show (1/4 : ℝ) ≤ 1; norm_num
  · show 0 < (p11SecularData D).sigma/72; linarith
  · show (p11SecularData D).sigma/72 ≤ 1; linarith
  · show 1 ≤ 2*(p11SecularData D).L+1; linarith
  · show 0 < p11M0 n (p11PatchData D).mu (p11SecularData D).L
    unfold p11M0; positivity
  · exact (hbM.trans (min_le_right _ _))
  · show (0 : ℝ) < 1/2; norm_num
  · show ENNReal.ofReal (1/2) < volume (p11PreparedBox n)
    rw [hvol]
    exact ENNReal.ofReal_lt_one.2 (by norm_num)
  · show ((n+n : ℕ) : ℝ) - 1 < (p11SecularData D).tau
    push_cast; linarith
  · exact hbM.trans (min_le_left _ _)

theorem p11_single_mem {N : ℕ} {s : ℝ} {U : Set (Fin N → ℂ)}
    {z : (Fin N → ℂ) × (Fin N → ℂ)} (hz : z ∈ KAM.complexStrip N s ×ˢ U) (c : Fin N → ℂ)
    (hc : ∀ j, (c j).im = 0) : (z.1 + c, z.2) ∈ KAM.complexStrip N s ×ˢ U :=
  ⟨fun j => by simpa [hc j] using hz.1 j, hz.2⟩

/-- Integer shifts of the angles leave a `1`-periodic function unchanged. -/
theorem p11_periodic_int {N : ℕ} {f : (Fin N → ℂ) × (Fin N → ℂ) → ℂ} {s : ℝ}
    {U : Set (Fin N → ℂ)}
    (hper : ∀ z ∈ KAM.complexStrip N s ×ˢ U, ∀ i : Fin N,
      f (z.1 + Pi.single i 1, z.2) = f z)
    (z : (Fin N → ℂ) × (Fin N → ℂ)) (hz : z ∈ KAM.complexStrip N s ×ˢ U) (k : Fin N → ℤ) :
    f (z.1 + fun i => (k i : ℂ), z.2) = f z := by
  have hsing : ∀ (i : Fin N) (m : ℤ), ∀ j, ((Pi.single i (m : ℂ) : Fin N → ℂ) j).im = 0 :=
    fun i m j => by by_cases h : j = i <;> simp [Pi.single_apply, h]
  have hone : ∀ (i : Fin N) (m : ℤ), ∀ z ∈ KAM.complexStrip N s ×ˢ U,
      f (z.1 + Pi.single i (m : ℂ), z.2) = f z := by
    intro i m
    induction m using Int.induction_on with
    | zero => intro z hz; simp
    | succ m ih =>
      intro z hz
      have e : (Pi.single i (((m + 1 : ℤ)) : ℂ) : Fin N → ℂ) =
          (Pi.single i ((m : ℤ) : ℂ) : Fin N → ℂ) + Pi.single i 1 := by
        rw [← Pi.single_add]; push_cast; rfl
      rw [e, ← add_assoc, hper _ (p11_single_mem hz _ (hsing i (m : ℤ)))]
      exact ih z hz
    | pred m ih =>
      intro z hz
      have e : (Pi.single i (((-(m : ℤ)) : ℤ) : ℂ) : Fin N → ℂ) =
          (Pi.single i (((-(m : ℤ) - 1 : ℤ)) : ℂ) : Fin N → ℂ) + Pi.single i 1 := by
        rw [← Pi.single_add]; push_cast; ring_nf
      have hp := p11_single_mem hz _ (hsing i (-(m : ℤ) - 1))
      have := hper _ hp i
      rw [← ih z hz, e, ← add_assoc]
      exact this.symm
  have hsum : ∀ t : Finset (Fin N), ∀ z ∈ KAM.complexStrip N s ×ˢ U,
      f (z.1 + (fun i => if i ∈ t then (k i : ℂ) else 0), z.2) = f z := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro z hz
      rw [show (fun i : Fin N => if i ∈ (∅ : Finset (Fin N)) then (k i : ℂ) else 0) = 0 by
        funext i; simp]
      simp
    | insert a t ha ih =>
      intro z hz
      have hz' : (z.1 + (fun i => if i ∈ t then (k i : ℂ) else 0), z.2) ∈
          KAM.complexStrip N s ×ˢ U :=
        p11_single_mem hz _ fun j => by split_ifs <;> simp
      have h1 : (fun i => if i ∈ insert a t then (k i : ℂ) else 0) =
          (fun i => if i ∈ t then (k i : ℂ) else 0) + Pi.single a (k a : ℂ) := by
        funext j
        by_cases hj : j = a
        · subst hj; simp [ha]
        · simp [hj, Pi.single_apply]
      rw [h1, ← add_assoc]
      rw [hone a (k a) _ hz', ih z hz]
  simpa using hsum Finset.univ z hz

end Datum

end KAM.Planetary

end

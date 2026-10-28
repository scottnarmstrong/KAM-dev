/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Holomorphic
public import KAM.Planetary.Averaging.OscillatorFinite

/-!
# Fast averaging: the oscillator dictionary (P11A-P5, `stepP:p11:af-apply`)

The working carrier `p11WorkingDom` is the oscillator domain `oscDom {J0}` with `m = n`, the
secular position `x` playing the oscillator coordinate `q` and the momentum `y` playing `p`
(frozen order `((θ,x),(J,y))`). This module records that dictionary: domains, the flat parameter,
and the weighted-norm conversion of the spectator parameters.
-/

@[expose] public noncomputable section
open Set Metric
namespace KAM.Planetary

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

theorem oscDom_eq_workingDom (J0 : P11Vec n) (r rz S : ℝ) :
    oscDom (m := n) {J0} r rz rz S = p11WorkingDom n J0 S r rz := by
  ext z
  simp only [oscDom, oscParams, p11WorkingDom, mem_preimage, mem_prod, mem_ofPred_eq,
    oscPack, KAM.actionNbhd, mem_singleton_iff, exists_eq_left]
  have h1 : ∀ (a : Fin n → ℂ) (b c : Fin n → ℂ),
      firstBlock (b := n + n) (Fin.append a (Fin.append b c)) = a := fun a b c => by
    funext i; simp [firstBlock]
  have h2 : ∀ (a : Fin n → ℂ) (b c : Fin n → ℂ),
      firstBlock (b := n) (lastBlock (a := n) (Fin.append a (Fin.append b c))) = b := fun a b c => by
    funext i; simp [firstBlock, lastBlock]
  have h3 : ∀ (a : Fin n → ℂ) (b c : Fin n → ℂ),
      lastBlock (a := n) (lastBlock (a := n) (Fin.append a (Fin.append b c))) = c := fun a b c => by
    funext i; simp [lastBlock]
  have h4 : KAM.realInclusion n J0 = fun i => (J0 i : ℂ) := by funext i; simp
  rw [h1, h2, h3, h4]
  have e1 : ∀ v : Fin (n + n) → ℂ, firstBlock (b := n) v = fun i => v (Fin.castAdd n i) :=
    fun v => rfl
  have e2 : ∀ v : Fin (n + n) → ℂ, lastBlock (a := n) v = fun i => v (Fin.natAdd n i) :=
    fun v => rfl
  rw [e1, e1, e2, e2]
  tauto

/-- The flat oscillator parameter `(J, p, q) = (J, y, x)`. -/
def p11Flat (J y x : P11CVec n) : Fin (n + (n + n)) → ℂ := Fin.append J (Fin.append y x)

theorem firstBlock_p11Flat (J y x : P11CVec n) : firstBlock (b := n + n) (p11Flat J y x) = J := by
  funext i; simp [firstBlock, p11Flat]

theorem p_p11Flat (J y x : P11CVec n) :
    firstBlock (b := n) (lastBlock (a := n) (p11Flat J y x)) = y := by
  funext i; simp [firstBlock, lastBlock, p11Flat]

theorem q_p11Flat (J y x : P11CVec n) :
    lastBlock (a := n) (lastBlock (a := n) (p11Flat J y x)) = x := by
  funext i; simp [lastBlock, p11Flat]

theorem oscFunction_flat (f : CHam (n + n)) (θ J y x : P11CVec n) :
    oscFunction f (θ, p11Flat J y x) = f (Fin.append θ x, Fin.append J y) := by
  simp only [oscFunction, Function.comp, oscUnpack, firstBlock_p11Flat, p_p11Flat, q_p11Flat]

theorem coeff_zero_flat (F : P11Phase (n + n) → ℂ) (eps : ℝ) (J y x : P11CVec n) :
    coeff (oscFunction (fun w : CPhase (n + n) => (eps : ℂ) * F w)) (p11Flat J y x) 0 =
      eps * p11FastMean F J (x, y) := by
  unfold coeff KAM.torusCoeffW p11FastMean
  simp only [oscFunction_flat, neg_zero, KAM.character_zero, one_smul]
  unfold KAM.torusAverage
  rw [← MeasureTheory.integral_const_mul]
  rfl

theorem spectator_coeff (fs : CHam (n + n)) (z : P11Phase n) (J : P11CVec n) (k : Fin n → ℤ) :
    coeff (fun u : P11CVec n × P11CVec n => fs (Fin.append u.1 z.1, Fin.append u.2 z.2)) J k =
      coeff (oscFunction fs) (p11Flat J z.2 z.1) k := by
  unfold coeff
  simp only [oscFunction_flat]

/-- Weighted spectator conversion: the bound for the flat oscillator parameter `(J, y, x)` is the
bound of the function with the secular pair `z = (x, y)` frozen. -/
theorem spectator_wsummable (fs : CHam (n + n)) (z : P11Phase n) (J : P11CVec n) (S : ℝ) :
    WSummable (fun u : P11CVec n × P11CVec n => fs (Fin.append u.1 z.1, Fin.append u.2 z.2)) S J ↔
      WSummable (oscFunction fs) S (p11Flat J z.2 z.1) := by
  unfold WSummable
  simp only [spectator_coeff]

theorem spectator_wsum_eq (fs : CHam (n + n)) (z : P11Phase n) (J : P11CVec n) (S : ℝ) :
    wsum (fun u : P11CVec n × P11CVec n => fs (Fin.append u.1 z.1, Fin.append u.2 z.2)) S J =
      wsum (oscFunction fs) S (p11Flat J z.2 z.1) := by
  unfold wsum
  simp only [spectator_coeff]

/-- `bpN:p4:sup-weighted` (b) for the oscillator carrier. -/
theorem oscBound_of_sup {D : Set (Fin n → ℝ)} {m : ℕ} {r rp rq σ σ' M : ℝ} {g : CHam (n + m)}
    (hσ : 0 < σ) (hσ' : 0 < σ') (hcl : oscClass D r rp rq (σ + σ') g)
    (hM : ∀ z ∈ oscDom (m := m) D r rp rq (σ + σ'), ‖g z‖ ≤ M) :
    oscBound D r rp rq σ g (coth (Real.pi * σ') ^ n * M) := by
  refine oscBound_of_flat (G := oscFunction g) hσ (fun y _ => rfl) fun x hx => ?_
  have hfc := hcl.flat
  have hmem : ∀ θ ∈ KAM.complexStrip n (σ + σ'), (θ, x) ∈ KAM.complexStrip n (σ + σ') ×ˢ
      oscParams (m := m) D r rp rq := fun θ hθ => ⟨hθ, hx⟩
  have hd : DifferentiableOn ℂ (fun θ : Fin n → ℂ => oscFunction g (θ, x))
      (KAM.complexStrip n (σ + σ')) :=
    hfc.1.comp (differentiable_id.prodMk (differentiable_const x)).differentiableOn hmem
  obtain ⟨h1, h2⟩ := KAM.summableWeighted_torusCoeffW (ρ := σ + σ') (δ := σ') hσ' (by linarith) hd
    (fun i θ hθ => hfc.2 i (θ, x) (hmem θ hθ))
    (fun θ hθ => hM _ (oscUnpack_mem_oscDom.2 (hmem θ hθ)) |>.trans_eq' (by
      simp [oscFunction, Function.comp]))
  have he : σ + σ' - σ' = σ := by ring
  rw [he] at h1 h2
  exact ⟨h1, h2⟩

end KAM.Planetary

end

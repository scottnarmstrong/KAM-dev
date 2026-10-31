/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteB.Sched
public import KAM.Sharp2.SmallDiv.Scale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The classical certificates of route B

The constructors of the hypothesis `hcert` of `g1_v2B_frozen` and `iso_g1_v2B_frozen`
(AUDIT-ROUTEB-fixed-1, F2; route A's counterpart is `NumA.cert_classical`):

* `NumB.cert_classical`: the classical constants `cohConstC` of `bp:p2s2sd:classical` at the bites
  of the schedule (`δ_s`, the split bite, the full bite `min r_s 1`, `δ_kp`, `min r_kp 1`) are
  certificates on the Diophantine set, at every scale `γ > 0` (statement of the audit's probe);
* `NumB.cert_of_le`: the same with constants that dominate them.

The tail certificates serve every bite `≤ δ_kp` and every full bite `min r_j 1`, `j ≥ kp`, since
`cohConstC` is monotone in the bite and the full bites decrease along the schedule.
-/

@[expose] public section

namespace KAM.Sharp2.RouteB

open KAM KAM.Sharp2

variable {n : ℕ} {N : NumB n}

/-- The full strips decrease along the schedule. -/
theorem NumB.Wf.r_anti (hN : N.Wf) {j k : ℕ} (h : k ≤ j) : N.r j ≤ N.r k := by
  rw [hN.r_eq j, hN.r_eq k]
  have hc0 : 0 ≤ 3 * N.a / (N.a - 1) := by
    have := hN.a_gt
    have : 0 < N.a - 1 := by linarith
    positivity
  have := mul_le_mul_of_nonneg_left (hN.δ_anti h) hc0
  linarith

/-- **Constants dominating the classical ones are certificates on the Diophantine set.** -/
theorem NumB.cert_of_le (hN : N.Wf) {γ : ℝ} (hγ : 0 < γ)
    (hc : ∀ s < N.kp, cohConstC n N.τ (N.δ s) ≤ N.c s)
    (hc' : ∀ s < N.kp, cohConstC n N.τ (N.split * N.δ s) ≤ N.c' s)
    (hcb : ∀ s < N.kp, cohConstC n N.τ (N.bfull s) ≤ N.cbar s)
    (hct : cohConstC n N.τ (N.δ N.kp) ≤ N.ctail)
    (hcbt : cohConstC n N.τ (N.bfull N.kp) ≤ N.cbtail) :
    N.Cert γ {ω | IsDiophantine γ N.τ ω} := by
  have hn : 1 ≤ n := by have := hN.two_le; omega
  have hτ := hN.τ_ge
  have hb1 : ∀ s, N.bfull s ≤ 1 := fun s => min_le_right _ _
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, fun b hb hbk => ?_, fun j hj => ?_⟩
  · exact (sdConst_classical hn hτ hγ (hN.δ_pos s) (hN.δ_le_one s)).of_le_const hγ (hc s hs)
  · have h0 : 0 < N.split * N.δ s := mul_pos hN.split_pos (hN.δ_pos s)
    have h1 : N.split * N.δ s ≤ 1 :=
      (mul_le_of_le_one_left (hN.δ_pos s).le hN.split_lt_one.le).trans (hN.δ_le_one s)
    exact (sdConst_classical hn hτ hγ h0 h1).of_le_const hγ (hc' s hs)
  · exact (sdConst_classical hn hτ hγ (hN.bfull_pos s) (hb1 s)).of_le_const hγ (hcb s hs)
  · exact (sdConst_classical_of_le hn hτ hγ hb hbk (hN.δ_le_one _)).of_le_const hγ hct
  · exact (sdConst_classical_of_le hn hτ hγ (hN.bfull_pos j)
      (min_le_min_right 1 (hN.r_anti hj)) (hb1 _)).of_le_const hγ hcbt

/-- **The classical constants of the schedule are certificates on the Diophantine set**
(the constructor of `hcert`; AUDIT-ROUTEB-fixed-1, F2). -/
theorem NumB.cert_classical (hN : N.Wf) {γ : ℝ} (hγ : 0 < γ)
    (hc : ∀ s < N.kp, N.c s = cohConstC n N.τ (N.δ s))
    (hc' : ∀ s < N.kp, N.c' s = cohConstC n N.τ (N.split * N.δ s))
    (hcb : ∀ s < N.kp, N.cbar s = cohConstC n N.τ (N.bfull s))
    (hct : N.ctail = cohConstC n N.τ (N.δ N.kp))
    (hcbt : N.cbtail = cohConstC n N.τ (N.bfull N.kp)) :
    N.Cert γ {ω | IsDiophantine γ N.τ ω} :=
  NumB.cert_of_le hN hγ (fun s hs => (hc s hs).ge) (fun s hs => (hc' s hs).ge)
    (fun s hs => (hcb s hs).ge) hct.ge hcbt.ge

end KAM.Sharp2.RouteB

end

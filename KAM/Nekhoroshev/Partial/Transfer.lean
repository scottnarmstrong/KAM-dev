/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Continuation
public import KAM.Nekhoroshev.Partial.RealSystem
public import KAM.Nekhoroshev.Partial.Symplectic
public import KAM.Nekhoroshev.Stability.Setting
public import KAM.ODE.Maximal
public import KAM.ODE.Uniqueness

/-!
# Stopped transfer through a symplectic map (`bpN:p11:transfer`)

`KAM.Nekhoroshev.transfer_conditional` is the conditional helper of Part 11: if every normal-form
orbit that stays slowly displaced obeys the a priori confinement `(T3)` (a premise of this helper
only), then every physical orbit that stays slowly stopped is confined.

The proof is `transfer_core`, an abstract statement about two fields `F`, `Ft` and a map `P`; the
time-reversed case is the same statement for `-F`, `-Ft`.  The good set `E` of the source is
`stepN:p11:tr-E`; its closedness uses `KAM.Nekhoroshev.continuation` on a compact transverse tail.
-/

@[expose] public noncomputable section

open Set Metric KAM.ODE KAM.Weighted

namespace KAM.Nekhoroshev

variable {n k : ℕ}

/-! ### Real domains and compact tails -/

private theorem realDom_eq (b : PartialBlock n k) (r : ℝ) :
    b.realDom r = univ ×ˢ {v : Fin (n+(k+k)) → ℝ | (fun i => (v i : ℂ)) ∈ polyNbhd b.base r} := by
  ext z
  simp only [PartialBlock.realDom, Dom, mem_setOf_eq, mem_prod, mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨KAM.ofReal_mem_complexStrip one_pos z.1, h⟩⟩

private theorem isOpen_realDom_of (b : PartialBlock n k) (r : ℝ) : IsOpen (b.realDom r) := by
  rw [realDom_eq]
  refine isOpen_univ.prod ((isOpen_polyNbhd b.base r).preimage ?_)
  exact continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)

private theorem norm_snd_sub_le_R (a b : ER n k) :
    ‖a.2 - b.2‖ ≤ max ‖fastAction a - fastAction b‖ ‖slowPair a - slowPair b‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).mpr fun i => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine le_max_of_le_left ?_
    simpa [fastAction] using norm_le_pi_norm (fastAction a - fastAction b) j
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · refine le_max_of_le_right ?_
      have h := norm_le_pi_norm (slowPair a - slowPair b).1 l
      refine le_trans ?_ (h.trans (le_max_left _ _))
      simp [slowPair]
    · refine le_max_of_le_right ?_
      have h := norm_le_pi_norm (slowPair a - slowPair b).2 l
      refine le_trans ?_ (h.trans (le_max_right _ _))
      simp [slowPair]

private theorem continuous_fastAction_snd :
    Continuous (fun v : Fin (n+(k+k)) → ℝ => fastAction ((0 : Fin n → ℝ), v)) :=
  continuous_pi fun i => continuous_apply _

private theorem continuous_slowPair_snd :
    Continuous (fun v : Fin (n+(k+k)) → ℝ => slowPair ((0 : Fin n → ℝ), v)) :=
  (continuous_pi fun i => continuous_apply _).prodMk (continuous_pi fun i => continuous_apply _)

private theorem continuous_slowPair : Continuous (slowPair : ER n k → KAM.Planetary.Phase k) :=
  (continuous_pi fun i => (continuous_apply _).comp continuous_snd).prodMk
    (continuous_pi fun i => (continuous_apply _).comp continuous_snd)

/-- A real point with fast action within `r` of `Ic` and slow pair within `r` of the slow pair of a
point of `λ⁻¹ S` lies in `realDom r`. -/
private theorem mem_realDom_of_close (b : PartialBlock n k) (hbR : 0 < b.rB) (hbw : 0 < b.w)
    {r : ℝ} {w u : ER n k} (hu : b.lam • slowPair u ∈ b.S)
    (h1 : ‖fastAction w - b.Ic‖ < r) (h2 : ‖slowPair w - slowPair u‖ < r) :
    w ∈ b.realDom r := by
  have hlam : b.lam ≠ 0 := (div_pos hbw hbR).ne'
  set q : ER n k := (0, Fin.append b.Ic (Fin.append (slowPair u).1 (slowPair u).2)) with hq
  have hfq : fastAction q = b.Ic := by
    ext i; simp [fastAction, hq, Fin.append_left]
  have hsq : slowPair q = slowPair u := by
    ext i <;> simp [slowPair, hq, Fin.append_right, Fin.append_left]
  have hbase : (extCx q).2 ∈ b.base := by
    refine ⟨b.lam • slowPair u, hu, ?_⟩
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [extCx, hq, Fin.append_left]
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simp [extCx, hq, Fin.append_right, Fin.append_left, hlam]
      · simp only [extCx, hq, Fin.append_right, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
        have hc : (b.lam : ℂ) ≠ 0 := by exact_mod_cast hlam
        push_cast
        field_simp
  rw [realDom_eq]
  refine ⟨mem_univ _, (extCx q).2, hbase, ?_⟩
  have hd : (fun i => (w.2 i : ℂ)) - (extCx q).2 = KAM.realInclusion _ (w.2 - q.2) := by
    ext i; simp [extCx]
  rw [hd, KAM.norm_realInclusion]
  refine lt_of_le_of_lt (norm_snd_sub_le_R w q) (max_lt ?_ ?_)
  · rwa [hfq]
  · rwa [hsq]

/-- The compact slow tube around the slow pairs of a compact set `Y`. -/
private theorem isCompact_tube {Nrm : (Fin n → ℝ) → ℝ} (hN : KAM.Stability.IsActionNorm Nrm)
    (c : Fin n → ℝ) (a dx : ℝ) {Y : Set (KAM.Planetary.Phase k)} (hY : IsCompact Y) :
    IsCompact {v : Fin (n+(k+k)) → ℝ |
      Nrm (fastAction ((0 : Fin n → ℝ), v) - c) ≤ a ∧
        slowPair ((0 : Fin n → ℝ), v) ∈ cthickening dx Y} := by
  have hcl : IsClosed {v : Fin (n+(k+k)) → ℝ |
      Nrm (fastAction ((0 : Fin n → ℝ), v) - c) ≤ a ∧
        slowPair ((0 : Fin n → ℝ), v) ∈ cthickening dx Y} := by
    refine IsClosed.inter ?_ ?_
    · exact isClosed_le (hN.continuous.comp (continuous_fastAction_snd.sub continuous_const))
        continuous_const
    · exact isClosed_cthickening.preimage continuous_slowPair_snd
  obtain ⟨C, hC⟩ := (hY.isBounded.cthickening (δ := dx)).exists_norm_le
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  refine (isBounded_iff_forall_norm_le).2 ⟨max (a + ‖c‖) C, fun v hv => ?_⟩
  have hfa : ‖fastAction ((0 : Fin n → ℝ), v)‖ ≤ a + ‖c‖ := by
    calc ‖fastAction ((0 : Fin n → ℝ), v)‖
        ≤ ‖fastAction ((0 : Fin n → ℝ), v) - c‖ + ‖c‖ := by
          have := norm_sub_norm_le (fastAction ((0 : Fin n → ℝ), v)) c
          linarith
      _ ≤ a + ‖c‖ := add_le_add ((hN.norm_le _).trans hv.1) le_rfl
  have h := norm_snd_sub_le_R ((0 : Fin n → ℝ), v) (0 : ER n k)
  have h0 : fastAction (0 : ER n k) = 0 := rfl
  have h0' : slowPair (0 : ER n k) = 0 := rfl
  have e1 : ((0 : Fin n → ℝ), v).2 - (0 : ER n k).2 = v := by simp
  rw [e1, h0, h0', sub_zero, sub_zero] at h
  exact h.trans (max_le_max hfa (hC _ hv.2))

/-- The slow tube of radius `a` about `λ⁻¹ S`. -/
def slowTube (b : PartialBlock n k) (a : ℝ) (x : KAM.Planetary.Phase k) : Prop :=
  ∃ v ∈ b.S, ‖x-b.lam⁻¹ • v‖ ≤ a

/-! ### The abstract stopped transfer -/

private theorem transfer_core (b : PartialBlock n k) (hbR : 0 < b.rB) (hbw : 0 < b.w)
    {R r d dx a : ℝ} {T : ENNReal} (hr : 0 < r)
    (Nrm : (Fin n → ℝ) → ℝ) (hN : KAM.Stability.IsActionNorm Nrm)
    (hd : 0 ≤ d) (hdx : 0 ≤ dx) (hdxr : dx < r) (hgap : d+a < r)
    (P : ER n k → ER n k)
    (hdisp : ∀ z ∈ b.realDom r, Nrm (fastAction (P z)-fastAction z) ≤ d ∧
      ‖slowPair (P z)-slowPair z‖ ≤ dx)
    (hpre : ∀ y : ER n k, fastAction y = b.Ic → b.lam • slowPair y ∈ b.S →
      ∃ x ∈ b.realDom r, P x = y ∧ Nrm (fastAction x-b.Ic) ≤ d)
    (F Ft : ER n k → ER n k) (hFt : ContDiffOn ℝ 1 Ft (b.realDom r))
    (hFtp : ∀ ℓ : Fin n → ℤ, ∀ z ∈ b.realDom r, Ft (z.1+(fun i => (ℓ i:ℝ)), z.2) = Ft z)
    (hF : ContDiffOn ℝ 1 F (b.realDom R))
    (hconj : ∀ (J : Set ℝ) (y : ℝ → ER n k), IsSolutionIn Ft (b.realDom r) J y →
      IsSolutionIn F (b.realDom R) J (P ∘ y))
    (hT3 : ∀ J : Set ℝ, J.OrdConnected → (0:ℝ) ∈ J → ∀ y : ℝ → ER n k,
      IsSolutionIn Ft (b.realDom r) J y → Nrm (fastAction (y 0)-b.Ic) ≤ d →
      (∀ u ∈ J, slowTube b dx (slowPair (y u))) →
      ∀ u ∈ J, ENNReal.ofReal |u| ≤ T → Nrm (fastAction (y u)-fastAction (y 0)) ≤ a)
    {y : ℝ → ER n k} {t1 : ℝ} (ht0 : 0 ≤ t1)
    (hy : ∀ u ∈ Icc 0 t1, HasDerivAt y (F (y u)) u)
    (hI : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    (htT : ENNReal.ofReal t1 ≤ T)
    (hstop : ∀ u ∈ Icc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ Icc 0 t1, y u ∈ b.realDom R ∧ Nrm (fastAction (y u)-b.Ic) ≤ a + 2*d := by
  sorry

end KAM.Nekhoroshev

end

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
  simp only [PartialBlock.realDom, Dom, mem_ofPred_eq, mem_prod, mem_univ, true_and]
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
  continuous_pi fun _ => continuous_apply _

private theorem continuous_slowPair_snd :
    Continuous (fun v : Fin (n+(k+k)) → ℝ => slowPair ((0 : Fin n → ℝ), v)) :=
  (continuous_pi fun _ => continuous_apply _).prodMk (continuous_pi fun _ => continuous_apply _)

private theorem continuous_slowPair : Continuous (slowPair : ER n k → KAM.Planetary.Phase k) :=
  (continuous_pi fun _ => (continuous_apply _).comp continuous_snd).prodMk
    (continuous_pi fun _ => (continuous_apply _).comp continuous_snd)

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
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show Fin.append b.Ic (Fin.append (slowPair u).1 (slowPair u).2)
        (Fin.natAdd n (Fin.castAdd k i)) = _
      rw [Fin.append_right, Fin.append_left]
    · show Fin.append b.Ic (Fin.append (slowPair u).1 (slowPair u).2)
        (Fin.natAdd n (Fin.natAdd k i)) = _
      rw [Fin.append_right, Fin.append_right]
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
    {R r d dx a : ℝ} {T : ENNReal}
    (Nrm : (Fin n → ℝ) → ℝ) (hN : KAM.Stability.IsActionNorm Nrm)
    (hdx : 0 ≤ dx) (hdxr : dx < r) (hgap : d+a < r)
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
  have hlam : b.lam ≠ 0 := (div_pos hbw hbR).ne'
  have hW : IsOpen (b.realDom r) := isOpen_realDom_of b r
  have hWR : IsOpen (b.realDom R) := isOpen_realDom_of b R
  have htri : ∀ p q m : Fin n → ℝ, Nrm (p - q) ≤ Nrm (p - m) + Nrm (m - q) := fun p q m => by
    have := hN.add_le (p - m) (m - q)
    rwa [show p - m + (m - q) = p - q by abel] at this
  have hycont : ∀ u ∈ Icc 0 t1, ContinuousAt y u := fun u hu => (hy u hu).continuousAt
  obtain ⟨x, hxW, hPx, hxd⟩ := hpre (y 0) hI hx
  obtain ⟨⟨Tm, Tp, z, hz⟩, -⟩ := gen_maximal hW hFt hxW
  have hz0 : z 0 = x := hz.init
  have hzsol : ∀ J : Set ℝ, J ⊆ eIoo Tm Tp → IsSolutionIn Ft (b.realDom r) J z :=
    fun J hJ => hz.isSolution.mono hJ
  set E : Set ℝ := {τ | τ ∈ Icc 0 t1 ∧ Icc 0 τ ⊆ eIoo Tm Tp ∧
    ∀ u ∈ Icc 0 τ, y u = P (z u)} with hE
  have h0E : (0:ℝ) ∈ E := by
    refine ⟨⟨le_rfl, ht0⟩, fun u hu => ?_, fun u hu => ?_⟩
    · rw [le_antisymm hu.2 hu.1]; exact zero_mem_eIoo hz
    · rw [le_antisymm hu.2 hu.1, hz0, hPx]
  have hdown : ∀ τ ∈ E, ∀ τ', 0 ≤ τ' → τ' ≤ τ → τ' ∈ E := fun τ hτ τ' h0 hle =>
    ⟨⟨h0, hle.trans hτ.1.2⟩, (Icc_subset_Icc_right hle).trans hτ.2.1,
      fun u hu => hτ.2.2 u (Icc_subset_Icc_right hle hu)⟩
  -- the slow variables of the normal-form orbit stay within `dx` of the physical ones
  have hsp : ∀ τ ∈ E, ∀ u ∈ Icc 0 τ, ‖slowPair (z u) - slowPair (y u)‖ ≤ dx := by
    intro τ hτ u hu
    have hzW : z u ∈ b.realDom r := (hzsol _ hτ.2.1 u hu).1
    have := (hdisp (z u) hzW).2
    rwa [← hτ.2.2 u hu, norm_sub_rev] at this
  -- bounds on every prefix
  have hbd : ∀ τ ∈ E, ∀ u ∈ Icc 0 τ, Nrm (fastAction (z u) - fastAction x) ≤ a := by
    intro τ hτ u hu
    have htube : ∀ u ∈ Icc 0 τ, slowTube b dx (slowPair (z u)) := fun u hu =>
      ⟨b.lam • slowPair (y u), hstop u ⟨hu.1, hu.2.trans hτ.1.2⟩, by
        rw [inv_smul_smul₀ hlam]; exact hsp τ hτ u hu⟩
    have h := hT3 (Icc 0 τ) ordConnected_Icc ⟨le_rfl, hτ.1.1⟩ z (hzsol _ hτ.2.1)
      (by rwa [hz0]) htube u hu (by
        rw [abs_of_nonneg hu.1]
        exact (ENNReal.ofReal_le_ofReal (hu.2.trans hτ.1.2)).trans htT)
    rwa [hz0] at h
  -- `E` is open on the right
  have hopen : ∀ τ ∈ E, τ < t1 → ∃ τ' ∈ E, τ < τ' := by
    intro τ hτ hlt
    have hτm : τ ∈ eIoo Tm Tp := hτ.2.1 ⟨hτ.1.1, le_rfl⟩
    have hτy : y τ ∈ b.realDom R := by
      rw [hτ.2.2 τ ⟨hτ.1.1, le_rfl⟩]
      exact (hconj _ _ (hzsol _ hτ.2.1)) τ ⟨hτ.1.1, le_rfl⟩ |>.1
    have hev1 : ∀ᶠ u in nhds τ, u ∈ eIoo Tm Tp := (isOpen_eIoo Tm Tp).mem_nhds hτm
    have hev2 : ∀ᶠ u in nhds τ, y u ∈ b.realDom R :=
      (hycont τ ⟨hτ.1.1, hτ.1.2⟩).eventually (hWR.mem_nhds hτy)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hev1.and hev2)
    set τ' := min (τ + ε/2) t1 with hτ'
    have hτ'τ : τ < τ' := lt_min (by linarith) hlt
    have hIsub : Icc τ τ' ⊆ eIoo Tm Tp ∧ ∀ u ∈ Icc τ τ', y u ∈ b.realDom R := by
      have : ∀ u ∈ Icc τ τ', dist u τ < ε := fun u hu => by
        rw [Real.dist_eq, abs_lt]
        have := hu.2.trans (min_le_left _ _)
        constructor <;> linarith [hu.1]
      exact ⟨fun u hu => (hball (this u hu)).1, fun u hu => (hball (this u hu)).2⟩
    have hyI : IsSolutionIn F (b.realDom R) (Icc τ τ') y := fun u hu =>
      ⟨hIsub.2 u hu, hy u ⟨hτ.1.1.trans hu.1, hu.2.trans (min_le_right _ _)⟩⟩
    have hzI : IsSolutionIn F (b.realDom R) (Icc τ τ') (P ∘ z) :=
      hconj _ _ (hzsol _ hIsub.1)
    have heq := gen_uniqueness hWR hF ordConnected_Icc (t₀ := τ) ⟨le_rfl, hτ'τ.le⟩ hyI hzI
      (by rw [hτ.2.2 τ ⟨hτ.1.1, le_rfl⟩]; rfl)
    refine ⟨τ', ⟨⟨hτ.1.1.trans hτ'τ.le, min_le_right _ _⟩, fun u hu => ?_, fun u hu => ?_⟩, hτ'τ⟩
    · rcases le_total u τ with h | h
      · exact hτ.2.1 ⟨hu.1, h⟩
      · exact hIsub.1 ⟨h, hu.2⟩
    · rcases le_total u τ with h | h
      · exact hτ.2.2 u ⟨hu.1, h⟩
      · exact heq ⟨h, hu.2⟩
  -- `E` is closed
  have hbdE : BddAbove E := ⟨t1, fun τ hτ => hτ.1.2⟩
  set τs := sSup E with hτs
  have hτs0 : 0 ≤ τs := le_csSup hbdE h0E
  have hτs1 : τs ≤ t1 := csSup_le ⟨0, h0E⟩ fun τ hτ => hτ.1.2
  have hbelow : ∀ τ, 0 ≤ τ → τ < τs → τ ∈ E := fun τ h0 hlt => by
    obtain ⟨e, he, hτe⟩ := exists_lt_of_lt_csSup ⟨0, h0E⟩ hlt
    exact hdown e he τ h0 hτe.le
  have hτsE : τs ∈ E := by
    rcases hτs0.eq_or_lt with h0 | hpos
    · rw [← h0]; exact h0E
    have hTp : (τs : EReal) < Tp := by
      by_contra hcon
      push Not at hcon
      set Ut : Set (Fin (n+(k+k)) → ℝ) :=
        {v | (fun i => (v i : ℂ)) ∈ polyNbhd b.base r} with hUt
      have hUo : IsOpen Ut := (isOpen_polyNbhd b.base r).preimage
        (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))
      have hWeq : b.realDom r = univ ×ˢ Ut := realDom_eq b r
      set Y : Set (KAM.Planetary.Phase k) := (fun u => slowPair (y u)) '' Icc 0 t1 with hY
      have hYc : IsCompact Y := isCompact_Icc.image_of_continuousOn
        (continuous_slowPair.comp_continuousOn
          (fun u hu => (hy u hu).continuousAt.continuousWithinAt))
      have hKc := isCompact_tube hN (fastAction x) a dx hYc
      have hKU : {v : Fin (n+(k+k)) → ℝ | Nrm (fastAction ((0 : Fin n → ℝ), v) - fastAction x) ≤ a ∧
          slowPair ((0 : Fin n → ℝ), v) ∈ cthickening dx Y} ⊆ Ut := by
        rintro v ⟨hv1, hv2⟩
        rw [hYc.cthickening_eq_biUnion_closedBall hdx] at hv2
        obtain ⟨p, ⟨u, hu, rfl⟩, hp⟩ := mem_iUnion₂.1 hv2
        rw [mem_closedBall_iff_norm] at hp
        have h1 : ‖fastAction ((0 : Fin n → ℝ), v) - b.Ic‖ < r :=
          lt_of_le_of_lt ((hN.norm_le _).trans ((htri _ _ (fastAction x)).trans
            (add_le_add hv1 hxd))) (by linarith)
        have hmem : ((0 : Fin n → ℝ), v) ∈ b.realDom r :=
          mem_realDom_of_close b hbR hbw (hstop u hu) h1 (lt_of_le_of_lt hp hdxr)
        rw [hWeq] at hmem
        exact hmem.2
      have hTpT := continuation hUo (by rw [← hWeq]; exact hFt) (by rw [← hWeq]; exact hFtp)
        (z0 := x) (by rw [← hWeq]; exact hz) hKc hKU ?_
      · rw [hTpT] at hcon; exact absurd hcon (by simp)
      · refine ⟨0, le_rfl, hz.pos_lt, fun t ht htT => ?_⟩
        have htlt : t < τs := by
          have : (t : EReal) < τs := lt_of_lt_of_le htT hcon
          exact_mod_cast this
        have htE := hbelow t ht htlt
        refine ⟨hbd t htE t ⟨ht, le_rfl⟩, ?_⟩
        refine closedBall_subset_cthickening (x := slowPair (y t)) ?_ dx ?_
        · exact ⟨t, ⟨ht, htE.1.2⟩, rfl⟩
        · rw [mem_closedBall_iff_norm]; exact hsp t htE t ⟨ht, le_rfl⟩
    have hτsm : τs ∈ eIoo Tm Tp :=
      ⟨lt_of_lt_of_le (by simpa using hz.neg_lt) (by exact_mod_cast hτs0), hTp⟩
    have hsubS : Icc 0 τs ⊆ eIoo Tm Tp := fun u hu => by
      rcases hu.2.eq_or_lt with h | h
      · rw [h]; exact hτsm
      · exact (hbelow u hu.1 h).2.1 ⟨hu.1, le_rfl⟩
    have hPz : IsSolutionIn F (b.realDom R) (Icc 0 τs) (P ∘ z) := hconj _ _ (hzsol _ hsubS)
    have hyc : ContinuousOn y (Icc 0 τs) := fun u hu =>
      (hycont u ⟨hu.1, hu.2.trans hτs1⟩).continuousWithinAt
    have heqIco : EqOn y (P ∘ z) (Ico 0 τs) := fun u hu =>
      (hbelow u hu.1 hu.2).2.2 u ⟨hu.1, le_rfl⟩
    have heqS : EqOn y (P ∘ z) (Icc 0 τs) :=
      heqIco.of_subset_closure hyc hPz.continuousOn Ico_subset_Icc_self
        (by rw [closure_Ico hpos.ne])
    exact ⟨⟨hτs0, hτs1⟩, hsubS, fun u hu => heqS hu⟩
  have hτst : τs = t1 := by
    by_contra hne
    obtain ⟨τ', hτ'E, hlt⟩ := hopen τs hτsE (lt_of_le_of_ne hτs1 hne)
    exact absurd (le_csSup hbdE hτ'E) (not_le.2 hlt)
  have ht1E : t1 ∈ E := hτst ▸ hτsE
  intro u hu
  have hyu := ht1E.2.2 u hu
  have hzu : z u ∈ b.realDom r := (hzsol _ ht1E.2.1 u hu).1
  refine ⟨?_, ?_⟩
  · rw [hyu]; exact (hconj _ _ (hzsol _ ht1E.2.1) u hu).1
  · have h1 := (hdisp (z u) hzu).1
    have h2 := hbd t1 ht1E u hu
    rw [hyu]
    calc Nrm (fastAction (P (z u)) - b.Ic)
        ≤ Nrm (fastAction (P (z u)) - fastAction (z u)) + Nrm (fastAction (z u) - b.Ic) :=
          htri _ _ _
      _ ≤ d + (Nrm (fastAction (z u) - fastAction x) + Nrm (fastAction x - b.Ic)) :=
          add_le_add h1 (htri _ _ _)
      _ ≤ a + 2*d := by linarith

/-! ### The conditional transfer theorem -/

/-- Conditional helper only. T3 is proved by nonresonant integration or energy_free,
never forwarded as a premise of nonresonant, resonant, block or the provider. -/
theorem transfer_conditional (b : PartialBlock n k) (hbR : 0 < b.rB) (hbw : 0 < b.w)
    {R s r t d dx a : ℝ} {T : ENNReal}
    {H Ht : EC n k → ℂ} {Ψ : EC n k → EC n k} (hc : ExtConjHyp b R s r t H Ht Ψ)
    (Nrm : (Fin n → ℝ) → ℝ) (hN : KAM.Stability.IsActionNorm Nrm)
    (hd : 0 ≤ d) (hdx : 0 ≤ dx) (hdxr : dx < r) (ha : 0 < a) (hgap : d+a < r) (hT : 0 < T)
    (hdisp : ∀ z ∈ b.realDom r, Nrm (fastAction (reExtMap Ψ z)-fastAction z) ≤ d ∧
      ‖slowPair (reExtMap Ψ z)-slowPair z‖ ≤ dx)
    (hpre : ∀ y : ER n k, fastAction y = b.Ic → b.lam • slowPair y ∈ b.S →
      ∃ x ∈ b.realDom r, reExtMap Ψ x = y ∧ Nrm (fastAction x-b.Ic) ≤ d)
    (hT3 : ∀ J : Set ℝ, J.OrdConnected → (0:ℝ) ∈ J → ∀ y : ℝ → ER n k,
      ExtOrbit b r Ht J y → Nrm (fastAction (y 0)-b.Ic) ≤ d →
      (∀ u ∈ J, slowTube b dx (slowPair (y u))) →
      ∀ u ∈ J, ENNReal.ofReal |u| ≤ T → Nrm (fastAction (y u)-fastAction (y 0)) ≤ a)
    (F : ER n k → ER n k) (hF : EqOn F (realWfield b.c (realHamiltonianExt b R H)) (b.realDom R))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u)
    (hI : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    {t1 : ℝ} (ht1 : t1 ∈ J) (htT : ENNReal.ofReal |t1| ≤ T)
    (hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, y u ∈ b.realDom R ∧ Nrm (fastAction (y u)-b.Ic) ≤ a+2*d := by
  obtain ⟨-, hFc, -, -, -, -⟩ := real_system b hc.R_pos hc.s_pos hc.outer
  obtain ⟨-, hFtc, -, -, hFtp, -⟩ := real_system b hc.r_pos hc.t_pos hc.inner
  have hFc' : ContDiffOn ℝ 1 F (b.realDom R) := hFc.congr hF
  have hconj : ∀ (J : Set ℝ) (y : ℝ → ER n k),
      IsSolutionIn (realWfield b.c (realHamiltonianExt b r Ht)) (b.realDom r) J y →
      IsSolutionIn F (b.realDom R) J (reExtMap Ψ ∘ y) := fun J y hy u hu => by
    obtain ⟨hm, hd⟩ := conj b hc hy u hu
    exact ⟨hm, by rw [hF hm]; exact hd⟩
  rcases le_total 0 t1 with ht | ht
  · rw [uIcc_of_le ht]
    refine transfer_core b hbR hbw Nrm hN hdx hdxr hgap (reExtMap Ψ) hdisp hpre
      F _ hFtc hFtp hFc' hconj hT3 ht (fun u hu => hy u (hJ.out h0 ht1 hu)) hI hx
      (by rwa [abs_of_nonneg ht] at htT) (fun u hu => hstop u (by rwa [uIcc_of_le ht]))
  · rw [uIcc_of_ge ht]
    set Ft0 := realWfield b.c (realHamiltonianExt b r Ht) with hFt0
    have hneg : ∀ (G : ER n k → ER n k) (W : Set (ER n k)) (J' : Set ℝ) (w : ℝ → ER n k),
        IsSolutionIn (fun x => -G x) W J' w →
        IsSolutionIn G W (Neg.neg ⁻¹' J') (fun u => w (-u)) := fun G W J' w h => by
      simpa using gen_symmetry_neg h
    have hconj' : ∀ (J' : Set ℝ) (w : ℝ → ER n k),
        IsSolutionIn (fun x => -Ft0 x) (b.realDom r) J' w →
        IsSolutionIn (fun x => -F x) (b.realDom R) J' (reExtMap Ψ ∘ w) := fun J' w hw => by
      have h2 := gen_symmetry_neg (hconj _ _ (hneg _ _ _ _ hw))
      have e : Neg.neg ⁻¹' (Neg.neg ⁻¹' J') = J' := by ext; simp
      rw [e] at h2
      simpa [Function.comp_def] using h2
    have hord : ∀ J' : Set ℝ, J'.OrdConnected → (Neg.neg ⁻¹' J').OrdConnected := fun J' hJ' =>
      ⟨fun x hx y hy z hz => hJ'.out hy hx ⟨by simpa using hz.2, by simpa using hz.1⟩⟩
    have hT3' : ∀ J' : Set ℝ, J'.OrdConnected → (0:ℝ) ∈ J' → ∀ w : ℝ → ER n k,
        IsSolutionIn (fun x => -Ft0 x) (b.realDom r) J' w → Nrm (fastAction (w 0)-b.Ic) ≤ d →
        (∀ u ∈ J', slowTube b dx (slowPair (w u))) →
        ∀ u ∈ J', ENNReal.ofReal |u| ≤ T → Nrm (fastAction (w u)-fastAction (w 0)) ≤ a :=
      fun J' hJ' h0' w hw hw0 htube u hu huT => by
        have := hT3 (Neg.neg ⁻¹' J') (hord J' hJ') (by simpa using h0') (fun u => w (-u))
          (hneg _ _ _ _ hw) (by simpa using hw0) (fun v hv => htube (-v) hv) (-u)
          (by simpa using hu) (by simpa [abs_neg] using huT)
        simpa using this
    have hmem : ∀ u ∈ Icc 0 (-t1), -u ∈ J := fun u hu =>
      hJ.out ht1 h0 ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have key := transfer_core b hbR hbw Nrm hN hdx hdxr hgap (reExtMap Ψ) hdisp hpre
      (fun x => -F x) (fun x => -Ft0 x) hFtc.neg (fun ℓ z hz => by
        show -Ft0 _ = -Ft0 _
        rw [hFtp ℓ z hz])
      hFc'.neg hconj' hT3' (y := fun u => y (-u)) (t1 := -t1) (by linarith)
      (fun u hu => by
        have := (hy (-u) (hmem u hu)).scomp u (hasDerivAt_neg u)
        simpa [Function.comp_def] using this)
      (by simpa using hI) (by simpa using hx)
      (by rw [abs_of_nonpos ht] at htT; exact htT)
      (fun u hu => hstop (-u) (by
        rw [uIcc_of_ge ht]; exact ⟨by linarith [hu.2], by linarith [hu.1]⟩))
    intro u hu
    simpa using key (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩

end KAM.Nekhoroshev

end

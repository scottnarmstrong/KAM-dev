/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteBQWf
public import KAM.CertificateSharp.V2.SmallDivQ
public import KAM.Sharp2.RouteB.Classical
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Fourier certificates of a run of route B

`NumB.Cert` asks for constants at three bites of each prefix stage (`δ_s`, the split bite
`τ/(τ+1) δ_s`, the full bite `min r_s 1`), at every bite `≤ δ_kp` in the tail and at every full bite
`min r_j 1`, `j ≥ kp`.

* `NumBQ.sitesOk`: the prefix sites, each certified (`some`, the balanced checker on the ray of a
  clock frequency) or classical (`none`), by `siteOk` of `V2/SmallDivQ.lean`;
* `NumBQ.tailOk`: the classical constants at `δ_kp` and at `min r_kp 1`; they serve every smaller
  bite (`cohConstC_mono`, `sdConst_classical_of_le`; the full bites decrease along the schedule);
* `NumBQ.cert_ray`: the certificates on the ray `{s ω* : s ≥ 1}` (the isoenergetic scheme);
* `NumBQ.cert_classical`: with every site classical, the certificates on the Diophantine set at
  every scale (the hypothesis `hcert` of `iso_g1_v2B_frozen`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.Sharp2 KAM.Sharp2.RouteB KAM.Sharp2.RouteA

/-- The witnesses of the three sites of each prefix stage. -/
abbrev BSites := List (Option BiteWit × Option BiteWit × Option BiteWit)

namespace NumBQ

variable (Q : NumBQ) (n : ℕ)

/-- The prefix sites. -/
def sitesOk (J : ℕ) (box : FreqBox) (κ γ : ℚ) (sites : BSites) : Bool :=
  (List.range Q.kp).all fun s =>
    siteOk n Q.τ J box κ γ (Q.δ s) (Q.c.getD s Q.ctail) (sites.getD s (none, none, none)).1 &&
    siteOk n Q.τ J box κ γ (Q.split * Q.δ s) (Q.c'.getD s Q.ctail)
      (sites.getD s (none, none, none)).2.1 &&
    siteOk n Q.τ J box κ γ (Q.bfull s) (Q.cbar.getD s Q.cbtail) (sites.getD s (none, none, none)).2.2

/-- The tail: classical constants at `δ_kp` and at `min r_kp 1`. -/
def tailOk (J : ℕ) : Bool :=
  classicalOk n Q.τ J (Q.δ Q.kp) Q.ctail && classicalOk n Q.τ J (Q.bfull Q.kp) Q.cbtail

variable {Q n}

/-- Sharding: `sitesOk` from its stages. -/
theorem sitesOk_of {J : ℕ} {box : FreqBox} {κ γ : ℚ} {sites : BSites}
    (h : ∀ s < Q.kp,
      siteOk n Q.τ J box κ γ (Q.δ s) (Q.c.getD s Q.ctail) (sites.getD s (none, none, none)).1 =
        true ∧
      siteOk n Q.τ J box κ γ (Q.split * Q.δ s) (Q.c'.getD s Q.ctail)
        (sites.getD s (none, none, none)).2.1 = true ∧
      siteOk n Q.τ J box κ γ (Q.bfull s) (Q.cbar.getD s Q.cbtail)
        (sites.getD s (none, none, none)).2.2 = true) :
    Q.sitesOk n J box κ γ sites = true := by
  simp only [sitesOk, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  intro s hs
  obtain ⟨h1, h2, h3⟩ := h s hs
  exact ⟨⟨h1, h2⟩, h3⟩

/-- The schedule facts the certificates need, at rational data. -/
theorem sched_facts (hN : (Q.toNum n).Wf) (s : ℕ) :
    0 < Q.δ s ∧ Q.δ s ≤ 1 ∧ 0 < Q.split * Q.δ s ∧ Q.split * Q.δ s ≤ 1 ∧ 0 < Q.bfull s ∧
      Q.bfull s ≤ 1 := by
  have h1 := hN.δ_pos s
  have h2 := hN.δ_le_one s
  have h3 := hN.bfull_pos s
  have h4 := hN.split_pos
  have h5 := hN.split_lt_one
  rw [cast_δ] at h1 h2
  rw [cast_bfull] at h3
  rw [cast_split] at h4 h5
  have q1 : 0 < Q.δ s := by exact_mod_cast h1
  have q2 : Q.δ s ≤ 1 := by exact_mod_cast h2
  have q4 : 0 < Q.split := by exact_mod_cast h4
  have q5 : Q.split < 1 := by exact_mod_cast h5
  refine ⟨q1, q2, mul_pos q4 q1, ?_, by exact_mod_cast h3, min_le_right _ _⟩
  nlinarith

/-- The full bites decrease along the schedule. -/
theorem bfull_anti (hN : (Q.toNum n).Wf) {j k : ℕ} (h : k ≤ j) :
    (Q.toNum n).bfull j ≤ (Q.toNum n).bfull k :=
  min_le_min_right 1 (hN.r_anti h)

theorem one_le_n (hN : (Q.toNum n).Wf) : 1 ≤ n := by have := hN.two_le; omega

theorem one_le_τ (hN : (Q.toNum n).Wf) : 1 ≤ Q.τ := by
  have h : (1 : ℝ) ≤ (Q.τ : ℝ) := hN.τ_ge
  exact_mod_cast h

/-- The tail certificates on any set of Diophantine vectors. -/
theorem cert_tail (hN : (Q.toNum n).Wf) {J : ℕ} (ht : Q.tailOk n J = true) {γ : ℝ} (hγ : 0 < γ)
    {Ω : Set (Fin n → ℝ)} (hΩ : Ω ⊆ {ω | IsDiophantine γ (Q.τ : ℝ) ω}) :
    (∀ b, 0 < b → b ≤ (Q.toNum n).δ (Q.toNum n).kp →
      SDConst n (Q.toNum n).τ γ b (Q.toNum n).ctail Ω) ∧
    ∀ j, (Q.toNum n).kp ≤ j → SDConst n (Q.toNum n).τ γ ((Q.toNum n).bfull j)
      (Q.toNum n).cbtail Ω := by
  simp only [tailOk, Bool.and_eq_true] at ht
  have hn := one_le_n hN
  have hδ := sched_facts hN Q.kp
  refine ⟨fun b hb hle => ?_, fun j hj => ?_⟩
  · have h1 := sdConst_classical (n := n) hn hN.τ_ge hγ hb (hle.trans (hN.δ_le_one _))
    have h2 : cohConstC n (Q.toNum n).τ b ≤ (Q.toNum n).ctail := by
      refine (cohConstC_mono hN.τ_ge hb.le hle).trans ?_
      rw [cast_δ]
      exact cohConstC_le_of_ok hδ.1.le ht.1
    exact sdConst_subset (sdConst_mono hγ h1 h2) hΩ
  · have hb1 : (Q.toNum n).bfull Q.kp ≤ 1 := by rw [cast_bfull]; exact_mod_cast hδ.2.2.2.2.2
    have h1 := sdConst_classical_of_le (n := n) hn hN.τ_ge hγ (hN.bfull_pos j)
      (bfull_anti hN hj) hb1
    have h2 : cohConstC n (Q.toNum n).τ ((Q.toNum n).bfull Q.kp) ≤ (Q.toNum n).cbtail := by
      rw [cast_bfull]
      exact cohConstC_le_of_ok hδ.2.2.2.2.1.le ht.2
    exact sdConst_subset (sdConst_mono hγ h1 h2) hΩ

/-- **The certificates on the ray**, from the prefix sites and the classical tail. -/
theorem cert_ray (hN : (Q.toNum n).Wf) {J : ℕ} {box : FreqBox} {κ γ : ℚ} {sites : BSites}
    (hs : Q.sitesOk n J box κ γ sites = true) (ht : Q.tailOk n J = true) (hγ : 0 < γ)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n box ωstar)
    (hdio : IsDiophantine (γ : ℝ) (Q.τ : ℝ) ωstar) : (Q.toNum n).Cert γ (ray ωstar) := by
  simp only [sitesOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  have hn := one_le_n hN
  have hτ := one_le_τ hN
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hsub : ray ωstar ⊆ {ω | IsDiophantine (γ : ℝ) (Q.τ : ℝ) ω} := by
    rintro ω ⟨t, ht, rfl⟩
    exact isDiophantine_ray hdio ht
  obtain ⟨htail, htbar⟩ := cert_tail hN ht hγ' hsub
  refine ⟨fun s hsk => ?_, fun s hsk => ?_, fun s hsk => ?_, htail, htbar⟩
  · have hf := sched_facts hN s
    rw [cast_δ]
    exact sdConst_of_siteOk hn hτ hγ hf.1 hf.2.1 (hs s hsk).1.1 hω hdio
  · have hf := sched_facts hN s
    rw [cast_split, cast_δ, ← Rat.cast_mul]
    exact sdConst_of_siteOk hn hτ hγ hf.2.2.1 hf.2.2.2.1 (hs s hsk).1.2 hω hdio
  · have hf := sched_facts hN s
    rw [cast_bfull]
    exact sdConst_of_siteOk hn hτ hγ hf.2.2.2.2.1 hf.2.2.2.2.2 (hs s hsk).2 hω hdio

/-- **The classical certificates on the Diophantine set**, at every scale: every site
classical (`NumB.cert_of_le`). -/
theorem cert_classical (hN : (Q.toNum n).Wf) {J : ℕ} {box : FreqBox} {κ γ : ℚ}
    (hs : Q.sitesOk n J box κ γ [] = true) (ht : Q.tailOk n J = true) {γ' : ℝ} (hγ : 0 < γ') :
    (Q.toNum n).Cert γ' {ω | IsDiophantine γ' (Q.toNum n).τ ω} := by
  simp only [sitesOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.getD_nil] at hs
  simp only [tailOk, Bool.and_eq_true] at ht
  have hk := sched_facts hN Q.kp
  refine NumB.cert_of_le hN hγ (fun s hsk => ?_) (fun s hsk => ?_) (fun s hsk => ?_) ?_ ?_
  · rw [cast_δ]; exact cohConstC_le_of_ok (sched_facts hN s).1.le (hs s hsk).1.1
  · rw [cast_split, cast_δ, ← Rat.cast_mul]
    exact cohConstC_le_of_ok (sched_facts hN s).2.2.1.le (hs s hsk).1.2
  · rw [cast_bfull]; exact cohConstC_le_of_ok (sched_facts hN s).2.2.2.2.1.le (hs s hsk).2
  · rw [cast_δ]; exact cohConstC_le_of_ok hk.1.le ht.1
  · rw [cast_bfull]; exact cohConstC_le_of_ok hk.2.2.2.2.1.le ht.2

end NumBQ

end KAM.CertificateSharp.V2

end

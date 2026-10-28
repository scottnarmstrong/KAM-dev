/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ExtensionTubeData
public import KAM.Planetary.PGAssembly.ExtensionDefs

/-!
# P Part 5: the periodized extension `tubeP` (`stepP:p5:ext-per`)

From a `PGTube d` define `tubeP T mu z = F (pack mu (z - ι (fastShift k)))` for any `k` for which
the packed point lies in the thin tube (`Valid`); the value is independent of `k` by the shift
identities of `PGTube`. Holomorphy, joint continuity, periodicity, the bound and the agreement
with `d.P` on the real points of the closed cylinder are proved here.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-EX.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology Function

namespace KAM.Planetary

variable {a b : ℕ}

theorem fastShift_add (k m : Fin a → ℤ) :
    (fastShift (b := b) (k + m) : Phase (a + b)) = fastShift k + fastShift m := by
  refine Prod.ext ?_ ?_
  · funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [fastShift, mul_add]
    · simp [fastShift]
  · simp [fastShift]

theorem fastShift_fst_castAdd (k : Fin a → ℤ) (i : Fin a) :
    (fastShift (b := b) k : Phase (a + b)).1 (Fin.castAdd b i) = 2 * Real.pi * (k i : ℝ) := by
  simp [fastShift]

theorem realInclusion_pgShift (m : Fin a → ℤ) :
    KAM.realInclusion _ (pgShift a b m) =
      packVec (0 : ℂ) (KAM.realInclusion₂ (a + b) (fastShift m)) := by
  rw [pgShift, realInclusion_packVec, Complex.ofReal_zero]

/-- The packed point of `z` shifted back by `k` lies in the thin tube. -/
def PGTube.Valid {d : PGData a b} (T : PGTube d) (mu : ℝ) (z : PGComplexPhase (a + b))
    (k : Fin a → ℤ) : Prop :=
  packVec (mu : ℂ) (z - KAM.realInclusion₂ (a + b) (fastShift k)) ∈
    KAM.actionNbhd (pgX d) T.rho

open Classical in
/-- The periodized extension. -/
def PGTube.P {d : PGData a b} (T : PGTube d) (mu : ℝ) (z : PGComplexPhase (a + b)) : ℂ :=
  if h : ∃ k, T.Valid mu z k then
    T.F (packVec (mu : ℂ) (z - KAM.realInclusion₂ (a + b) (fastShift h.choose))) else 0

theorem PGTube.valid_angle {d : PGData a b} (T : PGTube d) {mu : ℝ} {z : PGComplexPhase (a + b)}
    {k : Fin a → ℤ} (hk : T.Valid mu z k) (i : Fin a) :
    -T.rho < (z.1 (Fin.castAdd b i)).re - 2 * Real.pi * k i ∧
      (z.1 (Fin.castAdd b i)).re - 2 * Real.pi * k i < 2 * Real.pi + T.rho := by
  obtain ⟨J, ⟨⟨mu', w⟩, ⟨hmu', hw⟩, rfl⟩, hJ⟩ := mem_actionNbhd_iff.1 hk
  have h1 := (norm_le_pi_norm _ (Fin.succ (Fin.castAdd (a + b) (Fin.castAdd b i)))).trans_lt hJ
  rw [realInclusion_packVec] at h1
  simp only [Pi.sub_apply, packVec_fst, Prod.fst_sub, KAM.realInclusion₂_apply,
    KAM.realInclusion_apply] at h1
  have h2 := (Complex.abs_re_le_norm _).trans_lt h1
  have h3 : ((z.1 (Fin.castAdd b i) - (((fastShift (b := b) k : Phase (a + b)).1
      (Fin.castAdd b i) : ℝ) : ℂ)) - ((w.1 (Fin.castAdd b i) : ℝ) : ℂ)).re =
      (z.1 (Fin.castAdd b i)).re - 2 * Real.pi * k i - w.1 (Fin.castAdd b i) := by
    simp [fastShift_fst_castAdd]
  rw [h3, abs_lt] at h2
  have hw1 := hw.1 i
  constructor <;> linarith [hw1.1, hw1.2]

theorem PGTube.valid_diff {d : PGData a b} (T : PGTube d) {mu : ℝ} {z : PGComplexPhase (a + b)}
    {k k' : Fin a → ℤ} (hk : T.Valid mu z k) (hk' : T.Valid mu z k') (i : Fin a) :
    |(k' - k) i| ≤ 1 := by
  have h1 := T.valid_angle hk i
  have h2 := T.valid_angle hk' i
  have hpi := Real.pi_gt_three
  have hr := T.rho_le
  have hlt : |((k' i - k i : ℤ) : ℝ)| < 2 := by
    rw [abs_lt]
    push_cast
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have : |k' i - k i| < 2 := by exact_mod_cast hlt
  simp only [Pi.sub_apply]
  omega

theorem PGTube.P_eq {d : PGData a b} (T : PGTube d) {mu : ℝ} {z : PGComplexPhase (a + b)}
    {k : Fin a → ℤ} (hk : T.Valid mu z k) :
    T.P mu z = T.F (packVec (mu : ℂ) (z - KAM.realInclusion₂ (a + b) (fastShift k))) := by
  have hex : ∃ k, T.Valid mu z k := ⟨k, hk⟩
  have hspec := hex.choose_spec
  simp only [PGTube.P, hex, ↓reduceDIte]
  set k0 := hex.choose
  have hm := T.valid_diff hspec hk
  have hsub : z - KAM.realInclusion₂ (a + b) (fastShift k0) -
      KAM.realInclusion₂ (a + b) (fastShift (k - k0)) =
      z - KAM.realInclusion₂ (a + b) (fastShift k) := by
    rw [sub_sub, ← map_add, ← fastShift_add]; simp
  have hglue := T.hglue (k - k0) hm _ hspec (by
    rw [realInclusion_pgShift, packVec_sub, sub_zero, hsub]
    exact hk)
  rw [hglue, realInclusion_pgShift, packVec_sub, sub_zero, hsub]

end KAM.Planetary

end

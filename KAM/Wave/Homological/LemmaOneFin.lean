/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneAssembly
public import KAM.Wave.Homological.Schur
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite-support expansions of the pairings (`bpW:w4:lemma1`, step *The equation*, algebra)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

* `homPairOmegaRaw_gen ha hp hpb W c z = ∑ (D ĉ)_j Ω_j z_j`, the pairing `⟨c, Ωz⟩₀` of `L_N`
    (`bpW:w4:lie`);
* for `z, z'` supported in a finite set `S`, the pairings are finite sums over `S`
  (`homPairRep_fin_gen`, `homPairRep_op_fin_gen`, `homPairOmega_fin_gen`,
      `homPairOmega_op_fin_gen`), with the
  entries `S(M)_ij = (ΛM)_ij = D_i M̂_ij` (`homSent_gen`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- INTERNAL totalized `∑' j, (D ĉ)_j Ω_j z_j` (zero on divergent series); use the source-domain
`homPairOmega_gen`, which carries `HomOmegaCarrier`. -/
def homPairOmegaRaw_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (W : ℕ+ → ℝ) (c z :
    HomL2) :
    ℂ :=
  ∑' j, homLamDiag_gen ha (homPP hp hpb) c j * (W j : ℂ) * z j

/-- **Carrier evidence** for the pairing `⟨c, Ωz⟩₀`: the series `∑_j (D ĉ)_j Ω_j z_j` converges for
all `c, z ∈ ℓ^N_{a,p}` (true under `|Ω_j| ≤ K₀(j+2)`, `1 ≤ p + p_+`, `homOmegaCarrier_of_bound`, or
under the guard (G), `homOmegaCarrier_of_guard`). -/
def HomOmegaCarrier {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (W : ℕ+ → ℝ) : Prop :=
  ∀ c z : HomL2, Summable fun j => homLamDiag_gen ha (homPP hp hpb) c j * (W j : ℂ) * z j

/-- **The pairing `⟨c, Ωz⟩₀`** on the source domain (`bpW:w4:lie`): defined under the carrier
evidence `HomOmegaCarrier`; `homPairOmega_hasSum_gen` is the convergent-sum characterization. -/
def homPairOmega_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {W : ℕ+ → ℝ}
    (_hC : HomOmegaCarrier ha hp hpb W) (c z : HomL2) : ℂ :=
  homPairOmegaRaw_gen ha hp hpb W c z

theorem homPairOmega_hasSum_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    {W : ℕ+ → ℝ} (hC : HomOmegaCarrier ha hp hpb W) (c z : HomL2) :
    HasSum (fun j => homLamDiag_gen ha (homPP hp hpb) c j * (W j : ℂ) * z j)
      (homPairOmega_gen ha hp hpb hC c z) :=
  (hC c z).hasSum

/-- The entries `S(M)_ij = D_i M̂_ij` of `ΛM`. -/
def homSent_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (M : HomOp) (i j : ℕ+) : ℂ :=
  kamEntry (homLamCLM_gen ha (homPP hp hpb) M) i j

theorem homOp_apply_fin (M : HomOp) {z : HomL2} {S : Finset ℕ+} (hz : ∀ j ∉ S, z j = 0)
    (i : ℕ+) : M z i = ∑ j ∈ S, kamEntry M i j * z j := by
  rw [← (homOp_hasSum M z i).tsum_eq]
  exact tsum_eq_sum fun j hj => by rw [hz j hj, mul_zero]

theorem homPairRep_fin_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (c : HomL2) {z :
    HomL2}
    {S : Finset ℕ+} (hz : ∀ j ∉ S, z j = 0) :
    homPairRep_gen ha (homPP hp hpb) c z = ∑ j ∈ S, homLamDiag_gen ha (homPP hp hpb) c j * z j :=
  tsum_eq_sum fun j hj => by rw [hz j hj, mul_zero]

theorem homPairRep_op_fin_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (M : HomOp) {z
    z' :
    HomL2}
    {S : Finset ℕ+} (hz : ∀ j ∉ S, z j = 0) (hz' : ∀ j ∉ S, z' j = 0) :
    homPairRep_gen ha (homPP hp hpb) (M z) z' = ∑ i ∈ S, ∑ j ∈ S, homSent_gen ha hp hpb M i j * z j
        * z' i
        := by
  rw [homPairRep_fin_gen ha hp hpb _ hz']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [homLamDiag_apply_gen, homOp_apply_fin M hz i, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [homSent_gen, kamEntry_homLamCLM_gen]
  ring

theorem homPairOmega_fin_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (W : ℕ+ → ℝ) (c :
    HomL2)
    {z : HomL2} {S : Finset ℕ+} (hz : ∀ j ∉ S, z j = 0) :
    homPairOmegaRaw_gen ha hp hpb W c z = ∑ j ∈ S, homLamDiag_gen ha (homPP hp hpb) c j * (W j : ℂ)
      *
        z j :=
  tsum_eq_sum fun j hj => by rw [hz j hj, mul_zero]

theorem homPairOmega_op_fin_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (W : ℕ+ → ℝ)
    (M :
    HomOp)
    {z z' : HomL2} {S : Finset ℕ+} (hz : ∀ j ∉ S, z j = 0) (hz' : ∀ j ∉ S, z' j = 0) :
    homPairOmegaRaw_gen ha hp hpb W (M z) z' =
      ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * homSent_gen ha hp hpb M i j * z j * z' i := by
  rw [homPairOmega_fin_gen ha hp hpb W _ hz']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [homLamDiag_apply_gen, homOp_apply_fin M hz i]
  have : homLamD_gen a p pb i * (∑ j ∈ S, kamEntry M i j * z j) * (W i : ℂ) * z' i =
      ∑ j ∈ S, (W i : ℂ) * (homLamD_gen a p pb i * kamEntry M i j) * z j * z' i := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [homSent_gen, kamEntry_homLamCLM_gen]

end KAM.Wave

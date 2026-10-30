/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Kernel.Stage
public import KAM.Certificate.Arith.Rat

/-!
# Stage-memoization tests

Toy recipes in `ℚ` in the shape of design SO-CSPLIT §3.4: every stage is a separate theorem
`t = lit` (by `decide +kernel`), the table lemmas move the stages under the landed binders, and the
residual is one `decide +kernel` on literals. Each recipe's result is compared with the monolithic
`decide +kernel` run of the landed definition. Data are copies of `KAM.Certificate.Tests.Torsion`
(exposed so that the kernel can unfold them), with the flat embedding `K(θ) = (θ, 1)` and the Gram
witness `B = 1`, so that every stage literal is short.

* **Products.** `matMulEntry_eq_of_products` with two separately proved products and
  `modelMatMul_eq_of_entries` reproduce a `1 × 2` by `2 × 1` product with genuine radii.
* **Gram.** One entry stage, `gramModels_eq_of_entries`, one `B·G` stage,
  `gramDefectRows_eq_of_entries` and `gramCheck_eq_of_rows` give `gramCheck = some (0, 1)`.
* **Torsion and frames.** Thirteen stages and `torsionModels_eq_of_stages` give the bordered
  torsion models; `frameNModels_eq_of_stage` reuses torsion's `[4,0]` literal.

**R7 timing note.** Profiled on 2026-10-30 (`lake env lean -Dprofiler=true`, no option kept in
the file): the whole module type-checks in about 1.1-1.5 s, no single declaration above 0.5 s, and
the recipes (stage theorems, table lemmas, residual) cost no more than the monolithic `_whole`
runs; the stage equalities are applied, not re-evaluated through defeq. On toys this small the test
cannot separate the residual from the stages; the at-scale R7 measurement is the CAL-2 gate's.
-/

@[expose] public section

namespace KAM.Certificate

open KAM.CertificateSharp CertArith

deriving instance DecidableEq for CC
deriving instance DecidableEq for CertPoly
deriving instance DecidableEq for CertModel

/-! ### Data (copied from `KAM.Certificate.Tests.Torsion`; flat embedding) -/

def stageW : CertWeight := ⟨1 / 100, 11 / 10⟩

def stagePi : PiEnclosure ℚ := ⟨314159 / 100000, 1 / 10000, 5, 2⟩

/-- Every torsion, Gram and composition product key, advised `direct`. -/
def stageCfg : ModelConfig ℚ :=
  ⟨100, 10, 4, fun _ _ => none,
    (((List.range 11).flatMap fun t => (List.range 4).flatMap fun i => (List.range 4).flatMap
      fun j => (List.range 4).map fun k => [4, t, i, j, k]) ++
     ((List.range 2).flatMap fun t => (List.range 4).flatMap fun i => (List.range 4).flatMap
      fun j => (List.range 4).map fun k => [3, t, i, j, k]) ++
     ((List.range 32).map fun k => [0, k])).map fun key => (key, .direct)⟩

/-- The flat embedding `K(θ) = (θ, 1)`. -/
def stageK : CertEmbedding ℚ := ⟨[-1], [⟨0, []⟩], [0], [⟨1, []⟩]⟩

/-- `H = I²/2`. -/
def stageH : HamExpr 1 := .mul (.const (1 / 2)) (.mul (.action 0) (.action 0))

def stageB : List (List (CertPoly ℚ)) := [[⟨[([0], ⟨1, 0⟩)]⟩]]

def stageWit : Witnesses ℚ := ⟨[], [], [], []⟩

def stageBox : FreqBox := [(1, 1 / 1000)]

/-- The constant model `x` with radius `r` (key `[0]`). -/
def stageC (x r : ℚ) : CertModel ℚ := ⟨0, ⟨[([0], ⟨x, 0⟩)]⟩, r⟩

/-- The empty model. -/
def stageO : CertModel ℚ := ⟨0, ⟨[]⟩, 0⟩

/-! ### Products -/

def stageA : ModelMatrix ℚ := [[stageC 2 (1 / 100), stageC 3 0]]

def stageBm : ModelMatrix ℚ := [[stageC 5 0], [stageC (-1) (1 / 1000)]]

theorem stage_product0 :
    CertModel.mul stageW stageCfg ([4, 10] ++ [0, 0, 0]) (modelMatrixEntry stageA 0 0)
      (modelMatrixEntry stageBm 0 0) = stageC 10 (1 / 20) := by
  decide +kernel

theorem stage_product1 :
    CertModel.mul stageW stageCfg ([4, 10] ++ [0, 0, 1]) (modelMatrixEntry stageA 0 1)
      (modelMatrixEntry stageBm 1 0) = stageC (-3) (3 / 1000) := by
  decide +kernel

/-- The entry from its two memoized products; the residual sums literals. -/
theorem stage_entry :
    matMulEntry stageW stageCfg stagePi [4, 10] 2 stageA stageBm 0 0 = stageC 7 (53 / 1000) := by
  rw [matMulEntry_eq_of_products (Pk := fun k => if k = 0 then stageC 10 (1 / 20)
    else stageC (-3) (3 / 1000))]
  · decide +kernel
  · intro k hk
    rcases k with _ | _ | k
    · exact stage_product0
    · exact stage_product1
    · omega

theorem stage_matMul :
    modelMatMul stageW stageCfg stagePi [4, 10] 1 2 1 stageA stageBm = [[stageC 7 (53 / 1000)]] :=
  modelMatMul_eq_of_entries _ _ _ _ _ _ _ _ _ rfl (by decide) fun i hi j hj => by
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 0 := by omega
    exact stage_entry

/-- The monolithic run agrees. -/
theorem stage_matMul_whole :
    modelMatMul stageW stageCfg stagePi [4, 10] 1 2 1 stageA stageBm =
      [[stageC 7 (53 / 1000)]] := by
  decide +kernel

/-! ### Gram -/

theorem stage_gramEntry : gramEntryModel 1 stageK stageW stageCfg stagePi 0 0 = stageC 1 0 := by
  decide +kernel

theorem stage_gramModels : gramModels 1 stageK stageW stageCfg stagePi = [[stageC 1 0]] := by
  rw [gramModels_eq_of_entries (E := fun _ _ => stageC 1 0) _ _ _ _ _ fun a ha b hb _ => by
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    exact stage_gramEntry]
  decide +kernel

theorem stage_gramBG : gramBGModel 1 stageB [[stageC 1 0]] stageW stageCfg stagePi 0 0 =
    stageC 1 0 := by
  decide +kernel

theorem stage_gramRows :
    gramDefectRows 1 stageB (gramModels 1 stageK stageW stageCfg stagePi) stageW stageCfg
      stagePi = [0] := by
  rw [stage_gramModels, gramDefectRows_eq_of_entries (T := fun _ _ => stageC 1 0) _ _ _ _ _ _
    fun i hi j hj => by
      obtain rfl : i = 0 := by omega
      obtain rfl : j = 0 := by omega
      exact stage_gramBG]
  decide +kernel

theorem stage_gramCheck : gramCheck 1 stageK stageB stageW stageCfg stagePi 2 = some (0, 1) := by
  rw [gramCheck_eq_of_rows _ _ _ _ _ _ _ (by decide +kernel) stage_gramRows]
  decide +kernel

theorem stage_gramCheck_whole :
    gramCheck 1 stageK stageB stageW stageCfg stagePi 2 = some (0, 1) := by
  decide +kernel

/-! ### Torsion and frames -/

/-- The bordered torsion models of the flat toy. -/
def stageT : ModelMatrix ℚ := [[stageC 1 0, stageC 1 (1 / 1000)], [stageC 1 0, stageO]]

theorem stage_eps : gramInvRadius ((0, 1) : ℚ × ℚ) = some 0 := by decide +kernel

theorem stage_ms : Slp.compose 1 stageH.jet.prog stageK stageWit stageW stageCfg stagePi
    (torsionSlots 1 stageH.jet) =
      some [stageC 0 0, stageC 1 0, stageC 0 0, stageC 0 0, stageC 0 0, stageC 1 0] := by
  decide +kernel

theorem stage_L : dkModels 1 stageK stageW stagePi = [[stageC 1 0], [stageO]] := by
  decide +kernel

theorem stage_Gi : gramInvModels 1 stageB 0 = [[stageC 1 0]] := by decide +kernel

theorem stage_DL :
    dkwModels 1 stageK stageBox 1 stageW stageCfg stagePi = [[stageO], [stageO]] := by
  decide +kernel

theorem stage_N0 : modelMatMul stageW stageCfg stagePi [4, 0] (1 + 1) 1 1 [[stageC 1 0], [stageO]]
    [[stageC 1 0]] = [[stageC 1 0], [stageO]] := by
  decide +kernel

theorem stage_torsion :
    torsionModels 1 stageH stageK stageWit stageB (0, 1) stageBox 1 stageW stageCfg stagePi =
      some stageT := by
  rw [torsionModels_eq_of_stages _ _ _ _ _ _ _ _ _ _ _ stage_eps stage_ms stage_L stage_Gi stage_DL
    stage_N0 (DG1 := [[stageO]]) (by decide +kernel) (DG2 := [[stageO]]) (by decide +kernel)
    (DGi0 := [[stageO]]) (by decide +kernel) (DGi1 := [[stageO]]) (by decide +kernel)
    (DN1 := [[stageO], [stageO]]) (by decide +kernel) (DN2 := [[stageO], [stageO]])
    (by decide +kernel) (XN1 := [[stageC 1 0], [stageC 0 0]]) (by decide +kernel)
    (Tb := [[stageC 1 0]]) (by decide +kernel) (Y := [[stageC 1 0]]) (by decide +kernel)]
  decide +kernel

theorem stage_torsion_whole :
    torsionModels 1 stageH stageK stageWit stageB (0, 1) stageBox 1 stageW stageCfg stagePi =
      some stageT := by
  decide +kernel

/-- `frameNModels` from torsion's `[4,0]` literal: nothing is recomputed. -/
theorem stage_frameN : frameNModels 1 stageK stageB 0 stageW stageCfg stagePi =
    modelMatOmega 1 1 [[stageC 1 0], [stageO]] :=
  frameNModels_eq_of_stage _ _ _ _ _ _ _ stage_L stage_Gi stage_N0

theorem stage_frameN_whole : frameNModels 1 stageK stageB 0 stageW stageCfg stagePi =
    modelMatOmega 1 1 [[stageC 1 0], [stageO]] := by
  decide +kernel

end KAM.Certificate

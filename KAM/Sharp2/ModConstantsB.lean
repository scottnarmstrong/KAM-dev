/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModConstantsB.Mono2

/-!
# Positivity and monotonicity of the repaired step constants (v2, route B)

`stepConstsB_nonneg`, `stepConstsB_mono`, `stepCondB_anti` (signatures verbatim from
`docs/campaign/design/APOST-SHARP-V2-SIGNATURES.lean.txt`, lines wrapped). The definitions are in
`ModConstantsB.Defs`; the work is one lemma per `let` (`ModConstantsB.Data`, `.Nonneg`, `.Mono1`,
`.Mono2`).
-/

@[expose] public noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace KAM.Sharp2

/-- `stepConstsB` through the helpers (`rfl`). -/
theorem stepConstsB_eq (p : StepInB) : stepConstsB p =
    ⟨sCΩ p, sCEL p, sCEN p, sCE p, sCDE p, sC0 p, sCxiN p, sCKt p, sCDLt p, sCDLtT p, sCEt p,
      sQtN p, sCgL p, sCxiL p, sCDK p, sCEb p, sCG p, sCBb p, sCNb p, sCNbT p, sCab p, sBsup p,
      sBloc p, sQbN p, sQL p, sQ p, sCnu p⟩ := rfl

/-- Nonnegativity of every constant on admissible inputs (the engine's `hnn`). -/
theorem stepConstsB_nonneg {p : StepInB} (hp : p.Ok) :
    0 ≤ (stepConstsB p).Q ∧ 0 ≤ (stepConstsB p).CDK ∧ 0 ≤ (stepConstsB p).CBb ∧
      0 ≤ (stepConstsB p).CNb ∧ 0 ≤ (stepConstsB p).CNbT ∧ 0 ≤ (stepConstsB p).Cab ∧
      0 ≤ (stepConstsB p).Bloc ∧ 0 ≤ (stepConstsB p).Cnu :=
  ⟨nn_sQ hp, nn_sCDK hp, nn_sCBb hp, nn_sCNb hp, nn_sCNbT hp, nn_sCab hp, nn_sBloc hp,
    nn_sCnu hp⟩

/-- The step conditions through the helpers. -/
def condH (p : StepInB) (X : ℝ) : Prop :=
  max 1 (p.sB ^ 2) * sCΩ p * sg p * X ≤ p.q ∧ sCDE p * sg p * X ≤ p.n ∧ sCxiL p * X ≤ p.θξ ∧
    sCΩ p * sCgL p * X ≤ p.θΩ ∧ sCKt p * (sg p * p.δ) * X ≤ 1 ∧ sCDLt p * sg p * X ≤ p.θ * p.sK ∧
    sCDLtT p * sg p * X ≤ p.θ * p.sLt ∧ p.sB * sCG p * sCDK p * X ≤ p.θ ∧ sBsup p * X ≤ p.ts ∧
    sBloc p * X ≤ p.bF ∧ (p.iso = true → sC0 p * (sg p * p.δ) * X ≤ p.θω) ∧
    (p.selfcons = true → sCNbT p * sCEL p * X ≤ p.θN ∧
      max 1 (p.sB ^ 2) * (1 + p.n * p.θξ) ^ 2 * sCΩ p * sQtN p * sg p * X ^ 2 ≤ p.q)

theorem stepCondB_eq (p : StepInB) (X : ℝ) : stepCondB p X ↔ condH p X := Iff.rfl

/-- Monotonicity (the engine's `htail`): every constant is nondecreasing, and the conditions of
the dominating input imply those of the dominated one. Holds for iso as well (SHARP2-B3 signal
resolved: no `1/C_ξL`). -/
theorem stepConstsB_mono {p p' : StepInB} (hp : p.Ok) (hp' : p'.Ok) (hd : p.Dom p') :
    (stepConstsB p).Q ≤ (stepConstsB p').Q ∧ (stepConstsB p).CDK ≤ (stepConstsB p').CDK ∧
      (stepConstsB p).CBb ≤ (stepConstsB p').CBb ∧ (stepConstsB p).CNb ≤ (stepConstsB p').CNb ∧
      (stepConstsB p).CNbT ≤ (stepConstsB p').CNbT ∧ (stepConstsB p).Cab ≤ (stepConstsB p').Cab ∧
      (stepConstsB p).Cnu ≤ (stepConstsB p').Cnu ∧
      ∀ X, 0 ≤ X → stepCondB p' X → stepCondB p X := by
  have hl := hd.toLe
  refine ⟨mo_sQ hp hp' hl, mo_sCDK hp hp' hl, mo_sCBb hp hp' hl, mo_sCNb hp hp' hl,
    mo_sCNbT hp hp' hl, mo_sCab hp hp' hl, mo_sCnu hp hp' hl, ?_⟩
  intro X hX hc
  have hc : condH p' X := hc
  show condH p X
  have a1 := nn_sCΩ hp; have a2 := nn_sCDE hp; have a3 := nn_sCxiL hp; have a4 := nn_sCgL hp
  have a5 := nn_sCKt hp; have a6 := nn_sCDLt hp; have a7 := nn_sCDLtT hp; have a8 := nn_sCG hp
  have a9 := nn_sCDK hp; have a10 := nn_sBsup hp; have a11 := nn_sBloc hp; have a12 := nn_sC0 hp
  have a13 := nn_sCNbT hp; have a14 := nn_sCEL hp; have a15 := nn_sQtN hp; have a16 := nn_sg hp
  have a1' := nn_sCΩ hp'; have a2' := nn_sCDE hp'; have a3' := nn_sCxiL hp'
  have a4' := nn_sCgL hp'; have a5' := nn_sCKt hp'; have a6' := nn_sCDLt hp'
  have a7' := nn_sCDLtT hp'; have a8' := nn_sCG hp'; have a9' := nn_sCDK hp'
  have a10' := nn_sBsup hp'; have a11' := nn_sBloc hp'; have a12' := nn_sC0 hp'
  have a13' := nn_sCNbT hp'; have a14' := nn_sCEL hp'; have a15' := nn_sQtN hp'
  have a16' := nn_sg hp'
  have b1 := mo_sCΩ hp hp' hl; have b2 := mo_sCDE hp hp' hl; have b3 := mo_sCxiL hp hp' hl
  have b4 := mo_sCgL hp hp' hl; have b5 := mo_sCKt hp hp' hl; have b6 := mo_sCDLt hp hp' hl
  have b7 := mo_sCDLtT hp hp' hl; have b8 := mo_sCG hp hp' hl; have b9 := mo_sCDK hp hp' hl
  have b10 := mo_sBsup hp hp' hl; have b11 := mo_sBloc hp hp' hl; have b12 := mo_sC0 hp hp' hl
  have b13 := mo_sCNbT hp hp' hl; have b14 := mo_sCEL hp hp' hl; have b15 := mo_sQtN hp hp' hl
  have b16 := mo_sg hp hp' hl
  unfold condH at hc ⊢
  try simp only [hl.n, hl.sB, hl.q, hl.θξ, hl.θΩ, hl.θ, hl.sK, hl.sLt, hl.ts, hl.bF, hl.iso,
    hl.θω, hl.selfcons, hl.θN] at hc ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := hc
  obtain ⟨⟩ := hp.flat
  obtain ⟨⟩ := hp'.flat
  obtain ⟨⟩ := hl
  refine ⟨le_trans (by gcongr) c1, le_trans (by gcongr) c2, le_trans (by gcongr) c3,
    le_trans (by gcongr) c4, le_trans (by gcongr) c5, le_trans (by gcongr) c6,
    le_trans (by gcongr) c7, le_trans (by gcongr) c8, le_trans (by gcongr) c9,
    le_trans (by gcongr) c10, fun hi => le_trans (by gcongr) (c11 hi),
    fun hs => ⟨le_trans (by gcongr) (c12 hs).1, le_trans (by gcongr) (c12 hs).2⟩⟩

/-- Downward closure of the conditions (the engine's `hcondT`). -/
theorem stepCondB_anti {p : StepInB} (hp : p.Ok) {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y)
    (hY : stepCondB p Y) : stepCondB p X := by
  have hY : condH p Y := hY
  show condH p X
  have a1 := nn_sCΩ hp; have a2 := nn_sCDE hp; have a3 := nn_sCxiL hp; have a4 := nn_sCgL hp
  have a5 := nn_sCKt hp; have a6 := nn_sCDLt hp; have a7 := nn_sCDLtT hp; have a8 := nn_sCG hp
  have a9 := nn_sCDK hp; have a10 := nn_sBsup hp; have a11 := nn_sBloc hp; have a12 := nn_sC0 hp
  have a13 := nn_sCNbT hp; have a14 := nn_sCEL hp; have a15 := nn_sQtN hp; have a16 := nn_sg hp
  unfold condH at hY ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := hY
  obtain ⟨⟩ := hp.flat
  refine ⟨le_trans (by gcongr) c1, le_trans (by gcongr) c2, le_trans (by gcongr) c3,
    le_trans (by gcongr) c4, le_trans (by gcongr) c5, le_trans (by gcongr) c6,
    le_trans (by gcongr) c7, le_trans (by gcongr) c8, le_trans (by gcongr) c9,
    le_trans (by gcongr) c10, fun hi => le_trans (by gcongr) (c11 hi),
    fun hs => ⟨le_trans (by gcongr) (c12 hs).1, le_trans (by gcongr) (c12 hs).2⟩⟩

end KAM.Sharp2

end

/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.StepsSeq
public import KAM.Nekhoroshev.NormalForm.StepsInduct
public import KAM.Nekhoroshev.NormalForm.StepsOut
public import KAM.Nekhoroshev.NormalForm.StepsCaseB

/-!
# The Normal Form Lemma: the step sequence (facade)

Re-exports `StepsSeq` (`nfState`, `NFHyp`, `NFInv`, the decomposition of `g_{i-1}`), `StepsInduct`
(`nf_hyp`, `nf_inv_succ`, `nf_inv_all`), `StepsOut` (per-step properties, chain identity,
displacement sums, final state) and `StepsCaseB` (reality, Case B). Design
`docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-8 (session 1).
-/

public section

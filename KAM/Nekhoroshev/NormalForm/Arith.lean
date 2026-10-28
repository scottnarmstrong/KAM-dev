/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.ArithBase
public import KAM.Nekhoroshev.NormalForm.ArithInduct
public import KAM.Nekhoroshev.NormalForm.ArithDisp

/-!
# The Normal Form Lemma: numerics (facade)

Re-exports `ArithBase` (schedule, Step 0, Cases A/B, number of steps), `ArithInduct` ((6.1), (6.2),
the induction constant, the decomposition norm, (a)) and `ArithDisp` (displacement, radii).
Design `docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-8.
-/

public section

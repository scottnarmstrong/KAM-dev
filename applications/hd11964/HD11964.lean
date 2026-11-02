/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.Cover
public import HD11964.CoverPlan
public import HD11964.NoCrossing
public import HD11964.NoCrossingObs
public import HD11964.ReducedRange
public import HD11964.Threshold

/-!
# HD 11964 (application package root)

The modules of the HD 11964 application (decision D51; opt-in, outside the core build). Phase 2,
part A: the action box, `B = Λ_c` and the data of LP-LIFT (`HD11964.Threshold`); the certificate
region `R(d)` and no orbit crossing given the certificate's bounds on it (`HD11964.NoCrossing`). The
bridge from a certified Λ-drift to no orbit crossing is in the core (`KAM.Application.LambdaDrift`).
Phase 2, the cover: the cover lemma for affine cells (`HD11964.Cover`) and the fitted 50-cell plan
of `R(1/500)` with its decided check (`HD11964.CoverPlan`). The reduced-mass bridge (scoping note
§4): the reduced Delaunay actions and the analytic range of `G - Λ` on `R(r)`
(`HD11964.ReducedRange`), and no orbit crossing with the first exit driven by them
(`HD11964.NoCrossingObs`).
-/

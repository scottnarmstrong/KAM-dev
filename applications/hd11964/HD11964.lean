/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.NoCrossing
public import HD11964.Threshold

/-!
# HD 11964 (application package root)

The modules of the HD 11964 application (decision D51; opt-in, outside the core build). Phase 2,
part A: the action box, `B = Λ_c` and the data of LP-LIFT (`HD11964.Threshold`); the certificate
region `R(d)` and no orbit crossing given the certificate's bounds on it (`HD11964.NoCrossing`). The
bridge from a certified Λ-drift to no orbit crossing is in the core (`KAM.Application.LambdaDrift`).
-/

/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Spatial.Vector
public import KAM.Planetary.Spatial.Model
public import KAM.Planetary.Spatial.Field
public import KAM.Planetary.Spatial.Elements
public import KAM.Planetary.Spatial.Orbital
public import KAM.Planetary.Spatial.Momentum
public import KAM.Planetary.Spatial.Newton
public import KAM.Planetary.Spatial.RotationAlgebra
public import KAM.Planetary.Spatial.Rotation
public import KAM.Planetary.Spatial.RotationSolution
public import KAM.Planetary.Spatial.Alignment

/-!
# The spatial exact model (facade)

Package LP-SP-MODEL (wave 4), `LP:MAIN §1 (9–93)`, Lemmas 1–3 (`d = 3`) and rotation invariance;
track LP, non-frozen; the statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
Public import path for the modules `KAM.Planetary.Spatial.*` (namespace `KAM.Planetary.Spatial`).
-/

public section

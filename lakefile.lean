import Lake

open Lake DSL

package «kam» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

private def projectLeanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`linter.unusedSimpArgs, true⟩,
  ⟨`linter.unnecessarySimpa, true⟩,
  ⟨`linter.deprecated, true⟩
]

-- BEGIN GENERATED BLOCK (scripts/gen_root_imports.py; do not edit by hand)
/-- Per library, the frozen theorem anchors in state `DRAFT_SORRY` and their provider modules.
The frozen-anchor quarantine forbids every other module, the roots included, from importing
them, so each library builds them as extra globs beside its root. -/
private def quarantinedModules : Array (Lean.Name × Array Lean.Name) := #[
  (`KAM, #[`KAM.Frozen.Magnetic.Theorems.MagneticBarrier, `KAM.Frozen.SpinOrbit.Theorems.LunarSyncLock, `KAM.Frozen.SpinOrbit.Theorems.LunarSyncOrbitBound, `KAM.Frozen.SpinOrbit.Theorems.LunarSyncOrbitSpec, `KAM.Frozen.SpinOrbit.Theorems.LunarSyncOrbitUnique, `KAM.Provider.Magnetic.MagneticBarrier, `KAM.Provider.SpinOrbit.LunarSyncLock, `KAM.Provider.SpinOrbit.LunarSyncOrbitBound, `KAM.Provider.SpinOrbit.LunarSyncOrbitSpec, `KAM.Provider.SpinOrbit.LunarSyncOrbitUnique])]
-- END GENERATED BLOCK

/-- The globs of library `lib`: its root (with its whole import closure) and its quarantined
modules, which no root may import. -/
private def libGlobs (lib : Lean.Name) : Array Glob :=
  #[.one lib] ++ (((quarantinedModules.find? (·.1 == lib)).map (·.2)).getD #[]).map .one

/-- The core of the KAM formalization: reusable infrastructure, proofs, and (under `KAM.Frozen`)
the author-approved frozen statements. The library builds its root `KAM.lean` and its import
closure, plus the quarantined `DRAFT_SORRY` anchors and their providers. The root imports every
core module, so a plain `lake build` compiles every core theorem; it does not compile the
certificate applications below (decision D51). Which library owns a module is declared in
`scripts/build_roots.json`, and `scripts/gen_root_imports.py` writes the roots from it. -/
@[default_target]
lean_lib «KAM» where
  roots := #[`KAM]
  globs := libGlobs `KAM
  leanOptions := projectLeanOptions

/-! Certificate applications (decision D51): numerical certificates of physical systems, whose
kernel checks take CPU-hours and GB. Each is an opt-in library, not a default target: build it with
`lake build <Lib>` through the serial capped driver (`scripts/prebuild_heavy.py --lib <Lib>`). Its
modules keep their `KAM.*` names (so their builds are shared with the core library's options); its
root `<Lib>.lean` is generated from `scripts/build_roots.json`. -/

/-- SO-2: the Moon's spin–orbit band. The N = 65 barrier-torus certificate data under
`KAM/SpinOrbit/Data`, the final assembly `KAM.SpinOrbit.LunarFinalR2V2`, and the sealed frozen
theorems `lunar_barriers` and `lunar_spin_confinement` with their providers. -/
lean_lib «KAMLunarBand» where
  roots := #[`KAMLunarBand]
  globs := libGlobs `KAMLunarBand
  leanOptions := projectLeanOptions

/-- SO-3: the Moon locked in synchronous rotation. The N = 65 lock certificate data under
`KAM/SpinOrbit/Data/LockN65` and its assembly (empty until they land). -/
lean_lib «KAMLunarLock» where
  roots := #[`KAMLunarLock]
  globs := libGlobs `KAMLunarLock
  leanOptions := projectLeanOptions

/-- MAG: the magnetic field-line barrier at `ε = 3/2500` (D66, D68). The certificate data under
`KAM/Magnetic/Data` (its generated chain lands with the certificate run). -/
lean_lib «KAMMagneticBarrier» where
  roots := #[`KAMMagneticBarrier]
  globs := libGlobs `KAMMagneticBarrier
  leanOptions := projectLeanOptions

/-
Template for a further application inside this package (for example LG00). New applications
should rather be separate Lake packages `applications/<name>/` that require this one
(docs/campaign/design/APPLICATIONS.md); use this template only when existing builds must be kept.
Add the library to `scripts/build_roots.json`, then run `scripts/gen_root_imports.py`.

/-- <Track>: <one line on the physical system and what is certified>. -/
lean_lib «KAMLG00» where
  roots := #[`KAMLG00]
  globs := libGlobs `KAMLG00
  leanOptions := projectLeanOptions
-/

private def runProjectScript (name : String) (args : List String) : ScriptM ExitCode := do
  let pkg ← getRootPackage
  let child ← IO.Process.spawn {
    cmd := (pkg.dir / "scripts" / name).toString
    args := args.toArray
    cwd := some pkg.dir
  }
  child.wait

/-- Check source-level invariants that Lean's typechecker cannot express. -/
@[lint_driver]
script lintSources (args) do
  runProjectScript "lint_sources.sh" args

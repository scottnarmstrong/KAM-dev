import Lake

open Lake DSL

/-- HD 11964 (decision D51): a certified no-orbit-crossing time for the planar Newtonian three-body
model of HD 11964, an application package on top of the core `kam`. Opt-in: build it from this
directory through the capped driver; the core's builds and its Mathlib are reused through the path
dependency. -/
package «kam-hd11964» where

require kam from "../.."

/-- The core's Lean options (`lakefile.lean` of `kam`, `projectLeanOptions`), byte for byte. -/
def hd11964LeanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`linter.unusedSimpArgs, true⟩,
  ⟨`linter.unnecessarySimpa, true⟩,
  ⟨`linter.deprecated, true⟩
]

/-- The HD 11964 application: the root `HD11964.lean` and its import closure (modules
`HD11964.*`). -/
@[default_target]
lean_lib «HD11964» where
  leanOptions := hd11964LeanOptions

# SO-CONF prover handoff (branch inp-soconf, e4edfebe; off inp; track SO package run by the main orchestrator)


**Files:** new `KAM/SpinOrbit/Barrier.lean` (232 lines). No other file touched (KAM.lean not regenerated; the lint reports it out of date, as expected for a new module — orchestrator regenerates).

**Declarations:** `SoBarrier` (verbatim from SOSignatures §I; defined here, so `Graph.lean` must import Barrier and not redefine it), `so_confinement` (verbatim statement), plus helpers `soVq_contDiff`, `soField_contDiff`, `soForceBound`, `soVq_abs_le`, `soRadius`, `soSolution_norm_le`, `so_global_exists_unique`.

**Approach:** the force `-soVq` is bounded by `A = 4πε Σ|A_m|` so on `[-T,T]` every solution stays in an explicit ball (mean value inequality per component: φ'=1, |p'|≤A, q'=p). `gen_confinement` with that ball (`gen_uniform_compact`) gives maximal interval ⊃ [-τ,τ] for all τ; `gen_maximal` uniqueness identifies it, so it is `(⊥,⊤)`. Uniqueness: `gen_uniqueness` on `univ`. Confinement: `gen_barrier` with V the open slab between the graphs, S the union of the two invariant graphs (`isInvariantSet_union`); frontier(V) ⊆ S by closure. Both time directions are covered by `gen_barrier`. No ordering `B₁ < B₂` hypothesis is needed (none in the signature).

**Checks:** `inp_lake_build.sh … KAM.SpinOrbit.Barrier`: Build completed successfully, no warnings in my file (only a pre-existing linter warning in KAM/ODE/Exit.lean). `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; only message "KAM.lean is out of date" (generated file, untouched per rule 10). Max line length ≤100.
`#print axioms KAM.SpinOrbit.so_confinement` and `so_global_exists_unique`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / errata / deviations:** none. Signed statements were true as written. No heartbeat options, no sorry.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, now Revision 3); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean. Owner ruling O1: the initial region is a constant momentum window. Check global existence and uniqueness of the lunar ODE (globally Lipschitz periodic force), and that two invariant continuous barrier graphs confine every solution starting between them for ALL real times in both directions, with no conclusion-shaped premise (invariance of the graphs is an input property of SoBarrier: check it is stated as invariance under the actual flow, not as the confinement conclusion).

AUDIT FOCUS: the package's signed declarations match the draft signatures verbatim (except the ruled deviation above); every proof is sound with no added premise; the slice the design assigns to these modules is complete. Audit ONLY KAM/SpinOrbit/Barrier.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.

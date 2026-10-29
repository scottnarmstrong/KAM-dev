# GAP-I7a prover handoff (branch inp-gi7a, df537c97; off inp; track I graph-gap programme package run by the main orchestrator)


Files: new `KAM/Iso/DelaunayStepNodes.lean` (~135 lines). No landed file edited. Imports only landed modules.

| node | declaration | statement |
|---|---|---|
| `stepI:p7:om-hol` | `KAM.Kepler.orbitStep_om_hol` (e₁∈(0,1)) | on `orbitDomC e₁`: u, cos u, sin u DifferentiableOn ℂ; `0 < 1-ϑ*`; `1-ϑ* ≤ ‖1 - e cos u‖`; `orbitMapC` holomorphic; `‖e‖ ≤ e₂ < 1`; `0 < Re(1-e²)`; `(1-e²)^(1/2)` holomorphic (k-clause, also closes the orbit-maps-e over-claim) |
| `stepI:p7:sy-ext` | `KAM.Kepler.delaunayStep_sy_ext` | `IsSymplecticOn 1 delaunay deDom` (cv-sympl precedent form) ∧ ∀ w∈deDom, ∃ A≃L = fderiv, `LinearMap.det A ≠ 0` ∧ Ω(A⁻¹u,A⁻¹v)=Ω(u,v) (the latter is `DQ𝕁DQᵀ=𝕁`, equivalent to symplecticity of the inverse) |
| `stepI:p7:sy-field` | `KAM.Kepler.delaunayStep_sy_field` (U open, ContDiffOn ℝ 1 H U) | (a) `D𝒬 X_{H∘𝒬}=X_H∘𝒬` on deDom ∩ 𝒬⁻¹U; (b) curve differentiable at t, w t∈deDom, 𝒬(w t)∈U: HasDerivAt iff |

Approach: assembled from `keplerEq_tube`, `Tube.tube_bounds`, `orbitMapC_differentiableOn`, `delaunay_symplectic`, `delaunay_fderiv_equiv`, `delaunay_hamiltonianVectorField`, `delaunay_hasFDerivAt`. Reverse curve direction uses injectivity of D𝒬 (𝒬 is not globally injective). Premises: only source hypotheses (no proved output used as premise).

Checks: `inp_lake_build.sh . KAM.Iso.DelaunayStepNodes` succeeded, no warnings from my file. `#print axioms` of all three: propext, Classical.choice, Quot.sound. `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK; only note "KAM.lean is out of date" (generated; run scripts/gen_root_imports.py at landing; not edited by me).

Uncertainties: sy-ext uses form language (per OVERNIGHT 05:10 ruling) not explicit Matrix; the dual identity is stated as inverse-symplecticity. No suspected errata or deviations. No heartbeat issues.

ORCHESTRATOR RULING (OVERNIGHT 05:10, owner to review): matrix-form symplecticity follows the cv-sympl precedent (I-2-audit-1.md:24): the form statement IsSymplecticOn is accepted as the literal content where that precedent applied it. Track I graph-gap programme (/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-I.md, section GAP-I7a).

AUDIT FOCUS: for each node (stepI:p7:om-hol, sy-ext, sy-field) read its NODE record in docs/graph/I/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint-I lines it cites; per-node verdict: does the named declaration state the literal conclusion under only the source's hypotheses, quantifiers in source order (sy-ext judged under the cv-sympl precedent: confirm the precedent at I-2-audit-1.md:24 covers it)? An export taking a proved dependency's OUTPUT as a premise is a FAIL. Audit ONLY KAM/Iso/DelaunayStepNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

# GAP-I7a independent package audit 1

Overall: **PASS WITH NOTES** for the three-node graph-gap package. No frozen theorem is proved or sealed by this package; per-anchor seal readiness is not applicable. All three named graph conclusions are established under source hypotheses, with the explicitly authorized form-language interpretation for `sy-ext`.

Audited HEAD: `df537c97a51992180ba5f769b7805db515302ab4`; comparison ref `inp`: `ab3459def1182c7cf70d8b920eded286c93b2737`. The full `git diff inp...HEAD` adds only `KAM/Iso/DelaunayStepNodes.lean` (123 lines). The pre-existing untracked handoff was read and left untouched. Audit scope is exclusively this module. This report is in the package worktree at the user's exact absolute destination, overriding the generic brief's MAIN-worktree destination.

## Declaration ledger and completeness

All declaration names below have namespace `KAM.Kepler`.

| Graph node / source | Declaration and location | Verdict | Reason |
|---|---|---|---|
| `stepI:p7:om-hol`; DEPGRAPH:9210–9230; blueprint-I/parts/p7-delaunay.tex:170–176 | `orbitStep_om_hol`, module:38–71 | PASS WITH NOTES | For every `e₁` with `0 < e₁ < 1`, proves complex differentiability of `u`, `cos u`, `sin u`, the positive denominator lower bound, and the actual five-variable `orbitMapC` on its full intended open domain. Also proves `‖e‖ ≤ e₂ < 1`, positive real part of `1-e²`, and holomorphy of the principal square root. No Kepler-solution or denominator theorem is a premise. See intermediate-bound note below. |
| `stepI:p7:sy-ext`; DEPGRAPH:9529–9549; blueprint:205–210,236–237 | `delaunayStep_sy_ext`, module:76–89 | PASS under the specified cv-sympl precedent | No hypotheses. On every point of `deDom`, exports preservation of the frozen form, a continuous linear equivalence equal to the actual derivative, nonzero linear-map determinant, and preservation of the form by its inverse. These give the two symplectic matrix identities under the authorized form-language reading; neither symplecticity nor invertibility is assumed. |
| `stepI:p7:sy-field`; DEPGRAPH:9558–9577; blueprint:210–214,239 | `delaunayStep_sy_field`, module:93–120 | PASS | Quantifies over open `U`, then a real Hamiltonian `H` of class C¹ on `U`, then points in `deDom` whose image belongs to `U`; proves the literal field transport equation. Then quantifies over curves and times and proves both derivative implications, under pointwise differentiability and membership in that same set. This is stronger than requiring an entire C¹ curve in W. |

The GAP-I7a design slice in `/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-I.md:360–383` maps exactly these three nodes to this module. All three are exported, and there are no other new public declarations. The module and handoff explicitly classify these exports as UNSIGNED. They do not replace any SIGNED declaration; there is no new frozen/provider signature contract to compare. Searches of the available design/signature locations found no signed declarations with these names. Consequently provider/frozen type equality and proposed seal-body probes are not applicable. Fresh exact-signature re-export probes for all three declarations nevertheless elaborated successfully.

The square-root clause supplies the omission identified for the existing `bpI:p7:orbit-maps-e` parent by GAP-PLAN-I.md:110; this audit does not modify that parent's graph record or independently re-audit its other clauses.

## Source fidelity, premises and representations

**om-hol.** `orbitDomC e₁` is exactly `(x 0,x 3) ∈ keplerTube e₁` and `x 2 ≠ 0` (`OrbitComplex.lean:48`): coordinates are `(ell,g,L,e,k)`, and g and k remain arbitrary complex numbers. In particular the orbit-map theorem does not accidentally impose `k = sqrt(1-e²)` or exclude e=0. The separate last conjunct proves the principal root as a function of e on the same domain. The proof derives its slit-plane condition from `0 < Re(1-e²)` and uses `DifferentiableOn.cpow_const`; it does not select a root through a conclusion-shaped field.

The blueprint:176 says “`abs e < e₂ < 1`”; module:48 exports `‖e‖ ≤ e₂` and `e₂ < 1`, exactly as the GAP-I7a export design specifies. This is a weaker intermediate e₂-bound, not an export of the strict comparison itself. All requested holomorphy and nonvanishing conclusions hold, and the export still directly gives `‖e‖ < 1`. The blueprint's quantitative lower bound `Re(1-e²) ≥ 1-abs e²` is likewise an intermediate estimate rather than a separate exported inequality; the needed strict positivity is exported. Do not cite this declaration alone as a theorem of the strict `‖e‖ < e₂` comparison. No downstream requirement for that strict intermediate comparison appears in this three-node slice. No conclusion needed by `om-hol` is passed in as an input.

**sy-ext precedent.** I checked `docs/tracks/I/audits/I-2-audit-1.md:24` directly: its cv-sympl row accepts `periodOneMap_symplectic`, “Frozen symplectic form preserved with factor **1** ... Blueprint's opposite sign for the form cancels on both sides”. Thus it really is a form-preservation precedent, as invoked by the handoff's OVERNIGHT 05:10 ruling. It does not itself provide Delaunay invertibility; this package supplies that independently as an output. The prior `KEP-6-audit-1.md:59–63` also explicitly explains the form/derivative-equivalence interface.

For the canonical Gram matrix J, the exported form statement is `AᵀJA=J`. Its inverse-form statement is `A⁻ᵀJA⁻¹=J`; inverting this equality and using `J⁻¹=-J` gives `AJAᵀ=J`. Nonzero `LinearMap.det A` is determinant nonvanishing for the actual derivative because the equality to `fderiv` is exported. These are the graph's two identities and determinant conclusion in the permitted coordinate-free presentation, with no basis or carrier change. The frozen form is `sum dI_i wedge dtheta_i`; its negative is the blueprint's form, and preservation of either is identical. No explicit `Matrix` identity is exported; acceptance here is specifically under the user's required precedent, not an assertion that Lean elaborated a matrix corollary.

**sy-field.** The binders occur in source order, with `hU` immediately after U and `hH` immediately after H. Using an ambient total function with `ContDiffOn` on open U faithfully represents a C¹ Hamiltonian on U: all derivative evaluations are at image points in U, where `ContDiffOn` yields actual differentiability. W is expressed by its two membership conditions. No regularity or value outside U is used. The curve version is pointwise; its reverse direction uses `HasDerivAt.unique` and injectivity of the proved derivative equivalence. It does not assume global injectivity of the periodic Delaunay map, a global inverse chart, or the desired ODE identity. All previously proved analytic, symplectic and vector-field outputs are obtained inside the proof.

## Definition classification and hygiene review

There are **no new definitions, abbreviations, structures, instances, private/public helper declarations, or namespaces shadowing root objects**. All three theorem short names have exactly one declaration site in KAM. The namespace is the established `KAM.Kepler` namespace. Local `have` bindings are proof-local, not new API.

Referenced objects checked for interpretation: `orbitMapC` is the explicit orbit formula on all five coordinates; `orbitDomC` excludes L=0 and restricts only the Kepler tube; `deDom = {0<G<L}` is the full real Delaunay domain; `delaunay` is the landed real orbit map; `Phase 2` is `(Fin 2 → ℝ) × (Fin 2 → ℝ)`; the form and Hamiltonian vector field are the frozen definitions. Totalized inverses, fderiv and square roots are used only where their required nonvanishing, differentiability and branch conditions are proved. No junk/fallback definition is introduced or used to obtain a result.

A recursive local-KAM import traversal visited 55 modules, found **zero providers and zero frozen theorem modules** (and hence zero DRAFT_SORRY theorem imports). Frozen dependencies are definitions only, so no SEALED-theorem import exception is needed. The new file has the required copyright, `module`, public imports, module docstring and `@[expose] public noncomputable section`. It has 123 physical lines, maximum 97 Unicode characters per line, and no line above 100. A direct forbidden-token/resource-option search returned no matches. No EuclideanSpace, heartbeat/recursion/synthesis override, proof escape, reused HELPER short name, or harmful root shadow was found.

## Independent validation

Commands ran from `/root/code/KAM-inp-gi7a`. All Lean-bearing checks were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5` (the build wrapper itself invokes nice). No parallel audit agent or second Lean/Lake invocation was used.

1. Full comparison and protected paths:

   ```sh
   git diff inp...HEAD
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD
   ```

   The full diff is one new 123-line module. Protected-path diff is empty; diff whitespace check exits 0 with no output. No protected file was edited by the auditor.

2. Required targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gi7a KAM.Iso.DelaunayStepNodes
   ```

   Exit 0. Output begins `[inp-gate] slot 1 acquired 05:16:38 for KAM.Iso.DelaunayStepNodes` and ends `Build completed successfully (9101 jobs).` The only warnings replayed are pre-existing unused `hm` and `hκ` in `KAM/Kepler/Energy.lean:106:35,48`. No warning in the audited file. The job count includes cached/replayed dependencies; this was a targeted build, not a library rebuild from scratch.

3. Fresh probe, created solely in `.lake/abi-scratch/GAPI7aAudit.lean`:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPI7aAudit.lean
   ```

   Exit 0, no warnings. It imports `KAM.Iso.DelaunayStepNodes`; copies each complete declaration type under fresh namespace `GAPI7aAudit` and name `probe_<original>`; uses respectively `exact KAM.Kepler.orbitStep_om_hol h0 h1`, `exact KAM.Kepler.delaunayStep_sy_ext`, and `exact KAM.Kepler.delaunayStep_sy_field hU hH`. It also runs `#check @...` and `#print axioms` on each original declaration. The printed types have precisely the binders and conclusions described in the ledger. Exact axiom output:

   ```text
   'KAM.Kepler.orbitStep_om_hol' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Kepler.delaunayStep_sy_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Kepler.delaunayStep_sy_field' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. One kernel replay invocation for the sole new module (no provider module exists):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.DelaunayStepNodes
   ```

   Exit 0. Exact output: `replaying KAM.Iso.DelaunayStepNodes`.

5. Repository lint, including module, frozen-anchor and ABI checks:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1 solely for the generated-root discrepancy expressly permitted by the brief. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1267 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The generated root was left untouched. No substantive lint failure was present.

## Uncertainties, errata and deviations

No suspected new pinned-source defect was found in this module. The audited blueprint steps are the project's own proofs; no new claim of checking the pinned Chierchia PDF is made. The existing missing-root and signature-representation issues are reported above with their exact scope. The intermediate strict e₂ comparison is not exported; the source's holomorphy conclusion is fully present under the stated design. Explicit matrix expressions are not exported, as authorized by the handoff's cv-sympl ruling; this is an acknowledged representation choice, not a silent substitution. The stronger pointwise curve theorem needs no extra source premise.

No repository source, graph, manifest, generated root or README was changed. The scratch probe was removed after validation. The only auditor artifact is this report. This package is ready for the scoped graph-node update under the stated ruling; it does not itself seal a theorem anchor or update any graph status.

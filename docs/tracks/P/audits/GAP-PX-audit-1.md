# GAP-PX independent package audit 1

Overall verdict: **PASS WITH NOTES** for this four-node infrastructure slice. No frozen anchor is proved or proposed for sealing by this package; provider/frozen-type and seal-body probes are therefore not applicable. There are no FAIL nodes.

Audited 2026-10-29 in `/root/code/KAM-inp-gpx`, HEAD `fe59e9e95f3ce8f31699258c0b11ca5eb3903b53`, against `inp` at `02f1bcd96b3681d37a276e77c2ec795dbece6ae4`. Read AGENTS.md, PLAN, DECISIONS, the package audit brief, handoff/AUDIT FOCUS, GAP-PLAN-P2's GAP-PX section, relevant design tables, track-P statement, all four NODE records and their cited blueprint passages. The user's exact report-path instruction overrides the generic brief's main-worktree destination. No implementation, frozen, manifest, graph or generated file was edited.

## Scope and per-node fidelity

The complete `git diff inp...HEAD` contains only the three new modules below (234 lines). All four exports are explicitly UNSIGNED under the package ruling, so there is no signed declaration requiring a signature-file equality probe. The GAP-PX plan's four-node table is completely covered. Older design tables locate these steps inside larger parent proofs; this package supplies the new leaf exports and does not re-audit those parents or claim their entire contracts.

| Node | Declaration and locator | Verdict | Source comparison |
|---|---|---|---|
| `stepP:p3:sum-radii` | `KAM.Planetary.sum_radii`, `KAM/Planetary/TwoScale/SumsRadiiNodes.lean:26` | PASS | DEPGRAPH:5350, blueprint `p3b-two-scale-limit.tex:6–15`: original `KamHyp` precedes `k ≥ 1`; both `rhoHat (seq p k) ≤ rhoHat p * 16⁻¹^k` and `(seq p k).s = p.s * 12⁻¹^k` are literal conclusions. No iterative-output premise. The proof uses the formula-level minimum bound and the actual scale recurrence. |
| `stepP:p6:ma-newton` | `KAM.Planetary.ma_newton`, `KAM/Planetary/Newtonian/AssemblyNewtonNodes.lean:28` | PASS WITH NOTES | DEPGRAPH:12656 and blueprint `p6-newtonian-models.tex:266–277` explicitly list S1 and S2 as source hypotheses. `hSt`, `_hS`, and `hS2` are exactly those inputs, not an assumed proved dependency output. Physical data precede S, then `∀ z ∈ S`, then witnesses `w K θ`, then `∀ φ` and the exact all-time Newton solution with actual masses and barycentric positions/velocities. `ma_coll` is invoked to derive collision exclusion, not assumed. See AxisData note below. |
| `bpP:p12:sec-set#data` | `KAM.Planetary.cylnorm`, `KAM/Planetary/PlanarAssembly/FastInverseNodes.lean:30`, together with existing dictionary definitions classified below | PASS WITH NOTES | DEPGRAPH:31652 and blueprint `p12-planar-assembly.tex:15–20`: the property is the exact squared Euclidean slow-length bound `< 2*r²`. It holds for arbitrary V and r, hence also for bounded open boxes and positive radii. The definition portion is covered by existing definitions under the explicit package ruling; `cylnorm` alone is not claimed to define the whole dictionary. |
| `stepP:p12:fd-inv` | `KAM.Planetary.PlanarAssembly.fd_inv`, `KAM/Planetary/PlanarAssembly/FastInverseNodes.lean:82` | PASS | DEPGRAPH:31982 and blueprint `p12-planar-assembly.tex:54–60`: positive κ and masses, then the positive-endpoint action box, precede all conclusions. The local g is exactly `(κ²*m_i³/v_i)^(1/3 : ℝ)`. Analyticity on the frequency image and both inverse identities, including `g v ∈ W`, are exported. Frequency formula and rectangular image are derived inside the proof, not supplied as premises. Analyticity implies the requested C¹ statement; no narrowing to mere C¹ remains. |

`ma_newton` accepts `AxisData a γ A` rather than prescribing the canonical extrema. Its fields are only positive lower bounds on axes and gaps and an upper bound on axes (`Tube.lean:44–49`), not collision, torus, or Newton conclusions. The existing `axisData_canonical` (`Tube.lean:55`) constructs this bundle from source positivity, distinctness and `n > 0`, with γ = axisGap a and A = axisMax a. This recovers precisely the source tube radius. The audit probe elaborates the full Newton conclusion directly from those original source premises. Dropping the unused `n > 0` from the export strengthens it. `_hS` and `_H` are retained source hypotheses even though these particular proofs do not need them.

No new public HELPER short name is reused, and no root declaration is introduced. The four new public names occur only at their respective declarations in the KAM source tree. Four cube-root lemmas are private to FastInverseNodes; their short names cannot shadow public declarations for downstream consumers.

## Definition classification and completeness

No new top-level `def`, `abbrev` or `structure` occurs in the audited diff. The local W and g in `fd_inv` are the intended open product box and explicit real cube-root formula. Lean's total real division/rpow outside the positive frequency image is irrelevant to the claims: the proof first derives positivity throughout that image, and uses positive constants and actions in every inverse computation. There is no fallback object used to satisfy a theorem.

For the definition portion of `bpP:p12:sec-set#data`, the existing named objects agree with the source on their whole stated carriers:

| Source object | Existing Lean object | Classification |
|---|---|---|
| Phase and coordinate/index dictionary | frozen `Phase`, `assemble`, `fast`, `slow`; `Poincare/Product.lean:39` `planetBlock`; `PlanarTorsion/Lift/Defs.lean:48–55` `p11cL_act`, `p11cL_ang`, `p11cL_slow` | Literal finite-coordinate projections: `assemble I phi p q = ((phi,q),(I,p))`; slow pair is `(q,p)`. Both dimension expressions reduce to 4. Planets 0,1 keep their ordered indices. |
| κ, reference actions and inverse axes | `PlanarData.kappa`, `.actions`, `.axes`, `p11c_axes` in `PlanarTorsion/Setting.lean:38–43`; `PlanarAssembly.action_center` in `Geometry.lean:40` | Literal `G*m0`, `m_i*sqrt(κ*a_i)`, `I_i²/(m_i²*κ)` and `0<a₀<a₁`. Total formulas agree with the source; physical applications use its positivity premises. |
| Product chart Ψ | `poincareProd` in `Poincare/Product.lean:45` | Bodywise actual Poincaré chart, fast block first, specialized to n=2. No replacement chart or extension is introduced by this slice. |
| Γᵢ and oscillator actions Rⱼ | `poincareGamma (planetBlock w i)` and frozen `oscillatorAction` | Literal half-sum of the two slow-coordinate squares, in the dictionary `(x,y)=(q,p)`; the audit probe checks this identity. |
| Euclidean slow length and cylinder | `p11c_slowLength` in `Setting.lean:51`; `p11cL_slow`; frozen `cylinder` | Square root of the sum of all four squares, not the ambient Pi norm. The cylinder has two strict disc inequalities; summing them gives the exported bound. |

The proof of `sum_radii` relies on existing `ScaleData`, `constants`, `nextScale`, and `seq` (`TwoScale/Constants.lean:29–69`). These are formula data and genuine iteration: `rhoHat` is a minimum including ρ, the next ρ is the preceding rhoHat/16, and s is divided by 12. The bound needs no artificial recurrence assumption. `KamHyp` contains the original analytic/KAM inputs, not this radius conclusion.

## Independent checks

All Lean/Lake commands below were serialized with `LEAN_NUM_THREADS=1`, default heartbeat settings and `nice -n 5` (the build wrapper supplies nice). No clean, update, cache retrieval, protected-file mutation or state-changing git command was used.

Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gpx KAM.Planetary.Newtonian.AssemblyNewtonNodes KAM.Planetary.PlanarAssembly.FastInverseNodes KAM.Planetary.TwoScale.SumsRadiiNodes
```

Exit 0. Final output: `Build completed successfully (9496 jobs).` The build replayed existing dependency warnings (unused variables/simp arguments and deprecated syntax); no heartbeat failure or build error occurred.

Kernel replay (one invocation):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Newtonian.AssemblyNewtonNodes KAM.Planetary.PlanarAssembly.FastInverseNodes KAM.Planetary.TwoScale.SumsRadiiNodes
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.TwoScale.SumsRadiiNodes
replaying KAM.Planetary.PlanarAssembly.FastInverseNodes
replaying KAM.Planetary.Newtonian.AssemblyNewtonNodes
```

Axiom/applicability probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAP-PX-probe.lean
```

Final exit 0, exact output:

```text
'KAM.Planetary.sum_radii' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ma_newton' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.cylnorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.fd_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The probe also elaborated the original-source `ma_newton` specialization using `axisData_canonical`, the C¹ consequence of `fd_inv` using `AnalyticOnNhd.contDiffOn_of_completeSpace`, the assembled coordinate projections, the Γ/oscillatorAction identity, and the action-center identity. An initial scratch-only probe needed correction: the general `.contDiffOn` method requires UniqueDiffOn, whereas `.contDiffOn_of_completeSpace` applies here directly; the coordinate proof also needed extensionality before simplification. These were probe errors, not package failures; the corrected full probe passed without warnings.

Import and static inspection: recursively followed the KAM imports of the three changed modules (450 source files in the closure). No provider import and no frozen theorem import occurs in this closure; thus no DRAFT_SORRY or unverified sealed theorem is imported. All new theorems have only `[propext, Classical.choice, Quot.sound]`, independently of the static result. No prohibited proof token, resource override, EuclideanSpace carrier, missing module header, new bundled conclusion hypothesis, or harmful root shadow was found in the slice. The three files have respectively 46, 139 and 49 total lines; maximum line lengths are 93, 100 and 92 Unicode characters.

`git diff --check inp...HEAD` and `git diff --check` both exit 0 without output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. The pre-existing untracked handoff is preserved.

## Notes, suspected defects and limits

- Handoff `GAP-PX-handoff.md:24` says “no r > 0 hypothesis needed (implied)”. The parenthetical is false: cylinder membership depends on r² and is unchanged on replacing r by -r. For example, the zero phase point belongs to `cylinder Set.univ (-1)` at b=2. The theorem itself correctly needs no positive-radius premise, and is stronger than the blueprint. This is a handoff-prose correction, not a Lean or pinned-source defect.
- The unused original `KamHyp` and measurable-set arguments and the omitted positive-dimension hypothesis are harmless and are recorded above. No new source assumption or conclusion weakening was introduced.
- The definition node is accepted using the explicit ruling permitting existing definitions plus the property export; it must not be recorded as if the single `cylnorm` type encoded every dictionary definition.
- No suspected mathematical defect was found in the cited blueprint statements. No fresh pinned-PDF erratum is asserted: this audit compares the local graph/blueprint contract with the implementation. No campaign theorem, physical headline, frozen anchor or unrelated consumer is certified by this four-node result.

## Final lint receipt and disposition

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely for the explicitly permitted generated-root mismatch. Exact complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1216 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All substantive lint gates pass. The generated-root message is an expected merge-time action for the orchestrator under the package ruling, not a failure finding; KAM.lean was not regenerated. The full script's literal exit status is retained above rather than reported as zero.

Final disposition: **PASS WITH NOTES**, all four mapped nodes covered, no FAIL node, no frozen seal requested. The exact permitted report is the only new repository artifact written by this audit; all audit scratch probes and logs were deleted after recording their results.

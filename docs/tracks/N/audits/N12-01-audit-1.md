# N12-01 independent package audit 1

Overall verdict: **PASS WITH NOTES** for N12-01 (`Setting`, `Field`). No blocking mathematical,
statement, definition, or proof-hygiene defect found. The only lint failure is the explicitly
permitted stale generated `KAM.lean`. This is an infrastructure-package verdict: no frozen anchor
is proved or seal-ready in this package.

## Scope and authority

Audited 2026-10-28 in `/root/code/KAM-inp-n1201`, HEAD
`6457d8904f14bc7815fb708431b71c7a99eb23f8`, against `inp`
`ef8fc426c638557035e6101216aad4ef8b8a570e` using `git diff inp...HEAD`.
The diff adds only `KAM/Nekhoroshev/Averaging/Setting.lean` (112 lines) and
`KAM/Nekhoroshev/Averaging/Field.lean` (219 lines).

Read AGENTS.md, PLAN.md, DECISIONS.md, the supplied package-audit brief and N12-01 handoff;
N12-LEAN-DESIGN.md (package row, proof plan, Appendix A); both DESIGN-N12 design audits;
Part 12's standing data, field and averaged nodes; track N's averaging statement; and the frozen
analytic/rank/error/solution/root interfaces. The user-specified report path overrides the generic
brief's main-worktree destination. Only this report and temporary `.lake/abi-scratch/` probes were
written. No production edits, state-changing git, or delegation.

The referenced `.drafts/design/N12Signatures.lean` is absent in this package worktree. Read the
actual delivered file at `/root/code/KAM-inp/.drafts/design/N12Signatures.lean` and verified that
it equals the current design Appendix A, after removing enclosing whitespace. Its SHA-256 is
`0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369`.
The definitions/structure/variables block matches exactly; both theorem signatures match exactly.
Design audit 2's correction concerns `wreg` in N12-06, outside this package.

Frozen anchors `averaging_mean` and `averaging_most`: **not implemented here**. Provider=frozen-type
and frozen seal-body probes are inapplicable. Instead, fresh examples copied both design theorem
types and applied `@fbounds n R s h f d` / `@averaged n R s h f d`; both elaborated.

## Declaration and node review

Names below are in `KAM.Nekhoroshev`. PASS concerns each stated package contract.

| Node / obligation | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| s-setting#data | `AvgPhase` (Setting:29) | PASS | Real Pi product, angles then actions; exact design carrier. |
| s-setting#data | `AvgComplexPhase` (Setting:30) | PASS | Complex Pi product matching the real carrier. |
| s-setting#data | `AveragingData` (Setting:33) | PASS | Only dimension, positive radii, frozen analytic and global rank premises. No conclusion-shaped field. |
| s-setting#data | `avgDomain` (Setting:45) | PASS | All real angles times the frozen open max-norm action ball. |
| s-setting#data | `avgG` (Setting:46) | PASS | Closed max-norm action ball of radius 3R/4. |
| s-setting#data | `avgH` (Setting:47) | PASS | Literal frozen realHamiltonian with complex-scaled perturbation εf. |
| fbounds | `avgA` (Setting:49) | PASS | Negative real angle partial of Re(f∘ι), coordinate by coordinate. |
| fbounds | `avgB` (Setting:52) | PASS | Real action partial of the same function. |
| s-setting#data | `avgM` (Setting:55) | PASS | Entry i,j is derivative of frequency component i along coordinate j. |
| Auxiliary source-data projection | `AveragingData.toData` (Setting:59) | PASS | Forgets dimension/rank fields; retains literal size-one analytic premises. |
| Auxiliary domain inclusion | `avgDomain_subset_Wdom` (Setting:62) | PASS | Uses s>0 to include B(R) in B(R+s); no extra premise. |
| s-setting#data compact bounds | `avg_compact_bounds` (Setting:82) | PASS | Constructs finite nonnegative Ω₀,M₂ before all I and row indices, on the full closed ball of radius R. |
| fbounds / fb-poly | `fbounds`; private `norm_fderiv_le` (Field:66) | PASS | The closed s/2 polydisc stays in the exact frozen strip/action tube; no R≤s assumption or enlarged analytic domain. |
| fbounds / fb-cauchy | `fbounds` (Field:126) | PASS | Size-one holomorphic f and radius s/2 give derivative norm ≤2/s, hence both max-norm bounds. |
| fbounds / fb-real | `fbounds` (Field:126) | PASS | Real chain rule yields the actual frozen field (ω+εB, εA), for every real ε. |
| averaged | `averaged` (Field:191) | PASS | Continuous real angle slice, coordinate period one, and integrable vector field yield zero unit-cube average. |

No extra theorem premise, changed norm, weakened design conclusion, or widened numerical-constant
dependence was found. Internal `1 ≤ n` and all-real ε in the field identity are exactly the design's
permitted generality. These local results do not need compact initial K or a solution-family premise.

The blueprint's real/complex partial identification is supplied by the imported `holo_real_b`
interface (HoloReal:200 onward): its k=1 identities for h+f and h, subtracted, identify the
perturbation derivative on real directions. `toData` supplies its premises and the domain inclusion
supplies membership. Field:49–59 independently proves the real-part derivative formula needed by
the estimates. Thus the exported result follows the approved real-field design signature; it does
not silently redefine a complex partial or invoke a whole-strip reality theorem.

## Definition classification and proof inspection

All nine new public type/object declarations above are faithful definitions on their complete
carriers. `AveragingData` is a source-premise proposition bundle; no inverse, bound, flow, or
conclusion is hidden in it. `avgH` is definitionally the intended Hamiltonian even for arbitrary
real ε. Private `avgF` (Field:30) is exactly Re(f∘ι), everywhere.

`avgA`, `avgB`, and `avgM` intentionally use Mathlib's total `fderiv`. Off differentiability domains,
this has the standard zero convention. No theorem uses that convention as a substitute for an
actual derivative: holomorphy and openness establish differentiability on Wdom, and real C³
regularity of h establishes C² frequency and continuous frequency derivative on B(R+s).
The compact closed ball lies strictly inside that domain because s>0.

For compact bounds, continuity and finite-dimensional compactness bound ω and the sum of all
absolute matrix entries; each row sum is bounded by that total. Taking max with zero makes both
witnesses nonnegative. The witnesses are upper bounds, rather than claims of attaining the exact
maxima written in the blueprint's informal notation. This is the expressly assigned finite-bound
deliverable, matches `envelopes_from_slab`'s hΩ/hM on the closed radius-R ball (design:815–818),
and does not weaken any required numerical estimate. No canonical maximizer is introduced.

The field identity differentiates Re h + ε Re f and preserves the Hamiltonian signs and coordinate
order. The averaged proof first proves continuity/integrability on the compact unit cube, commutes
coordinate projection with the Bochner integral, and uses `torusAverage_coordinate_eq_zero`.
It cannot succeed merely because a nonintegrable Bochner integral defaults to zero. Periodicity
comes from the frozen integer-shift hypothesis with a single-coordinate integer mode.

## Independent checks and exact receipts

All audit-owned Lean/Lake operations were sequential with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No resource override, cache command, clean, or unrestricted library build was used.

1. Targeted compile gate:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1201 KAM.Nekhoroshev.Averaging.Setting KAM.Nekhoroshev.Averaging.Field
   [inp-gate] slot 1 acquired 07:52:27 for KAM.Nekhoroshev.Averaging.Setting KAM.Nekhoroshev.Averaging.Field
   Build completed successfully (2899 jobs).
   ```

   Exit 0; no warnings or errors. The job count is Lake's dependency accounting for the targeted build.

2. Exact-signature examples and every new named public theorem's axioms:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1201Audit.lean
   'KAM.Nekhoroshev.AveragingData.toData' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.avgDomain_subset_Wdom' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.avg_compact_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.fbounds' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.averaged' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Exit 0; both examples accepted; no sorryAx or nonstandard axiom.

3. Kernel replay, one invocation for both package modules:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.Setting KAM.Nekhoroshev.Averaging.Field
   ```

   ```text
   replaying KAM.Nekhoroshev.Averaging.Field
   replaying KAM.Nekhoroshev.Averaging.Setting
   ```

   Exit 0; both module replays passed.

4. Repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (460 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Exit 1 solely for the permitted stale generated root. No 100-character-line violation:
   maximum lengths are 97 (Setting) and 99 (Field). Both files satisfy the module/header/docstring/
   public-section rules and remain below 1500 lines; definitions are exposed by their section.
   Scoped forbidden-token scan found no sorry/admit/axiom/unsafe/opaque/EuclideanSpace/set_option.

5. Import closure: recursively inspected 36 local KAM modules; no provider modules, frozen theorem
   modules, or DRAFT_SORRY theorem dependencies. The direct frozen imports are definition anchors.
   Consequently no imported frozen theorem's SEALED status is needed here.

6. `git diff --check inp...HEAD`: exit 0, no output.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty.
   `git diff -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty.
   Final report whitespace check and scratch cleanup are recorded below.

Audited source hashes:

```text
ff7136f9cedc798cc8ca51f767e2e1d1fc645405334feafd67f19e9934cec78e  KAM/Nekhoroshev/Averaging/Setting.lean
1e8797c4cf34ae101ff7120d3469936abe87c24b5dae8d49e85d1588e57e3053  KAM/Nekhoroshev/Averaging/Field.lean
```

## Notes, uncertainties, errata and deviations

No suspected new blueprint, frozen-statement, or pinned-source defect was identified in this scoped
audit. No independent re-audit of the original AKN06/Nei76 PDFs is claimed. The recorded historical
Nei76 maximum-error issue belongs to the later stopped-mean argument, outside N12-01.

The three extra helper theorems and placement of avgA/avgB in Setting agree with the handoff;
none changes the approved signatures or source objects. The finite-bound witness choice described
above is harmless for the assigned consumers. The remaining N12 packages, provider proofs and root
seals remain outside this verdict. The orchestrator must regenerate the root when landing; this
auditor did not change it.

Closeout: the temporary `.lake/abi-scratch/N1201Audit.lean` probe was deleted.
`git diff --no-index --check /dev/null docs/tracks/N/audits/N12-01-audit-1.md`: exit 0, no output.
Final status contains only the pre-existing untracked handoff and this new untracked report;
no tracked working-tree changes.

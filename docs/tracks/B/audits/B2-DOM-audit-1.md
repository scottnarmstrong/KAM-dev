# B2-DOM independent package audit 1

Verdict: **PASS WITH NOTES** for B2-DOM, as ordinary geometric infrastructure for the next one-step soundness package. No blocking mathematical or statement-fidelity defect found. No frozen anchor is proved or sealed by this package; provider/frozen type-equality and seal-body probes are therefore inapplicable.

Audited worktree: `/root/code/KAM-inp-b2dom`. Report destination is this worktree, following the user's explicit override of the generic audit brief's main-worktree destination.

## Revision and scope

- HEAD: `091cc83ee0a18c8679b17c2d06ba0ef6d2008b59`.
- Comparison ref `inp`: `a8005126dc3cb9ad964977b2c575184ab9034b9c`.
- Merge base: `81c50a9c7b92b41e9d687b66a8250c02547b73ec`.
- `git diff inp...HEAD`: only `KAM/EffectiveStability/PolyDomain.lean` (192 added lines) and `docs/tracks/B/audits/B2-DOM-handoff.md` (32 added lines).
- Lean file SHA256: `42a20cab40a9d00638922a633d0bbd6fd5726b82befbb672b38208688098ad3e`.

Read AGENTS, PLAN, DECISIONS, the generic package-audit brief, the handoff including AUDIT FOCUS, `/root/code/KAM-inp-b1/.drafts/B/brief-B1-common.md`, `brief-B2-DOM.md`, Track B SPEC and FREEZE-PROPOSAL, and program-b-plan §3.1 (lines 300–340). The controlling source for this unfrozen B package is the eight-item B2-DOM brief, rather than unrelated I/N/P theorem anchors. Inspected the actual consumer interfaces in Canonical Flow/FlowRegular and EffectiveStability RealFlow/Basic, Domains, and the frozen HamiltonianVectorFieldC and OscillatorAction definitions. No external-source assertion required a PDF review.

## Declaration review

All names below are in `KAM.EffectiveStability`; line numbers refer to `KAM/EffectiveStability/PolyDomain.lean`.

| Brief item / node | Declaration (line) | Verdict | Reason / note |
|---|---|---|---|
| 1 | `cpolyOpen` (31) | PASS | Exactly the requested coordinatewise open complex polydisc on the full stated carrier. |
| 1 | `isOpen_cpolyOpen` (34) | PASS | Finite intersection of strict norm sublevel sets; no positivity or dimension premise needed. |
| 2 | `gaugeScalar` (44) | PASS | Complex continuous linear equivalence multiplying by the real positive scalar's complex inverse. |
| 2, auxiliary | `gaugeScalar_apply` (49) | PASS | Definitional scalar-action identity, no extra premise. |
| 2 | `norm_gaugeScalar_apply` (52) | PASS | Exactly `‖W v‖ = ‖v‖ / δ`; uses `δ > 0`, no dimension factor. |
| 3 | `mem_gaugeInterior_cpolyOpen` (68) | PASS WITH NOTES | Closed gauge ball inclusion from strict coordinate margins. Required `0 ≤ c` retained but unused; premise order differs from implication presentation in brief without changing logical content. |
| 4, auxiliary | `differentiableOn_hamVFℂ_poly` (81) | PASS | On any open complex domain, holomorphy of φ yields holomorphy of its derivative and hence of the frozen Hamiltonian field. No polynomial premise; valid general helper. |
| 4 | `smallField_of_coord_bounds` (93) | PASS | Builds every SmallField field from the source premises, including holomorphy and the actual gauge bound from both coordinate-partial estimates. |
| 5 | `mem_realInterior_cpolyOpen` (113) | PASS | Real inclusion preserves coordinate absolute values; uses the full δ margin as requested. |
| 5 | `osc_subset_realInterior` (126) | PASS | Action `(p²+q²)/2 < c`, `2c ≤ r²`, and `r ≥ 0` imply both coordinate bounds; no positivity assumption on c added. |
| 5 | `oscClosed_subset_realInterior` (139) | PASS | Same reasoning with non-strict action bounds, including zero actions. |
| 6 | `cauchyDisc_subset_gaugeInterior` (152) | PASS WITH NOTES | Triangle inequality gives radius `r + δc`; strict remaining margin δ/2 puts the closed Cauchy polydisc in the half interior. Drops unnecessary `0 < δc`, a stronger result. |
| 7 | `flow_mem_cpolyOpen` (172) | PASS WITH NOTES | Direct specialization of `(flow_b h).2.2.1`, for arbitrary F satisfying SmallField, hence stronger than the Hamiltonian-only request. |
| 8 | `smallField_zero_smoke` (180) | PASS | Zero Hamiltonian, ε = 0; valid for arbitrary ρ and positive δ. |
| 8 | `zero_mem_gaugeInterior_smoke` (186) | PASS | Explicit `c*δ < ρ` supplies the required margin at the origin; c = 0 covers every positive ρ. |
| 2–3, private | `gauge_le_iff` (57) | PASS | Divides/multiplies by strictly positive δ. |
| 3, private | `coord_le_of_gauge` (61) | PASS | Coordinate norms are bounded by each Pi norm, each Pi norm by the product maximum norm. |

There are 15 new public declarations: two definitions and thirteen theorems, plus two private proof helpers. No additional public declaration, bundled field, instance, or conclusion-shaped hypothesis conceals a hard step. Explicit source assumptions in the brief are preserved; no constants acquire additional dependence.

## Definitions and mathematical checks

`cpolyOpen` is an exact set-builder on `(Fin n → ℂ) × (Fin n → ℂ)` for every real ρ, including empty or zero-dimensional cases. `gaugeScalar` is the intended inverse scalar map for every permitted δ, with no junk branch or fallback. There are no new abbrevs, structures, or instances. Both definitions are in `@[expose] public noncomputable section`.

The Pi norm is the sup norm and the product norm is the maximum of its two factors. Thus `‖W v‖ ≤ c` gives `‖v.1 i‖, ‖v.2 i‖ ≤ c δ`. Adding these to the strict center margins proves inclusion of the entire **closed** gauge ball, matching `Canonical.gaugeInterior` (Flow.lean:47–48); it does not merely prove center membership. No converse characterization was requested or claimed.

For φ, the frozen field is `(∂p φ, -∂q φ)`. The proof takes h2 for the first factor and h1 for the second, removes the minus sign under the norm, and uses the product maximum and Pi supremum to get `‖Xφ(z)‖ ≤ ε δ`. Dividing by δ proves the required `‖W(Xφ(z))‖ ≤ ε`. Holomorphy is derived with `ContDiffOn ℂ ∞`, not assumed for the field and not confused with the analytic order `⊤`.

For real charts, `realInterior W Ω c` is exactly `{x | ι x ∈ gaugeInterior W Ω c}`. The inclusion uses complex norms of real coordinates equal to absolute values. The oscillator inequalities correctly use action units: `p_i² + q_i² ≤ 2c_i ≤ r_i²`; the nonnegative r premise justifies taking coordinate square roots. The outer δ and half-interior δ/2 margins remain strict even for closed initial boxes and Cauchy discs.

For δc < 0 and n > 0 the Cauchy-disc set is empty, so omitting positivity remains correct; δc = 0 is also valid. Dimension zero is harmless throughout. The existing totalized `Canonical.flow` definition has a fallback, but `SmallField` and the half-interior premise allow the existing flow theorem to establish actual domain membership on all `[-1,1]`, endpoints included. This package adds no totalized flow definition.

The plan's larger obligation includes inverses and compositions. B2-DOM supplies the requested geometric inclusions and domain membership; it does not claim that the future one-step soundness theorem, inverse/composition accounting, or certificate checker is complete.

## Hygiene and exact checks

All Lean/Lake invocations in this audit were sequential and used the following wrapper (also applied around lint because its ABI check invokes Lean):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

No heartbeat, recursion-depth, or synthesis-budget override was used. Build used the prescribed compile gate and the existing build overlay; no clean, cache fetch, full library target, or application build was requested. The build driver's nested `nice -n 5` only further increases niceness.

Targeted build, exact command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b2dom KAM.EffectiveStability.PolyDomain
```

Output, exit 0, no warning:

```text
[inp-gate] slot 1 acquired 00:55:38 for KAM.EffectiveStability.PolyDomain
Build completed successfully (2940 jobs).
```

Kernel replay, exact command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 LEAN_PATH=/root/code/KAM-inp-b2dom/.lake/build/lib/lean lake env leanchecker --verbose KAM.EffectiveStability.PolyDomain
```

Output: `replaying KAM.EffectiveStability.PolyDomain`; exit **0**. This is the only newly added Lean module; no provider module exists. Explicit LEAN_PATH points at the audited worktree's artifact directory.

Axiom probe `.lake/abi-scratch/B2DomAudit.lean` imported the audited module and ran `#print axioms KAM.EffectiveStability.<name>` for each of the 15 public declarations. Exact invocation:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 LEAN_PATH=/root/code/KAM-inp-b2dom/.lake/build/lib/lean lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/B2DomAudit.lean
```

Exit **0**. Complete output:

```text
'KAM.EffectiveStability.cpolyOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.isOpen_cpolyOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.gaugeScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.gaugeScalar_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_gaugeScalar_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.mem_gaugeInterior_cpolyOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.differentiableOn_hamVFℂ_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.smallField_of_coord_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.mem_realInterior_cpolyOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.osc_subset_realInterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscClosed_subset_realInterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.cauchyDisc_subset_gaugeInterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.flow_mem_cpolyOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.smallField_zero_smoke' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.zero_mem_gaugeInterior_smoke' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Public short-name gate:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b2dom KAM.EffectiveStability.PolyDomain
```

Output: `short-name check OK (no reused public short name)`; exit **0**.

Python enumeration of the audited source's lines returned `line count: 192` and `lines >100: []`. Module header, copyright, public imports, docstring and exposed public section are present. `git diff --check inp...HEAD` returned no output, exit 0. The forbidden proof escapes/resource overrides and ambient-type rules are also covered by the lint below.

A recursive inspection of the 37 local KAM modules in the import closure found no provider and no frozen theorem import. The nine imported frozen entries are all definitions with manifest state SEALED: ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, and Planetary/OscillatorAction.

Protected-path command:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md KAM/Root lakefile.lean
```

No output; exit **0**.

LINT_RESULT_PENDING

## Notes, errata and handoff

- N1: `mem_gaugeInterior_cpolyOpen` retains unused `_hc : 0 ≤ c` because the brief explicitly requests it. This is redundant source data, not a conclusion premise or defect; removing it would strengthen the API, but no repair is required.
- N2: Cauchy radius positivity is dropped and flow membership is generalized to arbitrary SmallField F. Both are mathematically valid strengthenings. Item 3's binders are reordered from the brief's implication presentation; there is no frozen ABI here.
- No suspected pinned-source or blueprint defect found in this scope. No Lean proof or source deviation introduced by the auditor.
- No default-heartbeat failure or memory-cap failure observed. No remaining uncertainty about the checked declarations; future soundness assembly remains outside this package.
- Only this report was edited in the repository. The axiom probe was created under `.lake/abi-scratch/` and removed after use. No state-changing git command was run.

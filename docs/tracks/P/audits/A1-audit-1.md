# A1 independent package audit 1

**Overall verdict: PASS WITH NOTES.** All three A1 declarations pass statement fidelity, completeness, proof, axiom and kernel checks. The only validation exception is the expressly permitted stale generated `KAM.lean` lint notice. No blocking finding.

Audit date: 2026-10-28. Audited only `KAM/Planetary/AMD/Elements.lean`, as required by the handoff's AUDIT FOCUS. HEAD: `2a9f95f0502f87c82402239ffad6c2ed39509b78`; comparison ref `inp`: `3444c636bc3b49d0d73986ef0898f7f976454760`. `git diff inp...HEAD` contains exactly this new 275-line module. Module SHA-256: `22cef00dacea4cdb787379958b6f5ff0e46d6eb359167a9d31833dec49aa7d78`.

## Authority and scope

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local `A1-handoff.md`, P14-LEAN-DESIGN.md (A1 row, Appendix A and node rows), both DESIGN-P14 design audits, the relevant track-P statement text, blueprint p14a lines 42–73, Kepler/Plane and the frozen definitions actually used.

The user's explicit absolute report path overrides the generic brief's main-worktree destination. This report is in `/root/code/KAM-inp-p14-a1`, not `/root/code/KAM-inp`. No source, generated file, frozen file, manifest or git state was edited. The pre-existing untracked A1-handoff.md was preserved. The temporary probe was confined to this worktree's `.lake/abi-scratch/` and removed afterwards.

**Per-anchor disposition:** no frozen anchor is assigned to A1. This is an ordinary helper package, with no provider export or seal body. Provider-versus-frozen equality and literal seal-body probes are therefore inapplicable. The four eventual P14 root anchors are outside this audit; none is certified seal-ready here. Instead, all three ordinary exports were checked against their exact independent design contracts.

## Statement fidelity and completeness

For each public theorem, Python extracted the complete declaration header through the type (before `:=`) and compared it byte for byte with both `/root/code/KAM-inp/.drafts/design/P14Signatures.lean` and Appendix A. Results:

```text
elements signature bytes equal: True Appendix A bytes equal: True
eccentricity_deficit signature bytes equal: True Appendix A bytes equal: True
ecc_bound signature bytes equal: True Appendix A bytes equal: True
```

Original signature-file SHA-256: `cd28718f0ef82c8da477ff5be2985046d08d795614be4d36fd0b7e267de98dd7`; design SHA-256: `a283ad509cb312a6c3ea06b6d94ce031903d7d05a5604d23553c17b9b7050ef7`. These match the revision-2 audit inputs. Audit 1's F2 is resolved: the first two helpers assume only the selected planet's four scalar conditions, not all-planet ellipticity. No extra premise, weakened conclusion, altered carrier, hidden constant dependence or conclusion-shaped public hypothesis was found.

The A1 package row (design line 367) names exactly `elements`, `eccentricity_deficit`, `ecc_bound`; the implementation's complete public theorem inventory is exactly these three names. Design lines 97–106 assign precisely the elements/ecc-bound nodes and eight internal steps below to AMD/Elements. There is no missing A1 declaration. `amdOuter`, `amdInner`, `amdCollar`, `amdCompact`, `geometry`, `amd_compact` and `closure` belong to adjacent packages.

All names below are in `KAM.Planetary`; line numbers refer to Elements.lean.

| Node / obligation | Lean declaration | Verdict | Evidence / reason |
|---|---|---|---|
| `bpP:p14:elements` | `elements` (134–213) | PASS | Exact contract; all elementary conclusions of blueprint (a)–(f), with the threshold part in the next helper. |
| `stepP:p14:el-a` | `elements`, via private `elements_scalar` | PASS | Positive axis/action, action square and energy identity from the literal definitions and positive mass/negative energy. |
| `stepP:p14:el-b` | `elements`, via `planeSq_ecc_aux` and `elements_scalar` | PASS | Component expansion proves the Lagrange identity consequence; exports eccentricity square, eccentricity below one, C≤Lambda, nonnegative eccentricity and the positive square-root identity. |
| `stepP:p14:el-c` | `elements` | PASS | Both dot-product identities are exported; coordinate algebra derives C²/m²−r without an assumed identity. |
| `stepP:p14:el-d` | `elements` | PASS | Both radial bounds follow from Kepler/Plane.abs_planeDot_le and the proved eccentricity bound; divisions/cancellation use positive 1±eccentricity. |
| `stepP:p14:el-e` | `elements` | PASS | Strict momentum-square bound follows from negative Kepler energy. Frozen planeSq is the physical squared Euclidean length. |
| `stepP:p14:el-f` | `elements`; `eccentricity_deficit` (217–231) | PASS | Equality and nonnegativity of the deficit are in elements; the separate exact-signature helper proves the full threshold inequality by square-root monotonicity. |
| `bpP:p14:ecc-bound` | `ecc_bound` (234–271) | PASS | Exact all-planet contract and both strict conclusions. |
| `stepP:p14:eb-sum` | `ecc_bound`, local hdef/hsum/hle | PASS | Unfolds the original physicalAMD and totalMomentum; each nonnegative deficit is at most their sum, which is strictly below A. |
| `stepP:p14:eb-ecc` | `ecc_bound` | PASS | Positive threshold factor and strict lo<Lambda give deficit below Lambda times the threshold factor; eccentricity_deficit gives the contradiction, and rearrangement gives the angular-momentum conclusion. |
| Internal algebra | private `planeSq_ecc_aux` (38–56) | PASS | Coordinate polynomial identity under positive mass/radius; no unproved analytic step. |
| Internal scalar proof | private `elements_scalar` (60–131) | PASS | Its identity premises are derived inside elements before application; this private conditional helper does not replace a source theorem. |

## Definitions, carriers and imports

There are **no new def/abbrev/structure declarations**. The two private additions are theorems. Local `set` and `generalize` commands introduce proof variables only, not replacement physical objects.

The consumed frozen objects retain their intended bodies: bodyVector extracts Cartesian pairs; planeSq/planeDot/planeCross are their coordinate formulas; planeLength is sqrt(planeSq); keplerEnergy, keplerAxis, keplerAction and keplerEccVector are the literal mass-scaled formulas; physicalAMD is sum(action) minus totalMomentum. Positive mass, positive radius, negative energy and positive cross product guard the used divisions and square roots. Derived positive axis/action and 1−eccentricity² justify later operations. No total-function fallback is used to obtain a conclusion outside these guards. Circular points remain allowed.

A recursive static traversal found 48 KAM modules in the import closure, **zero provider imports and zero frozen theorem imports**. Frozen imports are definitions, so there is no DRAFT_SORRY or sealed-theorem dependency to authorize. Existing Kepler/Plane facts supply physical length identities and Cauchy–Schwarz; the long algebra is proved locally. Searching all other KAM Lean files for declaration sites of each of the three names found none. The compilation and axiom checks corroborate that there is no public name collision or untrusted proof dependency.

## Independent checks and exact output

All Lean/Lake invocations were sequential and used `LEAN_NUM_THREADS=1` and `nice -n 5`. The build wrapper itself applies nice. No resource overrides, cache operations, library clean/rebuild request or generated-root regeneration was performed. The compile-gate wait was expected and completed normally.

1. Targeted gated build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-a1 KAM.Planetary.AMD.Elements
```

Output, exit **0**:

```text
[inp-gate] slot 2 acquired 15:11:40 for KAM.Planetary.AMD.Elements
Build completed successfully (9094 jobs).
```

2. Exact-contract elaboration and axioms:

The probe imported only KAM.Planetary.AMD.Elements and copied each complete theorem header from the independent original signature file under `audit_<name>`. Bodies were respectively `by exact elements i hz`, `by exact eccentricity_deficit i hz he he1 hle`, and `by exact ecc_bound hz hlo hact hA he he1 hbar`. For each name it additionally elaborated `example : type_of% @audit_<name> := @<name>`. Thus the explicit binder applications and the full polymorphic types both check; no admitted signature file was imported. It then printed axioms for all three public results.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/A1Audit.lean
```

Output, exit **0**, no warnings/errors:

```text
'KAM.Planetary.elements' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.eccentricity_deficit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ecc_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay, one invocation for the sole new lemma module:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.AMD.Elements
```

Output, exit **0**:

```text
replaying KAM.Planetary.AMD.Elements
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Output, exit **1**, solely the expressly permitted generated-root exception:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (766 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The root was left unchanged. The module has 275 lines, the required copyright/module/public imports/docstring/public section, and no sorry, admit, axiom, unsafe, opaque, EuclideanSpace or set_option occurrence. Lint found no other source issue.

5. Scope and whitespace:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
git diff --check
```

Each exits **0** with no output. Post-audit status contains only the pre-existing untracked handoff and this new untracked report; the scratch probe is removed and tracked source contents remain unchanged.

## Notes, uncertainty and errata

No suspected pinned-source defect, blueprint defect or new implementation deviation was found in the audited slice. This is a local blueprint/contract/proof audit, not a renewed pinned-PDF audit or closure of the downstream AMD, exponential-safety or secular-box theorems. The design's inherited analytic/chart/N-release obligations remain outside A1.

`eccentricity_deficit` retains the contract's he1 premise although the proof does not need it independently; it is already implied by hle and elements. This is harmless and preserves the exact approved design signature. No default-heartbeat design failure occurred in the independent checks. The sole delivery note is the allowed generated-root lint exception, to be handled by the orchestrator.

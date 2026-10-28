# N11-B independent package audit 1

Overall verdict: **FAIL against the explicit no-reused-public-short-name audit requirement**.
The mathematical statements, literal definition bodies, and assigned N11-B surface match the
approved signatures. The failure is naming hygiene, not a mathematical counterexample or an
extra premise. No frozen theorem is sealed by this infrastructure package.

| Anchor / package result | Verdict |
|---|---|
| N11-B infrastructure acceptance | FAIL, F1 naming policy conflict |
| `KAM.Nekhoroshev.exponents` proof/source/signature | PASS |
| N11-B literal bodies and source-data carriers | PASS |
| Frozen `KAM.Nekhoroshev.partialConvex_nekhoroshev` | FROZEN_UNPROVED (`DRAFT_SORRY`), outside this package; not seal-ready |

There is no provider export or seal body in N11-B, so the brief's provider-to-frozen-type
probe is inapplicable. The theorem/definition probes below check the actual B exports.

## Scope and fixed inputs

Audit date: 2026-10-28. Only `KAM/Nekhoroshev/Partial/Constants.lean` is audited.
Permission: report-only writes, transient probes under this worktree's `.lake/abi-scratch/`,
read-only git, serialized Lean checks with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The user's exact report destination overrides the brief's generic main-worktree destination.
Method: focused tier-2 statement/body audit, mathematical reconstruction, separate adversarial
recheck of candidate findings, then build/kernel/axiom/hygiene checks. No subagents or network.
Read AGENTS.md, PLAN.md, DECISIONS.md (including D25), package brief, handoff, both N11 design
audits, design/package/node tables, track statement, relevant frozen definitions and theorem,
and p11a/p11c source spans. The pinned blueprint and frozen exponent formulas are the source
boundary here; this is not a fresh audit of the historical Nek77 scan.

| Input | Revision / SHA-256 |
|---|---|
| Audited HEAD | `0980c13b4c714c9a839beda1cb79dcab166bc14c` |
| Compared `inp` ref at start | `d1a02150c8e815febce9e0fade2dd194d5ee7795` |
| Merge base | `a341f3aebaad7052378f3fd4846d8619bf8da9d9` |
| Constants.lean, 112 lines | `c181ba74380c4ab9cc82b69ad28c4d2e1f29b39977c943d433e856c0d162e2b0` |
| Delivered N11Signatures.lean | `23bd2cc2645243b3357acccda6e04ff69fad4d055963010025c582f3c886a0e4` |
| N11-LEAN-DESIGN.md | `f0fd0d111b6abd5c335a5ea144135a07b28be326f3d699f3c2761c46ad097609` |
| DESIGN-N11-design-audit-1.md | `7fa316de9f393f151c995fe5b6ee2fe56953f6a551821dd52acad1e91c56517d` |
| DESIGN-N11-design-audit-2.md | `4501712ff383cbcd0395d8406ddf087ba000738c5b2177b107c887d6e23d6b20` |
| p11a-partial-route.tex | `dede87e5ec7b638136dff072abbf021b24ed4a4cedf6befae88eddf6e87d57b3` |
| p11b-partial-nf.tex | `4005a51b99ed21cba7c6cbca27b8e70392f9d8d6c67d6b59fec9e25cac51232d` |
| p11c-partial-stability.tex | `5d6fe7fc6b09459b6bf307596832695fcda1b62bf5292bd926d84bf216f7b7ea` |
| Current N DEPGRAPH.md | `4d44f80153235af569f33d044867418ce493e7bec550ee6de6e9471ac53c5a60` |

`git diff inp...HEAD` adds exactly this one 112-line Lean file. The handoff was already
untracked on entry. Graph status has evolved since the design fingerprint; the four audited
node contracts were read live and agree with the cited source spans. No graph status is edited.
The shared `inp` ref advanced during this audit (to `a81e8d4215d2f99f8c148dd4ca24915a17ca95b5`
at final comparison); HEAD and all three audited module/design/signature hashes stayed fixed,
and `git diff inp...HEAD --stat` still shows only the same 112-line addition.

## Findings and refutation

**F1 — naming hygiene, survives refutation.** The prompt's controlling handoff focus says
“no reused public short name”. At Constants.lean:103, `def constants` repeats the public
short name at `KAM/Planetary/TwoScale/Constants.lean:44`; that file's namespace at line 27 is
`KAM.Planetary`. At Constants.lean:70, `def kappa` repeats public short names in
`KAM/Apost/Constants.lean:60` (`KAM.Apost.kappa`) and
`KAM/Iso/R3bp/Region.lean:62` (`KAM.Iso.R3bp.kappa`).

Adversarial recheck: these are different fully qualified names, so they are legal Lean and do
not cause declaration replacement or root shadowing. All appear in public sections. Namespace
qualification refutes a *full-name collision* allegation but does not satisfy the explicitly
stated *short-name* prohibition. Both N11 definitions are exact signature requirements; silently
renaming them would violate the other controlling requirement. The package therefore needs an
explicit policy resolution or coordinated signature revision before this hygiene gate passes.
No rename is made by this report. No mathematical theorem is rejected on this ground.

**N1 — handoff correction.** The handoff says the earlier `constants` is
`KAM.Planetary.TwoScale.constants`; the source declares `KAM.Planetary.constants`.
Its claim “No other clashes found” misses `kappa`. This is a receipt accuracy issue, separate
from proof validity.

No suspected new pinned-source defect was found in the audited constants/exponents.
The earlier design's open-ball and adjoint-locator notes concern other packages and are not
reclassified as N11-B findings. Earlier design F1–F4 were repaired at design revision 2 and
none concerns this unchanged constants surface.

## Declaration and node ledger

Names below are relative to `KAM.Nekhoroshev`; `PC` means `PartialConstants`.
PASS here describes mathematical/signature fidelity; F1 separately controls package acceptance.
A = p11a-partial-route.tex; C = p11c-partial-stability.tex at the hashes above.

| Node / source | Lean declaration | Verdict | Evidence |
|---|---|---|---|
| bpN:p11:exponents, A67–73 | exponents | PASS | Exact signature; frozen a=2/q, b=3/q; only n≥2. |
| stepN:p11:ex-den, A71 | internal exponents | PASS, internal | Positive denominator by nlinarith; 2<3. Stronger q≥32 is elementary, independently probed. |
| stepN:p11:ex-cmp, A72 | internal exponents | PASS, internal | Positive-denominator cross multiplication; 6n²−15n+14>0. |
| bpN:p11:constants, A78 | PartialConstants | PASS | Fields n,ρ,g,m,Mc only. |
| A79 | PC.s | PASS | ρ/(4π). |
| A79 | PC.m1 | PASS | m/(2π). |
| A79 | PC.M1 | PASS | Mc/(2π). |
| A79 | PC.g1 | PASS | g/(2π). |
| A79 | PC.r0 | PASS | min(ρ/2,32g/m). |
| A79 | PC.A | PASS | 40Mc/m, source's second literal formula. |
| A80 | PC.eps0 | PASS | m1*r0²/(2^14*A^(2n)); natural exponent 2n. |
| A80 | PC.R0 | PASS | r0/A. |
| A80 | PC.kappaC | PASS | Weighted.coth(πs)^n. |
| A80 | PC.cK | PASS | (2π*eps0/kappaC)^(1/(2n)); real exponent. |
| A81 | PC.eps | PASS | kappaC*μ/(2π). |
| A81 | PC.K | PASS | (eps0/eps μ)^(1/(2n)); real exponent. |
| A81 | PC.d | PASS | μ^(frozen partialDriftExponent n). |
| A81 | PC.kappa | PASS math; FAIL F1 | 2π*K μ*s/sqrt(n), exact source and signature. |
| C147,C156 | PC.rTheta | PASS | r0/(A*K μ)^n. |
| C156 | PC.blockTime | PASS | s*m1*rTheta μ/(240*M1*eps μ)*exp(kappa μ/6). |
| A78 / frozen premises | PartialData | PASS | Exact signature fields; expanded below. |
| A78–81 | constants | PASS math; FAIL F1 | Exact projection ⟨n,ρ,g,m,Mc⟩. |
| A78 / HasDefiniteFastPart | DefiniteSign | PASS | Literal selected single global sign and original frequency/Hessian inequalities. |

The type of `exponents`, the complete `PartialConstants` namespace block, `PartialData`,
`constants`, and `DefiniteSign` compare byte-for-byte with their delivered signature commands
(except the theorem proof replacing its design `sorry`). There are 21 explicit declarations:
one theorem, two structures, and eighteen defs. Generated structure projections/recursors are
standard elaborator declarations, not additional source lemmas.

The export's three inequalities are an equivalent arithmetic presentation of A68, as both
design audits explicitly recognize. The probe derives b<1/(2n) and all three positive gamma
consequences from the export alone, with no extra premise. The implementation uses q>0 rather
than storing q≥32; the design explicitly allows the two proof steps to remain internal.
It is not an independent exported theorem with a renamed or weaker source-node conclusion.

The N11-B row (design:349) is complete. `block_setting`/`blockPert` and the associated
`signedH`, `signedF`, `slowScale` physical/scaled construction belong to N11-E3 Domain
(design:354), whose signatures:653–667 use PartialBlock from N11-A. `hessian` belongs to
N11-E3 Hessian. Their absence here is not missing work. Source aliases w=d/4 and K_a=K/sqrt(n)
are represented in that block construction and consumer expressions; μ0 belongs to N11-O
`threshold` (design:369), and p,q,b_c are covering/normal-form parameters. This report certifies
the design-assigned B slice of bpN:p11:constants, not every later inequality or threshold in
the broad source definition. N11-G's upstream dispatch gate remains outside scope.

## Premise and definition audit

The complete binder test for the only new public theorem is:

| Binder | Bin | Source |
|---|---|---|
| implicit n : ℕ | TYPING | A68, dimension |
| explicit hn : 2≤n | SOURCE | A68, “For n≥2” |

Counts: SOURCE=1, STANDING=0, TYPING=1, RULED=0, EXCESS=0. No k binder is captured.
No source proof result is a theorem premise.

Expanded `PartialData` fields and logical inputs:

| Field / expanded condition | Bin | Frozen theorem / definition evidence |
|---|---|---|
| indices n,k; G,G′,D; ρ,g,m,Mc; h | TYPING/source data | PartialConvexNekhoroshev.lean:49–59, same carriers |
| hn, hk | SOURCE | Frozen theorem:49 |
| hG, hGc | SOURCE | :51 |
| hG′, hGc′, hD | SOURCE | :52 |
| hρ, hMc | SOURCE | :53 |
| collar | SOURCE | :54, closed max-norm ball |
| hol | SOURCE | :56 |
| C2 | SOURCE | :57 |
| real | SOURCE | :58–59; realInclusion unfolds to coordinatewise complex inclusion |
| Hess | SOURCE | :60, actual complex operator norm, same bound |
| definite: 0<g | SOURCE | HasDefiniteFastPart.lean:36 |
| definite: 0<m | SOURCE | same |
| definite: real C³ on U | SOURCE | same, U is real slice of actionNbhd G′ ρ |
| definite: ∃ single global σ=±1 | SOURCE | :37 |
| definite: for all I∈U, frequency lower bound | SOURCE | :38 |
| definite: for all I∈U,v, signed Hessian lower bound | SOURCE | :39 |

No EXCESS fields, normal-form outputs, stability bounds, frequency upper bounds, nonempty-G
assumption, μ/P/C/z/t, or future slow confinement are bundled. Empty G and D remain allowed.
`DefiniteSign` is the last source witness predicate, not an assumed existence theorem: a probe
extracts `∃ σ, DefiniteSign a σ` directly from `a.definite.2.2.2`.

Classification for every definition/structure in the ledger: **literal**.
For each, BODY_MATCH=OK; PUBLIC_CARRIER=OK; WELL_DEFINEDNESS=N/A_LITERAL;
CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS.
`PartialData` is a literal source-data record; `PartialConstants` is an unrestricted numerical
record, and `constants` is its literal projection, not arbitrary choice. `DefiniteSign` is a
literal source predicate. All sixteen PC functions are the exact arithmetic bodies in the
ledger; no piecewise/default/fallback branch or hidden choice occurs. Source A82 explicitly
says “the numerical definitions themselves are meaningful for every data”; Lean total division
and real powers do not assert positivity off the source domain. No positivity theorem is
claimed for arbitrary PC. `coth` unfolds to cosh/sinh (Weighted/Norm.lean:167).

## Verification

Static import closure follows 37 project modules. All 23 reachable frozen anchors are SEALED
definitions; no provider or DRAFT_SORRY theorem is reachable. This checks the actual manifest
states rather than assuming every frozen import is admissible. No global instance, root
namespace declaration, or shadow of a pre-existing fully qualified declaration is introduced.
The two short-name repetitions are exactly those in F1. All definitions are in the exposed
public noncomputable section; the file has the required header/module/docstring/interface.

Fresh mechanical checks: 112 lines, maximum line width 94 characters; forbidden token scan
for sorry/admit/axiom/unsafe/opaque/EuclideanSpace/set_option returned `[]`.
`git diff --check` exits 0 with no output.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` has no output.

1. Targeted build, independently rerun:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
     /root/code/KAM-inp-n11b KAM.Nekhoroshev.Partial.Constants
   ```

   Exit **0**. Output:

   ```text
   [inp-gate] slot 2 acquired 18:38:46 for KAM.Nekhoroshev.Partial.Constants
   Build completed successfully (2899 jobs).
   ```

   This is the targeted cached dependency closure, not a clean library rebuild. No warnings.
   The wrapper executes `nice -n 5 lake build`; the gate wait preceded the build.

2. Transient exact-type, defining-equation and source-premise probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11BAudit1.lean
   ```

   Exit **0**, no warnings/errors. Probe imports only the audited module. It applies
   `@KAM.Nekhoroshev.exponents` at the exact signature type, checks all sixteen numerical
   defining equations by `rfl`, checks the `constants` projection by `rfl`, extracts the global
   sign from the frozen definiteness bundle, derives every omitted comparison/gamma consequence
   from `exponents`, proves the source's stronger denominator bound q≥32, checks a(2)=1/16 and
   b(2)=3/32, and constructs `PartialData` directly from the exact frozen input binder types.
   Thus no signature-copy `sorry`, draft theorem, or helper premise is part of the probe.

   Independent `#print axioms` output for `KAM.Nekhoroshev.exponents`:

   ```text
   'KAM.Nekhoroshev.exponents' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Every one of the eighteen defs (PC.s through PC.blockTime, constants, DefiniteSign)
   independently prints the identical axiom list. No sorryAx or project axiom occurs.

3. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
     KAM.Nekhoroshev.Partial.Constants > .lake/abi-scratch/N11BAudit1-kernel.log 2>&1
   ```

   Exit **0**. Complete output:

   ```text
   replaying KAM.Nekhoroshev.Partial.Constants
   ```

4. Source lint, serialized after kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely the brief-permitted generated-root exception. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (880 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No root regeneration was performed. The ABI subprocess inherits the single-thread
   environment and nice priority. No Lean/Lake/checker checks in this audit overlapped.
   The lint exception is nonblocking under the explicit brief; it is not the reason for F1.

5. Final artifact validation:

   ```sh
   git diff --check
   git diff --no-index --check /dev/null docs/tracks/N/audits/N11-B-audit-1.md
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git status --short
   ```

   `git diff --check` exits 0. The no-index check exits 1 with no diagnostics (the report
   is a new file relative to /dev/null); there are no whitespace errors. The protected-path
   diff is empty. Final status contains
   only this new report and the pre-existing untracked handoff. The temporary
   `N11BAudit1.lean` and `N11BAudit1-kernel.log` were deleted after recording their results.
   The audited source hash is unchanged. No production/source/manifest/generated file,
   package cache, or git state was edited by this auditor.

## Closeout

All 21 explicit declarations have been classified; exact signatures/bodies, numerical source
correspondence, source-premise expansion, assigned-slice completeness, kernel replay, axiom
closure, targeted build and required lint are checked. No unresolved mathematical finding or
new source erratum remains in this bounded slice. The short-name policy conflict F1 survives
refutation and blocks an unqualified package PASS. Resolving it requires an explicit naming
policy exception or coordinated signature/name changes by the owner/orchestrator, followed by
a narrow recheck. The report makes no provider or frozen-theorem closure claim.

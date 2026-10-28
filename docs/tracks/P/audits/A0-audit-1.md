# A0 independent package audit 1

Audit date: 2026-10-28. Scope: **only** `KAM/Planetary/AMD/Setting.lean`.

## Verdict

**PASS WITH NOTES**. The four definitions implement A0 exactly. A0 contains no theorem, provider, or frozen anchor to seal; provider/frozen-type and explicit-binder seal-body probes are therefore not applicable. This verdict establishes the definitions package only, not geometry, compactness, closure, confinement, or any P14 theorem.

The note is the brief-permitted stale generated `KAM.lean` (see lint receipt below). It must not be regenerated in this report-only audit.

## Inputs and comparison

- Worktree: `/root/code/KAM-inp-p14-a0`; HEAD `f93fcab7f864beeea93f907339924a5da0f37649`; comparison ref `inp` at inspection `dca5e7e3ee3a8b0d8f0f2b53a377bf87ac1fc024`.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/P/audits/A0-handoff.md`, including its narrowed AUDIT FOCUS.
- `git diff inp...HEAD --stat`: one new file, 43 insertions, `KAM/Planetary/AMD/Setting.lean`. The complete implementation diff was read.
- Implementation SHA-256: `eea0d8147e0072114206a1bf38577b6123fec87a84e4aff87ee1b719b8781eb0`.
- Design: `docs/tracks/P/design/P14-LEAN-DESIGN.md`, row A0 at line 366, node row at line 135, Appendix A lines 637–648. SHA-256 `a283ad509cb312a6c3ea06b6d94ce031903d7d05a5604d23553c17b9b7050ef7`.
- The signature file is absent in the package worktree. Read the original `/root/code/KAM-inp/.drafts/design/P14Signatures.lean` read-only; SHA-256 `cd28718f0ef82c8da477ff5be2985046d08d795614be4d36fd0b7e267de98dd7`. The four-definition block is byte-identical to both that file and Appendix A (Python substring comparison: `True` for each).
- Design audits are under `/root/code/KAM-inp/docs/tracks/P/design/DESIGN-P14-design-audit-{1,2}.md`, rather than the handoff's suggested audits directory. Read them there. Audit 1 classifies these four objects as literal wrappers/geometric inequalities; revision-2 audit passes the repaired design and confirms the definitions unchanged. Those receipts are context, not substitutes for this audit's checks.
- Read the relevant track-P statement, especially lines 446–515, and blueprint `blueprint-P/parts/p14a-amd-expsafe.tex`: outer/inner at 20–24, geometric set at 75–90, collar at 93–102. Read the six directly imported frozen definitions and their relevant guards, Kepler-energy/axis, angular-momentum, and plane-square definitions.
- The user's explicit absolute report destination overrides the generic brief's main-worktree output instruction. All persistent audit edits are confined to this report. The pre-existing untracked `A0-handoff.md` is untouched.

## Declaration ledger and definition classification

All names below are in `KAM.Planetary`; all four implement `bpP:p14:conv#data` (the compact/collar bodies are specified in the later geometry/closure nodes as well).

| Node / declaration | Implementation locator | Verdict | Meaning and fidelity |
|---|---|---|---|
| `bpP:p14:conv#data` / `amdOuter` | `Setting.lean:29` | PASS | Literal frozen `LowAMDRegion B.mass B.lower B.upper B.outerAMD`; outer endpoints and A1 retained. |
| `bpP:p14:conv#data` / `amdInner` | `Setting.lean:30` | PASS | Literal frozen `LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD`; inner endpoints and A0 retained. |
| `bpP:p14:conv#data`, `bpP:p14:closure(b)` / `amdCollar` | `Setting.lean:31` | PASS | Exactly the subset of the outer region with closed action bounds `lower + delta ≤ Lambda ≤ upper - delta` and AMD `≤ initialAMD + n*delta`; both conjunctions, all indices and the n coefficient retained. |
| `bpP:p14:conv#data`, `bpP:p14:geometry` / `amdCompact` | `Setting.lean:35` | PASS | Exactly K1: closed radial bounds d,R, momentum bound `mass i * sqrt (2/d)`, and all distinct ordered pairs separated by d. No angle coordinates, additional constraints, or missing pair order. |

**Whole-carrier classification.** Each object is a total set-valued definition on the intended physical carrier `Phase (n*2)`; the implicit dimension is arbitrary `n : ℕ`, B is the literal frozen `AMDBox n`, and delta is arbitrary real. There are no new structures, instances, abbreviations, witnesses, conditionals, default branches or junk-value constructions. The bodies define precisely their written predicates even for inadmissible B or nonpositive delta; no geometric theorem is asserted there. Later source results supply `2 ≤ n`, B.Admissible and the required delta margins. Adding these as definition parameters would unnecessarily change the exact contract.

`LowAMDRegion` includes `ProgradeElliptic`, which supplies positive masses/radii, negative Kepler energy and positive angular momentum before any physical interpretation of totalized Kepler formulas. `amdCollar` retains this guard through outer membership. `amdCompact` does not use Kepler quantities: its square root/division is the literal source geometric bound, interpreted under positive distance in later admissible-box theorems. No theorem here exploits its total value at zero or negative distance. `planeLength` is the frozen square root of the sum of squares, not the ambient Pi max norm; `bodyVector` uses frozen `finProdFinEquiv` and correctly extracts positions from z.1 and momenta from z.2.

The identifier `amdCompact` alone proves neither compactness nor collision freedom for arbitrary box data. Those are assigned to A2 under source hypotheses, as are the inclusion of the outer region in this set and the inner/outer inclusion. No conclusion-shaped premises or hidden proof obligations occur in A0.

## Completeness supplement (orchestrator request)

**PASS: all 4 assigned declarations are present; missing declarations: none.** This checks the full design assignment, independently of the prover brief's summary.

Searched the entire P14 design for every `AMD/Setting` occurrence and parsed every node-table row whose module column is exactly `AMD/Setting`. The only node assignment is design line 135 (`bpP:p14:conv#data`); the separate package table at line 366 assigns that module to A0. That node's complete declaration list is `amdOuter`, `amdInner`, `amdCollar`, `amdCompact`. There are no additional node rows assigning a theorem, helper, structure, abbreviation or instance to this module.

Cross-checked the assigned names against all declaration headers in the original `/root/code/KAM-inp/.drafts/design/P14Signatures.lean`: their definitions are at lines 114–125 (headers at 114, 115, 116 and 120). Compared that expected inventory with all declaration headers in `KAM/Planetary/AMD/Setting.lean`, rather than checking only whether the four expected strings occur. Exact set comparison gives:

```text
Expected declarations: ['amdCollar', 'amdCompact', 'amdInner', 'amdOuter']
Expected names absent from signatures: []
Actual declarations: ['amdCollar', 'amdCompact', 'amdInner', 'amdOuter']
Missing: []
Extra: []
```

The following `elements`, `eccentricity_deficit`, `ecc_bound`, `geometry`, `amd_compact` and `closure` signatures are assigned to A1/A2/A3 in the full design, not A0. In particular `amd_compact` (a theorem) is distinct from A0's `amdCompact` (a set definition), and is explicitly an A2 output at design line 368. Its absence from Setting is therefore not a completeness finding. No change to the overall PASS WITH NOTES verdict.

Only the report changed for this supplement; the earlier build, exact-body probes, axiom checks, kernel replay and lint receipts remain applicable to the unchanged Lean module.

## Independent verification

All Lean/Lake checks are serialized with `LEAN_NUM_THREADS=1`, and run at niceness 5. No resource override, cache repair, root regeneration or state-changing git command is used.

1. Targeted gated build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-a0 KAM.Planetary.AMD.Setting
   ```

   Output, exit **0** (wrapper runs `nice -n 5 lake build`):

   ```text
   [inp-gate] slot 1 acquired 15:04:30 for KAM.Planetary.AMD.Setting
   Build completed successfully (9090 jobs).
   ```

2. Independent signature/body/axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/A0Audit.lean
   ```

   Exit **0**, no errors or warnings. The probe imports only the implemented module; it copies the four definitions from the original signature file under fresh `auditRef_` names. For each name D it elaborates both `example : type_of% @D := @auditRef_D` and `example : @D = @auditRef_D := rfl`. Thus implicit dimensions, inferred set carriers, telescopes and bodies are checked, rather than merely textual spelling. Four `#print axioms` commands output:

   ```text
   'KAM.Planetary.amdOuter' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.amdInner' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.amdCollar' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.amdCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   There are no provider exports or public theorems; all four public definitions were checked as an additional safeguard. No `sorryAx` occurs.

3. Kernel replay, single invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.AMD.Setting
   ```

   Exit **0**, output:

   ```text
   replaying KAM.Planetary.AMD.Setting
   ```

4. Source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely the permitted generated-root exception; exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (766 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No other lint diagnostics. The generated root was left untouched as required.

Static checks already completed:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check` and `git diff inp...HEAD --check`: no output, exit 0.
- `rg -n '\b(amdOuter|amdInner|amdCollar|amdCompact)\b' KAM`: only their four definitions and amdOuter's reference inside amdCollar in the audited file. No pre-existing public-name collision.
- File size 43 lines. Copyright/authors, `module`, public imports, module docstring and `@[expose] public noncomputable section` are present. Definition bodies are exposed.
- Static forbidden-token scan of this entire file: `[]` for sorry, admit, axiom, unsafe, opaque, EuclideanSpace and set_option; there are no heartbeat, recursion-depth or synthesis overrides.
- Recursive source-import traversal: 43 transitive KAM modules; no provider or frozen theorem imports. All frozen inputs in that closure are definitions, so no DRAFT_SORRY theorem or seal-state dependency is introduced. Broad Mathlib import is harmless to this scoped result.

## Uncertainties, errata and deviations

No blocking source/design defect, suspected pinned-source erratum, or implementation deviation was found in this A0 scope. In particular the source texts “outer and inner regions” (p14a lines 21–23), “K1” (line 83), and the displayed collar (line 97) retain their literal meanings. The inherited P14 analytic/continuation feasibility gates and N anchor release gate belong to later packages and are not paid by these definitions. No new pinned-PDF audit or claim about those later proofs is made.

Temporary probes are confined to this worktree's `.lake/abi-scratch/` and removed after use. No production, frozen, manifest or generated file is edited.

Final boundary check: `git status --short` lists only the new audit report and pre-existing untracked handoff; protected-path diff remains empty. The temporary A0 probe was deleted.

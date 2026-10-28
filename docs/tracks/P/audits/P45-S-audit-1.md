# Independent package audit 1: P45-S

Overall verdict: **PASS WITH NOTES** for P45-S, scoped exclusively to
`KAM/Planetary/PG/Setting.lean`. The definitions match the designated signatures and source
carriers; both bridge proofs pass elaboration, axiom inspection and kernel replay. The notes are
the permitted stale generated-root lint failure and a correction to the handoff's axiom claim.
There is no provider or frozen theorem sealed by this package. In particular, frozen P-G remains
`DRAFT_SORRY`; this report does not establish P-G or any downstream analytic/measure result.

## Snapshot and authorities

- Worktree: `/root/code/KAM-inp-p45s`; HEAD
  `6649c818882f45d0ad023ce46c778ef70f7b8c0f`.
- Comparison: `git diff inp...HEAD`, with `inp` at
  `ef8fc426c638557035e6101216aad4ef8b8a570e`. Exactly one new tracked file, 98 insertions.
- Audited file SHA256:
  `7ea095c135528a11faae685f63e05ec47429d213da471ae97b1fd675aa471492`.
- Read AGENTS.md, PLAN.md, DECISIONS.md, the shared package-audit brief, and the local
  `P45-S-handoff.md`, including its overriding AUDIT FOCUS. This report follows the user's
  explicit worktree-local destination rather than the generic brief's main-worktree destination.
- Design Revision 3: `docs/tracks/P/design/P45-LEAN-DESIGN.md`, especially Section 2,
  node ownership, package row P45-S at line 477 and Appendix A at lines 946–1002.
- Shared `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`, SHA256
  `f4c7752bf23b8b149e4e5c0f1fac5288b4c32c10d19c4a17d3afe79af1c13ca2`.
  Its full text equals the design's Appendix A byte-for-byte. The package segment equals
  Setting after whitespace normalization and replacing only the two `:= sorry` with `:= rfl`.
- Read design audits 1–3 under `docs/tracks/P/design/`. Their scoped rows approve these twelve
  declarations; Revision 3 resolves the earlier downstream design findings. Those earlier audit
  receipts are context, not substitutes for the independent checks below.
- Source checks: `blueprint-P/parts/p4-pg-measure.tex:7–20,153–154`,
  `p5-pg-assembly.tex:11–23`, `docs/tracks/P/statement.md:48–130`, the actual frozen P-G
  telescope and its frozen definition closure. D20 supplies the exact approved track-P v0.2
  contract; older prose saying approval is pending does not replace that contract.

## Declaration decisions

All names below are in `KAM.Planetary`; line numbers refer to Setting. The node column
identifies source roles, including coordinate helpers rather than claiming new source theorems.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| `bpP:p4:conv#data` | `blockFast` (37) | PASS | First `a` coordinates via `Fin.castAdd b`, scalar-generic with no norm instance. |
| `bpP:p4:conv#data` | `blockSlow` (39) | PASS | Last `b` coordinates via `Fin.natAdd a`, same carrier and order. |
| `bpP:p4:conv#data` | `blockFast_real` (41) | PASS | Exact real specialization equals frozen `fast`; reflexivity, no premise. |
| `bpP:p4:conv#data` | `blockSlow_real` (43) | PASS | Exact real specialization equals frozen `slow`; reflexivity, no premise. |
| `bpP:p4:conv#data`; `bpP:p5:order` | `PGData` (46–76) | PASS | Exactly the frozen P-G input telescope, in order; no prepared witness or conclusion field. |
| `bpP:p5:order`, collar constants | `pgBoundaryA` (78) | PASS | Selects the first constant from the original boundary hypothesis. |
| `bpP:p5:order`, collar constants | `pgBoundaryD` (80) | PASS | Selects its paired radius from that same first choice, preserving the bound. |
| `bpP:p4:conv#data`, collar | `realNbhd` (83) | PASS | Strict witness neighbourhood in the ambient Pi max metric. |
| `bpP:p4:conv#data`, collar | `innerCore` (86) | PASS | Membership in V and distance at least t from every frontier point. |
| `bpP:p4:conv#shell` | `actionShell` (89) | PASS | Open coordinate product `(l,u)^b`, no radius or scale change. |
| `bpP:p4:conv#shell`, flattened product | `joinedActions` (91) | PASS | Both block-membership conditions on `Fin (a+b) → ℝ`. |
| Period-one cell helper | `unitCube` (94) | PASS | Half-open `[0,1)^n`; not the physical fast-angle cell `[0,2*pi)^a`. |

The design's early node table assigns shell declarations to PGMeasure/Setting while the explicit
P45-S package row and Appendix A place their implementation here. This is a location cross-reference,
not a changed mathematical interface or duplicate declaration.

## Premises and carriers

For each of the two bridge theorems the complete binder audit is:

| Binder | Bin | Authority |
|---|---|---|
| `{a : ℕ}` | TYPING | Signature dimensions; frozen Fast/Slow block convention. |
| `{b : ℕ}` | TYPING | Signature dimensions; frozen Fast/Slow block convention. |
| `(v : Fin (a+b) → ℝ)` | TYPING | Arbitrary real coordinate vector in the exact bridge signature. |

Per theorem counts: SOURCE 0, STANDING 0, TYPING 3, RULED 0, EXCESS 0. No instance or
logical input is hidden in either theorem. There are no additional assumptions, weakened conclusions
or constants whose dependence needs to be paid by these bridge proofs.

The source-data structure has dimension parameters `a,b : ℕ` (TYPING) and these 27 fields.
SOURCE here means the literal approved P-G telescope, including its D20-approved corrections;
this does not claim they are the uncorrected printed CP10 premises.

| Field | Bin | Exact frozen/source role |
|---|---|---|
| `ha` | SOURCE | `0 < a`. |
| `hb` | SOURCE | `0 < b`. |
| `V` | TYPING | Real fast-action set. |
| `hV` | SOURCE | Open V. |
| `hVc` | SOURCE | Connected V, including nonemptiness. |
| `hVb` | SOURCE | Bounded V. |
| `W` | TYPING | Real fast-action neighbourhood set. |
| `hW` | SOURCE | Open W. |
| `hVW` | SOURCE | `closure V ⊆ W`. |
| `hboundary` | SOURCE | Positive A and d, two-sided max-distance collar, every `0<t<d`. |
| `r0` | TYPING | Fixed real cylinder radius. |
| `mu0` | TYPING | Fixed real parameter bound. |
| `B` | TYPING | Fixed real torsion bound. |
| `hr0` | SOURCE | Positive r0. |
| `hmu0` | SOURCE | Positive mu0. |
| `hB` | SOURCE | Positive B. |
| `H0` | TYPING | Real Hamiltonian on fast actions. |
| `P` | TYPING | Real perturbation family on frozen `Phase (a+b)`. |
| `P0` | TYPING | Real constant Birkhoff coefficient family. |
| `Omega` | TYPING | Real slow-frequency family. |
| `beta` | TYPING | Real b-by-b matrix family. |
| `hP` | SOURCE | Joint analyticity near `[0,mu0] × closure (cylinder V r0)`. |
| `hperiod` | SOURCE | Original fast-angle lattice shift, on `[0,mu0]` and cylinder. |
| `hfreq` | SOURCE | Exact frozen `HasFastDiffeomorphism H0 W`. |
| `hBNF` | SOURCE | Exact frozen `HasSecularBirkhoffForm`, on V. |
| `htorsion` | SOURCE | `B ≤ abs(det beta)` on `[0,mu0] × V`. |
| `hsymm` | SOURCE | Symmetric beta on that same domain. |

Field counts: SOURCE 17, TYPING 10, STANDING 0, RULED 0, EXCESS 0; with dimension parameters,
TYPING becomes 12. An independently generated probe copied the actual frozen telescope verbatim
and constructed `PGData a b` using these fields in exactly this order; it elaborated successfully.

Expanded source predicates were checked directly. `hfreq` comprises analyticity of H0 on W,
openness of its frequency image, and a C1 inverse with both inverse identities on their specified
domains. These are literal frozen source assumptions. `hBNF` comprises integrability on the
product-of-discs oscillator locus and the epsilon/delta order-four remainder, including zero.
It does not assume a uniform remainder, analytic extension, averaging map or KAM torus.
The frozen average retains `(2*pi)^(-a)`, actions retain `(p_j^2+q_j^2)/2`, `assemble` retains
`(phi,q;I,p)`, and `fastShift` retains `2*pi*k`. No boundary values of the arbitrary total
functions P0/Omega/beta are asserted. Source data precede every later small parameter.

## Definition classification

The seven ordinary coordinate definitions (`blockFast`, `blockSlow`, `realNbhd`, `innerCore`,
`actionShell`, `joinedActions`, `unitCube`) are literal formulas, not characterization-defined
objects. They match their complete signatures on their entire declared carriers, including zero
dimensions, empty sets and arbitrary real radii/endpoints. For example, empty X gives an empty
`realNbhd X s`, and nonpositive s gives no witness; there is no empty-set `infDist` fallback.
`innerCore` uses the explicit universal frontier condition even for an empty frontier. The source
collar applications require the standing positive-dimensional bounded nonempty open V and t>0;
this package claims no compactness theorem for other arguments.

For each of these seven definitions: BODY_MATCH OK; PUBLIC_CARRIER OK;
WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A;
DEFINITION_VERDICT PASS. Rfl probes checked each defining equation on its full carrier.

`PGData` is a literal source-assumption structure, classified separately from a theorem-shaped
result bundle: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL;
CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS.
It adds no existence or quantitative result beyond the frozen hypotheses.

`pgBoundaryA` and `pgBoundaryD` are literal existential-witness extractors, exactly as prescribed
by the design. Their source object is an admissible pair of constants, not a uniquely
characterized mathematical function. A is chosen from the explicit source existential; d is
chosen from the resulting dependent existential. Neither is selected from an unproved downstream
theorem. Uniqueness is neither asserted nor needed: every selected pair satisfies the original
positive-constant collar property. The independent probe proved, with no added premise:

```lean
example {a b : ℕ} (d : PGData a b) :
    0 < pgBoundaryA d ∧ 0 < pgBoundaryD d ∧
      ∀ t : ℝ, 0 < t → t < pgBoundaryD d →
        volume {I : Fin a → ℝ | ∃ J ∈ frontier d.V, dist I J < t} ≤
          ENNReal.ofReal (pgBoundaryA d * t) := d.hboundary.choose_spec.choose_spec
```

For both extractors: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS OK (the original
source existential); CHARACTERIZATION OK (the full admissibility property checked above);
CHOICE_INDEPENDENCE N/A (no unique numerical value claimed); DEFINITION_VERDICT PASS.
Their only dependence is on fixed source data. No junk branch, default, invented inverse or
off-source reconstruction was found. There are no new abbreviations.

## Independent verification

All Lean invocations were sequential, with `LEAN_NUM_THREADS=1` and niceness 5. No clean,
update, cache retrieval, heartbeat override or production edit was performed. Build job totals
are Lake's reported dependency totals, not a claim of a clean rebuild.

1. Targeted build, exact command:

   ```sh
   env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p45s KAM.Planetary.PG.Setting
   ```

   Exit 0. Output:

   ```text
   [inp-gate] slot 2 acquired 07:56:50 for KAM.Planetary.PG.Setting
   Build completed successfully (9061 jobs).
   ```

2. Exact-type, source-telescope, defining-equation and boundary-witness probes:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P45SAudit1.lean
   ```

   Exit 0, no warnings or errors. The bridge probes repeated the full signature statements
   under fresh anonymous names, with `exact blockFast_real v` and `exact blockSlow_real v`.
   Provider equality/seal-body probes are N/A: this package exports no provider and attempts
   no frozen theorem seal. The actual frozen P-G theorem was inspected as source text, not
   imported into the production module or used as an available proof.

   Exact `#print axioms` output:

   ```text
   'KAM.Planetary.blockFast_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.blockSlow_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pgBoundaryA' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pgBoundaryD' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Both new public theorems therefore have only allowlisted axioms; no sorryAx or project axiom.
   The handoff's inference of axiom-freedom from `rfl` is inaccurate for these elaborated exports.

3. Kernel replay, one invocation for the only changed module:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PG.Setting
   ```

   Exit 0. Exact output: `replaying KAM.Planetary.PG.Setting`.

4. Source lint:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the expressly allowed generated-root discrepancy. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (464 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Niceness and LEAN_NUM_THREADS were inherited by lint's sequential ABI Lean subprocess.

5. Static hygiene: 98 total lines, maximum line length 99 Unicode characters, no overlong
   lines, no banned token or option. Copyright, `module`, public imports, module docstring,
   exposed public noncomputable section are present. No new instance, `EuclideanSpace`,
   sorry/admit/axiom/unsafe/opaque or resource override.

6. Recursive project import inspection: 15 project modules including Setting, zero providers,
   zero unmanifested frozen imports, all imported frozen anchors SEALED. All six direct project
   imports are frozen definitions; no frozen theorem is imported. Thus the DRAFT P-G theorem
   is outside the module's dependency closure.

7. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   `git diff --check`: exit 0. Final scratch/report checks are recorded below.

## Findings, limits and closeout

No failing statement, definition, proof, forbidden premise or source-carrier discrepancy was found
in the assigned file. No new suspected pinned-paper erratum or mathematical deviation was
introduced or discovered. The inherited CP10/CP11 allegations and downstream design repairs were
not re-adjudicated against PDFs in this scoped settings-module audit. The blueprint's compact-core,
measure, analytic-extension and KAM claims are not proved merely by these definitions.

The expected generated-root lint discrepancy is explicitly allowed by the brief; no generated
file was regenerated. The axiom note above corrects the prover's receipt without invalidating
the allowed axiom closure. These are the reasons for PASS WITH NOTES.

Scratch probe `.lake/abi-scratch/P45SAudit1.lean` was deleted after successful checks. The only
persistent file written by this audit is this report at the requested absolute worktree path.
The pre-existing untracked `P45-S-handoff.md` was preserved. Final status has only that handoff
and this report untracked, with no tracked worktree modification. Report whitespace, fences,
all twelve declaration rows and absence of pending placeholders were checked; protected-path
branch diff and `git diff --check` remain clean.

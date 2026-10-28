# N2-ZORBIT independent package audit 1

Date: 2026-10-28. Audited HEAD: `f25b8f92fec3962ac1f00a7cdfbb6249e58add91`.

## Verdict and scope

**PASS WITH NOTES** for N2-ZORBIT and its relation to N-ZERO
(`nekhoroshev.zero_perturbation.v1`, export
`KAM.Nekhoroshev.zero_perturbation`, manifest state **SEALED**).
This package adds six implementation receipts; it neither supplies a new provider nor
changes the existing frozen seal. No mathematical or statement-fidelity failure found.
Final mechanical results are recorded below.

The audited implementation is only `KAM/Nekhoroshev/QcZero/ZeroOrbit.lean` (83 lines),
as required by the handoff's AUDIT FOCUS. Read the common package brief, AGENTS.md,
PLAN.md, DECISIONS.md, track-N statement, N2 design and its independent design audit,
the blueprint p0/p2 statements, relevant frozen definitions, and implementation dependencies.
The user's exact report destination overrides the common brief's main-worktree destination.

Baseline evidence:

```text
git diff --name-status inp...HEAD
warning: inp...HEAD: multiple merge bases, using 25f3d65bb0d5a30674a6e5286c44befb321e7e9d
A .drafts/handoff-N2-ZORBIT.md
A KAM/Nekhoroshev/QcZero/ZeroField.lean
A KAM/Nekhoroshev/QcZero/ZeroOrbit.lean
```

`inp` resolved to `46bfbcb5e40e5540583d781ad736c36bd2abd4ab`;
`inp-n2z` resolved to `41b5b8843da2a98e3aed4c561c38d47dae91b22d`.
The requested `git diff inp...HEAD` was inspected. Also compared with `inp-n2z`:
the latter branch is not a simple parent snapshot, and both its triple-dot comparison
(which includes Kernel) and endpoint comparison contain unrelated integration history.
Only the handoff-owned ZeroOrbit module is audited here. ZeroField is byte-identical
between `inp-n2z` and HEAD and is an inherited dependency, not a fresh audit target.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty
(apart from the multiple-merge-base warning). No protected-path change is attributed
to this package. The initial untracked `docs/tracks/N/audits/N2-ZORBIT-handoff.md`
was preserved.

## Declaration-by-declaration review

All names below are in `KAM.Nekhoroshev`; line numbers refer to ZeroOrbit.lean.
Source locators are in `blueprint-N/parts/p2-qc-zero.tex`.

| Node | Declaration | Verdict | Reason |
|---|---|---|---|
| `stepN:p2:z-init`, L88 | `z_init`, L38 | PASS | Exact initial-value and all-time constant-action conjunction. Valid for arbitrary total h; dropping analytic/radius premises is the stronger statement explicitly recorded as D-N2-4. |
| `stepN:p2:z-ball`, L90 | `z_ball`, L43 | PASS | Exact strict max-norm inclusion from R/2 to R using R>0. No theta0, h, s or f binder survives. |
| `stepN:p2:z-H`, L92 | `z_h`, L48 | PASS | Gives all three intended receipts: action in B(R), orbit in Wdom, and genuine differentiability of the actual H=h+f. Applies `zero_deriv` with a proved Wdom membership. |
| `stepN:p2:z-curve`, L94 | `z_curve`, L62 | PASS | Exact two-sided HasDerivAt of the affine orbit for every real time. Requires no differentiability of h to differentiate a time-constant frequency vector. |
| `stepN:p2:z-eq`, L96 | `z_eq`, L68 | PASS | Exact frozen IsSolutionOn predicate on B(R) and all real times. Obtains the complete solution conjunct from `zero_perturbation_core`; no clause is discarded. |
| `bpN:p2:zero`, L82-L86; `bpN:p0:zero`, p0 L239-L246 | `zero`, L74 | PASS | Exact frozen-shaped initial/solution/constant-action conjunction, with unchanged quantifier order and source premises. Reuses the existing implementation as explicitly required by the design. |
| Existing N-ZERO anchor | `zero_perturbation` | PASS WITH NOTES | Already SEALED; consistency/type and seal-body checks are evidence for this package's compatibility, not a new sealing event. |

Signatures were checked against the design's embedded signatures at
`docs/tracks/N/design/N2-LEAN-DESIGN.md:474-503` and the actual signature source
`/root/code/KAM-inp/.drafts/design/N2Signatures.lean:165-193`.
The relative `.drafts/design/N2Signatures.lean` does not exist in this worktree;
the main-worktree copy and embedded design agree on all six signatures.
Transient probe copies of these signatures call the actual exports with their
explicit binders in order. No constants, witness scopes, norm conventions or carriers change.

## Expanded binder audit

The following inventory has one row per distinct binder or expanded conjunction field;
the applicability column identifies every theorem using it. Logical fields are SOURCE,
and data carriers are TYPING. No instance, conclusion-shaped premise, extra derivative
assumption, quasi-convexity condition, or quantitative bound on h is introduced.

Abbreviations: I=`z_init`, B=`z_ball`, H=`z_h`, C=`z_curve`, E=`z_eq`, Z=`zero`.
Sources p0 and p2 mean the corresponding blueprint-N parts.

| Binder / expanded field | Applies to | Bin | Exact source / design authority |
|---|---|---|---|
| `{n : ℕ}` | I B H C E Z | TYPING | p0 `bpN:p0:zero`: every natural dimension, including zero |
| `{R : ℝ}` | B H E Z | TYPING | p0 `bpN:p0:zero`; p2 z-ball |
| `{s : ℝ}` | H E Z | TYPING | p0 `bpN:p0:zero` |
| `hR : 0 < R` | B H E Z | SOURCE | p0 zero; p2 z-ball |
| `hs : 0 < s` | H E Z | SOURCE | p0 zero; p2 z-H |
| `{h : (Fin n → ℂ) → ℂ}` | I H C E Z | TYPING | p0 orbit; p0 zero |
| `hh.1`: complex differentiability | H E Z | SOURCE | p0 integrable (i), L109 |
| `hh.2.1`: continuity on closure | H E Z | SOURCE | p0 integrable (ii), L110 |
| `hh.2.2.1`: ∃ A≥0, bound on complex action neighbourhood | H E Z | SOURCE | p0 integrable (iii), L111; existential remains inside hh, not an independently fixed constant |
| `hh.2.2.2.1`: reality on realActionDomain | H E Z | SOURCE | p0 integrable (iv), L112 |
| `hh.2.2.2.2`: real C³ on realActionDomain | H E Z | SOURCE | p0 integrable (v), L113; explicit source guard |
| `{f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}` | H E Z | TYPING | p0 zero: actual perturbation, not substituted global zero |
| `hf.1`: 0≤0 | H E Z | SOURCE | p0 perturbation preamble, L122 |
| `hf.2.1`: complex differentiability | H E Z | SOURCE | p0 perturbation (i), L124 |
| `hf.2.2.1`: continuity on closure | H E Z | SOURCE | p0 perturbation (i), L124 |
| `hf.2.2.2.1`: integer-periodicity | H E Z | SOURCE | p0 perturbation (ii), L125 |
| `hf.2.2.2.2.1`: reality at real points | H E Z | SOURCE | p0 perturbation (iii), L126 |
| `hf.2.2.2.2.2`: pointwise norm≤0 on complexDomain | H E Z | SOURCE | p0 perturbation (iv), L127; adopted non-strict convention D18/D20 |
| `theta0 : Fin n → ℝ` | I H C E Z | TYPING | p0 orbit, L175-L176; p0 zero |
| `I0 : Fin n → ℝ` | I B H C E Z | TYPING | p0 orbit; p0 zero |
| `hI : I0 ∈ actionBall n (R/2)` | B H E Z | SOURCE | p0 zero L241; p2 z-ball |
| `t : ℝ` | H C | TYPING | p2 z-H / z-curve, all real times |

Expanded counts (each outer logical field counted once, not its bound variables):

| Theorem | SOURCE | STANDING | TYPING | RULED | EXCESS |
|---|---:|---:|---:|---:|---:|
| z_init | 0 | 0 | 4 | 0 | 0 |
| z_ball | 2 | 0 | 3 | 0 | 0 |
| z_h | 14 | 0 | 8 | 0 | 0 |
| z_curve | 0 | 0 | 5 | 0 | 0 |
| z_eq | 14 | 0 | 7 | 0 | 0 |
| zero | 14 | 0 | 7 | 0 | 0 |

The boundedness witness inside hh is exactly the source existential, with its
nonnegativity and pointwise-bound conjuncts; it does not impose a numerical bound
or change constant dependence. All source quantifiers within hh/hf range over
the same real or complex domains as the frozen definitions. The universal time
in the constant-action conclusion is an output, not a hypothesis.

## Definition classification and actual consumption

There are **no new def, abbrev or structure declarations** in this package.
For the new-definition audit: BODY_MATCH / PUBLIC_CARRIER / WELL_DEFINEDNESS /
CHARACTERIZATION / CHOICE_INDEPENDENCE are N/A; DEFINITION_VERDICT: PASS (empty inventory).

Reviewed the inherited semantic closure: frozen `integrableOrbit` is literally
`(theta0 + t • frequencyMap h I0, I0)`; frozen `actionBall` is the open Pi max-norm
ball. `realPart`, `realHamiltonian` and the Hamiltonian vector field are the actual
real restriction and canonical `(∂I H, -∂theta H)` field. The frozen frequency map
uses fderiv evaluated on coordinate basis vectors. Its total off-regularity value
is irrelevant to the purely affine I/C receipts and is guarded by analytic
regularity in H/E/Z. No junk derivative is interpreted as a genuine gradient.

Frozen `IsSolutionOn` expands to **all three** requirements at each t∈J:
action membership, differentiability of H, and two-sided HasDerivAt with the
actual vector field. `z_eq` consumes that precise predicate from the core;
`zero` consumes its full conjunction. `z_h` proves Wdom membership using
`‖I0‖<R<R+s` and invokes `zero_deriv` at that exact point.
The existing core was read: it uses local eventual equality with `realPart h ∘ snd`,
obtains genuine derivatives from C³ on the open action domain, identifies the
field and proves the affine derivative. No hard step is assumed as a new premise.

`Wdom` (Interfaces/Setting.lean:35) is literally univ×B(0,R+s).
It is inherited, not a newly invented fallback. Frozen realActionDomain and
complexDomain retain their neighbourhood/product definitions. All eight N-ZERO
manifest definition-closure file hashes were independently recomputed and matched.

## Mechanical checks

All Lean/Lake operations initiated for this audit were sequential, with
`LEAN_NUM_THREADS=1` and niceness 5. No heartbeat, synthesis or recursion override,
cache download, clean, library rebuild or state-changing git operation was used.

1. Targeted build, through the prescribed gate:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n2o KAM.Nekhoroshev.QcZero.ZeroOrbit
   [inp-gate] slot 1 acquired 07:14:14 for KAM.Nekhoroshev.QcZero.ZeroOrbit
   Build completed successfully (2899 jobs).
   exit 0
   ```

2. Lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (446 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The exit 1 is solely the explicitly allowed stale generated-root check.
   All other lint stages passed, including the 100-character line check;
   no root regeneration was performed.

3. Exact-type, explicit-binder assembly and axioms probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N2ZOrbitAudit.lean
   exit 0
   ```

   The scratch file imported ZeroOrbit, the existing frozen ZeroPerturbation
   anchor, and its provider. It copied the six source design signatures under
   `audit_` names, retaining section `include`/`omit`, with these bodies:

   ```lean
   -- In source-signature order, in namespace KAM.Nekhoroshev:
   z_init theta0 I0
   z_ball hR I0 hI
   z_h hR hs hh hf theta0 I0 hI t
   z_curve theta0 I0 t
   z_eq hR hs hh hf theta0 I0 hI
   zero hR hs hh hf theta0 I0 hI
   ```

   It also elaborated both exact whole-type checks:

   ```lean
   example : type_of% @KAM.Nekhoroshev.zero_perturbation :=
     @KAM.Nekhoroshev.zero
   example : type_of% @KAM.Nekhoroshev.zero_perturbation :=
     @KAM.Provider.Nekhoroshev.zero_perturbation
   ```

   Two fresh copies of the literal frozen theorem, with unchanged binders and
   conclusions, elaborated with these complete assembly bodies:

   ```lean
   by exact KAM.Nekhoroshev.zero hR hs hh hf θ₀ I₀ hI
   by exact KAM.Provider.Nekhoroshev.zero_perturbation hR hs hh hf θ₀ I₀ hI
   ```

   `#check @...` confirmed the surviving binders recorded in the binder table.
   In particular z_ball has only `{n} {R} hR I0 hI`, while H/E/Z retain all
   analytic premises and C retains only `{n} {h} theta0 I0 t`.
   The exact `#print axioms` output was:

   ```text
   'KAM.Nekhoroshev.z_init' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.z_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.z_h' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.z_curve' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.z_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.zero' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.zero_perturbation' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Provider.Nekhoroshev.zero_perturbation' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. Kernel replay, one invocation including the existing provider and the audited
   lemma module:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Provider.Nekhoroshev.ZeroPerturbation KAM.Nekhoroshev.QcZero.ZeroOrbit
   replaying KAM.Nekhoroshev.QcZero.ZeroOrbit
   replaying KAM.Provider.Nekhoroshev.ZeroPerturbation
   exit 0
   ```

5. Source hygiene: 83 total lines, longest line 95 Unicode characters; copyright,
   module, public imports, module docstring and public section present. No
   forbidden token or option override; no new definitions; six public theorems.
   `git diff --check inp...HEAD` exits 0, with only the recorded merge-base warning.

6. Independently traversed the production project imports from ZeroOrbit:
   36 KAM modules, zero provider imports, zero frozen theorem imports, zero
   DRAFT_SORRY imports. This is distinct from the explicitly permitted scratch
   probe imports of the existing sealed anchor and its provider.

## Notes, suspected defects and limitations

* The stale generated KAM.lean is the brief's explicitly permitted lint exception;
  it is not regenerated in this read-only audit.
* Design node table L89 lists z_h/z_curve/zd_field as the z_eq source route,
  while design L111-L112 and L198-L201 expressly require the implemented route
  through the existing core. The actual code follows that instruction; it does
  not term-consume those separate receipts in z_eq/zero. This is dependency-table
  granularity to retain when integrating, not a proof failure or circularity.
* Blueprint p2 L4 says, “This part proves two frozen theorems completely”. In
  this snapshot N-ZERO is already sealed. This package proves additional receipts
  and an exact convenience theorem; it is not new root closure. This scope point
  is also recorded in N2-LEAN-DESIGN.md:230-232.
* No new suspected pinned-source defect or frozen-statement defect was found.
  No fresh BM11 PDF audit is claimed: N-ZERO is the owner-approved direct
  integrable supplement, checked against its frozen text and p0/p2 proof here.
* No mathematical deviation introduced. The stronger premise-free affine
  receipts and implementation reuse are the already declared D-N2-4/D-N2-5.

Only this report was written in the repository. Temporary probes were confined
to `.lake/abi-scratch/` and removed after verification. No source, frozen anchor,
manifest, generated root, README or pre-existing handoff was edited.

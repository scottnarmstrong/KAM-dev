# P23-02 independent package audit 1

**Overall: PASS WITH NOTES.** The P23-02 infrastructure definitions and five public theorems
pass statement/definition fidelity, proof inspection, exact-type elaboration, axiom checks and
kernel replay. Full lint status is recorded below. No material mathematical or interface defect
was found. No frozen anchor is supplied or sealed by this package: “seal-ready” is inapplicable.
In particular this report does not certify P-G or the analytic two-scale iteration.

## Scope, authority and frozen inputs

Focused tier-2, refute-first audit on 2026-10-28. The only implementation audited is
`KAM/Planetary/TwoScale/Constants.lean`, all 225 lines. Read AGENTS, PLAN, DECISIONS,
the package audit brief, track-P statement, P23-02 handoff, design revision 2 and both design
audits. Reconstructed formulas and estimates from blueprint Parts 3a/3b, then compared the code.
Read the P-G anchor and its degenerate-Hamiltonian definition for the downstream boundary;
neither is a dependency of this module. The latest explicit prompt overrides the common
brief's main-worktree output instruction: this report is in the requested package worktree.

Snapshot `frozen-v1`:

- HEAD: `9251e4181b20fb9345a4db44fe943957b9aac373`.
- `inp`: `25c512a9ce353b8bac0852b616784748063a4cfb`; merge base:
  `29dbfb0f19abb6c634f7ce97adf459363f8ba243`.
- `git diff inp...HEAD`: one new file, `Constants.lean`, 225 insertions.
- Initially untracked `docs/tracks/P/audits/P23-02-handoff.md` was read and preserved.

| Frozen input | SHA-256 |
|---|---|
| `KAM/Planetary/TwoScale/Constants.lean` | `46678cb2eb7ce88c66150bd662f857c74216da9ef00303404d8217157bf1710f` |
| `docs/tracks/P/design/P23-LEAN-DESIGN.md` | `5a03b76eb0f5ea6a090c52a0b64e4dbc9bfb0a3249f84cec1407c0f2e4c9f8b4` |
| `blueprint-P/parts/p3a-two-scale-iteration.tex` | `94327df07e9c89e6ff5186a71261fa66120a18993bfd9b3764ce4607c856328c` |
| `blueprint-P/parts/p3b-two-scale-limit.tex` | `e923c1f3856cd7c27fc73b1a5bdb21139a31d0484e30421c4e0db9cfdff86c1a` |
| `docs/tracks/P/design/DESIGN-P23-design-audit-1.md` | `695ebe468de5afa9056cd6c794df0cbcfb44cce7ac86a070b962371081d0362f` |
| `docs/tracks/P/design/DESIGN-P23-design-audit-2.md` | `e222d7c1245f63b5acaee70c4a231d53bb9465a615a5aa4c2847ccd27a21e3a2` |
| `docs/tracks/P/audits/P23-02-handoff.md` | `cae181b3fbc2f7013aa859d13c45c61ff5759d8e88730457584c17d04b058821` |

All line references below use frozen-v1. No implementation, frozen file, manifest, graph,
blueprint, generated root or README was edited; only this report and disposable probes were written.
No external messages, commits, cleanup of build artifacts, or subagents were used.

## Declaration ledger

All names below are in `KAM.Planetary`. Each of the ten structure/definition commands is
byte-identical to its corresponding command in design Appendix A (L841–880).

| Node | Declaration (implementation line) | Verdict | Fidelity and proof note |
|---|---|---|---|
| `bpP:p3:constants` | `ScaleData` (30) | PASS | Twelve real-number fields only; no hidden logical obligation or output witness. |
| `bpP:p3:constants` | `constants` (44) | PASS | Exact ordered triple K, radius, error; real exponent tau+1, logarithmic cutoff, all factors 3 and 6 retained. |
| `bpP:p3:constants` | `cutoff` (50) | PASS | First triple projection. |
| `bpP:p3:constants` | `rhoHat` (51) | PASS | Second triple projection. |
| `bpP:p3:constants` | `eHat` (52) | PASS | Third triple projection. |
| `bpP:p3:constants` | `kamConstant` (53) | PASS | Exactly max(8192 n, 24^(tau+1)/3); depends only on n,tau. |
| `bpP:p3:two-scale-kam` | `complementConstant` (54) | PASS | Exactly 1+(1+2^n)(1+(4/3)^n); depends only on n. |
| `bpP:p3:constants` | `initialL` (55) | PASS | Exact maximum of Mbar, 1/M, 1/Mhat. |
| `bpP:p3:seq` | `nextScale` (56) | PASS | All nine updated fields match P3a L238; tau and gamma fields preserved. L doubles rather than being recomputed. |
| `bpP:p3:seq` | `seq` (67) | PASS | Initial datum and forward recursion; numeric sequence only, no chosen analytic witnesses. |
| `bpP:p3:constants` totality | `cutoff_pos` (71) | PASS | Stronger domain: only s>0 needed; max with 1 pays positivity. |
| `bpP:p3:constants` totality | `rhoHat_pos` (77) | PASS | Only six positive parameters needed; no sign assumption on tau, E or L. Positive-base real power is positive. |
| `bpP:p3:rem-norm` | `rem_norm` (87) | PASS | Exact design signature L923–928, including all four comparisons. Correct G2 direction. |
| `bpP:p3:rem-norm` | `rem_norm_blocks` (117) | PASS WITH NOTES | Exact design type L987–990 after unfolding block adapters; term-level check passed. No dependency on P23-01. |
| `bpP:p3:sums` | `sums` (129) | PASS | Exact abstract design signature L1132–1142; every estimate and both summability assertions retained. |

## Definition classification

`ScaleData` is literal formula data. All nine `def`s are literal algebraic/projection/recursive
constructions, not characterization-defined objects. BODY_MATCH: OK; PUBLIC_CARRIER: OK;
WELL_DEFINEDNESS: N/A_LITERAL; CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A;
DEFINITION_VERDICT: PASS for each of the ten objects.

The total real carrier and Lean's total division/log/power are explicitly intended by the design
(L28, L51 and Appendix A), not a selected valid-locus fallback. No `if`, arbitrary selection,
choice of inverse, or conclusion-shaped predicate occurs. Positivity is required when proving
radius comparisons; later KAM consumers must supply their full `KamHyp`. A free L at this numeric
level is intentional: the analytic contract requires `initialL <= L`, and initial applications
supply equality. The source's permitted larger L is preserved under the sequence update (P3a
L236–239). This module does not assert that arbitrary numeric inputs satisfy the analytic theorem.

## Expanded binder audit

SOURCE here includes the explicit source-domain data and the premises of the deliberately
abstract scalar helper in the approved design; the recurrences are inputs to that helper,
not assumptions being substituted for the analytic iterative theorem. All binders are listed;
bundled positivity and radius hypotheses are expanded. No project typeclass hides premises.

| Declaration | Binder / expanded component | Bin | Authority |
|---|---|---|---|
| `cutoff_pos` | `{p : ScaleData}` | TYPING | Numeric data. |
| `cutoff_pos` | `hs : 0 < p.s` | SOURCE | P3a constants L42–55; K>=6/s. |
| `rhoHat_pos` | `{p : ScaleData}` | TYPING | Numeric data. |
| `rhoHat_pos` | `hs : 0 < p.s` | SOURCE | P3a constants. |
| `rhoHat_pos` | `hgamma1 : 0 < p.gamma1` | SOURCE | P3a constants. |
| `rhoHat_pos` | `hgamma2 : 0 < p.gamma2` | SOURCE | P3a constants. |
| `rhoHat_pos` | `hM : 0 < p.M` | SOURCE | P3a constants. |
| `rhoHat_pos` | `hMh : 0 < p.Mhat` | SOURCE | P3a constants. |
| `rhoHat_pos` | `hrho : 0 < p.rho` | SOURCE | P3a constants. |
| `rem_norm` | `p : ScaleData` | TYPING | Design L923. |
| `rem_norm` | `hp.1 : 0 < p.E` | SOURCE | Design L923–924; P3a constants. |
| `rem_norm` | `0 < p.M` | SOURCE | Same. |
| `rem_norm` | `0 < p.Mhat` | SOURCE | Same. |
| `rem_norm` | `0 < p.Mbar` | SOURCE | Same; unused, retained verbatim. |
| `rem_norm` | `0 < p.s` | SOURCE | Same. |
| `rem_norm` | `0 < p.gamma1` | SOURCE | Same. |
| `rem_norm` | `0 < p.gamma2` | SOURCE | Same. |
| `rem_norm` | `0 < p.rho` | SOURCE | Same. |
| `rem_norm` | `0 < p.L` | SOURCE | Same. |
| `rem_norm` | `0 < p.tau` | SOURCE | Same; unused, retained verbatim. |
| `rem_norm_blocks` | `{a : Nat}` | TYPING | P3a row-block convention, design L988. |
| `rem_norm_blocks` | `{b : Nat}` | TYPING | Same; zero-size blocks also allowed. |
| `rem_norm_blocks` | `A : (Fin (a+b) -> C) ->L[C] (Fin (a+b) -> C)` | TYPING | Same; max norm and induced CLM norm. |
| `sums` | `{e : Nat -> R}` | TYPING | Design L1132. |
| `sums` | `{R : Nat -> R}` | TYPING | Same. |
| `sums` | `{s : Nat -> R}` | TYPING | Same. |
| `sums` | `{c : R}` | TYPING | Same. |
| `sums` | `he : forall j, 0 <= e j` | SOURCE | Design L1133; nonnegative error sequence. |
| `sums` | `he0 : e 0 < 1/2` | SOURCE | Design L1133; P3b L3–4 smallness. |
| `sums` | `hquad : forall j, e (j+1) <= e j^2` | SOURCE | Design L1133; P3b L10 invokes iterative(iv). |
| `sums` | `hc : 0 <= c` | SOURCE | Design L1134; P3b positive scalar c. |
| `sums` | `hce : c*e 0 <= 1/2` | SOURCE | Design L1134; P3b (3.4). |
| `sums` | `hR`, first component: `forall j, 0 <= R j` | SOURCE | Design L1135; radius sequence. |
| `sums` | `hR`, second component: `forall j, R (j+1) <= R j/16` | SOURCE | Design L1135; P3b L15–16. |
| `sums` | `hs : forall j, s (j+1) = s j/12` | SOURCE | Design L1136; P3a L238. |

Counts after expanding bundles: SOURCE 25, STANDING 0, TYPING 10, RULED 0, EXCESS 0.
The corrected conclusion direction is a design ruling (G2), not an additional premise.
Universally quantified indices/vectors in the inputs and conclusions use only Nat/finite Pi
spaces; there are no extra instances or logical assumptions attached to them.

## Proof and adversarial pass

Inspected every proof. `rem_norm` splits the ordering of Mhat and M; replacing Mhat by their
minimum leaves max(M^-1,Mhat^-1) invariant. With L fixed the cutoff is definitionally unchanged;
only the slow-radius denominator decreases. Both old radii and denominators are proved positive
before inverse/power comparison, so increasing radius decreases EL/radius^2. No KAM smallness is
needed for these comparisons. `rem_norm_blocks` uses restriction <= full Pi norm <= operator norm
product, valid even for either block dimension zero.

`sums` proves quadratic iteration by induction, then dominates shifted errors by e(m)/2^k.
For the weighted bound it splits 2^k into k+(2^k-k), uses 2^k-k>=1, e(0)<=1/2 and
(c e(0))^k<=2^-k. Nonnegative-series domination supplies Summable before the tsum inequalities.
Separate inductions prove both radius and width formulas. No exchange of unproved infinite sums
or reliance on nonsummable tsum defaults occurs. The proof also covers e(0)=0, c=0 and zero radii;
widths need not be positive for the stated equality.

Adversarial re-checks rejected three candidate blockers: (a) unfolded block notation does not
weaken the theorem (compiled exact design-type application); (b) free L is expressly required
for iteration, rather than an omitted assumption in this formula module; (c) abstract hquad and
hR do not claim the analytic recurrence is proved. Exact design-type applications for all three
planned lemmas elaborate, with explicit arguments in order. No material survivor remains.
This was a separate second inspection by this auditor, not a claimed second-person review.

## Notes, source defects and deviations

**N1, accepted interface notation deviation.** Implementation L118–119 writes
`fun i : Fin a => A v (Fin.castAdd b i)` and the analogous `Fin.natAdd` expression instead of
`firstBlock (A v)` and `lastBlock (A v)`. Design L457–460 defines exactly these adapters.
The probe copied those literal definitions into a fresh namespace and applied the theorem at
the design type using `exact`; it passed. No named adapter is exported or duplicated in production.
No orchestrator repair is needed for definitional applicability; a cosmetic facade is optional.

**N2, inherited blueprint defect, corrected as designed.** P3a L91 says lowering Mhat
“this only decreases $\hat M$, which can increase $\hat\rho$ and $\hat E$”. With L unchanged, Ehat=EL/rhohat^2 instead decreases when radius
increases. Design G2, L230, explicitly corrects this direction. Implementation L90–91 proves
`rhoHat p <= rhoHat p'` and `eHat p' <= eHat p`. The inequality direction was independently
recomputed above; this is a surviving blueprint wording defect, not a defect in this package.
Keep the blueprint's instruction to choose compatible normalized constants before applying the
analytic theorem. No new pinned-CP10 defect was discovered; no fresh PDF audit was performed.

**N3, generated root.** The brief allows only the expected out-of-date KAM.lean lint diagnostic.
The final lint receipt below distinguishes that exception from all other checks.

## Independent verification

All Lean/lake invocations issued by this audit were sequential, with `LEAN_NUM_THREADS=1`
and `nice -n 5`; the build used the mandated compile gate. No heartbeat, recursion or synthesis
budget override was used. No Mathlib rebuild, cache operation or lake clean was requested.

1. Targeted build:

   ```sh
   env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2302 KAM.Planetary.TwoScale.Constants
   ```

   Exit 0. Output:

   ```text
   [inp-gate] slot 1 acquired 06:18:47 for KAM.Planetary.TwoScale.Constants
   Build completed successfully (9047 jobs).
   ```

   This was an up-to-date targeted build, not a clean 9047-job rebuild; no module compile lines
   were emitted. The existing module artifact was additionally subjected to kernel replay below.

2. Kernel replay, one invocation:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.Constants
   ```

   Exit 0; output: `replaying KAM.Planetary.TwoScale.Constants`.

3. Generated `.lake/abi-scratch/P2302Audit1.lean`: imported only the audited module, copied the
   design's two block definitions into `AuditP2302`, replaced each of the three design theorem
   commands by an `example` of the same full type, and supplied respectively
   `rem_norm p hp`, `rem_norm_blocks A`, and `sums he he0 hquad hc hce hR hs`.
   Added `rfl` checks for seq at zero/successor and all five `#print axioms` commands.

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2302Audit1.lean
   ```

   Final exit 0, no warnings/errors. The first scratch generation inadvertently copied lastBlock
   twice and exited 1 with “already been declared”; the duplicate scratch command was removed,
   and the full probe was rerun successfully. This was an auditor probe error, not package code.
   Exact axiom output:

   ```text
   'KAM.Planetary.cutoff_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.rhoHat_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.rem_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.rem_norm_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sums' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. Full source lint:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the brief-authorized generated-root exception. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (417 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Thus module/header, forbidden tokens, 100-character limits, frozen guard and ABI checks pass.
   This receipt includes the ABI Lean subprocess (inherited niceness and LEAN_NUM_THREADS=1),
   not merely static lint. KAM.lean was left untouched as required.

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   `git diff --check inp...HEAD`: empty, exit 0. Forbidden-token/override search of the module:
   no matches (rg exit 1). Python Unicode line-length census: `lines: 225`,
   `lines over 100: []`. Copyright, module, public import, docstring, exposed public section
   present. Only import is Mathlib: no provider, DRAFT_SORRY, or other project dependency.
   All ten definition-command comparisons with Appendix A returned `EXACT`.

## Closeout

All fifteen hand-written declarations classified; no material mathematical finding open.
No frozen export or provider seal check applies to this infrastructure-only package.
The independent probe verifies the notation bridge; no claim is made that future consumers,
private limit interfaces, P23-16 recurrence production or the final KAM theorem are complete.
Probe cleanup, final hashes and report-only change check are recorded at completion below.

Final completion checks: audited module and all six other frozen-v1 input hashes above rechecked
unchanged; probe deleted; `git diff --check` passed; report has no trailing whitespace and no
pending receipt. Final repository status contains only the pre-existing untracked handoff and
this new untracked report. Verdict remains **PASS WITH NOTES**, with no package repair required.

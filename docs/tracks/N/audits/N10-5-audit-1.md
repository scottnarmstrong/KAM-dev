# N10-5 independent package audit, round 1

Overall verdict: **PASS WITH NOTES** for the N-HEAD-C anchor
`KAM.Nekhoroshev.quasiConvex_nekhoroshev_complexBound` (provider/seal-key audit).
The provider and prospective seal pass the exact frozen type, axioms, and kernel checks.
The generated-root lint exception is permitted by the brief; separate N10-3/4 audit acceptance
remains an integration prerequisite. No mathematical blocker was found in N10-5.
Scope: the N-HEAD-C provider
`KAM.Provider.Nekhoroshev.quasiConvex_nekhoroshev_complexBound` and `KAM.Nekhoroshev.head`.

## Authority and comparison

Audited worktree `/root/code/KAM-inp-n105`, HEAD
`8af716880d931ba9d80e5b22ebbf690ed5e3a2be`, against `inp`
`b6dab3a6fc8453330a4abaa465a782e1aa713798`, using `git diff inp...HEAD`.
Read AGENTS.md, PLAN, DECISIONS, the package audit brief, N10-5 handoff/AUDIT FOCUS,
N10-LEAN-DESIGN (N10-5 row, binder/result table and Appendix A), its independent design audit,
the canonical `/root/code/KAM-inp/.drafts/design/N10Signatures.lean`, track N statement,
blueprint Part 10 and relevant Part 0/9 statements, and N-p910 graph entries.
Read the frozen anchor and its frozen predicate/domain/field definitions and manifest entry.
The user's exact report destination overrides the generic brief's main-worktree destination.

The diff comprises Confinement (170 lines), Existence (78), Headline (50), and the provider
(58 total lines, 43 added). N10-3/4 are inherited changes in this comparison; their direct assembly
interfaces and proofs were reviewed below. This report does not replace their separate independent
audit disposition or certify every earlier mathematical package anew.
The handoff was already untracked before this audit and is preserved.

## Declaration and node verdicts

All unqualified names are in `KAM.Nekhoroshev`. PASS rows describe statement/proof fidelity;
validation receipts follow separately.

| Node / role | Lean declaration and locator | Verdict | Reason |
|---|---|---|---|
| p10:head; hd-univ, hd-abc, hd-d | `head`, Assembly/Headline.lean:26 | PASS | Binder/result text is identical to the canonical signature. H1–H5 build the existing HeadHyp; existence supplies one z; hypotheses_check supplies Data; uniqueness applies to that same z. |
| p0:head; hd-order, hd-const, hd-dep | `KAM.Provider.Nekhoroshev.quasiConvex_nekhoroshev_complexBound`, provider:26 | PASS | Literal frozen telescope. HeadParams/Pos fields retain order; C,T,c,eps0 precede all h/f/epsilon and initial data. First five choice_props conjuncts supply positivity and margin. |
| cf-setting: neighbourhood bridge (private) | `cf_mem_realNbhd`, Confinement:31 | PASS | Real inclusion preserves max norm; equivalent neighbourhood membership, with no changed carrier. |
| cf-setting: derivative bridge (private) | `cf_fderiv_apply`, Confinement:40 | PASS | Differentiability guards the ordinary derivative application identity. |
| cf-setting: Hessian bridge (private) | `cf_hess`, Confinement:48 | PASS | Holomorphy on the open tube supplies derivative regularity; basis expansion converts the existing matrix action estimate. |
| p10:cf-setting (private) | `cf_setting`, Confinement:75 | PASS | Constructs the delivered Theorem1Setting from analytic clauses and arithmetic. No stability or orbital confinement field is assumed. |
| p10:cf-orbit | `cf_orbit`, Confinement:99 | PASS | Projects the frozen two-sided derivative clause on arbitrary time sets. |
| p10:cf-branch | `cf_branch`, Confinement:106 | PASS | Exact current signed signature, using the shorter uniform 2T prefactor. thm1, attained omega0 maximum and hc_time/head_time_prefactor discharge the source application. |
| p10:confinement; cf-trans | `confinement`, Confinement:143 | PASS | Exact radius/time and arbitrary OrdConnected J through zero. cp_rad translates the exponent/radius; positivity gives tau <= 2T exp(...) and rho/2 <= rho. |
| p10:ex-ball | `ex_ball`, Existence:28 | PASS | Triangle inequality gives norm I < R/2+R/4 < R. |
| p10:existence; ex-rho, ex-apriori, ex-glue | `existence`, Existence:40 | PASS | Constructs Data from actual source premises, proves the glue estimate for every required open interval, and invokes ODE.confinement_glue on the same frozen Hamiltonian. |
| p10:un-restrict | `head_solution_restrict`, Existence:58 | PASS | Restricts the time set only, preserving two-sided derivatives at endpoints. Stronger than the positive-L specialization. |
| p10:uniqueness; un-apply | `uniqueness`, Existence:65 | PASS | Valid stronger helper: analytic Data and arbitrary tau suffice. EqOn for the actual two solutions includes L=0; no competitor confinement is assumed. |

All eight new public assembly theorem telescopes in the comparison (cf_orbit, cf_branch,
confinement, ex_ball, existence, head_solution_restrict, uniqueness, head) match the current
canonical signature text exactly. Appendix A is byte-identical to the canonical signature file.
The provider telescope is byte-identical to the frozen telescope. No conclusion-shaped premise,
weakened final conclusion, changed ambient norm, or widened constant dependence was found.

## Assembly and full-chain consumer check

Provider lines 50–54 implement the design's binder/result table literally:
`HeadParams.mk R s M m Mcomplex ωmin`, the corresponding six positivity proofs,
witnesses `p.C,p.T,p.c,p.eps0`, the five constant clauses, then `head hn p hp`.
Unfolding expo/tau/rho gives exactly the frozen exponent, drift and closed time interval.
No bound on the unspecified holomorphic value size of h enters the constants.

Headline lines 41–46 preserve H1–H7 and the same initial data. `hz0` converts the competitor's
initial equality by `hy0.trans hz0.symm`; EqOn is applied pointwise. There is no division by L
or positive-L restriction. `ODE.uniqueness_closed` explicitly covers L=0; the restriction
helper retains the genuine two-sided HasDerivAt clauses.

Choice defines `tau = T*exp(c*epsilon^(-expo))` and `rho = C*epsilon^expo`.
In Confinement:153–167, cp_rad identifies the source exponential with the headline exponential
and the source radius with rho/2. Because T and exp are positive, every |t| <= tau satisfies
|t| <= 2T exp(source exponent), precisely the narrowed cf_branch premise. The latter uses
head_time_prefactor to compare 2T with the actual positive omega0 time prefactor. The maximum
is bounded using its attained point and hc_time, with hc_exc excluding the low-frequency branch.
Thus the narrowed signed helper suffices for the entire frozen horizon, including endpoints
and negative times. Existence then supplies the proved confinement lambda to the existing
ODE glue theorem; it does not promote that lambda to a source premise of head/provider.

## Definition classification and quarantine

There is no new def, abbrev, structure, or instance in the four-file comparison.
The provider's local `p` is the intended six-field HeadParams constructor; hp contains only
positivity. Existing HeadHyp contains exactly H1–H5, and Data exactly positive R/s and analytic
integrable/perturbation predicates. Neither bundles a desired confinement or existence result.

Reviewed reused numerical definitions in Choice: s1=s/2, F1=coth(pi*s/4)^n,
eps1=mu*r0^2/(2^10*A^(2*n)), R0=r0/A, epsPrime=F1*epsilon, tau and rho as above,
and choice=(C,T,c,eps0). They are the intended total numerical expressions; theorem applications
supply positive dimension/radii/epsilon wherever their usual nonzero interpretation is needed.
No theorem relies on a junk fallback. Frozen solution/domain/field objects are reused directly.

The provider has exactly one import, `KAM.Nekhoroshev.Assembly.Headline`.
A recursive source import scan found 158 reachable KAM modules, no missing KAM module,
no frozen theorem module, and no other provider. Thus it imports no DRAFT_SORRY theorem
(and no sealed frozen theorem whose status needs an exception).
The sole production importer of this provider is the corresponding frozen anchor.
The anchor manifest state remains DRAFT_SORRY; it is not sealed by this audit.

## Independent validation receipts

1. Targeted build (serialized, compile gate):

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n105 KAM.Nekhoroshev.Assembly.Headline KAM.Provider.Nekhoroshev.QuasiConvexNekhoroshevComplexBound
   ```

   Exit 0. Gate slot 2 acquired at 19:14:28 UTC. Final output:
   `Build completed successfully (3340 jobs).`
   No warnings from Headline or provider. Replayed unused-variable/section-variable warnings
   occurred in Interfaces/Period, Stability/Gradient, ResonanceGeometry/Maximal and Blocks,
   Poschel/BlockHypotheses, ODE/Exit, Stability/Transfer, Nonresonant, Resonant,
   ResonantStabilityCore, and Assembly/Existence:69 (`hL`). No proof-budget override was used.

2. Exact type, prospective seal, signed head, and all new public theorem axioms:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N105Audit.lean
   ```

   Exit 0, no warnings or errors. The untracked probe imported the actual frozen anchor
   and actual provider and elaborated:

   ```lean
   example : type_of% @KAM.Nekhoroshev.quasiConvex_nekhoroshev_complexBound :=
     @KAM.Provider.Nekhoroshev.quasiConvex_nekhoroshev_complexBound
   ```

   It also copied the entire frozen telescope under fresh name `auditProspectiveSeal`, with body:

   ```lean
   by
     exact KAM.Provider.Nekhoroshev.quasiConvex_nekhoroshev_complexBound
       hn hR hs hM hm hMcomplex hωmin
   ```

   These are exactly all seven explicit frozen binders in order; implicit parameters are inferred.
   A third declaration copied the canonical head signature under `auditHeadSignature`, with
   the inherited implicit `{n : ℕ}` explicit in the probe context and proof `exact KAM.Nekhoroshev.head hn p hp`.
   This independently checks elaborated head fidelity in addition to textual identity.

   Exact axiom output (provider wrapping normalized only):

   ```text
   'KAM.Nekhoroshev.cf_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.cf_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.ex_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.existence' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.head_solution_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.head' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Provider.Nekhoroshev.quasiConvex_nekhoroshev_complexBound' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   The frozen anchor imported for the type probe remains sorry-bound; no probe uses its
   proof as a premise of the provider. Provider's axiom closure contains no sorryAx.

3. Kernel replay, one invocation after the probe completed:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Provider.Nekhoroshev.QuasiConvexNekhoroshevComplexBound KAM.Nekhoroshev.Assembly.Headline KAM.Nekhoroshev.Assembly.Existence KAM.Nekhoroshev.Assembly.Confinement
   ```

   Exit 0. Entire stdout/stderr:

   ```text
   replaying KAM.Nekhoroshev.Assembly.Confinement
   replaying KAM.Nekhoroshev.Assembly.Existence
   replaying KAM.Nekhoroshev.Assembly.Headline
   replaying KAM.Provider.Nekhoroshev.QuasiConvexNekhoroshevComplexBound
   ```

4. Repository lint, after kernel replay, with niceness inherited by its ABI Lean subprocess:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the brief-permitted stale generated root. Entire output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (900 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No generated file was regenerated. Module format, source hygiene, frozen guard, and ABI
   checks pass. Comment-masked scans of all four changed files found no sorry/admit/axiom/
   unsafe/opaque, EuclideanSpace, or set_option. File lengths are 170/78/50/58; every line
   is at most 100 characters. All four have copyright, module, interface public imports,
   module docstring and public section. No new public HELPER short name is reused; scans
   found each of head/cf_orbit/cf_branch/confinement/ex_ball/existence/head_solution_restrict/
   uniqueness at its sole production declaration.

5. Preservation and final checks:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD
   git diff --check
   git status --short
   ```

   Both whitespace checks exit 0 with no output; protected-file diff is empty.
   HEAD and inp remain the hashes recorded above. Final status contains only:

   ```text
   ?? docs/tracks/N/audits/N10-5-audit-1.md
   ?? docs/tracks/N/audits/N10-5-handoff.md
   ```

   The second file predates this audit. Scratch N105Audit.lean, N105Kernel.log and N105Lint.log
   were removed after their results were recorded. All audit Lean/Lake/leanchecker invocations
   and lint's ABI elaboration ran sequentially, with LEAN_NUM_THREADS=1 and nice -n 5;
   the build alone used the prescribed compile wrapper. No clean/update/cache operation occurred.




## Defects, deviations and limits

No new suspected pinned-source, blueprint, or frozen-statement defect was found in this assembly.
Inherited Pos93 radius and norm adaptations remain as documented in blueprint Part 9 and the N10
design: the quoted condition “r0≤4l/m” alone does not ensure the full-rank block inequality
M*r0≤ell/2 when M/m is unbounded; this route uses r0≤ell/(2B). The max/l1 normalization also
changes the time exponent by sqrt(n). These inherited source reports were not independently
rechecked against a PDF here and are not new verified source errata.

The frozen anchor's proposal-language comment is historical prose; the D20-approved type and
manifest control this audit. No type repair is proposed. The design audit's deferred concrete
Part 9 setting/maximum and ODE import obligations are now actual applications in the reviewed
source, with their validation recorded above. Separate upstream audit acceptance remains an
integration responsibility.

No production Lean, frozen file, manifest, generated root, README, or git state was changed.
Only this report is a persistent auditor addition; temporary probes are removed after checks.

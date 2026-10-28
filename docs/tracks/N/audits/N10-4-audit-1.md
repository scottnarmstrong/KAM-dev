# N10-4 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the scoped infrastructure package. All four signed declarations pass; all eight assigned graph nodes are established. No scoped proof or statement defect was found. No frozen anchor is proved or seal-ready by this package alone: the N-HEAD-C provider and headline assembly belong to N10-5.

## Scope and authority

Audited only `KAM/Nekhoroshev/Assembly/Existence.lean` (78 lines), at HEAD `df56ace5773df1214c0a85e6ef0640864a994098`, against `inp` at `cc793a7c3e329bd89353f655ccc5630f3f4ddcef`, using `git diff inp...HEAD` (merge-base `ec23b835c48802c9afb977ff01f72600b82cca7f`). The full comparison also includes the 170-line `Assembly/Confinement.lean` from N10-3; that dependency was inspected for applicability, not independently audited here. The pre-existing untracked `N10-4-handoff.md` was left untouched.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, N10-4 handoff/AUDIT FOCUS, N10-LEAN-DESIGN.md (especially node map and N10-4 row 176), its independent design audit, blueprint-N/parts/p10-assembly.tex:111–134, the relevant track-N statement sections, frozen N-HEAD-C and the frozen definitions used by these results. The user's explicit absolute report destination overrides the generic brief's main-worktree destination. No state-changing git operation or production edit was performed.

Canonical signatures: `/root/code/KAM-inp/.drafts/design/N10Signatures.lean`, SHA-256 `22021dd133e9ee9b787f52fae98bed1f544f960de5a83ec3ba891c62fb413bfe`. All four complete telescopes/results are byte-for-byte identical to their signatures (lines 173–201). Fresh scratch declarations copied those telescopes and applied the corresponding production exports with precisely the explicit arguments in order; all elaborated at default resource limits. No provider/frozen seal probe applies: this slice supplies neither a provider export nor a seal body.

## Declaration and node coverage

All declaration names below are in `KAM.Nekhoroshev`; source locators refer to Existence.lean.

| Node | Declaration / realization | Verdict | Reason |
|---|---|---|---|
| `bpN:p10:existence` | `existence`, lines 40–55 | PASS | Literal initial value, genuine solution on the whole closed interval, and drift estimate; exact signed type. |
| `stepN:p10:ex-rho` | `existence`, line 48 (`cp_size`) | PASS | Supplies positive rho and tau, with the same epsilon and constants. |
| `stepN:p10:ex-ball` | `ex_ball`, lines 28–38 | PASS | Exact signed closed-ball inclusion; triangle inequality gives norm strictly below 3R/4, hence below R. |
| `stepN:p10:ex-apriori` | `existence`, lines 53–54 | PASS | Lambda covers every open OrdConnected J through zero; invokes existing confinement without adding a confinement premise. |
| `stepN:p10:ex-glue` | `existence`, lines 49–55 | PASS | Constructs Data from source hypotheses and applies ODE.confinement_glue; discards only its additional comparison-uniqueness output. |
| `bpN:p10:uniqueness` | `uniqueness`, lines 65–74 | PASS | Exact signed type. Valid strengthening to analytic Data, arbitrary tau, and arbitrary solutions; no QC or drift premise. |
| `stepN:p10:un-restrict` | `head_solution_restrict`, lines 58–62 | PASS | Exact signed type; set containment transports the complete frozen predicate, retaining two-sided endpoint derivatives. |
| `stepN:p10:un-apply` | `uniqueness`, lines 73–74 | PASS | Exact application of ODE.uniqueness_closed after restriction. Includes L=0; common initial value suffices. |

There are no extra public declarations, unsigned node-named exports, or uncovered nodes assigned to this module. `cp_size` is upstream and is consumed rather than reimplemented. All four public names are signed names; repository declaration search found no competing declarations with those short names. No new public helper or root-namespace shadow is introduced.

## Proof, hypotheses and definitions

`ex_ball` uses the existing Pi maximum norm and metric closed ball, with rho <= R/4, norm I0 < R/2, and R > 0. `existence` supplies `Data = ⟨hp.hR, hp.hs, hh.1, hf⟩`; this is exactly positivity plus frozen analytic integrable/perturbation membership, not a bundled dynamical assertion. The open action ball lies in ball 0 (R+s) because s > 0. The confinement callback supplies precisely the glue theorem's a-priori estimate on arbitrary eligible intervals. No solution, continuation, or drift is assumed in the existence theorem.

Restriction works for any H, U, tau and L with L <= tau, including empty target intervals. It preserves membership, differentiability of H at the visited point, and ordinary HasDerivAt. Uniqueness uses only analytic ODE Data and the two actual solution predicates. The unused `hL` binder is signature-mandated: ODE.uniqueness_closed already treats both nonnegative and negative L, so the signed nonnegativity assumption is harmless redundancy. For L=0 the common initial value gives the singleton-interval conclusion.

Definition classification: **no new def, abbrev, structure, instance, or numerical choice**. Existing `actionBall` is the open maximum-norm metric ball; `rho = C*epsilon^a`, `tau = T*exp(c*epsilon^(-a))`, `HeadHyp`, `Data`, `realHamiltonian`, and `IsSolutionOn` retain their existing meanings. No fallback, total-derivative junk value, norm substitution, or new carrier is used. In particular the frozen solution predicate retains its differentiability guard. All constants come from the fixed HeadParams, before h/f/epsilon/initial data.

## N10-3 re-scope and consumer applicability

The only N10-3 export consumed in this file is `confinement` (line 54); N10-4 never calls `cf_branch` or consumes its tube-membership clause. It requires exactly the signed estimate

`forall t in J, |t| <= p.tau epsilon -> norm ((y t).2 - I0) <= p.rho epsilon`.

Thus narrowing cf_branch to the uniform signed time window, while preserving this confinement export, meets every N10-4 need. In this snapshot the signed uniform branch window is explicitly `2*T*exp(pi*s1/(3*sqrt n)*(eps1/epsPrime)^a)`; `cp_rad` makes this `2*tau`. The local confinement proof uses only times up to tau, hence lies inside that window. It does not require the full upstream orbit-dependent time prefactor.

**Snapshot limitation:** both this worktree and the canonical signature file still contain the older tube-membership conjunct in cf_branch. The separate N10-3 re-scope is not present here, so this report does not certify that revision or N10-3 itself. Compatibility is established at the actual consumed confinement interface. If the handoff's shorthand “|t| <= 2T” instead means literally 2*T without the exponential, it alone does not imply the required tau estimate; the revised N10-3 audit must establish the unchanged confinement export. No assumption of an unobserved revision is used for this verdict.

## Independent validation

All Lean/Lake commands used LEAN_NUM_THREADS=1 and nice -n 5, strictly sequentially. No clean, dependency mutation, full-library rebuild, or resource override was used.

1. Targeted compile gate:

   `LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n104 KAM.Nekhoroshev.Assembly.Existence`

   Exit 0. Output: `[inp-gate] slot 2 acquired 18:57:40 for KAM.Nekhoroshev.Assembly.Existence`; `Build completed successfully (3338 jobs).` Replayed upstream unused-variable warnings; the only scoped warning is Existence.lean:69:13, variable `hL` not explicitly referenced. No heartbeat/design failure.

2. Fresh exact-signature application probes and axioms:

   `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N104Audit.lean`

   Exit 0. Four copied-signature applications elaborated. Output:

   ```text
   'KAM.Nekhoroshev.ex_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.existence' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.head_solution_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay (one invocation; no separate provider or other scoped lemma module exists):

   `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Assembly.Existence`

   Exit 0. Output: `replaying KAM.Nekhoroshev.Assembly.Existence`.

4. Source/import hygiene: 78 lines, no line over 100 characters, required copyright/module/public imports/module docstring/public section present. No forbidden escapes, ambient EuclideanSpace, resource overrides, or new assumptions. Recursive KAM import inspection visited 156 modules, with **zero frozen theorem imports and zero provider imports**; consequently no DRAFT_SORRY theorem is imported and no sealed-theorem state exception is needed.

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty. `git diff --check inp...HEAD`: exit 0, no output.

6. Repository lint:

   `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`

   Exit **1**. Complete diagnostic output:

   ```text
   Lean lines over 100 characters:
   /root/code/KAM-inp-n104/KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77:101
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (890 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The generated-root exception is expressly permitted by the brief. The separate frozen planetary line-length failure is **not** that exception, so repository-wide lint is not reported as passing. Its file is byte-identical to HEAD and the merge-base; it is inherited and outside the authorized audit slice. The current inp tip has a different seal-body formatting, but the required triple-dot comparison is empty for all frozen/generated paths. This finding prevents an unconditional clean-lint verdict; it is not a defect introduced by N10-4. No frozen/generated file was edited.

The temporary `.lake/abi-scratch/N104Audit.lean` was deleted. Final report verification: the report exists at the exact requested worktree path; only it was added by this audit, with the initial untracked handoff retained. `git diff --check` and `git diff --check inp...HEAD` exit 0.

## Findings, uncertainties, errata and deviations

- **Low, inherited hygiene:** global lint exits 1 for the frozen planetary 101-character line in addition to the permitted stale generated root. Keep this result visible for integration; no scoped repair is required or authorized.
- **Informational:** unused `hL` is required verbatim by the signature. It does not weaken or alter the theorem and is not a reason to change the signed telescope.
- **Dependency boundary:** the unseen N10-3 re-scope must preserve the signed confinement theorem. This audit establishes N10-4's exact consumer requirement and validates the current checkout; it does not re-audit Part 9/N10-3 or certify an unseen replacement.

No new suspected pinned-source or blueprint mathematical defect, extra premise, dropped conclusion, changed norm, widened constant dependence, or formalization deviation was found in the audited module. The broader uniqueness helper is the expressly reviewed design strengthening. No frozen anchor was edited or sealed. No heartbeat or other default-resource elaboration failure occurred.

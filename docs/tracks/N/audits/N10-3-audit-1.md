# N10-3 independent package audit, round 1

Overall verdict: **FAIL under the handoff's literal graph-export requirement**. The three public declarations match the canonical signatures exactly, and source inspection finds a sound proof of the scoped confinement estimate. The failure is a conflict between those approved signatures and the newer AUDIT FOCUS requirement that an export named after a graph node state its literal conclusion. Findings F1 and F2 below preserve both authorities rather than silently changing either.

N-HEAD-C anchor status: **not seal-ready on this package alone**. This slice supplies a-priori confinement, not the existence/uniqueness assembly or a provider. Provider/frozen-type and seal-body probes are inapplicable to this diff; no provider or anchor is added or changed. This is not a refutation of N-HEAD-C or of the confinement theorem.

## Scope and authority

Worktree `/root/code/KAM-inp-n103`; HEAD `4c45d2296071e453b7ba60d294f0339a8f3084f7`; comparison `inp` at `ea31a1aa7688d687938216c4d39a75e247356cb4` when inspected. `git diff inp...HEAD` adds only `KAM/Nekhoroshev/Assembly/Confinement.lean` (170 lines). The pre-existing untracked handoff was retained unchanged. The shared comparison ref advanced during validation (observed later at `a81e8d4215d2f99f8c148dd4ca24915a17ca95b5`); repeating `git diff inp...HEAD` still showed exactly the same one-file, 170-line addition and no protected-file changes.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief, N10-3-handoff.md, N10-LEAN-DESIGN.md (especially N10-3 and the node map), DESIGN-N10-design-audit-1.md, canonical `/root/code/KAM-inp/.drafts/design/N10Signatures.lean`, track N statement, Part 10 blueprint and graph packet, relevant Part 9 setting/maximum/stopped-theorem text and delivered Lean interfaces. Checked the frozen N-HEAD-C telescope and the frozen solution, Hamiltonian, vector field, frequency, action ball, analytic/QC/derivative/Hessian predicates used by this slice.

The user's exact absolute report destination overrides the generic brief's main-worktree destination. Only this report is a persistent auditor edit; temporary probes are confined to `.lake/abi-scratch/` and removed afterwards. No state-changing git operation or source edit is authorized or performed.

## Findings

**F1 — Literal graph-export mismatch, `cf_orbit`.** At `Confinement.lean:99–104`, the export states only `∀ t ∈ J, HasDerivAt y (hamiltonianVectorField H (y t)) t`. The graph packet `docs/graph/N/packets/N-p910.nodes.md:579–587` and blueprint `p10-assembly.tex:102` require the compound orbit-applicability conclusion: “F_* = X_{H_{h,f}} = X_{H^ℝ} on W”, the derivative clause, and “y(0)_2 ∈ P”. The latter two applicability facts are correctly supplied inside `cf_branch` (initial projection/closed-ball membership at lines 118–123, Hamiltonian equality at 124–128). They are absent from the named export's statement. The design audit explicitly accepted that split (its signature table row `cf_orbit`), so the implementation follows its signature; it does not meet the handoff's additional literal-export rule. Resolve the ownership contract explicitly: either approve the helper/split mapping as an exception, or revise the canonical signature and export together. Do not count the derivative-only signature as the literal whole graph node.

**F2 — Literal graph-export mismatch, `cf_branch`.** At `Confinement.lean:106–116`, the public estimate applies for `|t| ≤ 2*p.T*exp(...)`. Blueprint `p10-assembly.tex:104` and the graph packet at lines 609–618 (`stepN:p10:cf-branch`) require the full time `T₀*exp(...)`, where `T₀=A²*s1/Ω₀`. The proof derives `2*T ≤ T₀` and uses the full upstream theorem internally, then exports the shorter interval. A bound on the shorter interval does not entail the full node's conclusion. The canonical signature and design lines 135 and 425–435 deliberately prescribe this shortening; source proof correctness and exact-signature fidelity therefore pass, while the stricter named-node rule fails. Resolve by an explicit mapping exception or coordinated signature/export revision; the auditor has not repaired the source or design. The final `confinement` conclusion needs only the shorter time and is unaffected mathematically.

## Node and declaration coverage

All names below are in `KAM.Nekhoroshev`. Internal proof coverage is complete; literal named-export coverage has the two exceptions above.

| Node / obligation | Declaration / location | Verdict | Reason |
|---|---|---|---|
| Real/complex tube bridge | private `cf_mem_realNbhd`, 31 | PASS | Equivalence via the isometric real embedding and the same max-norm radius; no positive-radius premise needed. |
| Derivative application | private `cf_fderiv_apply`, 40 | PASS | Continuous-linear-map evaluation chain rule, assuming differentiability of the derivative. |
| Hessian interface bridge | private `cf_hess`, 48 | PASS | Holomorphy on an open domain gives derivative differentiability; coordinate expansion in the second slot matches the existing complexHessian definition exactly. |
| `stepN:p10:cf-setting`; local `stepN:p10:hc-setting` obligation | private `cf_setting`, 75; call at 119 | PASS | Builds the actual Theorem1Setting at the chosen closed real ball with r0,s1,mu,B,ell and the original h,f. Smallness and WBound supplied separately at 120–128. |
| `stepN:p10:cf-orbit` | public `cf_orbit`, 99; remaining facts inside `cf_branch` | FAIL literal export; PASS internal proof | F1; exact canonical signature, two-sided derivative on arbitrary J, no confinement premise. |
| `stepN:p10:cf-branch` | public `cf_branch`, 106 | FAIL literal export; PASS canonical signature/proof | F2; correct specialized branch (a), tube membership, half-radius bound, and justified shorter time. |
| `stepN:p10:cf-trans` | internal arithmetic in `confinement`, 153–166 | PASS | cp_rad identifies exponent and half-radius; positivity gives tau≤2T exp(...) and rho/2≤rho. |
| `bpN:p10:confinement` | public `confinement`, 143 | PASS | Literal conclusion on every OrdConnected interval through zero, including endpoints, with the original frozen IsSolutionOn and max displacement. |

No new `def`, `abbrev`, `structure`, instance, carrier or fallback is introduced. All seven new declarations are theorem proofs (four private, three public). Inherited `HeadParams`, `HeadHyp`, centralSet, numerical constants and the frozen Hamiltonian objects are reused. The local setting is a proved bundle of analytic/QC source premises, not a supplied stability conclusion. The choice of constants remains before h,f,epsilon; the existential h-value bound does not enter their choice.

## Reconciliation and proof review

The delivered Part 9 interface uses a real set P, with `cpx P` its complex image; that image is definitionally centralSet for the chosen closed real ball. `cf_mem_realNbhd` supplies the exact real/complex neighbourhood equivalence. `cf_hess` bridges the two existing presentations of the same Hessian action. The setting's conic quasi-convexity follows by the explicit ≤ / > case split, and the finite weighted norm is obtained from the genuine WBound.

The frozen solution is projected to a total-field derivative without assuming it stays in the smaller tube. `realH (fun w => h w.2 + f w) = realHamiltonian h f` is proved by rfl, so the general field-locality helper is unnecessary here. Although the blueprint describes a zero extension, its field agrees with this total Hamiltonian on the open tube, exactly as the stopped theorem permits. No alternative dynamics are substituted.

`omega0` supplies actual attainment at I1 in its Euclidean closed ball, and the central lower bound. `hc_exc` gives strict branch exclusion and positivity of the maximum; `hc_time` bounds its attained value by sqrt(n)*M; `head_time_prefactor` then proves 2T≤A²s1/Ω₀. Division and negative real powers are guarded by positive parameters/epsilon. No change of ambient norm, period, strip normalization, orbit or time is made.

## Independent validation

Every Lean/Lake invocation below was serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`; no resource override was used. The targeted build ran through the required compile gate. Lint's ABI Lean subprocess inherits both the thread setting and niceness.

1. **Targeted build, exit 0**:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n103 KAM.Nekhoroshev.Assembly.Confinement
   ```

   Relevant exact output:

   ```text
   [inp-gate] slot 2 acquired 18:35:09 for KAM.Nekhoroshev.Assembly.Confinement
   Build completed successfully (3336 jobs).
   ```

   There were replayed upstream unused-variable/section-variable warnings in Interfaces.Period, Stability.Gradient, ResonanceGeometry.Maximal, ResonanceGeometry.Blocks, Poschel.BlockHypotheses, ODE.Exit, Stability.Transfer, Stability.Nonresonant, Stability.Resonant and Stability.ResonantStabilityCore. No warning originated in the audited file. This was a targeted incremental build against the worktree snapshot, not a full-library rebuild.

2. **Exact signatures and axioms, exit 0**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/n103-audit-probe.lean
   ```

   The probe copied each of the three canonical theorem telescopes verbatim under a fresh name, supplied its proof by the corresponding production export, and checked `example : type_of% @audit_<name> := @KAM.Nekhoroshev.<name>`. Independent textual comparison also returned `True` for all three signatures (including binder order and implicitness). Exact output:

   ```text
   'KAM.Nekhoroshev.cf_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.cf_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. **Kernel replay, one invocation, exit 0**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Assembly.Confinement > .lake/abi-scratch/n103-leanchecker.log 2>&1
   ```

   Complete output:

   ```text
   replaying KAM.Nekhoroshev.Assembly.Confinement
   ```

   This is the only new lemma module and there is no package provider.

4. **Source lint**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, caused only by the explicitly permitted generated-root staleness. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (880 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   All other lint components passed; the generated root was deliberately left untouched.

5. **Mechanical hygiene/import checks**: 170 lines, maximum 100 Unicode characters per line; copyright/module/public imports/docstring/exposed public noncomputable section present; no banned proof token, ambient EuclideanSpace, heartbeat/recursion/synthesis override or new instance. The three public short names occur as declarations only in this file across KAM; all are in KAM.Nekhoroshev, with no root shadow. Source import traversal found 154 KAM modules, no provider, and 27 frozen definition files, every one recorded SEALED in the current manifest. No frozen theorem, including a DRAFT_SORRY theorem, occurs in that closure.

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD
   git diff --check
   ```

   All exit 0 with empty output. No generated root or README was edited. Final status retains the pre-existing untracked handoff and adds only this report. Audit-created scratch probe/import inventory/kernel log are deleted after inspection.

## Errata, deviations and limits

No new pinned-source erratum or frozen-statement defect was found. The inherited Pos93 radius strengthening and max/Euclidean cutoff adaptations remain disclosed in blueprint Part 9; this slice is not an independent PDF audit of those upstream decisions. F1/F2 concern graph/design/export bookkeeping, not a newly discovered false mathematical assertion. No silent change to hypotheses, constants, quantifiers, frozen text or consumer applicability was made.

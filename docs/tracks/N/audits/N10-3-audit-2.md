# N10-3 independent package audit, round 2

Overall verdict: **PASS WITH NOTES for N10-3 under the signed-signature ruling.** Round 1 F1/F2 are resolved by the user's explicit re-scope, not by a source change or an assertion that the shorter export implies the longer graph statement. All three exports have exactly the canonical signatures. The narrowed forms supply everything required by the specified N10-4/N10-5 consumers and the frozen headline telescope. No real consumer gap was found.

**N-HEAD-C anchor: not seal-ready from this package.** Its manifest state remains `DRAFT_SORRY`; this checkout has neither `Assembly/Existence.lean` nor `Assembly/Headline.lean`, and the provider file is still a declaration-free stub. This audit passes the confinement slice and its applicability to the designed consumers, not those undelivered packages or the frozen theorem's proof.

## Scope and authority

Report destination: `/root/code/KAM-inp-n103/docs/tracks/N/audits/N10-3-audit-2.md`, as explicitly requested, overriding the generic brief's main-worktree destination. Only this report is a persistent auditor edit; temporary probes are under this worktree's `.lake/abi-scratch/` and removed after validation. No production Lean, blueprint, graph, frozen file, manifest, generated root, README or existing audit was changed; no state-changing git operation was performed.

Read the package brief at `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, AGENTS.md, PLAN, DECISIONS, N10-3 handoff, round 1, N10 design and design audit, canonical `/root/code/KAM-inp/.drafts/design/N10Signatures.lean`, track statement, Part 10 source and graph packet, delivered Part 9 `thm1`, and the relevant frozen headline/solution definitions and ODE interfaces. The 18:47 ruling is supplied as authority by the current user prompt: signed exports follow the signature file; compound orbit applicability is supplied inside `cf_branch`, whose deliberately narrowed horizon is documented at design lines 135 and 425–435.

HEAD at inspection: `c1458ee3ada211131cfd3c20c64ec0158d129ea8`; `inp`: `be6fc7b01267bd5d16506ff11a84c1f7b93cc791`. `git diff inp...HEAD` adds Confinement.lean (170 lines), the handoff and round 1 report. Only the Lean addition is the implementation under audit. The shared `inp` ref advanced independently to `7413c7f87f6e8cdabb0c32c8683d46b65135ef5e` by the final check; the three-file comparison and protected-file emptiness were unchanged. This audit did not mutate it.

## Signatures and graph coverage

All declarations are in `KAM.Nekhoroshev`. Exact textual comparison of every telescope, including binder order and implicitness, returned `True` for `cf_orbit`, `cf_branch`, and `confinement`; independent elaboration against copied canonical telescopes is recorded below.

| Node / declaration | Location in Confinement.lean | Verdict and literal coverage |
|---|---|---|
| Real/complex tube bridge / private `cf_mem_realNbhd` | 31–37 | PASS. Same max-norm radius under real inclusion; no alternative carrier. |
| Hessian evaluation bridge / private `cf_fderiv_apply` | 40–45 | PASS. Differentiability of the derivative supports continuous-linear-map evaluation. |
| Hessian interface bridge / private `cf_hess` | 48–71 | PASS. Holomorphic regularity on the open tube supplies derivative differentiability; coordinate expansion reproduces the original complexHessian action. |
| `stepN:p10:cf-setting`, local `stepN:p10:hc-setting` / private `cf_setting` | 75–96; 119–120, 127 | PASS, internal. Actual Theorem1Setting on the chosen closed real ball; positive-small weighted bound supplied separately from hypotheses_check. |
| `stepN:p10:cf-orbit` / public `cf_orbit` | 99–104; 118–128 | PASS under ruling. **Exported:** two-sided derivative for every t in J, on any frozen solution. **Internal:** initial action in P at 118, 121–123; field choice/equality at 124–128. Together these cover the compound literal graph conclusion (`N-p910.nodes.md:587`, blueprint p10 line 102); the derivative-only export does not state that whole conjunction. |
| `stepN:p10:cf-branch` / public `cf_branch` | 106–140 | PASS under ruling. **Internal:** `ka` obtained at 127–128 is the actual full-T0 implication of thm1(a); its branch premise follows from `hc_exc` at 130, 138. **Exported:** tube membership and half-radius drift only for the signed shorter time `2*T*exp(E)`. It does not export the full-T0 graph conclusion (`N-p910.nodes.md:618`, blueprint p10 line 104). |
| `stepN:p10:cf-trans` / arithmetic inside `confinement` | 153–166, together with 129–139 | PASS, internal. cp_rad converts exponent/radius; positivity gives tau ≤ 2T exp(E) and rho/2 ≤ rho. The full chain tau ≤ 2T exp(E) ≤ T0 exp(E) is covered across the two proofs, rather than re-exported in one statement. |
| `bpN:p10:confinement` / public `confinement` | 143–166 | PASS, literal conclusion exported. Every OrdConnected J through zero, frozen original solution, endpoints included, exact tau/rho and max displacement. |

Here `E = (pi*s1/(3*sqrt n))*(eps1/epsPrime ε)^a`, `a=1/(2*n)`, and `T0=A^2*s1/Ω0`. The design's mapped setting, orbit, branch and translation obligations are thus covered internally. Graph bookkeeping should retain these enclosing proof locations and explicitly distinguish them from the narrower exported signatures; no literal full-node export is being certified for cf_orbit or cf_branch. No graph edits are made here.

The applicability proof does not assume future tube confinement. `hy` supplies the original total-field derivative; `hIP` follows from the strict initial ball and hy0; `realH (fun w => h w.2 + f w) = realHamiltonian h f` holds by rfl. The concrete delivered thm1 requires equality on its real strip; this global identity suffices, so the more general locality helper need not be called. `omega0` supplies genuine maximum attainment, not a guessed supremum bound; `hc_time` and `head_time_prefactor` prove `2T≤T0` with Ω0 positive. Strict exception exclusion comes from the original frequency lower bound. No new premise, norm instance, extension of the dynamics, or enlarged dependence of constants appears.

## Consumer audit

The signed consumer contracts are `N10Signatures.lean:173–217`; their design mapping is at `N10-LEAN-DESIGN.md:79–94,176–205`. The actual continuation and uniqueness APIs are `KAM/Nekhoroshev/ODE/Specialization.lean:174–212`.

The key equalities/inequalities are

```text
cp_rad: E = c*ε^(-a),  R0/2*(epsPrime ε/eps1)^a = rho ε/2
signed cf_branch endpoint = 2*T*exp(E) = 2*tau ε
frozen headline endpoint = T*exp(c*ε^(-1/(2*n))) = tau ε
0 < tau ε,  0 < rho ε ≤ R/4,  tau ε ≤ 2*tau ε ≤ T0*exp(E).
```

The last comparison is used only inside the confinement proof; consumers need the first endpoint tau, not T0. Neither closed endpoints nor negative times enlarge the requirement, since all estimates use `|t|≤tau` and the derivative remains two-sided.

| Consumer | Required inputs / conclusion | Applicability verdict |
|---|---|---|
| N10-4 `ex_ball` | closedBall I0 rho ⊆ actionBall n R | PASS. Triangle inequality from norm I0 < R/2 and rho ≤ R/4 gives norm I < 3R/4 < R. Uses cp_size, not either orbit/branch export. |
| N10-4 `existence` | one genuine solution on Icc(-tau,tau), correct initial value, drift ≤ rho | PASS. ODE.confinement_glue asks for the bound only for t in arbitrary open OrdConnected J through zero with `|t|≤tau` (lines 192–194), precisely supplied by public confinement, which even permits arbitrary OrdConnected J. Its other inputs are Data from hp.hR/hp.hs/hh.1/hf, openness and actionBall inclusion in ball 0 (R+s), cp_size and ex_ball. No 2tau or full-T0 continuation estimate is demanded. The API itself returns the closed-interval solution and two-sided endpoint derivatives. |
| N10-4 `head_solution_restrict` | a solution on Icc(-tau,tau) and L≤tau | PASS. Direct time-set restriction of the same frozen predicate; no orbit applicability conjunction or stability estimate needed. |
| N10-4 `uniqueness` | analytic Data, two genuine solutions with the same initial value, 0≤L≤tau | PASS. Restrict z, then invoke actual ODE.uniqueness_closed. It requires no prior confinement of the competitor and no cf_branch/full-T0 clause; L=0 is covered. |
| N10-5 `head` | exact H1–H7, chosen p constants, same z for existence/drift/comparison | PASS at contract level. Build HeadHyp in its existing order, use existence once, then uniqueness with the same z and each L/y. hy0 is converted using z's initial equality. No compound cf_orbit clause survives as a missing head premise. |
| N10-5 provider / frozen N-HEAD-C | constants before h/f/ε; positivity/margin; solution and drift through tau; comparison on every 0≤L≤tau | PASS at telescope/consumer level. Choose p from the six numeric inputs, use choice_props and head, unfold HeadParams.expo/tau/rho. The canonical provider telescope is textually identical to frozen lines 47–70. The frozen bound uses T, not 2T or T0. No extra consumer assumption or halving of the frozen T is required. Actual provider/seal proof validation is deferred until that package exists. |

A scratch-only elaborated compatibility probe constructs the exact signed ex_ball, existence, restriction and uniqueness statements using these production interfaces; it adds no assumptions and uses no sorry. This verifies the continuation boundary against delivered Lean, beyond merely reading the design. It is audit evidence, not a production N10-4 implementation or kernel replay of that future module. Head/provider applicability above is a telescope and assembly review, not a claim to have built their absent proofs.

## Definitions, hygiene and independent validation

No new def, abbrev, structure, instance or fallback is introduced by N10-3. The four private helpers and three public declarations are theorem proofs. The locally constructed setting contains proved analytic/QC source data, rather than an assumed stability conclusion. Existing HeadParams and frozen objects are reused unchanged on their original carriers. Constants precede h/f/ε; no bound on the value of h enters their choice.

All Lean/Lake invocations are serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`, at default resource budgets. The targeted build uses the compile gate; no cache command, clean, update or full-library rebuild is used.

1. **Targeted build, exit 0**:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n103 KAM.Nekhoroshev.Assembly.Confinement
   ```

   Exact gate/completion output:

   ```text
   [inp-gate] slot 1 acquired 18:51:09 for KAM.Nekhoroshev.Assembly.Confinement
   Build completed successfully (3336 jobs).
   ```

   Replayed upstream unused-variable/section-variable warnings appeared in Interfaces.Period, Stability.Gradient, ResonanceGeometry.Maximal/Blocks, Poschel.BlockHypotheses, ODE.Exit, Stability.Transfer/Nonresonant/Resonant/ResonantStabilityCore. None originated in Confinement. This was the required targeted incremental build.

2. **Copied canonical signatures and production axioms, exit 0**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/n103-audit2-signatures.lean
   ```

   Each canonical telescope was copied verbatim into an example proved by the corresponding export with its original explicit arguments. Complete output:

   ```text
   'KAM.Nekhoroshev.cf_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.cf_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. **Consumer compatibility probe, exit 0**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/n103-audit2-consumers.lean
   ```

   Exact copied canonical telescopes for ex_ball, existence, head_solution_restrict and uniqueness were proved under fresh audit2_ names. The existence proof actually passes public confinement to production ODE.confinement_glue at tau/rho; the uniqueness proof actually passes the restricted frozen solution to production ODE.uniqueness_closed. Axiom output:

   ```text
   'KAM.Nekhoroshev.audit2_ex_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.audit2_existence' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.audit2_head_solution_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.audit2_uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   The only diagnostic was the scratch uniqueness signature's unused `hL` at line 60: ``warning: Variable name `hL` is not explicitly referenced.`` This is because the delivered uniqueness_closed API handles negative L as an empty interval too. The copied signed telescope was retained unchanged; no linter/resource override was introduced.

4. **Kernel replay, exit 0**, one invocation for the only new Lean module:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Assembly.Confinement
   ```

   Complete output:

   ```text
   replaying KAM.Nekhoroshev.Assembly.Confinement
   ```

5. **Source lint, exit 1 only for the permitted generated-root exception**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (880 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The brief explicitly permits this generated-root staleness. KAM.lean was not regenerated. All remaining lint components passed; lint's ABI Lean subprocess inherited the same thread/niceness settings.

6. **Mechanical checks**: 170 lines, maximum 100 Unicode columns; copyright, module, public imports, module docstring and public noncomputable section present. No banned proof escapes, heartbeat/recursion/synthesis overrides, EuclideanSpace, instances or root declarations. The three public short names have no other theorem declaration in KAM. Import traversal: 154 KAM modules, no provider, no frozen theorem, 27 frozen definition files all covered by SEALED manifest entries. Complete manifest coverage/state assertions passed using its actual `path` field.

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD
   git diff --check
   ```

   All exit 0 with empty output. The current provider has no exported theorem, so a provider=frozen-type or explicit-binder seal-body elaboration probe is inapplicable to this package. The canonical intended provider telescope was independently compared with the actual frozen declaration and is textually identical. No provider/anchor proof closure is inferred from that comparison.

   Final `git status --short` contains only `?? docs/tracks/N/audits/N10-3-audit-2.md`. Both audit-created probes were removed after inspection. Whitespace checks of the comparison, tracked worktree and new report have no diagnostics (the new-file `git diff --no-index --check /dev/null <report>` returns 1 for the nonempty addition).

## Findings, errata and limits

No blocking finding remains under the explicitly revised authority. Round 1 F1/F2 correctly described an export-versus-literal-node distinction; the ruling accepts that distinction, and this round independently verifies downstream sufficiency. They are not being reclassified as literal signature equality with the graph.

No new pinned-source erratum or frozen-statement defect was found. Inherited Pos93 radius strengthening and norm/cutoff adaptations remain disclosed at design lines 153–162 and in blueprint Part 9; this re-scope is not an independent PDF audit of upstream estimates. The only bookkeeping note is to record the internal-versus-exported coverage above when updating the graph. The only proof-delivery limit is the separate N10-4/N10-5 and eventual provider/seal validation. Neither limit is a deficiency of the signed N10-3 exports.

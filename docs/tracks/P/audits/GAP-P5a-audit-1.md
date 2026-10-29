# GAP-P5a independent audit 1

Date: 2026-10-29. Auditor: maud-gp5a-1.

**Overall verdict: FAIL for literal graph-node completeness.**
`bpP:p5:kam-cond` is not fully stated by its assigned unsigned export
`KAM.Planetary.kam_cond_node`. The other five new public exports pass their node contracts;
the four skipped extension nodes have the required existing `PROVED` status. The Lean proofs
pass compilation, axiom inspection and kernel replay. This is a statement-completeness failure,
not a kernel-soundness failure.

## Scope and authority

Worktree: `/root/code/KAM-inp-gp5a`.
HEAD: `bf0e581ca1a871c90b5b922195ff6ef828d4a3ea`.
Comparison branch `inp`: `8dc8bedc37b2b4dad2163b79fbcf35ff51fdffdb`.
Read the audit brief at `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`,
AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the handoff including AUDIT FOCUS,
GAP-PLAN-P.md section GAP-P5a, the relevant P45 design table and signatures,
track P statement, frozen P-G statement and pertinent definitions, and every assigned NODE
record and cited blueprint passage. The user's explicit absolute report destination overrides
the generic brief's instruction to report in the main inp worktree.

The complete `git diff inp...HEAD` contains precisely these two new files:

- `KAM/Planetary/PGAssembly/ScaleNodes.lean`: 204 lines, maximum line length 98 characters.
- `KAM/Planetary/PGAssembly/ExtensionNodes.lean`: 65 lines, maximum line length 98 characters.

All six public additions are UNSIGNED under the explicit graph-gap ruling. None replaces a
SIGNED design declaration, provider or frozen theorem. Thus provider/frozen-type equality and
seal-body probes are not applicable to this package; no anchor is being certified seal-ready.
The existing frozen P-G anchor was read for standing hypotheses, not re-audited as a provider.

## Per-node and per-declaration verdicts

All short declaration names in this table are in `KAM.Planetary`.
Graph locators are in `docs/graph/P/DEPGRAPH.md`; blueprint locators are in
`blueprint-P/parts/p5-pg-assembly.tex`.

| Node / declaration | Lean declaration and location | Verdict | Reason |
|---|---|---|---|
| `stepP:p5:kc-eval` (graph 9570; blueprint 224) | `kc_eval`, ScaleNodes:117 | PASS | Actual P3 record expression `E*M^2*L/γ₁^2` equals `C₁^4/κ₀^2 ≤ 1`; exact cutoff `K₀`; P3-to-params radius/error attachment; displayed min, quotient and max identities. All derived internally from standing data and `0<r`, `0<mu≤1`. |
| `stepP:p5:kc-small` (9599; 225) | `kc_small`, ScaleNodes:143 | PASS | Exactly `ĉÊ<1`, `γ₂=mu*γ₁`, `γ₂≤γ₁`; no dependency-output premise. |
| `bpP:p5:kam-cond` (9536; 212–226) | `kam_cond_node`, ScaleNodes:156 | **FAIL** | Named export omits the required actual `x=C₁^4/κ₀^2` equality, P3 radius/error identification, and the constant-selection specification. See finding F1. |
| `stepP:p5:rk-dir` (9660; 233) | `rk_dir`, ScaleNodes:175 | PASS | All seven conjuncts: error bound, both links in the radius chain, min bound, half-rhoBar bound, relative-width bound, and power bound. Uses only standing data and source admissibility. |
| `bpP:p5:rK` (9629; 228–234), additional completion claimed by handoff | `rk_dir`, ScaleNodes:175 | PASS | Its final six conjuncts supply all the parent's literal displayed inequalities, completing the prior incomplete `r_k` reference. |
| `stepP:p5:be-an` (8375; 59) | `be_an`, ExtensionNodes:29 | PASS | Holomorphy of P0/Omega/beta jets in complex actions, joint continuity in `(mu,I)`, and complex matrix symmetry. Joint continuity is stronger than parameter-only continuity. |
| `stepP:p5:be-jet` (8403; 60) | `be_jet`, ExtensionNodes:50 | PASS | Every order `k≤4`, every multilinear input `v`, holomorphy on the half tube, and full multilinear-map vanishing on V and on the tube. This implies all source coordinate multi-index derivatives; it is stronger than just coordinate vanishing. |
| `stepP:p5:ext-loc` (8168; 33), skipped | existing `ext`, Extension.lean | PASS, status check | Graph explicitly `LEAN_STATUS: PROVED`, local to proved parent; LEAN_NOTE cites P5-CL audit. No new export required under the ruling. |
| `stepP:p5:ext-glue` (8195; 34), skipped | existing `ext`, Extension.lean | PASS, status check | Explicit `PROVED`; LEAN_NOTE cites P5-CG audit. |
| `stepP:p5:ext-per` (8222; 35), skipped | existing `ext`, Extension.lean | PASS, status check | Explicit `PROVED`; LEAN_NOTE cites P5-EX audit. |
| `stepP:p5:ext-H0` (8250; 36), skipped | existing `ext`, Extension.lean | PASS, status check | Explicit `PROVED`; LEAN_NOTE cites P5-EX audit. |
| private evaluation helper | `kcnode_L`, ScaleNodes:27 | PASS | Computes the defining maximum using positivity and `mu≤1`. |
| private evaluation helper | `kcnode_x`, ScaleNodes:37 | PASS | Positive-radius real-power identity and cancellation, no zero-denominator shortcut. |
| private evaluation helper | `kcnode_cutoff`, ScaleNodes:50 | PASS | Substitutes the exact x expression in cutoff. |
| private evaluation helper | `kcnode_rhoHat`, ScaleNodes:60 | PASS | Cancels positive mu in the two small-divisor radii; identifies the actual P3 min. |
| private evaluation helper | `kcnode_eHat`, ScaleNodes:78 | PASS | Substitution in `EL/rhoHat²` with positive mu. |
| private evaluation helper | `kcnode_Ehat_max`, ScaleNodes:85 | PASS | Positive min branches and squared real powers give the displayed maximum. |

Skipped-node verification used the NODE records themselves; an AMENDMENTS override was not
needed. These four rows certify the permitted skip, not a new independent source audit of ext.

## F1: incomplete unsigned export for bpP:p5:kam-cond

`DEPGRAPH.md:9543–9546` requires constants chosen before `(r,mu)` and the conclusion
“`L = C_1/mu, x = C_1^4/kappa_0^2, K = K_0 independent of (r,mu)`”, followed by the
actual Part 3 radius/error formulas and smallness. Blueprint lines 213–221 also include
items 1–3 specifying κ₀, κ₁ and G.

At `ScaleNodes.lean:158`, the second conjunct is merely
`(kam_c1 d)^4/(pgScales d).k0^2 ≤ 1`. It does not identify the actual P3 expression
`(pgKamScale d r mu).E * (pgKamScale d r mu).M^2 * (pgKamScale d r mu).L /
(pgKamScale d r mu).γ₁^2` with that quotient. At lines 160–166 the min and error
formulas concern `params`; the bridges `rhoHat (pgKamScale ...) = (params ...).rhoHat`
and `eHat (pgKamScale ...) = (params ...).Ehat` are absent. The proof at line 170
explicitly discards those components of `kc_eval`, including the actual x equality.

The omitted equality and bridges already occur in `kc_eval` (lines 119–128).
The ordered data-only selection is supported by existing `Scales.lean:kam_cond`,
`PGScaleSpec`, `pgScales_spec`, and the separate PROVED graph node
`bpP:p5:kam-cond#scales` (graph 10857). This establishes that repair is available;
it does not make `kam_cond_node` itself state the assigned literal conclusion.
In particular, merely citing `pgScales_spec` in the handoff does not expose the missing
κ₀/κ₁ inequalities and G bound in this unsigned export.

Constants are correctly functions of d alone, before r and mu; no wider constant dependence
was found. The smallness product form `ĉÊ<1` is equivalent to `Ê<1/ĉ` since `pgChat_pos`;
that presentation is not a defect. The failure is omission of literal clauses, not a demand
for syntactically identical notation. Even treating the separate scale-choice node as
sufficient for the choice clauses leaves the missing x equality as a decisive failure.

Required repair: extend this named export to retain the exact x equality and the P3
radius/error identifications, and include the scale specification before the universal
parameter conclusions (or obtain an explicit narrower node contract). Do not add these as
premises. No source files were changed by this audit.

## Definitions, hypotheses and carriers

There are **no new defs, abbrevs or structures** in either audited file. Proof-local `set`
values A and B in the max-identity proof are the two positive radius expressions, not new
public objects or fallbacks. No junk-valued definition is introduced or used to make a
conclusion vacuous.

Inspected the used existing definitions: `PGData` contains exactly the frozen P-G standing
inputs (Setting.lean:46); `PGScales`/`pgScales` choose data-only witnesses proved by
`kam_cond`; `params` gives explicit radius/error functions; `pgKamScale` is the actual
P3 ScaleData record with initialL; and `admissible` (Parameters.lean:71) is exactly the
positive r, r<R, positive mu, mu<mu0 and logarithmic upper bound. Its use by `rk_dir` does
not assume an output inequality. pgRstar is chosen from the proved threshold existence.

The scale exports hold for all positive r and `0<mu≤1`, stronger than the source's small-r
regime. Source quantifiers “mu≤1” in the kc-eval proof-step record are read in its enclosing
positive-r, positive-mu context, not as a new assertion at r=0 or mu=0.
For be_jet, mu precedes k and v; arbitrary v gives every coordinate derivative, while the
vanishing conclusion is equality of the whole continuous multilinear map. The domain is
`actionNbhd (closure V) (delta/2)`, exactly the half tube of the jets blueprint, on all its
complex points. The average and jet definitions are genuine normalized angular integration
and derivatives, and the remainder is that average minus its oscillator-action polynomial.
The diagonal factor 1/3 in jetBeta and off-diagonal derivatives agree with blueprint line 58.

No new public premise is a dependency's output. The design explicitly permits P5 helpers
to specialize to the full PGData standing context (P45-LEAN-DESIGN.md:439). No new theorem
assumes a holomorphic extension, vanishing jet, KAM bound or analytic witness as an input.
`be_an` uses proved JetsRegular outputs; `be_jet` obtains real/tube vanishing and
holomorphy inside its proof. The latter reaches the proved connected-tube/real-slice
identity argument in `remainder_jet_tube`.

## Independent validation

All commands below ran from this worktree. Lean/Lake work was serialized, with
`LEAN_NUM_THREADS=1` and `nice -n 5`, including the lint invocation whose ABI phase launches
Lean. No resource overrides, package-cache operations, clean or generated-file rewrites.

1. Full comparison: `git diff inp...HEAD` and `git diff --stat inp...HEAD`.
   Output: only the two scoped new files, 269 inserted lines.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   `git diff --check inp...HEAD`: empty, exit 0.
2. Targeted gate:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp5a KAM.Planetary.PGAssembly.ScaleNodes KAM.Planetary.PGAssembly.ExtensionNodes
   ```

   Exit 0. Output included `[inp-gate] slot 1 acquired 01:49:26` and
   `Build completed successfully (9231 jobs).` Replayed warnings were in existing dependencies
   CompactLipschitz, JetsPoly, Jets, Diophantine, Collar, OscillatorFinite and Hamiltonian
   Algebra/Chart; none was from either audited file.
3. Fresh scratch probe `.lake/abi-scratch/GAPP5aAudit.lean` imported the two modules and
   ran `#check @KAM.Planetary.<name>` and `#print axioms KAM.Planetary.<name>` for all six
   public theorems. Command:
   `env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP5aAudit.lean`.
   Exit 0. Exact axiom output:

   ```text
   'KAM.Planetary.kc_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kc_small' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kam_cond_node' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.rk_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.be_an' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.be_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. Kernel replay:
   `env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.ScaleNodes KAM.Planetary.PGAssembly.ExtensionNodes`.
   Exit 0. Exact output:

   ```text
   replaying KAM.Planetary.PGAssembly.ExtensionNodes
   replaying KAM.Planetary.PGAssembly.ScaleNodes
   ```

5. Lint: `env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`.
   Exit 1 solely for the permitted generated-root exception. Exact complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1198 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Hygiene verdict: PASS WITH NOTES under the explicit brief/handoff exception.
   KAM.lean was not regenerated.
6. Static source/import checks: no forbidden proof token or resource override in the two
   files; no EuclideanSpace; both have copyright, module, public imports, module docstring
   and public section; sizes and 100-character rule pass. Recursive KAM import traversal
   covered 185 modules and found **zero frozen theorem modules and zero provider modules**.
   Thus neither DRAFT_SORRY nor provider imports occur in the transitive closure. Frozen
   definition imports are allowed. Each new public short name has one declaration in KAM;
   all six remain in namespace KAM.Planetary, with no root shadow or reused public name.

## Source/blueprint issues, limits and deviations

No new suspected mathematical source erratum or frozen-statement defect was found in this
scope. F1 is a Lean export deviation from the literal blueprint/graph contract.

The graph still contains historical SOURCE_GAP notes at be-an (8401: parameter integration,
parameter continuity and mixed derivatives) and be-jet (8430: connected tube and identity
theorem). Lean suppliers are present: JetsRegular's average regularity and symmetry proofs,
and remainder_jet_tube's connected_complex_tube and real_slice_identity route. This audit
confirms their use without extra hypotheses; it does not edit or declare the source graph's
approved external-input bookkeeping closed. The skipped ext nodes likewise retain older
source-gap annotations alongside PROVED status. No graph status was changed.

Only this report was added. Scratch probe and audit logs were removed after recording results.
The existing untracked GAP-P5a-handoff.md was left intact. No git state-changing command ran.

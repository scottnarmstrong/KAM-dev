# C5-10 independent package audit 1

**Overall: PASS WITH NOTES.** The `canonical-map` implementation and all five principal theorem statements pass the mathematical and signature audit. The package has seven source-format violations in addition to the permitted generated-root discrepancy; lint is therefore not a clean pass. No frozen anchor is sealed by this infrastructure package.

Date: 2026-10-28. Scope: only `KAM/Canonical/CanonicalMap.lean`, including every new public declaration and all its private proofs. No theorem-closure claim for tracks I/N/P follows from this report.

## Authority, snapshot, and permission envelope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the supplied `C5-10-handoff.md`, `docs/tracks/N/statement.md`, the design's C5-10 row/proof plan/Appendix A, both design audits, and the relevant Part 4/5 blueprint statements and definitions. Applied the manuscript-audit and lean-statement-audit methods as a focused tier-2 audit. This is not a manifest-bound provider seal: there is no provider or frozen theorem in this diff, so provider/frozen equality and seal-body probes are N/A. Exact design-type probes replace those inapplicable checks.

The user's exact worktree-local report destination overrides the generic brief's main-worktree instruction. Authorized changes: this report and temporary probes/logs under this worktree's `.lake/abi-scratch/`, removed on closeout. No production edits, frozen edits, commits, network access, or delegated agents. All Lean invocations were serial within this audit, with `LEAN_NUM_THREADS=1` and `nice -n 5`; the build used the prescribed compile gate. Other campaigns' processes were not altered.

Frozen-v1 input revision: `HEAD = b95df0f0f56faf0f578dd324a818df8424770882`; comparison ref `inp = d030f8799fbc9a4c5e23582162b9bd844fa49574`. `git diff inp...HEAD` adds exactly one file, 343 lines. At entry the handoff was already untracked; it is not an audit-authored change.

The integration ref advanced during the audit. A closeout rerun observed `inp = f45c6617a5e134742856494cfee2a6f95ea2d1b6` and merge base `90cb224ec5c0651eb8ad9009c11dae256607bb02`; `git diff inp...HEAD` still contained exactly the same 343-line added module, with the protected-path diff empty and whitespace check clean. The audited HEAD and module hash remained unchanged.

| Input | SHA256 |
|---|---|
| `KAM/Canonical/CanonicalMap.lean` | `ad552edc72a0d85e9b8a60ccb62eb82aedee0a06da4213617cddd61a773888ab` |
| `docs/tracks/N/design/PART145-LEAN-DESIGN.md` | `635508031d6e95d9a5b3cf2fb19be41bfd2fd75cab9e5e8354c1513e738fd87e` |
| `docs/tracks/N/design/PART145-design-audit-1.md` | `7492d710f4ad5a7f7ae27975a20f4a2a8cba73bfd9bbd71d76a2646e772404a4` |
| `docs/tracks/N/design/PART145-design-audit-2.md` | `0ec8c1c2e58ba65217743cf3c491346b0042203449c7698ed2a899e86012c2df` |
| `blueprint-N/parts/p5-canonical-maps.tex` | `40560931653c109631d9edbebe453856a49dbb925002536cefc423aa15e01db0` |

All code locators below refer to frozen-v1. Acceptance criteria were exact signature/source correspondence, faithful definitions, no unproduced mathematical premise, sound use of existing dependencies, standard axiom closure, successful targeted build/kernel replay, and explicit disclosure of lint failures.

## Declaration ledger

All abbreviated names below have prefix `KAM.Canonical.`; all rows implement or support `bpN:p5:canonical-map` (blueprint Part 5, lines 215–232). PASS is mathematical/API acceptance; the overall formatting qualification applies to the file.

| Node / part | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| premises | `CanonData` (41) | PASS | Exactly the eight design fields; expanded analytic and weighted-bound fields contain only source premises. |
| domain | `CanonData.omega` (51) | PASS | Literal `Dom n D (r - ρ) (s - σ)`. |
| gauge | `CanonData.gauge` (54) | PASS | Literal `scaleCLE ρ σ hd.hρ hd.hσ`, with angle weight `σ⁻¹` and action weight `ρ⁻¹`. |
| gauge identity | `CanonData.norm_gauge` (157) | PASS | Existing `norm_scaleCLE`; no additional condition. |
| smallness sign | `CanonData.phi_div_nonneg` (160) | PASS | Nonnegative numerator and positive denominator. |
| restriction | `CanonData.omega_subset` (163) | PASS | Domain monotonicity with positive losses. |
| field | `CanonData.field_bound` (167) | PASS | `vf_bound` with its actual width hypotheses proved from `hd`. |
| components | `CanonData.field_comp_bound` (175) | PASS | Coordinate bounds converted to the finite-product sup norm; the minus sign in the action component disappears under norm. |
| flow premises | `CanonData.smallField` (186) | PASS | Openness, holomorphy, sign, smallness and bound are proved, not bundled as unproduced inputs. |
| half interior | `CanonData.gaugeInterior_half` (197) | PASS | Closed gauge ball of radius 1/2 fits the larger open domain using the original point's strict margin. |
| full interior | `CanonData.gaugeInterior_one` (205) | PASS | Same argument at radius 1. |
| (a) | `canonical_map_a` (218) | PASS | Exact design type; field, holomorphy, range, displacement and both component bounds at both time signs. |
| (b) | `canonical_map_b` (261) | PASS | Exact design type; integer angle translations and conditional reality on the source real locus. |
| (c) | `canonical_map_c` (302) | PASS | Exact design type; pointwise operator estimate in the correct gauge, for every `t ∈ [-1,1]` (stronger than the blueprint's time-one assertion). |
| (d) | `canonical_map_d` (313) | PASS | Exact design type; preserved symplectic form on the half-loss domain. Existing `canonical_*` results supply the blueprint's composition consequences. |
| (e) | `canonical_map_e` (323) | PASS | Exact design type; both inverse identities and the precise image inclusion. |

A Python extraction compared each entire `theorem canonical_map_a..e ... :=` prefix with Appendix A, design lines 1194–1241: all five printed `SIGNATURE_BYTES_MATCH`. Probes independently copied those design statements under fresh names and proved each by `exact canonical_map_<letter> hd`; all elaborated. Structure fields and the two definition bodies were also compared directly with design lines 1176–1191.

## Binder and definition audit

The following shared table applies separately to each of (a)–(e), and to the eight helpers insofar as they take `hd`. It opens the `CanonData`, `InClass`, and `WBound` bundles rather than counting `hd` as a single unexplained assumption. Output-side universal quantifiers are distinguished from theorem assumptions.

| Expanded input | Bin | Source / meaning |
|---|---|---|
| `{n : ℕ}` | TYPING | Part 4 domains permit zero dimension. |
| `{D : Set (Fin n → ℂ)}` | TYPING | Part 5 canonical-map explicitly permits arbitrary `D ⊆ ℂⁿ`. |
| `{r : ℝ}` | TYPING | Source radius parameter. |
| `{s : ℝ}` | TYPING | Source geometric strip width. |
| `{ρ : ℝ}` | TYPING | Source action loss. |
| `{σ : ℝ}` | TYPING | Source angle loss. |
| `{Φ : ℝ}` | TYPING | Numerical finite-norm upper bound, preceding the conclusions. |
| `{φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}` | TYPING | Total representative of the source holomorphic function, restricted in every assertion to its domain. |
| `hd.hρ : 0 < ρ` | SOURCE | Proposition premise `0 < ρ < r/2`. |
| `hd.hρr : ρ < r/2` | SOURCE | Same. |
| `hd.hσ : 0 < σ` | SOURCE | Proposition premise `0 < σ < s/2`. |
| `hd.hσs : σ < s/2` | SOURCE | Same. |
| `hd.φ_class.differentiableOn` | SOURCE | `φ ∈ O(r,s)`: complex differentiability on the open `Dom n D r s`. |
| `hd.φ_class.periodic` | SOURCE | `∀ j z ∈ Dom, φ(z.θ + Pi.single j 1,z.I) = φ z`; period one. |
| `hd.Φ_nonneg : 0 ≤ Φ` | SOURCE | Nonnegative norm bound, explicitly required by design D5/B3 even for `D=∅`. |
| `hd.φ_bound`: summability at every `I ∈ polyNbhd D r` | SOURCE | Finite weighted norm; `WSummable` is actual summability, not a bare total `tsum`. |
| `hd.φ_bound`: weighted sum at every such `I` is `≤ Φ` | SOURCE | The same norm bound, with weights `exp(2π s |k|₁)` and actual period-one Fourier coefficients. |
| `hd.eps_le : Φ/(ρ*σ) ≤ 1/2` | SOURCE | Precisely the proposition's smallness. |

For each principal theorem: SOURCE 10 expanded clauses; TYPING 8 parameter binders; STANDING 0; RULED 0; EXCESS 0. The universal indices internal to periodicity and WBound specify those source premises; they introduce no independent mathematical assumption. No instance binder or hidden theorem input occurs.

Remaining binders of the principal conclusions are exact source quantifiers: (a) `z`, domain membership, `t ∈ [-1,1]`; (b) integer `k`, `z` in the same domain, and, in the second conjunct, `RealOn (Dom n D r s) φ`, a real point `x`, and its domain membership; (c) `z` in the two-loss domain, `t ∈ [-1,1]`, and arbitrary vector `v`; (d) `z` in the half-loss domain and vectors `v,w`; (e) `z` in the two-loss domain. The reality condition is the blueprint's explicit “if φ is real on real points,” not an extra global reality requirement. `RealOn` unfolds to vanishing imaginary part at real inclusions in the specified domain.

The helpers introduce only the additional typing vector `x` in `norm_gauge`, and the source-domain point `z` and its membership in `field_comp_bound`. The other helpers take just the common data. Private `component_mvt` is an explicitly conditional auxiliary estimate; its solution and component-bound hypotheses are supplied from `flow_a` and `field_comp_bound` at its actual call sites.

Definition classification (all three are literal source objects, not characterization-defined choices):

| Check | `CanonData` | `.omega` | `.gauge` |
|---|---|---|---|
| BODY_MATCH | OK: literal source-premise record | OK: literal source domain | OK: literal diagonal equivalence |
| PUBLIC_CARRIER | OK | OK | OK: positive scaling from `hd` |
| WELL_DEFINEDNESS | N/A_LITERAL | N/A_LITERAL | N/A_LITERAL |
| CHARACTERIZATION | N/A_LITERAL | N/A_LITERAL | N/A_LITERAL |
| CHOICE_INDEPENDENCE | N/A | N/A | N/A |
| DEFINITION_VERDICT | PASS | PASS | PASS |

No new definition has a default branch or chooses a witness. Two scratch `rfl` examples verify the literal domain and gauge equations. Existing `flow` is totalized outside its solution locus; the package never uses that fallback: `smallField` and `gaugeInterior_half` produce the existence/uniqueness premises of `flow_a` on every asserted domain, for the full closed time interval. This is a check of actual use, not approval of off-domain semantics or a new audit of the upstream flow construction.

## Proof and refutation pass

Reviewed the complete 343-line implementation, separately challenging the following possible failure modes before accepting the statements:

* **Endpoint loss:** at `ε=1/2`, the non-strict displacement bound does not lose the needed open-domain membership. `dom_of_scaledNorm_le` (61–79) uses the starting point's strict membership and `polydisc_subset_Dom`, so adding a closed displacement radius still yields a strict inequality for the enlarged domain. Both inner radii are positive from `ρ<r/2`, `σ<s/2`. This verifies the endpoint in both gauge-interior lemmas and the final inclusion in (e), without convexity or nonemptiness of `D`.
* **Component constant:** `component_mvt` (137–151) applies the real Banach-space mean-value inequality to the projections of the genuine trajectory, using `γ(0)=z`. It retains `1/e` in the action bound; a scaled-norm-only proof would not supply that sharper component constant. Negative time is handled by `|t|`, then evaluated at `±1`.
* **Periodicity:** the subgroup proof generates every integer shift from the unit-coordinate periods, including negatives. All intervening shifts preserve the strip. `field_periodic` differentiates a neighborhood equality on an open domain, rather than incorrectly differentiating an equality at a single point. `flow_d` receives both full domain equality under the shift and field invariance.
* **Reality:** `hamiltonian_real` receives differentiability and real-valuedness on the original open domain, restricted to `omega`; `flow_e` receives the resulting real-locus preservation. Audit-2 R2-02 is respected: this is exactly the two-block carrier, with no claimed verbatim three-block specialization.
* **Derivative and symplecticity:** the two-loss points lie in `Ω¹`; `flow_c` supplies the derivative estimate. The vector inequality is equivalent to the conjugated operator bound because the gauge is a linear equivalence with the stated norm identity. For (d), `symplectic` receives the proved `SmallField` and half-interior premises, not an assumed canonical map.
* **Both inverses:** (e) extracts both identities from `flow_c` at a point in `Ω¹`. It separately proves the advertised smaller image domain from displacement, rather than confusing `Ω^{1/2}` with that geometric domain.
* **Composition consequences:** the blueprint says “Corollary ... canonical holds for Φ.” Although (d)'s signature exposes only form preservation, `Symplectic` is publicly imported and its `canonical_bracket`, `canonical_field`, and `canonical_orbit` remain applicable with `hd.smallField`, `hd.gaugeInterior_half`, the restricted holomorphy, and the range supplied by (a). Separate sorry-free consumer probes instantiate bracket invariance and field conjugacy at time one using those exact data; both elaborate. `canonical_orbit` has the same flow-side premises plus the source curve/domain hypotheses. No missing composition premise or new conditional bridge is being assumed.

These challenges were resolved against the source formulas and actual dependency types in a second audit pass. No mathematical finding survived. This audit was performed by one independent auditor, without claiming a second reviewer. The imported FlowInverse/Symplectic/VectorField proofs were not re-audited as separate packages.

## Hygiene and verification receipts

All commands ran in `/root/code/KAM-inp-c510`. No default-heartbeat failure or resource override occurred.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-c510 KAM.Canonical.CanonicalMap
   ```

   Exit 0. Output: `[inp-gate] slot 2 acquired 05:55:09 for KAM.Canonical.CanonicalMap` and `Build completed successfully (3199 jobs).` The script itself executes `nice -n 5 lake build`; no library-clean/rebuild or cache operation was requested.

2. Exact design-type/definition and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/C510Audit1.lean
   ```

   Exit 0. All five copied-design declarations and both literal-definition examples elaborated. For **each** of the eight `CanonData` helper theorems and five `canonical_map_a..e`, the exact axiom suffix was:

   ```text
   depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   No `sorryAx` or project axiom. The 13 exports are individually listed in the declaration ledger.

3. Actual composition-consumer probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/C510CompositionAudit1.lean
   ```

   Exit 0, no diagnostics. Proves bracket invariance and field conjugacy for this precise flow/domain at `t=1`, supplying all flow-side premises from this package.

4. Kernel replay (one invocation):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Canonical.CanonicalMap
   ```

   Exit 0. Complete output: `replaying KAM.Canonical.CanonicalMap`.

5. Full source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   **Exit 1**, with complete output:

   ```text
   Lean lines over 100 characters:
   /root/code/KAM-inp-c510/KAM/Canonical/CanonicalMap.lean:41:106
   /root/code/KAM-inp-c510/KAM/Canonical/CanonicalMap.lean:217:106
   /root/code/KAM-inp-c510/KAM/Canonical/CanonicalMap.lean:227:101
   /root/code/KAM-inp-c510/KAM/Canonical/CanonicalMap.lean:312:104
   /root/code/KAM-inp-c510/KAM/Canonical/CanonicalMap.lean:326:114
   /root/code/KAM-inp-c510/KAM/Canonical/CanonicalMap.lean:327:114
   /root/code/KAM-inp-c510/KAM/Canonical/CanonicalMap.lean:328:103
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (416 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   This independently confirms the frozen bytes and elaborated ABI checks passed. The seven long lines are an additional lint failure beyond the root exception expressly allowed by the audit brief.

Mechanical checks: 343 lines, correct copyright/module/public-import/docstring/public-section form, exposed definitions through `@[expose] public noncomputable section`; zero forbidden proof escapes, budget overrides, or `EuclideanSpace` occurrences. Recursive project-import inspection found 48 project modules, no provider, no frozen theorem, and seven frozen definition modules, each `SEALED` in the manifest: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsPrimaryOnStrip, IsRealOnReals, OmegaZero.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output. `git diff --check inp...HEAD` exited 0.

## Findings, errata, and limits

**F1 — LOW, source formatting:** `CanonicalMap.lean` lines 41, 217, 227, 312, 326, 327, 328 have respectively 106, 106, 101, 104, 114, 114, 103 characters. The lint script treats these as failures, not advisory notes. The handoff's “only notes” wording understates their mechanical status. Their origin in verbatim design text explains them but is not a lint exception. Refutation check: the exact line lengths were recomputed, and `lint_sources.sh` explicitly sets `status=1` for this condition. Suggested repair, outside this read-only audit: wrap these lines without changing declaration tokens/types. No mathematical repair is required.

**Generated-root note:** `KAM.lean` omits the new public module and is expected to be regenerated by the orchestrator. The brief explicitly permits this discrepancy during package review. Neither generated file was edited here.

No new suspected pinned-paper or blueprint defect was found. Inherited design §7 errata remain outside this package: Part 5's “symmetrically `T_- > -1`” should read `T_- < -1`, and Part 4's attribution of the sharp norm to current P averaging is stale. These are previously recorded prose issues, not newly verified pinned-PDF findings. No new mathematical deviation was introduced. This audit uses the local blueprint as requested; it does not independently re-certify the Pos93 PDF transcription, optional sharp norm, downstream normal-form iteration, three-block reality transport, or any I/N/P root theorem.

Closeout: all 16 public declarations classified; all 13 public theorem axiom closures checked; exact design-type and literal-definition probes passed; two actual composition-consumer probes passed; targeted build and kernel replay passed; full lint completed with the disclosed formatting/root failures and successful anchor/ABI guards. No mathematical blocker or unclassified declaration remains. PASS WITH NOTES does not waive the outstanding formatting repair or represent a clean landing gate.

The two probe sources and two captured logs were removed after their receipts were copied here. The audited module hash remains frozen-v1, report trailing-whitespace validation passes, and `git diff --check` passes. Final status contains only this audit-authored report and the pre-existing untracked handoff. No state-changing git command was used.

## Orchestrator addendum (lint-only fix, 2026-10-28)
Commit 42b7e3a wraps the seven over-long lines (41, 217, 227, 312, 326–328). Verified by the orchestrator (no separate Codex delta round, per the quota policy for lint-only fixes): the change is whitespace-only (whitespace-stripped file contents identical before/after); `scripts/lint_sources.sh` now reports only the permitted stale-root message (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK); no line exceeds 100 characters; kernel replay `lake env leanchecker KAM.Canonical.CanonicalMap` exits 0. The audit's mathematical verdict stands: **PASS WITH NOTES**.

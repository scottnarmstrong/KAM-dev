# P-CLOSE-LEAN independent audit 1

Overall verdict: **FAIL for closing all five literal graph contracts.** The two new Lean theorems compile and pass kernel replay and axiom checks. This is a statement-completeness failure, not a refutation of their Lean propositions or any sealed theorem.

Audited HEAD `b4b56e6055d6f1886d248b008befa6ba4953337d`, against `inp` `be4b40d5c5dd5b0ab472f8cc508e2600eee53ce4`. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package brief, handoff AUDIT FOCUS, the five DEPGRAPH records, their blueprint text and relevant definitions, and docs/tracks/P/statement.md. The last is historical draft material; the graph and approved frozen definitions control the present comparison. Production audit scope is exactly the two requested Lean diffs. The full `git diff inp...HEAD` adds only those two theorems and the handoff document. No frozen anchor or provider is added or changed, so provider/frozen type equality and seal-body probes are inapplicable; no fresh per-anchor seal verdict is claimed.

The report destination follows the user's explicit worktree path, overriding the generic brief's main-worktree destination. The previous graph audit/handoff are absent from this checkout; their copies in `/root/code/KAM-inp/docs/tracks/P/audits/` were read only for the quoted ruling and to locate the inherited rho mistake. They do not override the local graph or blueprint.

## Node verdicts

All names below are in `KAM.Planetary`. Conclusions were compared for mathematical content and quantifier dependency, allowing regrouping/reordering independent conjunctions. There are no existential constants with widened dependence.

| Node | Declaration | Verdict | Literal comparison |
|---|---|---|---|
| `bpP:p14:geometry` | `geometry_radial`, `KAM/Planetary/AMD/Geometry.lean:176–199` | **not PROVED** | The newly missing radial bounds are now explicit, with the existing axis, eccentricity, momentum, ordered-radius and collision clauses. However, DEPGRAPH:33824 and blueprint p14a:80–83 also require the pair-distance triangle chain and that K1 is a compact subset of W. The type has membership `z ∈ amdCompact B`, but no `IsCompact (amdCompact B)` or `amdCompact B ⊆ collisionFreeDomain n`. Those are a separate existing declaration `amd_compact` (:202–203). Thus one new declaration still does not state the complete literal parent conclusion. |
| `stepP:p14:geo-b` | `geometry_radial` first conjunct, :178–183 | **PROVED** | For every i it explicitly states both exact a(1±e) radial inequalities and d/R bounds. The standing enclosing data are admissible B and z in R_out; item (a) is proved in the same theorem rather than assumed. No new analytic or conclusion-shaped premise is introduced. This certifies the step directly from the enclosing source data; it does not certify the incomplete whole parent by ruling (b). |
| `bpP:p14:sb-cov` | `sb_cov_full`, `KAM/Planetary/SecularBox/Covariance.lean:125–144` | **PROVED** | Gamma, k=secularRoot, a=secularAxis, v covariance, x-shift, J-shift, q and p covariance all occur in this one type. Quantifiers m,w,theta then i,F have the required dependency. No ellipticity or mass-positivity premises are needed for these algebraic identities, so the whole-carrier statement is stronger. The additional Gamma/Lambda equality is harmless for this parent, whose SOURCE_CONCLUSION does not mention rho. |
| `stepP:p14:sb-cv-1` | `sb_cov_full` first conjunct, :126–131 | **not PROVED** | Gamma, k, a and v are explicit, but the third equality is Gamma/Lambda invariance. The source rho is `sqrt ((1 - Gamma/(2*Lambda))/Lambda)`, not Gamma/Lambda. Its invariance is not a literal conjunct. Ruling (b) under the now-proved covariance parent cannot supply a missing rho conjunct; it would require additional rewriting rather than a projection. |
| `stepP:p14:sb-cv-2` | `sb_cov_full` second conjunct, :132–134 | **PROVED** | Both x=v dot c and J shift equalities are literal conjuncts for every i,F. Pure projections from the proved parent establish the step; a fresh Lean probe confirmed this. |

## Exact unpaid clauses

1. **Geometry parent:** bundle compactness and containment of K1 in W into the same full geometry theorem, and explicitly retain the required pair-distance chain
   `d ≤ |q_i-q_j|`, `|q_i-q_j| ≤ |q_i|+|q_j|`, and `|q_i|+|q_j| ≤ 2R` for i≠j. Membership in the definition `amdCompact` supplies the lower bound by unfolding. `PairBounds` on barycentric positions supplies related distance bounds after algebra, but neither is the literal displayed triangle chain. The missing compactness/containment is independently decisive even if such definitional packaging is accepted. Existing `amd_compact` proves the compactness assertion; this is packaging work, not a new mathematical obstacle. The source region inclusion follows by universally quantifying the pointwise result. No independent quantifier dependence is lost by regrouping the per-index clauses.
2. **Slow-data step:** export, for every i, the actual equality
   ```lean
   Real.sqrt ((1 - secularGamma (secularRotation theta w) i /
       (2 * fast (secularRotation theta w).2 i)) /
       fast (secularRotation theta w).2 i) =
     Real.sqrt ((1 - secularGamma w i / (2 * fast w.2 i)) / fast w.2 i)
   ```
   as part of the slow-data conjunction. Fast-action and Gamma invariance already prove it by rewriting. Derivability does not meet this audit's literal-conjunct requirement. The existing Gamma/Lambda identity is true, but names a different quantity.

## Definition and hypothesis classification

There are **no new def/abbrev/structure declarations**, instances or bundled assumptions. The only additions are `geometry_radial` and `sb_cov_full` with their documentation.

Relevant unchanged objects inspected: `amdOuter` is the frozen LowAMDRegion wrapper; `amdCompact` is exactly K1's non-strict radial/momentum/pair-distance set. `secularRotation` rotates the explicit slow pair and preserves both fast blocks through `assemble`; it has no fallback or selected solution. `secularGamma`, `secularRoot`, `secularAxis`, `secularEccVector`, `longitudeJacobian`, `ellipsePosition` and `ellipseMomentum` are the literal chart formulas. Scalar x is written as the intended dot product. Physical lengths use `planeLength`, not the ambient Pi norm. The covariance identities remain algebraic on the whole carrier, including totalized division/sqrt: they preserve their scalar inputs and do not infer elliptic geometry at junk points. There is no new totalization or reliance on a junk branch.

Both new theorems have only source/typing hypotheses. `geometry_radial` projects existing genuine proofs (`geometry` and `elements`); `sb_cov_full` uses `sb_cov` and internal algebraic invariance results. No hard step is assumed. A source-import traversal of both modules found 65 KAM modules, zero provider imports and zero frozen theorem imports, hence no imported DRAFT_SORRY theorem in this closure.

## Independent checks

Commands ran in this worktree. Every Lean/Lake invocation used `LEAN_NUM_THREADS=1` and `nice -n 5`, serially; lint was started only after kernel replay exited because its ABI stage invokes Lean. No cache, update, clean, generated-root regeneration or state-changing git command was used.

1. Targeted compile gate:
   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-pcloselean KAM.Planetary.AMD.Geometry KAM.Planetary.SecularBox.Covariance
   ```
   Exit **0**. Output included:
   ```text
   [inp-gate] slot 1 acquired 16:20:32 for KAM.Planetary.AMD.Geometry KAM.Planetary.SecularBox.Covariance
   ⚠ [9098/9111] Replayed KAM.Kepler.Energy
   Build completed successfully (9111 jobs).
   ```
   Two inherited warnings at KAM/Kepler/Energy.lean:106:35 and :106:48 report implicitly used bindings hm and hκ. Neither audited file emitted a warning.

2. Scratch probe:
   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/PcloseAudit.lean
   ```
   Exit **0**. It imported both modules, checked both complete types, projected the geo-b conjunction and proved the cv-2 x/J conjunction using only projections. Exact axiom output:
   ```text
   'KAM.Planetary.geometry_radial' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sb_cov_full' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```
   These are all new public theorems in scope.

3. Kernel replay, one invocation:
   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.AMD.Geometry KAM.Planetary.SecularBox.Covariance
   ```
   Exit **0**. Complete replay output:
   ```text
   replaying KAM.Planetary.SecularBox.Covariance
   replaying KAM.Planetary.AMD.Geometry
   ```

4. Lint:
   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```
   Exit **0**. Complete output:
   ```text
   check_lean_modules: PASS (1339 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```
   No stale-root exception or other lint exception was needed.

5. Diff and source hygiene:
   ```sh
   git diff inp...HEAD
   git diff inp -- KAM/Planetary/AMD/Geometry.lean KAM/Planetary/SecularBox/Covariance.lean
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD
   ```
   Protected-path diff was empty, exit 0; diff whitespace check exited 0. Python removal of precisely each added documentation/theorem block reconstructed `git show inp:<file>` byte for byte for both files: all prior statements and bodies are unchanged. Geometry has 259 lines, maximum 100 Unicode characters; Covariance has 148 lines, maximum 99. Both retain copyright, module, public imports, module docstring and public noncomputable section. No forbidden sorry/admit/axiom/unsafe/opaque/native_decide/EuclideanSpace token or resource override occurs in either file. A declaration scan across KAM and Mathlib found exactly one declaration with short name geometry_radial and exactly one with short name sb_cov_full, both at the audited locations. No reused public short name was found.

## Source, blueprint and handoff defects

- **Incorrect rho identification in new documentation and inherited audit instructions.** Covariance.lean:123 says “ρ = Γ/Λ”; the package handoff repeats “rho = Gamma/Lambda” at lines 12 and 19. The previous graph audit in the main worktree likewise says “rho=Gamma/Lambda” in its slow-data row and remaining-work recommendation. In contrast, `blueprint-P/parts/p14b-secular-box.tex:27` explicitly defines “rho_i=sqrt((1-Gamma_i/(2 Lambda_i))/Lambda_i)”, and :170 requires that rho invariant. The frozen `SecularEccVector.lean` body agrees with the blueprint. This is a package/documentation deviation, not an error in the pinned external source, blueprint formula or frozen definition. The audit does not silently adopt the incorrect identification.
- **Geometry closure overstatement.** The handoff describes the added radial conjunction plus the old geometry conjunction as closing the whole parent. Under the explicit ONE-declaration test, compactness and K1 containment at blueprint p14a:83 remain separately exported, and the displayed triangle chain at :80 is not literal in the new type. The earlier audit's radial-only repair recommendation was sufficient to add the radial clause, but was not an exhaustive check of that stricter parent contract.
- No suspected defect in an external pinned publication was found within this two-diff audit. No mathematical falsity of either new Lean proposition was found. No proof, frozen file, manifest or graph status was edited by this audit.

The remaining uncertainty is whether an explicit future ruling will permit composing the separately exported geometry/compactness results and derived pair-distance chain for parent graph closure. The current brief requires one literal declaration; this report applies that rule. No such ruling can identify Gamma/Lambda with the source rho.

All three audit-created scratch files (probe, kernel log and lint log) were deleted after recording their results. Final repository status contains only this untracked audit report.

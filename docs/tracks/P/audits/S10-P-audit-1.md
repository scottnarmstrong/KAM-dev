# Independent S10-P package audit 1

Overall verdict: **PASS WITH NOTES** for S10-P infrastructure. The three blueprint exports pass statement and proof review. The only source-hygiene exception is the generated `KAM.lean` being stale; see the completed check receipts below. **No frozen anchor is sealed or claimed seal-ready by this package.** The P810 design explicitly assigns no provider or frozen theorem closure to Parts 8–10.

Audited worktree: `/root/code/KAM-inp-s10p`; HEAD `78f0769a91f47474fa68da9a81224483e500feb8`; comparison ref `inp` was `31f0bfbf70c07b1eefd006237f331c00e003a0e5`. `git diff inp...HEAD` warns of multiple merge bases and selects `f4d1a3178d2fd696e15dc0e0c9dd383f03b5e80c`. It lists the new 524-line `KAM/Planetary/Nondegeneracy/Peel.lean` and 125 inherited lines in `SecularForm/Coefficients.lean`. As the handoff's AUDIT FOCUS requires, this audit covers **only Peel.lean**; the coefficient delta is not independently re-audited here.

Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, S10-P-handoff.md, P810-LEAN-DESIGN.md (including S10-P ownership, source locators, dependency table and signature appendix), design audits 1–2 under `docs/tracks/P/design/`, the original `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`, Track P statement.md, relevant Part 8–10 blueprint conventions and Part 10 lines 57–89, and the actual imported coefficient, Laplace-series, norm, data and frozen-definition interfaces. The user explicitly overrides the generic brief's main-worktree report destination: this report is in the package worktree at the requested absolute path.

## Statement and proof findings

The **complete** types of `laplace_bounds`, `formula69`, and `peel`, and the **complete bodies** of `outerData` and `peelError`, match the original design signatures after whitespace normalization. Fresh scratch examples use the copied design theorem statements and apply the actual exports with exactly their explicit arguments. Scratch `rfl` checks exercise both definition bodies, and an additional example checks that the literal one-planet `coeffs` matrix is zero. There is no provider/frozen ABI or seal-body probe to perform: no provider or frozen theorem is delivered by S10-P.

All names in the following table are relative to `KAM.Planetary.Nondegeneracy`; line numbers refer to Peel.lean. PASS for an auxiliary lemma means that its actual hypotheses and conclusion implement the indicated source proof obligation or a valid general algebraic strengthening, not that the blueprint separately names that helper.

| Node / role | Lean declaration (line) | Verdict | Reason |
|---|---|---|---|
| `stepP:p10:lb-ratio` | `laplaceTerm_succ_le` (34) | PASS | Consecutive-term identity and ratio bound for every k ≥ 1 and α ≥ 0; does not divide by a possibly zero term. |
| `stepP:p10:lb-tail` | `laplaceTerm_le_geom` (55) | PASS | Induction gives geometric domination, including α = 0. |
| `stepP:p10:lb-series`, `lb-tail` | `laplace_bounds_aux` (67) | PASS | Actual integral coefficient is the sum; nonnegative first term and geometric majorant yield the bounds. Stronger k ≥ 1 statement is valid. |
| `bpP:p10:laplace-bounds` | `laplace_bounds` (85) | PASS | Exact design/source constants 3/2, 15/8 and factor 1 + 4α² on the closed interval [0,1/2]. |
| `bpP:p10:formula69` | `formula69` (99) | PASS | Exact two remainder witnesses, both in [0,4α²], for the literal halved pair coefficients. |
| `bpP:p10:peel`, outer system | `outerData` (128) | PASS | Same G and central mass; restricts planetary masses with Fin.succ; only positivity/positive dimension fields. |
| `bpP:p10:peel`, error matrix | `peelError` (130) | PASS | Literal full coefficient matrix minus the zero-padded outer coefficient matrix. |
| Formula 69 consequence | `pairA_bounds` (134) | PASS | Nonnegative pairA with exact 3/4 G mᵢmⱼ aᵢ²/aⱼ³ bound; same physical and ratio premises. |
| Formula 69 consequence | `pairB_bounds` (156) | PASS | Nonnegative pairB with exact 15/16 G mᵢmⱼ aᵢ³/aⱼ⁴ bound. |
| `stepP:p10:peel-bd`, action algebra | `sqrt_action` (179) | PASS | Square root of action has the required mass square root and quarter powers under positive axis. |
| Action positivity | `action_pos` (189) | PASS | Derived from Data positivity and aᵢ > 0; no assumed spectral fact. |
| `stepP:p10:peel-ent` | `action_outer` (193) | PASS | Definitional reindexing; no domain premise needed. |
| `stepP:p10:peel-ent` | `pairA_outer` (196) | PASS | Fin.succ preserves min/max in the literal pair coefficient. |
| `stepP:p10:peel-ent` | `pairB_outer` (201) | PASS | Same exact reindexing for pairB. |
| Symmetry algebra | `pairA_comm` (206) | PASS | Valid on the whole carrier by min/max symmetry. |
| Diagonal normalization | `sqrt_action_mul_self` (209) | PASS | Positivity justifies replacing the squared square root by action. |
| `stepP:p10:peel-ent` | `coeffs_zero_zero` (213) | PASS | First diagonal is minus the sum over outer planets divided by the first action. |
| `stepP:p10:peel-ent` | `coeffs_zero_succ` (221) | PASS | Exact first-row off-diagonal coefficient formula. |
| `stepP:p10:peel-ent` | `coeffs_succ_zero` (226) | PASS | Uses proved Hermitian symmetry of the literal coefficient matrix. |
| `stepP:p10:peel-ent` | `coeffs_succ_succ_ne` (230) | PASS | Outer off-diagonal entries agree exactly; only unequal indices required. |
| `stepP:p10:peel-ent` | `coeffs_succ_succ_diag` (235) | PASS | Outer diagonal changes by exactly −pairA₀ⱼ/actionⱼ. |
| Positive real-power algebra | `quart_pow` (258) | PASS | Positive fourth root cancellation, no totalization shortcut. |
| Positive real-power algebra | `quart_exists` (261) | PASS | Constructs the positive fourth root of a positive input. |
| `stepP:p10:peel-bd`, coupling algebra | `cross_alg` (265) | PASS | Exact coefficient 15G√(m₁mⱼ)/(16√κ), t^(11/4), a^(−17/4); scalar positivity premises only. |
| Positive square-root algebra | `sq_exists` (288) | PASS | Constructs a positive square root. |
| Positive square-root algebra | `sqrt_mul_sq` (291) | PASS | √(κu²) = √κu with positive factors. |
| `stepP:p10:peel-bd`, first diagonal | `diag_alg` (294) | PASS | Exact t^(3/2) a^(−3) cancellation of the inner mass/action. |
| `stepP:p10:peel-bd`, outer diagonal | `diag_alg2` (304) | PASS | Exact t² a^(−7/2) cancellation of the outer mass/action. |
| `stepP:p10:peel-bd`, finite sum bound | `frobenius_le_sum_abs` (314) | PASS | Explicit Frobenius norm bounded by sum of entry absolute values, all finite dimensions. |
| `stepP:p10:peel-bd`, operator norm | `op2_le_frobenius` (325) | PASS | Uses the intended Euclidean length bound from S9-N, not the ambient max norm. |
| Axes-domain construction | `cons_mem` (333) | PASS | Positivity, ordering and t ≤ a′ᵢ/2 imply Fin.cons t a′ lies in the full axes cone. |
| Formula 69 specialization | `pairA_peel` (355) | PASS | Derives the ratio hypothesis from the fixed outer axes and t bound. |
| Formula 69 specialization | `pairB_peel` (363) | PASS | Same derivation for the coupling coefficient. |
| `stepP:p10:peel-bd` | `peel_E00` (371) | PASS | Exact first-diagonal bound, including the sum of outer masses times a′⁻³. |
| `stepP:p10:peel-bd` | `peel_Ejj` (398) | PASS | Exact outer-diagonal t² bound. |
| `stepP:p10:peel-bd` | `peel_E0j` (419) | PASS | Exact first-row t^(11/4) bound and a′^(−17/4) dependence. |
| `stepP:p10:peel-ent` | `peel_off` (440) | PASS | Error vanishes at unequal outer indices by actual coefficient equality. |
| `bpP:p10:peel`, `stepP:p10:peel-bd` | `peel` (449) | PASS | Full design conclusion, C chosen before t, with all entry bounds and both norms retained. |

The source's n ≥ 2 is encoded as Data (n+1) with 0 < n, so n=1 here is the two-planet full system. In that case the outer one-planet matrix has an empty pair sum and is exactly zero. The condition `∀ i, t ≤ a′ i/2` is equivalent on the ordered positive outer axes to the source's bound by the first outer axis; it adds no substantive premise. Positivity and ordering also establish all required ratios are in (0,1/2].

For `peel`, the witness is `C = 1 + c00 + 2 * ∑ j, c0j j + ∑ j, cjj j` (lines 462–479), with the three coefficients depending only on D and the fixed a′. Positivity is proved from Data and the axes cone. The proof counts both first-row and first-column terms using symmetry, and uses t ≤ 1 to absorb t² and t^(11/4) into t^(3/2). It neither assumes the error estimate nor introduces a t-dependent constant. The Euclidean operator norm and Frobenius norm are the actual S9-N definitions on matrices over `Fin n → ℝ`; the ambient Pi norm is not substituted.

## Definition classification and hypotheses

There are exactly **two new definitions**, no abbreviations or structures:

- `outerData`: source data restriction, defined on every input of its declared carrier. It preserves G and the central mass and restricts only the planetary mass vector. Its proof fields are standing positivity/typing data, not conclusions.
- `peelError`: literal matrix difference on every axis vector, including vectors outside the physical cone. Its zero first row/column in the padded matrix is the intended block embedding, not a fallback branch. The physical estimates explicitly restrict to positive ordered axes; they do not exploit zero denominators or an undefined integral outside its valid domain.

Both definitions are under `@[expose] public noncomputable section`. The lemmas use only source/standing positivity, ordering, dimension, index separation and elementary scalar data. No bundled spectral, analytic, coefficient, error-bound or downstream conclusion is assumed. S8-C supplies actual coefficient identities and proved symmetry, S8-L supplies the actual Laplace integral/series identity, and S9-N supplies the stated Euclidean norms.

The recursive local import check reaches 70 KAM modules, including **47 frozen definitions, all manifest state SEALED**, no frozen theorem module and no provider. Thus there is no DRAFT_SORRY theorem dependency or quarantine breach. This import inspection and the transitive axiom checks do not extend the audit scope to re-proving all upstream packages.

## Independent validation receipts

1. **Targeted compile gate**, exit **0**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s10p KAM.Planetary.Nondegeneracy.Peel
   ```

   Exact gate/final output:

   ```text
   [inp-gate] slot 2 acquired 12:41:09 for KAM.Planetary.Nondegeneracy.Peel
   Build completed successfully (9116 jobs).
   ```

   No Peel.lean diagnostics. Replayed upstream warnings concern unused variables in Kepler/Energy.lean (106), Poincare/Chart.lean (212,247), Kepler/Mass.lean (147,157,500,524), and deprecated `ite_cond_eq_false` in SecularForm/Coefficients.lean (54,112). These files were not changed by the auditor. The command uses the overlay and targeted build; no clean/update/cache operation or resource override was used.

2. **Copied-design application, definition and one-planet probes; every new public theorem's axioms**, exit **0**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10PAudit.lean > .lake/abi-scratch/S10P-probe.log 2>&1
   ```

   The probe imports only `KAM.Planetary.Nondegeneracy.Peel`, opens the actual namespaces, elaborates all three complete copied theorem types by applying the production exports, checks the two definition bodies by `rfl`, and proves `coeffs D a = 0` for arbitrary `D : Data 1` and `a : Vec 1` by the empty-pair-sum formula. An initial scratch-only attempt lacked `open KAM.Planetary.Nondegeneracy`; correcting that probe namespace resolved its unknown-identifier error without changing production code or theorem types.

   The probe issues `#print axioms KAM.Planetary.Nondegeneracy.<name>` for **all 36** new public theorems. Complete successful output:

```text
'KAM.Planetary.Nondegeneracy.laplaceTerm_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.laplaceTerm_le_geom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.laplace_bounds_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.laplace_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.formula69' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.pairA_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.pairB_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sqrt_action' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.action_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.action_outer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.pairA_outer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.pairB_outer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.pairA_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sqrt_action_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.coeffs_zero_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.coeffs_zero_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.coeffs_succ_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.coeffs_succ_succ_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.coeffs_succ_succ_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.quart_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.quart_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.cross_alg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sq_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sqrt_mul_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.diag_alg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.diag_alg2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.frobenius_le_sum_abs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.op2_le_frobenius' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.cons_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.pairA_peel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.pairB_peel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.peel_E00' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.peel_Ejj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.peel_E0j' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.peel_off' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.peel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. **Kernel replay**, one invocation, exit **0**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Nondegeneracy.Peel > .lake/abi-scratch/S10P-leanchecker.log 2>&1
   ```

   Complete output:

   ```text
   replaying KAM.Planetary.Nondegeneracy.Peel
   ```

   All new lemmas reside in this one audited module; there is no separate provider module to replay.

4. **Repository lint, corrected serialized run**, exit **1**, solely the explicitly permitted stale generated root:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > .lake/abi-scratch/S10P-lint-final.log 2>&1
   ```

   Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (632 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   This is a literal nonzero lint exit, accepted only under the brief's named exception. The generated root was not regenerated. No other lint failure appeared.

5. **Static scope/hygiene**, all pass:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD -- KAM/Planetary/Nondegeneracy/Peel.lean
   rg -n 'sorry|admit|\baxiom\b|\bunsafe\b|\bopaque\b|set_option|EuclideanSpace' KAM/Planetary/Nondegeneracy/Peel.lean
   wc -l KAM/Planetary/Nondegeneracy/Peel.lean
   ```

   Protected-path diff and whitespace check exit 0 with no diff/whitespace output; Git emits the multiple-merge-base warning stated above. Forbidden-token search has no matches (rg exit 1). File count: `524 KAM/Planetary/Nondegeneracy/Peel.lean`; maximum line length, independently counted as Unicode characters: **100**. Copyright, `module`, public imports, module docstring, public section and exposed definition scope are present. No `set_option` occurs at all. SHA-256 of the audited file: `bdc105071e0625f27eaaf363ed0f384669da400c685ccedf462c1fe59fc9ff3c`.


## Scope, uncertainties, errata and deviations

No material statement mismatch, additional premise, weakened conclusion, junk-value reliance, conclusion-shaped hypothesis or blueprint contradiction was found in Peel.lean. No new suspected pinned-source erratum or implementation deviation was identified. The quoted Fej04r asymptotic exponents in Part 10 line 84 are already explicitly distinguished by the blueprint from the present normalization: its actual current bounds use outer-diagonal exponent 2 and coupling exponent 11/4, exactly as implemented. This audit validates the supplied blueprint/design and Lean package; it does not independently re-transcribe Fej04r's PDF or certify later good-axis/nondegeneracy consumers.

No frozen theorem/provider exists in this package, so the per-anchor verdict is **not applicable**; the per-node/declaration verdicts above are package proof verdicts. Later frozen physical headlines and the remaining P810 packages remain separate work. Execution deviation: the initial lint invocation omitted the explicit thread environment and nice wrapper. Its ABI stage was not used as the final receipt; lint was repeated with `LEAN_NUM_THREADS=1` and `nice -n 5`, after the other Lean checks completed. The lint script was paused during the targeted build before its ABI Lean stage and resumed only after that build exited. The ABI Lean stage and the auditor-controlled build/probe/replay jobs were serialized.

No production file was changed by this audit. The only repository artifact written is this report; temporary probes are confined to `.lake/abi-scratch/` and removed after validation. The pre-existing untracked S10-P-handoff.md is left untouched.

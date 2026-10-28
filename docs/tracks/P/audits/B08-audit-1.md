# B08 independent package audit 1

Overall verdict: **FAIL — literal graph-cut completeness**. The final `finite_divisor` theorem matches the pinned signature exactly and its proof follows the intended finite-stage argument. Two named intermediate exports stop short of their literal graph conclusions (F1–F2). This verdict does not assert that the final divisor inequality is false.

Date: 2026-10-28. Audited HEAD: `b3f65914fb00cb86e3c1297fbb81a12b1297b3e8`; comparison `inp`: `d9183adae208ecf2e726620694b69c8168e33006`.

## Scope and authority

Only `KAM/Planetary/WeakKAM/FiniteDivisor.lean` is audited. `git diff inp...HEAD` also contains the inherited Cutoff* and Extension* packages and B05 reports; these are outside this audit, not silently certified here. The pre-existing untracked B08 handoff was left intact. No frozen anchor or provider is assigned to B08: frozen/provider type equality and sealing are therefore inapplicable. The result is infrastructure, not closure of P-G, P-PLANAR or P-FIXED.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief, B08 handoff and its AUDIT FOCUS, P11B design (B08 row, node table, proof plan and N2), both P11B design audits, the pinned signature file, Track P statement conventions, blueprint p11a3 L233–251, and the authoritative live graph `/root/code/KAM-inp/docs/graph/P/DEPGRAPH.md` L25348–25463. The explicit user report path overrides the generic brief's main-worktree destination. Source-facing imported definitions and the frozen action-neighborhood, frequency and phase carriers were checked.

## Findings

**F1 — `fd_tel` does not expose the literal fd-tel graph conclusion.** FiniteDivisor.lean L77–83 exports only the frequency difference norm ≤ `selectionTail a m`. The graph L25387–25389 requires the telescoping identity and the full chain through the finite ell sum, S_m, γ T_m^(-τ-1), and γ |k|₁^(-τ-1). Its source premise includes the S_m bound and m=ν(k). The identity is only a local `hdiff` at L93–97; the finite-sum estimate is internal at L99–119. The parent L191–192 composes the first gamma endpoint bound, while the mode endpoint comparison is internal to the generic `fd_concl` at L158–159. No named declaration returns the full graph cut. Design N2 (L325) explicitly calls for the tail and gamma bounds; the handoff acknowledges that the gamma bound is applied outside `fd_tel`. Under the AUDIT FOCUS's requirement that each cut have its literal graph conclusion, this is incomplete. Keep the useful generic helper and add a distinct source-facing cut returning the identity and full inequality chain from the existing source premises. Do not change the pinned `finite_divisor` signature or add a new substantive premise.

**F2 — `fd_concl` omits the cutoff-wide endpoint of its graph conclusion.** FiniteDivisor.lean L136–142 returns only γ/|k|₁^τ ≤ |k·x|. The graph L25443–25445 and blueprint p11a3 L251 conclude further γ/|k|₁^τ ≥ γ T_ν^(-τ)=D_ν. That endpoint is correctly proved separately in `finite_divisor` L193–198, but is absent from the named `fd_concl` cut. The generic helper's T is T_m, so it cannot simply be relabelled T_ν. Preserve it as an implementation helper and expose the source-stage conclusion, including D_ν, under the actual stage cutoff premise. The final theorem already demonstrates the needed arithmetic without an extra assumption.

These are contract/export findings under the supplied focus. The older design permits internal proof blocks and says “Only the final divisor inequality is public” (L325); under that older, less strict interpretation the split proof establishes the intended final inequality. The current focus expressly demands literal graph conclusions and warns about unexported cuts, so it controls this verdict. Successful compilation or kernel replay cannot close F1–F2.

## Declaration and node coverage

All declaration names below have prefix `KAM.Planetary.`.

| Node / role | Declaration (FiniteDivisor.lean line) | Verdict | Reason |
|---|---|---|---|
| Shell membership / characterization | `selectionModeStage_mem_shell` (28) | PASS | Positive nonzero length lies below T_m and above T_(m−1) unless m=0; natural ceil handles lengths ≤T₀. |
| Least shell threshold | `selectionModeStage_le` (56) | PASS | L≤T_ν implies modeStage≤ν; together with membership this characterizes the least cutoff stage. |
| Nested prefixes | `selection_chain_antitone` (69) | PASS | Proves K_j⊆K_i from analytic-prefix nesting for i≤j≤ν. No resonance estimate assumed. |
| stepP:p11a:fd-tel | `fd_tel` (77) | FAIL (F1); stated helper sound | Stronger carrier b∈K_ν and arbitrary m≤ν are valid, but returned conclusion stops at S_m. |
| stepP:p11a:fd-test | `fd_test` (123) | PASS | Exact tested 2γ/|k|₁^τ margin on stage-m shell; m=ν uses hb directly, m<ν uses retained recursion and nesting. |
| stepP:p11a:fd-concl | `fd_concl` (136) | FAIL (F2); stated helper sound | Correct generic subtraction estimate; no D_ν endpoint exported by this cut. |
| bpP:p11a:finite-divisor | `finite_divisor` (174) | PASS WITH NOTES | Exact pinned signature and intended final pair of inequalities; package graph completeness remains FAIL. |

There is no frozen anchor to label seal-ready. Raw retained, chain, frequency and shell definitions belong to B02 and are imported rather than redefined. No B08 slice has been reassigned to another package to excuse F1–F2.

## Proof and definition review

No new `def`, `abbrev`, `structure`, instance or root-namespace declaration occurs in the audited module. Its seven declarations are theorems under `KAM.Planetary`; local `set` aliases L and m are exact aliases, not alternate mathematical objects. Imported raw definitions use existing `Fin n → ℝ` / `Fin n → ℂ` max norms, integer Fourier indices and the ℓ¹ mode length. `selectionModeStage` is the natural ceiling of log(length/T₀)/log 2. Its total log/ceil behavior at invalid parameters or zero modes is not exploited: both shell lemmas require positive length and T₀≥1. The full-carrier definitions remain B02's scope.

The finite frequency difference telescopes by cancellation of the same initial complex gradient and finite prefix sums. Increment bounds are applied only at b∈K_j, embedded into the positive-radius collar using zero distance. No derivative fallback or unrelated extension value is used. Positivity of q and ell_j justifies bounding the nonnegative finite sum by the shifted tsum; summability is exactly the signature's htail input, not a proof conclusion smuggled into the chain.

At m=ν the interval Ico m ν and range (ν−m) are empty, so the difference is zero. The tested stage ν is supplied directly by membership in `selectionRetained ... ν`; no future increment or limit is used. For earlier m, retained recursion gives K_(m+1), and nesting transports membership from K_ν. The complex scalar-product estimate is ℓ¹–ℓ∞ duality (`norm_le_pi_norm`), with one γ loss from the 2γ test. Negative-exponent monotonicity uses the upper shell endpoint T_m. The final cutoff comparison uses L≤T_ν and τ≥0. All divisions and power identities have positive base L or T_ν at their use. There is no limit-frequency argument or dependence on `divisor_wide`.

The hypotheses of `fd_concl` are legitimate explicitly conditional arithmetic-helper premises; it is not a source theorem replacement. `finite_divisor` introduces no extra premise relative to the pinned signature. Compactness, holomorphy and reality are unused by this finite algebraic estimate but are legitimate chain data; retained tests and increment bounds are the literal finite-chain input, not assumptions of the final divisor result.

## Validation

All Lean commands use `LEAN_NUM_THREADS=1` and `nice -n 5`; no overlapping audit Lean/Lake invocations, heartbeat override or frozen mutation is used.

1. Targeted gate build:

   ```sh
   env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b08 KAM.Planetary.WeakKAM.FiniteDivisor
   ```

   Exit **0**. After waiting for the compile gate, output included:

   ```text
   [inp-gate] slot 1 acquired 17:47:58 for KAM.Planetary.WeakKAM.FiniteDivisor
   ✔ [9110/9110] Built KAM.Planetary.WeakKAM.FiniteDivisor (24s)
   Build completed successfully (9110 jobs).
   ```

   Replayed dependency warnings concern unused variables/simp arguments and deprecated names in Schedule, StripBudget, MaximalStep/FourierCutoffTail, MaximalStep/Parameter and Cutoff*; no warning was emitted for FiniteDivisor.

2. Exact signature and fresh elaboration:

   A Python extraction of the complete theorem header through its conclusion, before `:=`, returned `Literal signature equality: True` against `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean` L399–411. No whitespace normalization was necessary. The scratch probe copied that signature under `audit_signature_copy` and supplied the direct body:

   ```lean
   exact finite_divisor d a c ν hc ht hT hτ hγ hs he htail
   ```

   It also checked `example : type_of% @audit_signature_copy := @finite_divisor`. Command:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B08Audit.lean
   ```

   Exit **0**, with these exact axiom outputs:

   ```text
   'KAM.Planetary.selectionModeStage_mem_shell' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionModeStage_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selection_chain_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fd_tel' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fd_test' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fd_concl' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.finite_divisor' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.FiniteDivisor > .lake/abi-scratch/B08Kernel.log 2>&1
   ```

   Exit **0**. Complete output:

   ```text
   replaying KAM.Planetary.WeakKAM.FiniteDivisor
   ```

   One invocation checks the only audited module, which contains all seven theorem declarations; there is no separate provider module.

4. Repository lint:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > .lake/abi-scratch/B08Lint.log 2>&1
   ```

   Exit **1**, solely for the expressly allowed stale generated-root exception. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (831 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No root regeneration was performed; no other lint failure occurred.

5. Static hygiene: **PASS** for this module. It has **199 physical lines**, including its trailing blank line (handoff says 198), with copyright, `module`, public imports, module docstring and public noncomputable section. Searches found none of `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option` or `EuclideanSpace`. Searching all KAM sources for each of the seven short names found no occurrence outside this file; all declarations are scoped under `KAM.Planetary`, with no root shadow. The transitive local import closure has **64 KAM modules**, **zero providers**, **zero frozen theorem modules**, and **12 frozen definition modules**, each manifest-state **SEALED**: ActionNbhd, ComplexStrip, FrequencyMap, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, RealHamiltonian, SymplecticForm, and Planetary/Phase. No DRAFT_SORRY theorem enters the proof.

6. Protected paths:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   ```

   Exit **0**, empty output. The worktree-local audit changes only the requested report; probes/logs are removed after checking. `git diff --check` exited **0**, empty output. The untracked report was also checked directly for trailing whitespace and final newline.

Audited file SHA256: `0e3802443b21c10d07a3625b189e0eb1e905ec94047d7aba3b1378f1d7b9cc23`.
Pinned signature file SHA256: `6800132b3e98b3badc215d5cb1cccc6b016e2f14ec976b661519e436cbf39596`.

## Source defects, deviations and limitations

No new suspected mathematical defect in a pinned external source was found. The blueprint explicitly labels this finite-stage lemma “Ours”; the corrected endpoint T_m and direct finite-stage route are preserved. F1–F2 concern implementation/graph contracts, not a newly alleged source erratum. The module docstring L16–17 says the named steps are local and “only the final inequality is public”, although all seven theorem declarations are in a public section: documentation should be aligned with the actual API. This is a minor note, separate from the two completeness failures.

No source, generated root, frozen file, manifest or git state was changed by this audit. Only this report and temporary worktree-local ABI scratch probes were written. No conclusion about the inherited B03/B04/B05 packages or campaign theorem closure is made.

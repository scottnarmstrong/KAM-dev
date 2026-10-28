# P23-05 independent package audit 1

Overall verdict: **PASS WITH NOTES** for P23-05, comprising `KAM.Planetary.direct` and `KAM.Planetary.direct_step`. No mathematical or proof defect found in the scoped file. Both statements match the revision-2 design signatures, and the proofs consume the exact N declarations on the same generator and flow. The only lint exception is the expected stale generated root (receipt below).

No frozen theorem anchor or provider is implemented by this package. Consequently provider/frozen-type equality and an actual frozen seal are **not applicable**; this is an infrastructure-package verdict, not P-G or campaign closure. The corresponding exact-type and explicit-binder application probes were run against both design signatures.

## Scope and authority

- Worktree and report destination: `/root/code/KAM-inp-p2305`; this report is written here, not in `/root/code/KAM-inp`.
- Audited HEAD: `beddbc6fca7c5cdcc05bb4178fe7576a3bfe730f`.
- Scoped production file: `KAM/Planetary/Averaging/Direct.lean`, 186 lines; SHA256 `2f83f920d721cc63a5a490e28b471786f8254661a45cffd63962d253d4da6185`.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local `P23-05-handoff.md`, track-P statement, revision-2 `P23-LEAN-DESIGN.md`, and both design audits in `docs/tracks/P/design/`.
- Statement authority: `/root/code/KAM-inp/.drafts/design/P23Signatures.lean`, SHA256 `7d7dae4308ea9ec0ca763a2a21ce4b83280bdbb4b91d2c4f5e7567b71085e834`; `direct` at L107–114 and `direct_step` at L214–243. The relative scratch path named in the handoff is absent here; the main-worktree copy has the exact hash recorded by design audit 2. The design Appendix A also supplies the signatures.
- Blueprint: `blueprint-P/parts/p2-averaging.tex:22–55`, especially `bpP:p2:setting`, `bpP:p2:direct` and `stepP:p2:dr-use`; inherited homological and iterative clauses in `blueprint-N/parts/p6-normal-form.tex:54–105`.
- Read the relevant live N interfaces and definitions (`Setting`, `Homological`, `IterativeMap`, `IterativeRemainder`, `IterativeReal`) and the imported frozen definitions. No frozen theorem is in this module's KAM import closure.

The requested `git diff inp...HEAD` was inspected. Git reports two merge bases and selects `33c688a1d1c9d25d7099f328479f4f53b0301bb4`; the other is `66c3746f8b9043a5ce0287413f8f775e025dc0ac`. At inspection `inp` was `42e1afbf28c6097caabe5a9b6d5d7a81463eeae7`. The resulting diff contains `Direct.lean` (+186), inherited `Iterative.lean` (+19), and inherited `IterativeReal.lean` (+132). These N files are dependencies, not additional package files covered by this verdict.

Also inspected `git diff inp-n67...HEAD`, as requested by AUDIT FOCUS. `inp-n67` currently resolves to `2675e0a54e803aa88ac46391116b2ff4465f3754`; that comparison includes unrelated inherited files and five additions to generated `KAM.lean`. This is not a clean package-only baseline. The `Direct.lean` addition is the same in both comparisons; its only file-history commits are `da1f8f5` and `beddbc6`. The user-requested `inp` comparison has **no protected-path changes**. No branch/ref, generated root, frozen file, or source was edited by this audit.

## Declaration and node review

All declaration names in the table have prefix `KAM.Planetary.`.

| Node / role | Declaration, Direct.lean line | Verdict | Reason |
|---|---|---|---|
| Arithmetic adapter | `conjExp_two`, 34 | PASS | Unfolding proves `conjExp 2 = 2`; no premises. |
| `bpP:p2:setting` adapter / `stepP:p2:dr-use` | `divisor_two`, 38 | PASS | Rewrites `2*α/q/conjExp 2` to `α/q`, then uses the original `H.div` on the whole complex neighbourhood. |
| Generator-bound adapter | `bound_two`, 44 | PASS | Exact coefficient identity `conjExp 2*δ/(2π*(2α/q)) = qδ/(2πα)`. Nonzero denominators follow from `H.α_pos`, `H.q_ge`, and π positivity. |
| Iterative smallness adapter | `iterU_two`, 52 | PASS | Same `iterU` coefficient; valid for all real `ρ,σ`, including zero, handled explicitly. No positivity premise is added to this helper. |
| `bpP:p2:direct`, homological selected view | `direct`, 67 | PASS | Exact design statement. Calls `KAM.NormalForm.homological_direct` with `p=2`, `α_N=2α/q`; projects class, equation and generator norm. |
| `bpP:p2:direct`, iterative selected view / `stepP:p2:dr-use` | `direct_step`, 88 | PASS | Exact design statement. Builds the full original `IterHyp` and uses `iterative_direct_a`, `_b`, `_c`, `_d`, `_e`, with the identical generator, flow, decomposition and remainder. |

There are no additional public declarations in the new file. The four adapters have distinct names and are arithmetic or predicate transport, not replacement statements for the source theorem. Their bundle premises are redundant for some arithmetic content, but no blueprint result is being weakened by those helpers.

## Fidelity and proof review

Both production theorem statements are equal to their design statements after whitespace normalization. Fresh declarations copied from the design, using the production definitions rather than design fixtures, elaborate with bodies:

```lean
by exact KAM.Planetary.direct H
by exact KAM.Planetary.direct_step H hρ hσ hsmall hg
```

For each copied signature, the additional test

```lean
example : type_of% @signature_direct := @KAM.Planetary.direct
example : type_of% @signature_direct_step := @KAM.Planetary.direct_step
```

elaborates. The probes preserve every implicit binder, explicit binder and conclusion, including conditional reality. They do not import the design's `sorry` declarations or restated N fixtures.

The substitution `p_N=2`, `α_N=2α/q` is legitimate for every `q≥1`, including `q=1`. It gives positive `α_N`, divisor `α_N/conjExp 2=α/q`, and multiplier `conjExp 2/α_N=q/α`. Neither `homGen` nor `iterMap` depends on `p` or `α_N`, so this substitution does not change the generating function or time-one map.

In `direct` L80–83, the projections are precisely c1 (generator class), c4 (homological equation) and c9 (generator bound). `homRes K Λ f` unfolds to `projMode Λ (truncate K f)` (`Homological.lean:47`), so the equation uses the original resonant component with unchanged Poisson sign.

In `direct_step` L128–149, every `IterHyp` field is paid from the original premises. `hg` provides the finite decomposition, bounds, and larger radii; `g=∑gj` supplies its equality by reflexivity. The smallness conversion uses positive `ρ,σ,α_N` and is exactly equivalent to the upstream `δ_small` field. No frequency Lipschitz assumption, output realness assumption, instance, or proof-shaped field is added.

The same `HI` feeds `_a` through `_d` at L150–153 and `_e` at L180. The explicit `Ψ` is definitionally `iterMap D r s ρ σ K Λ h f`; `gp` is definitionally `iterG`, and `fp` is definitionally `iterF`. The finite weighted expression `star` is the original `starNorm`. The rewrite at L168–170 preserves both the denominator `1-2u` and exponential tail `exp (-(2πKσ))`; L156–163 pays the exact displacement and remainder coefficients. Since `0≤u≤1/4`, the denominator is positive. The weights `rj-r+ρ` and `sj-s+σ` are positive from `hg` and the loss premises.

The inclusion at L154–155 is `V ⊆ U`, where `V` has twice losses and `U` has three-halves losses. It legitimately restricts upstream symplecticity, displacement and map reality. Holomorphy and maps-to retain their larger domain. For reality, L175–179 derives realness of `g` by restricting each given real `gj` to the original domain and summing imaginary parts. `_e` then yields the same `gp`, `fp`, and real map; only smaller-domain restrictions follow.

Relative to the prose normalization `δ=‖f‖`, using a nonnegative upper bound `WBound ... δ` is a stronger, monotone contract, already present in the accepted signatures. Likewise `Mj` are supplied norm upper bounds. There is no wider constant dependence or changed carrier: ambient vectors and Fourier indices are exactly the required finite function spaces, strip widths here are geometric, and `WBound` includes summability at every action point.

**Selected-view boundary:** the wrappers do not themselves return the full N contract. In particular, integer translations, inverse flow, gauge derivative bounds, and further generator/normal-form projections must be obtained from the full N theorems on this same data. Revision 2 explicitly requires this (`P23-LEAN-DESIGN.md:12,20,27,269`); `Direct.lean:63–65,84–87` discloses it. `iterative_direct_a` really returns the lattice law and inverse for this exact `iterMap` (`IterativeMap.lean:133–149`). This satisfies the assigned P23-05 boundary; it does not audit the future P23-12 consumer.

## Definition classification and imports

No new `def`, `abbrev`, `structure`, or instance occurs in `Direct.lean`; definition classification for new declarations is therefore empty. The theorem-local `let`s are explicit existing objects: `φ=homGen`, `Ψ` is its literal time-one flow on the one-loss domain, `g` is a finite sum, `gp` is the resonant update, `fp` is the literal Hamiltonian difference, and `u`, `star`, `V` are the stated scalars/domain. There is no selection function, default witness, or new fallback.

The inherited totalized division in `homGen` is guarded on all active modes of the theorem domain by the positive divisor bound. The inherited weighted `tsum` is guarded by `WSummable` inside every `WBound`; no junk zero is used to certify a bound. Flow claims are restricted to the domains supplied by the original N theorem. Empty domains and zero dimension create no new definition or exceptional proof premise.

The recursively inspected KAM import closure contains no provider and no frozen theorem, hence no `DRAFT_SORRY` theorem import. All twelve frozen modules reached have manifest kind `definition` and state `SEALED`: `ActionNbhd`, `ComplexStrip`, `HamiltonianVectorField`, `HamiltonianVectorFieldC`, `IsDiophantine`, `IsPrimaryOnStrip`, `IsRealOnReals`, `OmegaZero`, `SymplecticForm`, and planetary `Fast`, `Phase`, `Slow`. Their bodies were read; the canonical coordinate order, field and form are retained. No provider quarantine exception is needed.

## Independent validation receipts

All Lean/Lake commands were serialized and run under `nice -n 5` with `LEAN_NUM_THREADS=1`. The lint ABI subprocess inherited these settings. No heartbeat, recursion or synthesis budget override was used.

1. Targeted compile gate:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2305 KAM.Planetary.Averaging.Direct
   [inp-gate] slot 1 acquired 07:23:38 for KAM.Planetary.Averaging.Direct
   Build completed successfully (9127 jobs).
   exit 0
   ```

   The job count is Lake's target graph summary; this was a targeted build using the existing overlay, not a library rebuild or clean.

2. Exact signature and explicit-binder application probes, then all six axiom checks:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2305Audit.lean
   'KAM.Planetary.conjExp_two' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.divisor_two' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.bound_two' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.iterU_two' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.direct' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.direct_step' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   There was no other diagnostic. The scratch probe is deleted after validation.

3. One kernel replay invocation covers the only new lemma module (there is no provider module):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.Direct
   replaying KAM.Planetary.Averaging.Direct
   exit 0
   ```

4. Full source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (450 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   This exit 1 is solely the stale-root exception permitted by the audit brief. No root regeneration was performed.

5. Static checks: the scoped file has 186 total lines and maximum line length 98; copyright, `module`, public imports, module docstring and exposed public section are present. No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, or `set_option` occurs in it. `git diff inp...HEAD --check` exits 0 with only Git's multiple-merge-base warning. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` emits no diff, only that same warning. No working-tree diff of `Direct.lean` is present.

## Findings, uncertainty, errata and deviations

No blocking, major, or minor mathematical defect found in scope. The two operational notes are the inherited comparison-base history and expected generated-root lint exception, fully disclosed above. No suspected new blueprint or pinned-source defect was found; no source-PDF fidelity beyond the named blueprint/design interface is claimed. The blueprint already labels the direct-divisor variant as an intentional variant of the written N statement; this package proves it by the accepted exact upstream route.

No production deviation was introduced. Only this report was written outside `.lake/abi-scratch/`; temporary audit probes were removed. Existing untracked `P23-05-handoff.md` was left untouched. Full finite averaging, later consumers, frozen seals and the planetary headline remain outside this package verdict.

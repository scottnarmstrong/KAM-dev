# S10-J independent package audit 1

Verdict: **PASS WITH NOTES** for the assigned S10-J design contract. Both principal results, `f_pol` and `f_leib`, pass. No frozen anchor or provider is delivered by this package, so frozen-type equality and seal-body probes are not applicable. This is not a seal or closure verdict for a planetary headline.

Audited HEAD `cdea3ad88037d83cf5e3f6fceb15337881b6db48` in `/root/code/KAM-inp-s10j`. The requested report location in this worktree takes precedence over the generic brief's main-worktree output instruction. Only this report is edited; temporary audit files are confined to `.lake/abi-scratch/` and removed after checking.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the S10-J handoff, the P810 design (especially lines 267–270, row S10-J at 449, and signatures at 1056–1063 and 1208–1217), the two design audits, the original signature file, Track P statement conventions, and the relevant Part 10 blueprint statements. The original signatures and design audits are available in `/root/code/KAM-inp/.drafts/design/P810Signatures.lean` and `/root/code/KAM-inp/docs/tracks/P/design/DESIGN-P810-design-audit-{1,2}.md`; the signature scratch file is absent in this package checkout. The design audits are in `design/`, not `audits/`.

`git diff inp...HEAD` has two additions: the 172-line `KAM/Planetary/Nondegeneracy/DiagonalTensor.lean` and the upstream 158-line `KAM/Planetary/SecularSpectrum/Norms.lean`. Initially `inp` resolved to `5991245cabc06e69ec900cb6006b45f72cc85eb0`. During verification the shared ref advanced to `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`; Git then warned of multiple merge bases and selected the same initial `5991245` base. The final requested diff still has exactly those two additions and no protected-path changes. HEAD stayed fixed. The additional requested comparison against `inp-s9n` (`50de825c3f654adc885132a6517d4ad6c090d131`) contains unrelated intervening branch changes; restricting it to `KAM/Planetary/Nondegeneracy/DiagonalTensor*.lean` gives exactly the same 172-line addition. Per AUDIT FOCUS, only that file receives the package verdict. `Norms.lean` was read to verify the supplied carrier and Euclidean length; its remaining exports are not re-audited here.

## Declaration inventory

All names below are in `KAM.Planetary.Nondegeneracy`. Every public declaration in the scoped file is included.

| Node / role | Declaration and source line | Verdict | Reason / boundary |
|---|---|---|---|
| `bpP:p10:sec-index#data` | `jetNorm`, 31 | PASS | Exact design body, including separate order-zero value and Euclidean output length. |
| `bpP:p10:sec-index#data` | `scalarJet`, 34 | PASS | Exact design body; scalar absolute value and Euclidean unit directions. |
| `bpP:p10:sec-index#data` | `jetMax`, 37 | PASS | Exact design body; maximum includes every order from zero through `μ`. |
| Polarization proof cut | `hasDerivAt_diag`, 43 | PASS | Chain rule for the diagonal line; derivative is the sum of single-slot replacements. Valid also at order zero. |
| Polarization proof cut | `sum_update_eq_zero`, 55 | PASS | Derivative uniqueness for an identically zero diagonal; symmetry is not needed, so the statement is stronger than its docstring suggests. |
| Polarization proof cut | `sum_update_eq`, 64 | PASS | Explicit permutation symmetry makes all `n+1` terms equal to the first-slot term. |
| Polarization proof cut | `pol_aux`, 85 | PASS | Proves zero form from symmetry and zero diagonal by induction, including the nullary base case. |
| `bpP:p10:f-pol` | `f_pol`, 119 | PASS WITH NOTES | Exact design signature; all-diagonal equivalence proved. Unit-sphere/supremum equivalence is not exported; see N1. |
| Leibniz proof cut | `iteratedFDeriv_diag_eq`, 128 | PASS WITH NOTES | Correct local line-restriction identity, for the stated analytic-level `ContDiffOn ℝ ⊤` premise; see N2. |
| `bpP:p10:f-leib` | `f_leib`, 149 | PASS | Exact design signature, binomial coefficients, order-zero terms and `ν-k` order retained; analytic premises discharged locally. |

The three definition bodies and both principal theorem signatures match the original design signatures byte-for-byte after removing theorem proof bodies and trimming surrounding whitespace. Fresh Lean declarations copied from the two original theorem signatures and proved by the delivered exports elaborate successfully. There is no extra premise, constant dependence, changed binder order, or changed carrier relative to the assigned design contract.

## Definitions and proof review

`Vec d` is literally `Fin d → ℝ`. Upstream `length2 x = sqrt (∑ i, x i^2)` supplies the intended Euclidean scalar, independently of the ambient Pi max norm. No ambient norm instance is changed.

* `jetNorm`: literal diagonal derivative size. At order zero it is `length2 (f y)`; at positive order it is the real supremum of Euclidean lengths of diagonal evaluations on the Euclidean unit sphere.
* `scalarJet`: the same construction with scalar absolute value, with `|g y|` at order zero.
* `jetMax`: literal supremum of the finite nonempty set of scalar sizes indexed by `ν ≤ μ`; order zero is included even when `μ = 0`.

There are no other new definitions, abbreviations or structures. For positive input dimension, finite-dimensional compactness and continuity of each continuous multilinear derivative make the unit-sphere suprema genuine finite maxima. Those supporting lemmas are not exported here. For input dimension zero the unit sphere is empty; Lean's real empty supremum gives zero, consistent with every positive-order multilinear map on the zero vector space being zero. The separate nullary branch preserves the value of a constant nullary form. Off the differentiability locus, `iteratedFDeriv` retains Mathlib's totalized derivative convention; this package makes no differentiability-free theorem interpreting it as an existing classical derivative. No proof here obtains a result from a junk fallback.

The polarization induction differentiates the zero diagonal, applies symmetry to obtain `(n+1) * T(w,x,…,x) = 0`, cancels a strictly positive real natural-number coefficient, and applies the induction hypothesis to `curryLeft`. Permutations fixing the first slot supply the curried symmetry. The base case correctly uses the unique empty tuple rather than assuming a nonempty sphere.

For the Leibniz proof, translation gives an open set containing zero. The continuous linear line map has an open preimage containing zero, including when `v = 0`. The within-derivative chain rule is converted to unrestricted derivatives only at those interior points. This requires no assumption that the whole line lies in `B`. Analyticity supplies the regularity for each finite derivative order; Mathlib's one-variable product formula then gives the stated finite binomial sum. No missing factorial, norm factor or mixed-derivative premise was found.

The zero-diagonal premise of the named polarization helpers is the antecedent of the implication being proved, not an assumed supplier of the package conclusion. No analytic, symmetry, or derivative identity is bundled as an unproved field.

## Notes, source fidelity and limitations

**N1 — design result versus full norm-faithfulness export.** `blueprint-P/parts/p10-nondegeneracy.tex:28` states “is zero iff … the diagonal … is zero iff … the unit-sphere maximum … is zero.” Line 197 uses the last equivalence for derivative norms. The exact approved-for-this-audit signature at design lines 1208–1211, and the implementation at lines 119–122, export only the first equivalence. The remaining bridge needs homogeneity plus bounded-supremum facts, and a separate order-zero treatment. It is mathematically valid on the intended positive-dimensional carrier and can be proved by a later consumer, but no such lemma is delivered here. Thus S10-J satisfies its five-export design contract; it does not alone certify every clause of the printed `f-pol` node or close finite-type norm arguments. No later consumer proof was assigned or certified in this audit.

**N2 — analytic regularity terminology.** The helper docstring at lines 126–129 says “smooth function” but its premise is `ContDiffOn ℝ ⊤`. In pinned Mathlib, `ContDiff/Defs.lean:90,118–132` distinguishes smooth `∞` from top analytic `ω`; `⊤` here is the latter. The proof is valid, and `f_leib` supplies it from the exact design's analytic hypotheses. This is a documentation/generalization boundary, not an unproved premise. No general finite-regularity or arbitrary-smooth Leibniz interface is certified by this module.

No suspected defect in a pinned paper was discovered. No pinned-PDF claim or source erratum is inferred from N1/N2; they concern interface coverage and terminology. The alternative induction proof of polarization is valid and does not change its mathematical statement. No production deviation was introduced by this audit.

## Independent verification

All Lean/Lake commands below were serialized, used `LEAN_NUM_THREADS=1`, and ran at niceness 5. No clean, update, cache download, root regeneration, or state-changing git command was used.

1. Targeted compile gate:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s10j KAM.Planetary.Nondegeneracy.DiagonalTensor
   [inp-gate] slot 1 acquired 09:54:26 for KAM.Planetary.Nondegeneracy.DiagonalTensor
   Build completed successfully (9111 jobs).
   exit 0
   ```

   Replayed unused-variable warnings occur in upstream `KAM/Kepler/Energy.lean`, `KAM/Planetary/Poincare/Chart.lean`, and `KAM/Kepler/Mass.lean`. No scoped-file warning or heartbeat failure occurred.

2. Signature and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10JAudit1.lean
   exit 0
   ```

   The probe imports only the delivered module, copies the original `f_pol` and `f_leib` signatures under fresh names, and closes them respectively with `f_pol T hSym` and `f_leib hB hf hg hy v ν`. Its complete axiom output is:

   ```text
   'KAM.Planetary.Nondegeneracy.hasDerivAt_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Nondegeneracy.sum_update_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Nondegeneracy.sum_update_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Nondegeneracy.pol_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Nondegeneracy.f_pol' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Nondegeneracy.iteratedFDeriv_diag_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Nondegeneracy.f_leib' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation for the single scoped theorem/lemma module:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Nondegeneracy.DiagonalTensor
   replaying KAM.Planetary.Nondegeneracy.DiagonalTensor
   exit 0
   ```

   The command's output was captured temporarily in `.lake/abi-scratch/S10J-kernel.log`; the wrapper also printed `LEANCHECKER_EXIT=0`. There is no provider module to add to this invocation.

   Source lint, run after the replay finished:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (525 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   This is exactly the stale generated-root exception permitted by the audit brief. No other lint diagnostic occurred. The generated root was not edited.

4. Static hygiene: `wc -l KAM/Planetary/Nondegeneracy/DiagonalTensor.lean` gives `172`. Copyright/authors, `module`, public imports, module docstring, and `@[expose] public noncomputable section` are present. A scan for `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, and `set_option` has no matches (rg exit 1). `git diff --check inp...HEAD` exits 0. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty (exit 0).

5. Quarantine: direct imports are `Mathlib` and `KAM.Planetary.SecularSpectrum.Norms`. A recursive local-import traversal finds 65 modules and 47 frozen definition modules, with no provider or frozen theorem module. Consequently no DRAFT_SORRY theorem is imported and no theorem manifest-state exception is needed. The allowed axiom outputs independently exclude a hidden sorry dependency in every new theorem.

No anchor is changed or claimed seal-ready. Remaining work is precisely the norm bridge noted in N1 if a consumer requires it, plus the separately owned finite-type/stability and planetary theorem packages.

Final artifact check: the report is at `/root/code/KAM-inp-s10j/docs/tracks/P/audits/S10-J-audit-1.md`. The audit signature probe and kernel log have been deleted. Git status contains this new report and the pre-existing untracked `S10-J-handoff.md`; no tracked file was modified by this audit. Report whitespace validation passes.

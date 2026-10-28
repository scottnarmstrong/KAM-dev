# S10-Z independent package audit 1

Overall verdict: **PASS WITH NOTES** for the assigned `AnalyticZeros*.lean` package.
No frozen anchor is provided or sealed by this package; **seal readiness: N/A**.
The three design exports pass declaration fidelity and proof checks. This report does
not certify any planetary headline, the full P810 campaign, or unrelated branch changes.

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-s10z`.
Audited HEAD: `8835bc258a130aad4719a422777b6c4f44809cc5`.
Compared `inp`: `5991245cabc06e69ec900cb6006b45f72cc85eb0`.
Package commits: `19dbc141aa2b8c17c03d8bfc13a639526818e6c7` and HEAD.
Package parent: `6874491` (contains the S8-B dependency).

## Scope and authority

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the worktree handoff,
Track P statement, P810 revision-2 design and both design audits. The handoff's
`audits/DESIGN-P810-design-audit-{1,2}.md` locators are stale: the actual files
are under `docs/tracks/P/design/`. The untracked signature file is absent from
this worktree and was read at `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`.
It occurs verbatim in this worktree's design Appendix A.

Only production file audited:
`KAM/Planetary/Nondegeneracy/AnalyticZeros.lean` (258 lines), SHA-256
`6bfff67cbb465e979395a283235e3e399bd7640edee8a6674d73fff5a652dd9d`.
The original signatures have SHA-256
`492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`.

Source contracts are design row S10-Z (line 443), signatures `generic` at
408–414, `rnd_def` at 469–470 and `analytic_zero_null` at 735–737, together
with blueprint p9 line 23 and p10 lines 24–38,137–140. The design's implementation
sketch at lines 330–333 is a proof plan, not an extra hypothesis or theorem claim.
No provider export or frozen theorem is imported; exact-provider/frozen-type and
seal-body probes are consequently inapplicable. The semantic closure relevant to
these statements is `SecularForm.Vec n = Fin n → ℝ` (Basic.lean:33), standard
real analyticity, Pi Lebesgue volume, and standard topology.

## Declaration inventory

Names below are in `KAM.Planetary.Nondegeneracy`. Every public theorem and
both new definitions are included; helper statements are explicit local proof cuts,
not replacements for the source-facing results.

| Node / role | Declaration (file line) | Verdict | Reason |
|---|---|---|---|
| `bpP:p10:rnd-def` | `rnd_def` (38) | PASS | Literal real-relation predicate; every nonzero real vector, not just integral vectors. |
| One-dimensional proof cut | `countable_of_isolated` (43) | PASS | Isolated subset of ℝ is discrete and countable; no analytic or measure conclusion assumed. |
| One-dimensional proof cut | `null_zero_of_deriv` (60) | PASS | Zeros with nonzero derivative are isolated; the remainder is contained in the derivative's null zero set. No measurability assumption needed for this outer-measure argument. |
| Coordinate parametrization | `lineAt` (83) | PASS | Exactly `Fin.insertNth`, on its entire carrier. |
| Coordinate identity | `insertNth_eq_add` (85) | PASS | All coordinates and every real line parameter; exact standard basis decomposition. |
| Fubini proof cut | `volume_null_iff_lines` (90) | PASS | Measurable set, product Lebesgue volume, almost-everywhere coordinate sections. |
| Measurability proof cut | `measurableSet_zero_inter` (104) | PASS | Continuous on open V suffices; does not require global continuity. |
| Derivative descent | `null_zero_of_dir` (112) | PASS | Conditional helper with distinct name; its derivative-null premise is supplied by the induction at lines 200–202. |
| Taylor proof cut | `exists_coord_deriv_ne` (138) | PASS | Analytic nonflat germ has a nonzero coordinate derivative chain, including order zero. |
| Local induction | `local_null` (167) | PASS | Conditional helper; coordinate-chain premise is produced at line 215 and consumed at 216. |
| `bpP:p9:e-id`, `stepP:p10:gen-zero` | `analytic_zero_null` (206) | PASS | Exact design signature, connected open domain, analytic f, an actual nonzero witness, null zero set. |
| `bpP:p10:generic` | `generic` (225) | PASS | Exact design signature, common nonzero locus open and relatively dense, bad set null. |
| `bpP:p10:f-id`, identity/products | Mathlib identity theorem and consequence of `generic` | PASS WITH NOTES | Identity is consumed at line 214. No separately named product export exists; fresh consumer probe proves finite-product nonvanishing from `generic`, without additional premises. See N1. |

## Binders and literal definitions

The source-facing types match the original signatures after whitespace normalization.
Fresh Lean examples independently restated the types using `Fin d → ℝ`, applied
both theorem exports with all explicit source binders, and checked `rnd_def` by
`Iff.rfl`. The unused design variable `n` introduces no elaborated binder.
There are no constants or quantitative witnesses with hidden dependence.

Five-bin input audit for the source-facing theorems (SOURCE / STANDING / TYPING /
RULED / EXCESS). There are no bundled logical premises requiring further expansion.

| Declaration | Binder | Bin | Exact meaning / authority |
|---|---|---|---|
| `analytic_zero_null` | implicit `d : ℕ` | TYPING | Source dimension, signature 735. |
| `analytic_zero_null` | implicit `B : Set (Vec d)` | TYPING | Source domain, signature 735. |
| `analytic_zero_null` | `hB` | SOURCE | Open domain, signature 735; p9:23. |
| `analytic_zero_null` | `hBc` | SOURCE | Connected nonempty domain, signature 735; p9:23. |
| `analytic_zero_null` | implicit `f : Vec d → ℝ` | TYPING | Real scalar function, signature 736. |
| `analytic_zero_null` | `hf` | SOURCE | Analytic on the open domain, signature 736; p9:23. |
| `analytic_zero_null` | `hne` | SOURCE | Exists x in B with f x ≠ 0, signature 736; p9:23. |
| `generic` | implicit `d : ℕ` | TYPING | Source dimension. |
| `generic` | implicit `r : ℕ` | TYPING | Size of finite family, signature 408. |
| `generic` | implicit `B : Set (Vec d)` | TYPING | Source domain, signature 408. |
| `generic` | `hB` | SOURCE | Open domain, signature 408; p10:33. |
| `generic` | `hBc` | SOURCE | Connected nonempty domain, signature 408; p10:33. |
| `generic` | implicit `f : Fin r → Vec d → ℝ` | TYPING | Finite family of real scalar functions, signature 409. |
| `generic` | `hf` | SOURCE | Every member analytic, signature 409; p10:33. |
| `generic` | `hne` | SOURCE | Each member not identically zero, signature 410; p10:33. |

Counts: `analytic_zero_null`: SOURCE=4, STANDING=0, TYPING=3, RULED=0,
EXCESS=0. `generic`: SOURCE=4, STANDING=0, TYPING=4, RULED=0, EXCESS=0.
All typeclass instances come from the fixed standard real/Pi carriers; no new
instance, structure, theorem-shaped predicate, or bundled result is introduced.
Helper derivative-null and nonflatness conditions are intermediate assertions
proved in their callers, never added to either source-facing signature.

`rnd_def`: literal predicate on every `B : Set (Fin d → ℝ)` and every real-vector
map, asserting `∀ c ≠ 0, ∃ y ∈ B, ∑ i, c i * ω y i ≠ 0`.
Analyticity, nonemptiness and open connectedness are standing applicability
conditions in the source definition, not hidden fields or conclusions of this
predicate. Extending the literal algebraic predicate to arbitrary B and ω matches
the exact design body; there is no fallback value. For output dimension zero the
relation test is vacuous, as prescribed by quantification over nonzero vectors.

- BODY_MATCH: OK
- PUBLIC_CARRIER: OK
- WELL_DEFINEDNESS: N/A_LITERAL
- CHARACTERIZATION: N/A_LITERAL
- CHOICE_INDEPENDENCE: N/A
- DEFINITION_VERDICT: PASS

`lineAt`: literal abbreviation `Fin.insertNth i t y` for every coordinate i,
every y and every real t. It is the affine coordinate line with the other d
coordinates fixed; `insertNth_eq_add` verifies the formula globally.

- BODY_MATCH: OK
- PUBLIC_CARRIER: OK
- WELL_DEFINEDNESS: N/A_LITERAL
- CHARACTERIZATION: N/A_LITERAL
- CHOICE_INDEPENDENCE: N/A
- DEFINITION_VERDICT: PASS

Both bodies are exposed by `@[expose] public noncomputable section`.
The proof-local `choose! V` at line 217 selects already proved local neighbourhoods;
only its specifications for x ∈ B are used. It defines no exported arbitrary object
and cannot introduce off-domain semantics into a source definition.

## Proof refutation checks

The one-variable argument separates critical zeros from zeros with nonzero
derivative. The latter are isolated even among all zeros, hence countable;
monotonicity and a union of null sets finish without assuming the target nullity.

The coordinate split is the measure-preserving `piFinSuccAbove` equivalence,
not a coordinate norm argument or an unproved Jacobian assertion. Measurability
of both relevant zero sets is proved from continuity on the open V. Product
integration uses `Measure.prod_apply_symm` and a measurable section-measure
function, then transfers the almost-everywhere derivative-null sections through
the one-variable lemma. Thus no integrability or section-measurability gap is
hidden in Fubini. The product measure is the literal Pi `volume`.

If all coordinate evaluations of all Taylor tensors vanish, finite-dimensional
multilinearity expands arbitrary inputs in the standard basis and forces each
tensor to vanish. `HasFPowerSeriesOnBall.factorial_smul` and `hasSum` then make
the function zero on a genuine neighbourhood. The induction descends in derivative
order, not dimension: its successor case extracts d=d'+1 from an actual coordinate
index. Dimension zero is covered by the order-zero branch, with no fictitious
coordinate or zero-volume assumption. The higher-derivative identity is the pinned
`iteratedFDeriv_succ_apply_right` and a continuous-linear evaluation map.

The identity theorem at line 214 propagates an allegedly flat germ across B,
contradicting the explicit nonzero witness. Local nullity is globalized by an
actual countable neighbourhood cover, not an uncountable union of null sets.
`generic` takes a finite union of null zero sets; its openness uses only relative
continuity, and density follows because every nonempty open intersection W ∩ B
has positive Lebesgue measure. The empty family r=0 and d=0 require no added guard.

Pinned library implementations inspected: Analytic/Uniqueness.lean:205,
Calculus/FDeriv/Analytic.lean:855, Calculus/ContDiff/FTaylorSeries.lean:919,
MeasureTheory/Constructions/Pi.lean:819 and MeasureTheory/Measure/Prod.lean:722.
No new pinned-paper erratum is alleged; this audit does not re-audit the papers.

## Independent checks

All Lean/Lake invocations controlled by this auditor were sequential, inherited
`LEAN_NUM_THREADS=1`, and ran under `nice -n 5`. The targeted build used the
prescribed compile gate; no clean, update, cache fetch, root regeneration or
production edit was performed.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s10z KAM.Planetary.Nondegeneracy.AnalyticZeros
   [inp-gate] slot 2 acquired 09:41:31 for KAM.Planetary.Nondegeneracy.AnalyticZeros
   Build completed successfully (9110 jobs).
   exit 0
   ```

   No diagnostic in AnalyticZeros. Replayed upstream unused-variable warnings
   occur in Kepler/Energy.lean:106, Poincare/Chart.lean:212,247 and
   Kepler/Mass.lean:147,157,500,524; these were not changed or suppressed.

2. Exact-type/body, product-consumption and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10ZAudit1.lean
   exit 0; no errors or warnings
   ```

   It checked the literal definition equation, both exact source-facing types,
   and the product consequence quoted in N1. Each of these 12 `#print axioms`
   queries returned exactly `[propext, Classical.choice, Quot.sound]`:

   ```text
   KAM.Planetary.Nondegeneracy.rnd_def
   KAM.Planetary.Nondegeneracy.lineAt
   KAM.Planetary.Nondegeneracy.countable_of_isolated
   KAM.Planetary.Nondegeneracy.null_zero_of_deriv
   KAM.Planetary.Nondegeneracy.insertNth_eq_add
   KAM.Planetary.Nondegeneracy.volume_null_iff_lines
   KAM.Planetary.Nondegeneracy.measurableSet_zero_inter
   KAM.Planetary.Nondegeneracy.null_zero_of_dir
   KAM.Planetary.Nondegeneracy.exists_coord_deriv_ne
   KAM.Planetary.Nondegeneracy.local_null
   KAM.Planetary.Nondegeneracy.analytic_zero_null
   KAM.Planetary.Nondegeneracy.generic
   ```

3. Kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Nondegeneracy.AnalyticZeros
   replaying KAM.Planetary.Nondegeneracy.AnalyticZeros
   exit 0
   ```

4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (521 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The only failure is the stale generated root, explicitly allowed by the brief.
   All other source, module, frozen-anchor and ABI checks pass. No root file was
   regenerated. The ABI subprocess ran after kernel replay, under the same
   single-thread environment and inherited nice priority.

5. Scoped static hygiene: 258 physical lines, maximum Unicode line length 99,
   no line over 100, no forbidden proof escape or resource option, no
   `EuclideanSpace`. Copyright, module, public imports, module docstring and
   public exposed section are present. Only Mathlib and Basic are directly
   imported. Recursive project import scan: 64 modules, 47 manifested frozen
   definitions, all SEALED; zero providers and zero DRAFT_SORRY imports.

6. `git diff --check 6874491..HEAD`: exit 0. No package whitespace errors.
   `git diff --check inp...HEAD`: exit 2, inherited trailing whitespace at
   `docs/tracks/P/audits/P23-12-handoff.md:28`; see N2.

## Notes, limitations and disposition

**N1 — identity/products API boundary (informational).** Design row 443 lists
“rnd_def, analytic_zero_null, generic, identity/products”. Blueprint p10:33 says
“Then g=g1⋯gr not identically zero”; the signature's `generic` returns the
common nonzero locus rather than an explicitly named product theorem. There
is no product or separate identity signature in P810Signatures.lean. The identity
input is used directly from Mathlib at line 214. To verify that this does not
leave a substantive product proof unpaid, the independent probe elaborated:

```lean
example {d r : ℕ} {B : Set (Vec d)} (hB : IsOpen B) (hBc : IsConnected B)
    {f : Fin r → Vec d → ℝ} (hf : ∀ j, AnalyticOnNhd ℝ (f j) B)
    (hne : ∀ j, ∃ x ∈ B, f j x ≠ 0) :
    ∃ x ∈ B, ∏ j, f j x ≠ 0 := by
  obtain ⟨x, hx⟩ := hBc.nonempty
  have hc := (generic hB hBc hf hne).2.1 hx
  obtain ⟨y, hyB, hyg⟩ := (mem_closure_iff.1 hc) B hB hx
  exact ⟨y, hyB, Finset.prod_ne_zero_iff.mpr (fun j _ => hyg.2 j)⟩
```

This supplies every premise from the exact source contract, including nonempty B
when r=0. The finite-product zero/nonzero equivalences are elementary real field
facts. The package can serve the product step; do not record a separately named
production export which does not exist. A future consumer may either compose
this proof or add a distinct convenience lemma. This is a reporting/API note,
not a refutation of either exact design theorem.

**N2 — literal branch comparison is broader than assigned package.** Required
`git diff inp...HEAD` warns:

```text
warning: inp...HEAD: multiple merge bases, using 6f2cb1ec6284a98aaffeed74340762f20f4afc04
```

Both merge bases are `6f2cb1ec6284a98aaffeed74340762f20f4afc04` and
`408ea7a6f026a1ecf1d0cf0e988bdc54494497f9`. Git's selected comparison contains
22 files, 3721 insertions, including inherited averaging, PGAssembly/PGMeasure
modules and audit documents. In particular,
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**:
KAM.lean has 12 inherited import additions. Frozen files, manifest and README
have no changes in that comparison. This literal branch-wide hygiene condition
is therefore **not satisfied**; it must not be reported as an empty diff.

The package attribution check `git diff --stat 6874491..HEAD` reports only
AnalyticZeros.lean (258 additions), and
`git diff 6874491..HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
Both package commits touch only the assigned file. Given the explicit instruction
to audit ONLY AnalyticZeros*.lean, the inherited root delta and trailing whitespace
are recorded as branch integration notes rather than attributed to this package.
This report is not an all-branch hygiene PASS.

**Proof-plan deviation.** The design proposes dimension induction with rational
boxes (lines 332–333); the implementation uses derivative-order induction and
countably many open neighbourhoods. Both prove the exact same null-set theorem;
all measure and analyticity obligations are discharged. No changed source premise,
carrier, definition, constant dependence or weakened theorem signature was found.

Suspected new blueprint/source defects: none. Documentation discrepancies:
stale audit-file locators in the handoff and the unnamed identity/products API
boundary above. No errata ledger was edited. No frozen anchor closure is claimed.

## Final artifact integrity

Only this report was written in the tracked source tree by the auditor. The
pre-existing untracked S10-Z-handoff.md was preserved. Temporary type/body,
product-consumption and axiom probe and replay/lint logs were removed from
`.lake/abi-scratch/` after their results were recorded. The audited production-file
hash is unchanged. No state-changing git command was used. The report has no
trailing whitespace or unresolved result placeholders.

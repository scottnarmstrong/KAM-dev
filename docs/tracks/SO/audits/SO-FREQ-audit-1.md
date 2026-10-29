# SO-FREQ independent audit 1

Date: 2026-10-29. Verdict: **PASS WITH NOTES** for the signed SO-FREQ slice.
All three theorem exports pass; no frozen theorem is supplied or sealed by this package.
The notes concern generated-root staleness and an inconsistent sentence in the handoff,
not a missing premise or an unsound proof.

## Scope and authority

Audited only `KAM/Certificate/Freq.lean` and `KAM/SpinOrbit/Freq.lean` at
`6c395ff85d04bde7f811d86829eb8b360dd3a365`, comparing the complete `git diff inp...HEAD`;
`inp` resolved to `1c8cbfd1dad1fca3fb7260162646d619ac2a5a50`.
The diff adds precisely these two files (107 and 45 lines).
The pre-existing untracked `docs/tracks/SO/audits/SO-FREQ-handoff.md` was read, not edited.
The user's explicit worktree report destination overrides the generic brief's MAIN-worktree
destination. No repository source or generated file was edited.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the named package-audit brief,
the handoff and its AUDIT FOCUS, and the SO plan and Revision 3 design at their supplied paths.
The SO package has no corresponding I/N/P frozen theorem or blueprint node to seal;
the controlling declaration contract is the SO draft/design slice.

Contract sources:

- `/root/code/KAM-inp/.drafts/design/SOSignatures.lean`: lines 753–756, 853–863,
  1254–1260; SHA256 `4998870ab6e4f1d8dd8da16a7a01f71b733e7b842b80894e8beedf57d6304fb8`.
- `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`:
  F1, §1.10, §6, SO-FREQ package row, Appendix A §G and §I;
  SHA256 `450c56117fc73335025d3b6fe5cbb7cedc91a7ba94b4e7d61305adaea1f940fc`.
- `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md`: lines 3–5 fix
  `g = (√5 − 1)/2` and `ν± = 1 ± 1/(40+g)`.

## Declaration coverage

Names below are in `KAM.Certificate` except the indicated `KAM.SpinOrbit` names.
Every new declaration, including the two private lemmas, is listed.

| Node / slice | Declaration and source line | Verdict | Reason |
| --- | --- | --- | --- |
| F1 box carrier | `FreqBox`, Certificate/Freq:32 | PASS | Signed abbreviation and body identical. |
| F1 box semantics | `FreqEncloses`, Certificate/Freq:35 | PASS | Signed binders, proposition and body identical. |
| §G exact algebraic vector | `algFreq`, Certificate/Freq:39 | PASS | Signed binders and polynomial body identical; exact real coordinates. |
| §G interval implementation | `algTermLo`, Certificate/Freq:44 | PASS | Sign-dependent lower endpoint. Fresh helper name. |
| §G interval implementation | `algTermHi`, Certificate/Freq:47 | PASS | Sign-dependent upper endpoint. Fresh helper name. |
| §G interval implementation | `algRowLo`, Certificate/Freq:50 | PASS | Sum of the term lower endpoints over the actual row. |
| §G interval implementation | `algRowHi`, Certificate/Freq:54 | PASS | Sum of the term upper endpoints over the actual row. |
| §G Boolean checker | `checkAlgBox`, Certificate/Freq:59 | PASS | Exact signed interface; checks shape, nonnegative lower bound, and every coordinate enclosure. |
| §G private proof | `algTerm_bounds`, Certificate/Freq:65 | PASS | Powers monotone on the nonnegative interval; negative coefficients reverse inequalities. |
| §G soundness | `algFreq_encloses`, Certificate/Freq:82 | PASS | Exact signed theorem; only `hx` and passing-check premise; kernel replay and axiom check pass. |
| §I private expansion | `KAM.SpinOrbit.algFreq_two`, SpinOrbit/Freq:26 | PASS | Expands the literal two-row polynomial vector, with no premise. |
| §I lower frequency | `KAM.SpinOrbit.lunarFreqMinus_eq`, SpinOrbit/Freq:31 | PASS | Exact signed normalized vector and coefficients; kernel replay and axiom check pass. |
| §I upper frequency | `KAM.SpinOrbit.lunarFreqPlus_eq`, SpinOrbit/Freq:38 | PASS | Exact signed normalized vector and coefficients; kernel replay and axiom check pass. |

All seven signed declaration headers were compared directly as strings, including binder
names/order, constants and whitespace, through `:=`. `algFreq`'s local `noncomputable`
modifier replaces the draft's surrounding `public noncomputable section`; it changes no
signature or denotation. The three prescribed definition bodies (`FreqBox`, `FreqEncloses`,
`algFreq`) were also compared as strings and match. Fresh Lean examples copied every signed
interface and applied the corresponding implementation, including `algFreq_encloses hx h`.
The three theorem exports also passed `type_of%` probes. There are no provider exports or
frozen seal bodies here, so the provider/frozen equality and seal-copy checks are inapplicable.

The assigned slice is complete: box carrier and semantics, exact polynomial denotation,
computable checker and its soundness, and both lunar identities are present. Root enclosures,
actual lunar certificate boxes and `lunar{Lower,Upper}Cert_freq` are explicitly other modules
in the design; this result does not establish a passing torus certificate or lunar confinement.

## Definition classification and proof review

- `FreqBox`: intended finite rational centre/radius data, with no hidden proof field.
- `FreqEncloses`: intended coordinatewise real inequality on its entire `Fin n` carrier.
  As signed, a missing box entry denotes `(0,0)` and extra entries are ignored. These are
  explicit total semantics, not a substituted carrier; `checkAlgBox` separately requires
  `box.length = n`. Negative radii cannot enclose any actual real coordinate.
- `algFreq`: intended polynomial evaluation for every real `x`. Missing coefficient rows
  mean the zero polynomial; excess rows beyond `n` are ignored. The inner `getD j 0`
  is used only for `j < row.length`. No hypothesis is hidden in this definition.
- `algTermLo/Hi`, `algRowLo/Hi`: total rational arithmetic functions. Their endpoint
  interpretation is used only when `0 ≤ lo ≤ x ≤ hi`, as documented and proved.
- `checkAlgBox`: executable rational comparisons and a finite conjunction, with no
  noncomputable or assumed correctness component. The nonnegative-lower-bound check is
  essential and present. There is no explicit `lo ≤ hi` check; the theorem's `hx` supplies
  it whenever soundness is consumed. An empty interval therefore gives no counterexample.

For the soundness theorem, the passing Bool supplies `0 ≤ lo` and both rational bounds
at every `i.val < n`. `algTerm_bounds` proves the two signed monomial inequalities;
finite summation gives the polynomial bounds, exact rational casts preserve order, and
`abs_le` plus linear arithmetic gives the signed `FreqEncloses` conclusion. The proof
does not need the shape equality because the signed enclosure predicate already uses
total indexing; checking it remains faithful to the checker contract.

The lunar identities expand `algFreq` on `[[a,b],[c]]`, use the landed exact
`lunarNuMinus_eq`/`lunarNuPlus_eq`, and finish by ring identities. They do not replace
an irrational frequency with a rational centre. There are no additional hypotheses,
instances, bundled conclusions, widened constant dependencies or weakened conclusions.

## Independent validation

All Lean/Lake invocations below were serial and used `LEAN_NUM_THREADS=1` and `nice -n 5`.
The gate supplies `nice -n 5` for its build. No heartbeat, recursion or synthesis override
was used. No clean/update/cache download or `.lake/packages` mutation was performed.

### Targeted build

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sofreq KAM.Certificate.Freq KAM.SpinOrbit.Freq
[inp-gate] slot 2 acquired 12:21:53 for KAM.Certificate.Freq KAM.SpinOrbit.Freq
Build completed successfully (2197 jobs).
exit 0
```

### Signature, application, normalization and edge-case probe

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/sofreq-audit-1/Probe.lean
'KAM.Certificate.algFreq_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarFreqMinus_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarFreqPlus_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

These are all three new public theorems. The successful probe also proved that twice each
algebraic vector is exactly `![lunarNuMinus, 1]` or `![lunarNuPlus, 1]` respectively.
Kernel `decide +kernel` checked these cases:

```lean
checkAlgBox 1 [[1, -2, 3]] 1 2 [(6, 8)] = true
checkAlgBox 1 [[1]] (-1) 1 [(1, 0)] = false
checkAlgBox 1 [[1]] 0 1 [] = false
checkAlgBox 1 [[1]] 0 1 [(1, -1)] = false
checkAlgBox 0 [] 0 1 [] = true
checkAlgBox 1 [] 0 1 [(0, 0)] = true
```

The final probe emitted only unused/unnecessary tactic-sequencing warnings on its two
normalization examples (lines 36 and 41), with no package warnings or errors.
During probe development an extraction regex initially missed the local `noncomputable`
modifier and did not create a file; its attempted invocation reported the missing file.
A subsequent draft probe needed `ring` for normalization and kernel reduction for imported
definitions (`decide +kernel`, not `native_decide`). These probe-only failures were corrected
before the successful run above. No source change was needed. Probes were deleted afterward.

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Freq KAM.SpinOrbit.Freq
replaying KAM.SpinOrbit.Freq
replaying KAM.Certificate.Freq
exit 0
```

Both modules were passed together in the required single invocation.

### Imports and hygiene

Recursive inspection of project imports gave exactly:

```text
KAM.Certificate.Freq
KAM.Certificate.QuadraticDiophantine
KAM.Frozen.Defs.IsDiophantine
KAM.SpinOrbit.Freq
```

The sole frozen import is the definition `KAM.IsDiophantine`, manifest state `SEALED`.
No provider or `DRAFT_SORRY` module is imported. Definitions, lemmas and proofs stay in
`KAM.Certificate` or `KAM.SpinOrbit`; no root declaration is introduced. A repository-wide
declaration search for every new public short name found only its own declaration;
in particular the four new interval-helper short names are unique.

Both files have copyright, `module`, public imports, module docstring and exposed public
section. Certificate/Freq has 107 lines, maximum width 99 Unicode characters;
SpinOrbit/Freq has 45 lines, maximum width 97. Direct scans found no `sorry`, `admit`,
`axiom`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace` or `set_option` in either file.

```text
git diff --check inp...HEAD
exit 0; no output

git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
exit 0; no output
```

### Repository lint

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1296 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only lint failure is the generated-root exception expressly allowed by the audit brief.
There was no forbidden-token, line-width, file-size, module, errata-render, frozen-anchor
or ABI failure. The generated root was left untouched.

## Suspected defects, discrepancies and limits

1. **Handoff normalization wording.** `SO-FREQ-handoff.md:30` asks to check
   “the lunar frequency is EXACTLY (nu, 1)”. The signed statements instead identify
   `(ν±/2, 1/2)` with the polynomial vectors, exactly as implemented at
   `SpinOrbit/Freq.lean:31–39`. Design §6, lines 302–306, explicitly uses `s = 2`
   and a box for `(ν±/2, 1/2)`. Thus the physical frequency is exactly `(ν±,1)`
   after multiplication by `s = 2`; the base vector itself is not `(ν±,1)`.
   The independent probe proved this scaling equality. No silent change of normalization
   was made; the code passes the signed contract, with this handoff wording correction.
2. **Handoff golden-ratio wording.** The same line says “g the golden ratio”. The landed
   `QuadraticDiophantine.lean:30` defines `lunarG = (Real.sqrt 5 - 1)/2`, the conjugate
   convention explicitly fixed by the plan at lines 3–5, not `(1+√5)/2`.
   `lunarNuMinus`/`lunarNuPlus` at lines 33–37 have exactly the plan's denominators.
   The audited identities use these landed definitions unchanged. Substituting the other
   golden-ratio convention would change the exact frequencies and is not justified.

No suspected defect in a pinned mathematical source or in the signed SO-FREQ statements
was found. No deviation was introduced. Endpoint helpers are conservative interval
arithmetic, not a completeness claim about all true enclosures. The package does not prove
certificate data, the full black box, or the final confinement theorem. No frozen files,
manifest entries, generated root or README were changed.

# SO-ROTDIO independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-sorotdio`, branch `inp-sorotdio`.
Audited HEAD: `98a2bc31512e85ee1038217afae5c8d765de8fdb`.
Comparison ref `inp`: `f8405551c09bb7baf63ad01547cc2ecb8d372bbc`.

**Overall verdict: PASS WITH NOTES.** All five signed declarations PASS. The only hygiene
exception is the stale generated `KAM.lean`, expressly allowed by the audit brief. No frozen
anchor is proved or sealed by this helper package; provider/frozen seal-readiness is not applicable.

## Authority and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and
`docs/tracks/SO/audits/SO-ROTDIO-handoff.md`. The explicit AUDIT FOCUS limits the implementation
audit to `KAM/Certificate/DiophantineTransfer.lean`; the fixed signatures are in
`/root/code/KAM-inp/.drafts/briefs/offload-main/SO-ROTDIO.md` (Lean block).
Cross-checked the same five signatures in Revision 5 of
`/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md:2046-2084`,
and O5 at `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md:73-94`.
These are the governing SO helper contracts; unrelated I/N/P blueprint nodes and anchors are
outside this expressly restricted audit. This report's absolute destination follows the user's
explicit override of the generic brief's main-worktree destination.

Read the landed `KAM/Certificate/QuadraticDiophantine.lean` and frozen
`KAM/Frozen/Defs/IsDiophantine.lean`. The latter uses precisely the integer-index l1 sum and
real exponent requested by the fixed signatures. Its manifest entry `kam.IsDiophantine.v1`
is a SEALED definition. No replacement Diophantine predicate is introduced.

Inspected the complete `git -C /root/code/KAM-inp-sorotdio diff inp...HEAD`:
exactly one new file, `KAM/Certificate/DiophantineTransfer.lean`, 131 lines.
Initial status contained only the pre-existing untracked handoff. Repository edits by the
auditor are restricted to this report; temporary probes/logs were placed under
`.lake/abi-scratch/` and removed after recording the results.

## Declaration-by-declaration verdict

All locators below refer to `KAM/Certificate/DiophantineTransfer.lean`.
Public names are fully qualified under `KAM.Certificate`.

| Node / contract | Lean declaration | Verdict | Reason |
|---|---|---|---|
| Generic index transfer | `KAM.Certificate.isDiophantine_of_index_map` (28–50) | PASS | Exact fixed signature, including implicit arbitrary `n m : ℕ`, real `γ τ C`, binder order, all eight explicit inputs, and conclusion `IsDiophantine (γ / C ^ τ) τ ω'`. No additional premise or dimension restriction. |
| Rotated lunar minus | `KAM.Certificate.lunarNuMinus_rot_isDiophantine` (106–109) | PASS | Exact premise-free signature: constant `1/42`, exponent `1`, vector `![lunarNuMinus - 1, 1]`; applies landed minus SO-DIO theorem. |
| Rotated lunar plus | `KAM.Certificate.lunarNuPlus_rot_isDiophantine` (112–115) | PASS | Exact premise-free signature: constant `1/42`, exponent `1`, vector `![lunarNuPlus - 1, 1]`; applies landed plus SO-DIO theorem. |
| Rotated half minus | `KAM.Certificate.lunarNuMinus_rot_half_isDiophantine` (118–122) | PASS | Exact premise-free signature: constant `1/84`, exponent `1`, vector `![(lunarNuMinus - 1) / 2, 1 / 2]`; applies landed half-minus theorem. |
| Rotated half plus | `KAM.Certificate.lunarNuPlus_rot_half_isDiophantine` (125–129) | PASS | Exact premise-free signature: constant `1/84`, exponent `1`, vector `![(lunarNuPlus - 1) / 2, 1 / 2]`; applies landed half-plus theorem. |
| Private index definition | `rotIdx` (53) | PASS | Total intended map `k ↦ ![k 0, k 1 - k 0]` on all `Fin 2 → ℤ`. |
| Private full-vector transfer | `rot_transfer` (55–78) | PASS | Proves nonzero preservation, dot identity and norm factor `2` before applying the generic theorem; real exponent `1` simplifies. |
| Private half-vector transfer | `rot_half` (80–103) | PASS | Separately proves the corresponding three map properties with the half vector; no extra analytic or arithmetic assumptions. |

**Slice completeness and exactness.** A source comparison extracted each public declaration
header up to `:=` and compared it character-for-character with both the fixed brief and
Revision 5's stand-ins. All five matched. The source has exactly those five public declarations,
inside `namespace KAM.Certificate`, and three private helpers. No public name is added or omitted.
A fresh Lean probe also checked full elaborated type equality in both directions (see below).

## Definitions, premises and proof soundness

The only new definition is private `rotIdx`. There are no new public definitions, abbreviations,
structures, instances, bundled assumptions or fallback branches. Vector notation supplies both
coordinates on the entire two-element carrier; no junk value is used outside an intended domain.

The generic hypotheses are legitimate independent side conditions: `hω` is the source
Diophantine estimate, `hγ` controls division monotonicity, `hτ` controls real-power monotonicity,
`hC` controls positive scaling, and `T`, `hT`, `hdot`, `hnorm` specify the integer-index map and
its properties. None assumes the target Diophantine estimate or an equivalent analytic result.
Linearity, injectivity on the whole carrier, invertibility, and positive dimensions are not assumed.

For nonzero `k`, the proof applies `hω` to the nonzero `T k` and rewrites the dot product by
`hdot`. It proves `S_T = ∑ i, |(T k i : ℝ)| > 0` by a nonzero coordinate. Then
`S_T ^ τ ≤ (C * S_k) ^ τ = C ^ τ * S_k ^ τ` follows from `hnorm`, `hτ`, and nonnegative bases.
Positive `S_T ^ τ` and nonnegative `γ` justify
`(γ / C ^ τ) / S_k ^ τ ≤ γ / S_T ^ τ`. This gives exactly the desired inequality with the
frozen real-power convention. There is no hidden `τ > 0`, `γ > 0`, `C ≥ 1` or `n,m ≥ 1` premise.
In particular `τ = 0` and `γ = 0` are covered. If `m = 0`, the conclusion has no nonzero indices;
if `n = 0` and `m > 0`, `hT` is impossible, exactly as the stated side condition requires.

For the two-dimensional map, `T k = 0` forces first `k₀ = 0` and then `k₁ = 0`.
The dot identity is `k₀ x + (k₁ - k₀) = k₀ (x - 1) + k₁`, with the same identity divided by
`2` for the half vectors. The triangle inequality gives
`|k₀| + |k₁ - k₀| ≤ 2 (|k₀| + |k₁|)`. The four applications use exactly the landed
`lunarNu{Minus,Plus}_isDiophantine` and `lunarNu{Minus,Plus}_half_isDiophantine`, then prove
`(1/21)/2 = 1/42` or `(1/42)/2 = 1/84` by `norm_num`.

## Independent checks and exact output

Every Lean/Lake command below ran serially with `LEAN_NUM_THREADS=1` and `nice -n 5`;
no second such job was started before the preceding one exited. The lint ABI subprocess
inherited these settings. No heartbeat, recursion-depth or synthesis-budget override was used.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sorotdio KAM.Certificate.DiophantineTransfer
```

Exit **0**. Output:

```text
[inp-gate] slot 1 acquired 14:59:25 for KAM.Certificate.DiophantineTransfer
Build completed successfully (2194 jobs).
```

No warnings. This is the targeted gate using the existing build overlay, not a clean rebuild.

### Elaborated signature and axiom probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SORotDioAudit.lean
```

Exit **0**, no warnings or errors. The probe imported only
`KAM.Certificate.DiophantineTransfer`, opened `KAM` and `KAM.Certificate`, and placed fresh
declarations in namespace `SOAuditRotDio`. For each signed header, copied literally from the
fixed brief, it renamed only the theorem to `signature_0` through `signature_4` and supplied
`by exact KAM.Certificate.<export>`; for the generic theorem the application listed exactly
`hω hγ hτ hC T hT hdot hnorm`, in order. It then checked:

```lean
example : type_of% @KAM.Certificate.<export> := @signature_i
#print axioms KAM.Certificate.<export>
#check @KAM.Certificate.<export>
```

Thus each fresh statement accepts the implementation, and each implementation type accepts
the fully explicit fresh declaration. There is no provider or frozen theorem to perform a seal
probe against in this package; these probes perform the corresponding fixed-contract check.
The axiom output was exactly:

```text
'KAM.Certificate.isDiophantine_of_index_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinus_rot_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlus_rot_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinus_rot_half_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlus_rot_half_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`#check @...` displayed all five expected types. No `sorryAx` or additional axiom occurs.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.DiophantineTransfer
```

Exit **0**. Complete output:

```text
replaying KAM.Certificate.DiophantineTransfer
```

This single invocation replays the only new module, including all private helpers.

### Name, source and import hygiene

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sorotdio KAM.Certificate.DiophantineTransfer
```

Exit **0**:

```text
short-name check OK (no reused public short name)
```

Because the supplied checker exempts signed names, an additional Python scan applied its
comment-aware declaration extractor to all other KAM and Mathlib files **without signed-name
exemptions**. It found no collision for any of the five public short names. Inspection found
no root declaration or harmful root shadow: the only public namespace is `KAM.Certificate`.

A comment-masked scan using `scripts/check_lean_modules.py` found no `sorry`, `admit`, `axiom`,
`unsafe`, `opaque`, `EuclideanSpace`, `native_decide`, `set_option`, or `_root_` in the new file.
The file has **131 lines**, maximum **99 Unicode characters per line**, and the required
copyright, `module`, `public import`, module docstring and exposed `public section`.

Recursive inspection of the local import closure found exactly:

```text
KAM.Certificate.DiophantineTransfer
KAM.Certificate.QuadraticDiophantine
KAM.Frozen.Defs.IsDiophantine
```

All remaining imports are Mathlib. There is no imported provider or frozen theorem, hence
no imported DRAFT_SORRY anchor. The sole imported frozen definition is SEALED in the manifest.

### Repository lint and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the generated-root exception explicitly permitted by the brief.
Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1314 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No other lint diagnostics occurred. Module formatting, frozen-anchor integrity and all
144 frozen declaration ABI hashes pass. `KAM.lean` was not regenerated or edited.


```sh
git -C /root/code/KAM-inp-sorotdio diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git -C /root/code/KAM-inp-sorotdio diff --check inp...HEAD
git -C /root/code/KAM-inp-sorotdio diff --exit-code
```

All exit **0**, no output. Frozen files, manifest, generated root and README have no package
changes. The last command confirms no tracked worktree modification. The final status adds
only this report to the pre-existing untracked handoff; the auditor made no git mutation.

## Defects, deviations and limits

No suspected source or blueprint defect was found in the audited slice. No implementation
deviation from the five fixed signatures was found. The argument is elementary index transfer
against the landed frozen predicate and SO-DIO results; no external source repair is needed.
The report introduces no code changes. The stale generated root is the sole permitted hygiene
note. No unresolved mathematical uncertainty was identified within this package's scope.

This verdict covers the generic transfer and the four rotated lunar bounds. It does not assert
completion of the numerical certificate, the rotated Hamiltonian construction, a barrier or
confinement theorem, or sealing of any campaign anchor.

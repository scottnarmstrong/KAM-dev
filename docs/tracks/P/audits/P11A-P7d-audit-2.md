# P11A-P7d independent package audit 2

Date: 2026-10-29 UTC. Scope: round-2 delta audit of P7db, independently performed
in `/root/code/KAM-inp-p11ap7d`. Audited HEAD:
`d826cbe80c6d2de6533eb8b14e30333e24257acb`.

## Verdict and comparison boundary

**PASS WITH NOTES** for the P7db slow-assembly delta and its signed exports.
The stronger smallness is discharged from source data, both divisor conversions
are sound, no SIGNED declaration or `avg_slow_of_spec` statement changed, and all
five focused files have lines of at most 100 characters. No provider or frozen
anchor is implemented or sealed by this slice; frozen-type and seal-body probes
are inapplicable. This is infrastructure verification, not P-FIXED closure.

Read: AGENTS.md, PLAN.md, DECISIONS.md, the external package-audit brief, handoff,
round-1 report, track-P statement, the relevant frozen planetary headline anchors,
P11A-LEAN-DESIGN node table, signed P11ASignatures.lean:979-1044, and blueprint-P
p11-cp09-preparation.tex:170-185. Imported frozen definitions were checked against
the manifest: all 64 are SEALED; the project import closure has 372 modules and
contains no provider or frozen theorem.

The requested `git diff inp...HEAD` was inspected for the package, together with
the full changed-path/size inventory (87 files, 12143 insertions, 291 deletions).
Current `inp` is `0190e50c1424a2513c11a9e7bb51b8e9d8e0763a`. Git reports:

```text
warning: inp...HEAD: multiple merge bases, using 64ef7ba1c0803ab6393d221b73d1f7f1c01cad2b
```

Consequently the comparison includes unrelated inherited integration work and
52 additions to generated `KAM.lean`. The brief's whole-range protected-path
emptiness condition is **not literally satisfied**: only `KAM.lean` differs;
`KAM/Frozen`, `manifest`, and `README.md` do not. These generated-root edits
predate P7db (e.g. 3fcfb654, 62205e2c and earlier regeneration commits).
`git diff 01c51946 HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
They are recorded as inherited comparison noise, not attributed to this delta.
No generated file was repaired.

The exact delta was also inspected against `01c51946` and across
`7cd373f3` -> `11a05936`. The P7c merge brings SlowDivisor/SlowSmall changes;
the adaptation commit changes ONLY SlowAssembly.lean (17 insertions, 4 deletions).
The other four focused files are byte-identical to `01c51946`. All five are
unchanged between `11a05936` and current HEAD. The round-1 report itself says
it checked the final adaptation and records the same hashes; this conflicts
with its enclosing commit's “pre-P7db version” label. This audit uses independent
checks and the explicit commit boundary, not that label as validation evidence.

## Declaration and node review

Names are in `KAM.Planetary`; locators abbreviate Preparation file names.
Unchanged entries were compared to the baseline and revalidated through the facade.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| Smallness | `p11_slow_eventually`, SlowAssembly:35-72 | PASS | Conclusion strengthened from delta0/2 to delta0/4; supplied by source-derived `slow_R4_eventually`. No new premise. |
| Fixed constant | `p11SlowAsmC`, SlowAssembly:75-80 | PASS | Unchanged maximum of explicit constants, independent of epsilon. |
| Assembly | `p11_slow_at`, SlowAssembly:83-178 | PASS | Conditional helper explicitly requires the stronger smallness; final core supplies it. New hdiv0/hdiv conversion is sound. |
| bpP:p11:avg-slow core | `avg_slow_of_spec`, SlowAssembly:182-201 | PASS | Statement and body unchanged; all eventual conditions are proved before selecting a common positive threshold. |
| as-concl mean | `p11_torusAverage_natAdd`, SlowCoeff:31 | PASS | Unchanged product-torus integral identity. |
| as-concl zero mode | `p11_slow_coeff_zero`, SlowCoeff:53 | PASS | Unchanged native mean cancellation gives `(eps*MF)^3`; cf0 is MF^3. |
| as-nr bracket | `p11_C_norm_le`, SlowMW:29 | PASS | Unchanged source mean bound. |
| as-nr uniform bound | `p11SlowMW`, `p11SlowMW_nonneg`, `p11_slow_MW`, SlowMW:53-98 | PASS | Unchanged epsilon-independent bound, with eta1 <= 1 supplied by the eventual lemma. |
| SIGNED spec | `P11SlowSpec`, SlowSigned:26 | PASS | Exact signed body modulo whitespace; kernel rfl equality to the parametric spec. |
| SIGNED bpP:p11:avg-slow | `avg_slow`, SlowSigned:90 | PASS | Exact signed type; no new premise. |
| SIGNED constant | `p11SlowConstant`, SlowSigned:102 | PASS | Exact signed choice and fallback body. |
| SIGNED datum | `p11SlowData`, SlowSigned:105 | PASS | Exact signed choice and default body. |
| as-osc | `p11_slow_osc`, assembly o1-o12 | PASS | Unchanged P7b supply; identities, holomorphy, jets, reality, periodicity and weighted bound retained. |
| as-nr | `p11_slow_divisor`, assembly hdiv0/hdiv:136-152 | PASS | Strong pure/mixed bounds proved before weakening; literal mixed delta0/2 remains established. |
| as-b2 | eventual bound and hb2':157-163 | PASS | Unchanged B2 proof uses the actual chosen constant and cutoff. |
| as-concl | `p11_slow_conclude`, assembly:164-173 | PASS | Quarter divisor accepted on the exact domain and retained in the signed spec; other inputs unchanged. |
| Facade | Slow.lean | PASS | Unchanged exports; no new names or import regressions. |

All five nodes mapped to Preparation/Slow at design:171-175 remain accounted for.
All 26 outer conjuncts of the signed spec remain supplied: first three by the
restricted o1-o3, fourth by o4, fifth by o6 and constant monotonicity, sixth by
hdiv, and the remaining conjuncts by hU from p11_slow_conclude.

## Stronger smallness and conversion

Let K = p11K2 C nu eps, delta0 = C.gamma*K^(-C.tau), and
R = min (p11s1 C eps/4) (pi*C.rz^2/32).
SlowSmall:331-338 obtains `eps*K*MW <= delta0*R/4` by applying the existing
`slow_R_eventually` to `2*MW`, whose nonnegativity follows from MW >= 0,
and dividing the resulting inequality by two using linarith. The underlying
lemma (SlowSmall:258-314) derives its positive constants from `fast_consts hC`,
`1 <= nu`, and `eventually_eps_log_le`; it does not assume a limiting estimate.

SlowAssembly:70 instantiates MW with `p11SlowMW C`, using its proved
nonnegativity. The eta1 estimate at :50-68 comes from `p11eta1_source_rate hC`.
The final core at :187-201 fixes c0 and c before epsilon, extracts an interval
from the eventual result, then takes the minimum with the oscillation and fast
thresholds and 1/2. Thus the stronger `hs` of the conditional helper is derived
from the same source premises. No conclusion-shaped premise reaches the core.
The omission of P11SecularHReal is unchanged and valid: the invoked oscillation
lemma uses hC, and the needed reality facts are its proved outputs.

SlowDivisor:271-290 now returns pure-slow `eps*(3/4*delta0)` and mixed
`delta0/2`. Assembly:140-152 proves delta0 >= 0 from gamma >= 0 and K > 0,
then establishes the exact divisor input of p11_slow_conclude:

- Pure slow: `eps*gamma/4*K^(-tau) = eps*delta0/4 <= eps*(3/4*delta0)`;
  eps > 0 makes multiplication preserve the comparison. This is the nlinarith
  branch using `mul_nonneg heps.le hδ`.
- Mixed: `gamma/4*K^(-tau) <= delta0/2` is precisely
  `p11_slow_alpha1_le_half`; linarith handles the factor 1.

The split tests the identical fast-index projection, with the same I, k,
nonzero condition and cutoff. No eps factor is dropped in the pure case or
introduced in the mixed case. A separate fresh Lean arithmetic probe checks
both cases at arbitrary positive eps and K and nonnegative gamma.
`hdiv0` preserves the literal blueprint bound before `hdiv` weakens it.
Both p11_slow_conclude and the exact signed spec require only this quarter bound.

MW = p11SlowMW C and cf0 = C.MF^3 remain independent of epsilon; replacing MW
by 2*MW inside the eventual lemma changes only the threshold. No definition,
carrier, metric, norm, or constant dependence changed in P7db.

## Definition classification

No new definition, abbreviation or structure is introduced by P7db.
The focused existing definitions retain their intended whole-carrier behavior:
p11SlowMW is a total arithmetic bound; p11SlowAsmC is a total maximum;
P11SlowSpec is the exact signed proposition. p11SlowConstant uses the signed
choice for nu >= 1 and 1 otherwise. p11SlowData uses a signed witness when one
exists and default otherwise. On the theorem's common positive epsilon interval,
avg_slow supplies the witness for the selected constant; its successful branch
is available. The proof never relies on analytic properties of a default value.

## Independent validation receipts

All Lean/Lake/checker operations were serialized with LEAN_NUM_THREADS=1 and
nice -n 5; the gate script applies nice internally. No clean, cache retrieval,
toolchain change, source repair, or state-changing git command was used.

1. Build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap7d KAM.Planetary.Preparation.Slow
```

Exit 0. Exact gate/final lines:

```text
[inp-gate] slot 2 acquired 01:05:43 for KAM.Planetary.Preparation.Slow
Build completed successfully (9418 jobs).
```

Inherited warnings were replayed; focused warning: deprecated dif_pos at
SlowSigned.lean:98:10 (cosmetic).

2. Fresh signed-body/type, baseline-core, conversion and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP7dAudit2.lean
```

Exit 0. Copied all three signed definitions under fresh names and proved equality
by rfl; copied the signed avg_slow type with body `exact avg_slow D hnu`;
checked signed/parametric spec equality by rfl; instantiated the pre-P7db core
type with the current theorem; checked the arithmetic conversion. Independent
whitespace-normalized signed comparisons and exact baseline-core comparison
all returned True.

Exact axiom output (the local `open Classical` prints `choice`, i.e. Classical.choice):

```text
'KAM.Planetary.p11_torusAverage_natAdd' depends on axioms: [propext, choice, Quot.sound]
'KAM.Planetary.p11_slow_coeff_zero' depends on axioms: [propext, choice, Quot.sound]
'KAM.Planetary.p11_C_norm_le' depends on axioms: [propext, choice, Quot.sound]
'KAM.Planetary.p11SlowMW_nonneg' depends on axioms: [propext, choice, Quot.sound]
'KAM.Planetary.p11_slow_MW' depends on axioms: [propext, choice, Quot.sound]
'KAM.Planetary.p11_slow_eventually' depends on axioms: [propext, choice, Quot.sound]
'KAM.Planetary.p11_slow_at' depends on axioms: [propext, choice, Quot.sound]
'KAM.Planetary.avg_slow_of_spec' depends on axioms: [propext, choice, Quot.sound]
'KAM.Planetary.avg_slow' depends on axioms: [propext, choice, Quot.sound]
'KAM.Planetary.p11SlowConstant' depends on axioms: [propext, choice, Quot.sound]
'KAM.Planetary.p11SlowData' depends on axioms: [propext, choice, Quot.sound]
'KAM.Planetary.slow_R4_eventually' depends on axioms: [propext, choice, Quot.sound]
'KAM.Planetary.p11_slow_divisor' depends on axioms: [propext, choice, Quot.sound]
'KAM.Planetary.p11_slow_alpha1_le_half' depends on axioms: [propext, choice, Quot.sound]
```

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.Slow KAM.Planetary.Preparation.SlowAssembly KAM.Planetary.Preparation.SlowCoeff KAM.Planetary.Preparation.SlowMW KAM.Planetary.Preparation.SlowSigned KAM.Planetary.Preparation.SlowDivisor KAM.Planetary.Preparation.SlowSmall
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.Preparation.SlowSmall
replaying KAM.Planetary.Preparation.SlowDivisor
replaying KAM.Planetary.Preparation.SlowSigned
replaying KAM.Planetary.Preparation.SlowMW
replaying KAM.Planetary.Preparation.SlowCoeff
replaying KAM.Planetary.Preparation.SlowAssembly
replaying KAM.Planetary.Preparation.Slow
```

4. Repository lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the generated-root exception allowed by the brief. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1181 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No substantive lint failure. No generated root was rewritten.

5. Static and protected-path checks:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff 01c51946 HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check
```

All commands exit 0. First command emits the inherited KAM.lean diff and the
multiple-merge-base warning recorded above; second is empty; third is silent.
Focused scans found no forbidden proof escapes, resource overrides or EuclideanSpace.
All declarations are in KAM.Planetary; a comment-masked repository declaration
scan found each focused short name exactly once. Every focused file has the
required module header, imports, documentation and public section.

| File | Lines | Maximum characters per line | SHA256 |
|---|---:|---:|---|
| SlowAssembly.lean | 207 | 96 | `fd82f8a5fb604bbdc83a5d37d03f8f6a7a2599ce592300619a5ea68c095e54f5` |
| SlowCoeff.lean | 136 | 97 | `93c4b2fffa497b8d16ec2ca58fdb17342c66b80046d51fd2c3ee5d871f360672` |
| Slow.lean | 26 | 92 | `db07c52da6015539d636e3404437a6d444696a7ad30a15be24ec05b2de3187cd` |
| SlowMW.lean | 102 | 94 | `3cfdc56ffeaf60b487572a717b019770572e3ce26d2f6b00b6aed0b62df41093` |
| SlowSigned.lean | 110 | 99 | `f5e0b08c92310d01cda3b778d54625a93ea0611997b391519a19370b3b8dc24a` |

## Errata, deviations and limits

No new suspected pinned-source defect, blueprint contradiction, or semantic
deviation was found in the P7db delta. The strengthened unsigned divisor now
establishes the literal mixed half-bound of blueprint:182, then the assembly
weakens it to the signed consumer contract. Existing signature narrowing is
unchanged. The cosmetic deprecated dif_pos warning persists.

The inherited generated-root comparison difference and permitted stale-root
lint exception are reported explicitly above; neither was silently repaired.
Only this report and the temporary probe were authored by this auditor. The
probe was removed after validation. No source, handoff, prior audit, frozen
file, manifest or generated file was edited. HEAD and all five focused hashes
were checked again at completion. The user's exact report path overrides the
generic brief's main-worktree destination.

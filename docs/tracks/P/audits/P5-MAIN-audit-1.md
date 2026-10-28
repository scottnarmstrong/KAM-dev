# Independent P5-MAIN seal-key audit 1

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p5main`.
HEAD: `a454ffb6aa4e83179eb954c753e404f7c91cb64c`.
Comparison ref `inp`: `980388b435b56c1a548f7c9771a8f4c62033aba7`.


**Overall verdict for `planetary.properlyDegenerateKAM.v1`: PASS WITH NOTES.** P5-MAIN supplies the exact frozen theorem type and a proved, prospective seal term with only the three permitted axioms. No blocking Main finding was identified. The proof is ready for the P5-PROV wrapper/integration step; the actual provider is still an empty stub and the manifest anchor remains DRAFT_SORRY. The permitted generated-root lint exception and the previously reported blueprint wording issue are retained below. This is not a claim of an already completed seal.

## Scope and authority

The user's exact report destination overrides the generic brief's main-worktree destination. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the supplied handoff and AUDIT FOCUS, P45 design/node ownership and design audits 1–4, shared signatures, P-G in `docs/tracks/P/statement.md`, blueprint Part 5, the frozen theorem and its actual predicates, `PGData`, and the consumed assembly interfaces. Inspected the full `git diff inp...HEAD`: two new files, Main (140 lines) and inherited Strictness (426 lines). The handoff's “Nothing else touched” describes the Main increment, not the full three-dot diff. Strictness has its own audit; supplemental review and hygiene here cover its presence in this diff without replacing that audit.

Target: `KAM.Planetary.properlyDegenerateKAM`, manifest id `planetary.properlyDegenerateKAM.v1`. Current state is **DRAFT_SORRY**. The provider module `KAM/Provider/Planetary/ProperlyDegenerateKAM.lean` is an empty documented stub: it exports no theorem. This audit evaluates the completed Main proof and the handoff's **prospective** seal. It does not claim that the provider has been implemented or that the anchor is already sealed.

Input fingerprints:

| Input | SHA256 |
|---|---|
| `KAM/Planetary/PGAssembly/Main.lean` | `8dbea1ce8448559ec5e64c05bc1bad5172ad892c3331418f72011a9057c3e39a` |
| `docs/tracks/P/design/P45-LEAN-DESIGN.md` | `a1d2cd226b6b2f6b668f2712e66d6191a9fd6ab4c03ddc5183539f92c72d5dbf` |
| `/root/code/KAM-inp/.drafts/design/P45Signatures.lean` | `586ed2e3188b154d5cc6d44d3f85b420ef85ddd7faaa2bcbb6d6ca6db7d0f304` |
| `blueprint-P/parts/p5-pg-assembly.tex` | `f8a5bc1683f30fed2576d0bb1ab6d51a1e6f00c6bf78c180d5a32efb0cef9968` |

## Declaration and node correspondence

All names below are in `KAM.Planetary`. Main contains exactly three new public theorems and no definitions, abbreviations, structures or instances.

| Node / declaration | Lean declaration and locator | Verdict | Evidence |
|---|---|---|---|
| `bpP:p5:main` | `main`, Main:104–136 | PASS | Complete telescope and conclusion byte-identical to frozen theorem after name replacement, and to signed `main` at shared signatures:1251. Exact-type and prospective explicit-argument seal probes below. |
| unsigned bundled helper | `main_of_data`, Main:48–101 | PASS | Same full conclusion for precisely the bundled frozen inputs; no added source premise or narrower carrier. It supplies every clause of `main`. |
| unsigned ENNReal helper | `ofReal_mul_lt_of_slack`, Main:37–44 | PASS | Elementary strict-product consequence of `x<y`, positive finite nonzero cell mass, positive target and the nonstrict bound. This conditional arithmetic helper does not substitute for a graph theorem. |
| `bpP:p5:order` | `main_of_data`, Main:58–67; inherited data-only choices | PASS | All final constants are chosen before introducing `r,mu`; existential witnesses depend only on `d`. Design:135 explicitly requires no new theorem. |
| `stepP:p5:mn-const` | local to `main_of_data`, Main:58–66 | PASS | `rStar=finalRadius d`, `C=max (pgLoss d+1) Cw`, `c=2*pgTau a b+2=2(a+b)+4`; positivity and radius upper bounds proved. |
| `stepP:p5:mn-given` | local to `main_of_data`, Main:67–69 | PASS | `finalRadius≤pgRstar` supplies preliminary admissibility with the literal logarithmic exponent and the original `mu0` guard. |
| `stepP:p5:mn-set` | local to `main_of_data`, Main:70–95 | PASS | Entire ranges over `D0\B`; sigma compactness supplies measurability and cylinder inclusion. Original torus predicate, Diophantine clause, and both frequency bounds supplied. |
| `stepP:p5:mn-meas` | local to `main_of_data`, Main:96–101 | PASS | Strictness gives positivity and strict upper bound. Strict lower ENNReal inequality uses finite, nonzero cell mass and the positive square-root slack. |
| P5-PROV prospective wrapper | scratch copied frozen telescope, explicit handoff term | PASS (prospective) | Complete telescope with explicit handoff term elaborates; wrapper has not been written in production. |

The design's complete Main ownership slice is exactly `bpP:p5:order`, `bpP:p5:main`, and the four `mn-*` steps (design:135,215–219). Every row is accounted for. There is no unsigned graph-named export asserting a weakened substitute.

### Proof review

`PGData` at `KAM/Planetary/PG/Setting.lean:47` contains the frozen data, typing conditions and source assumptions only. Main:135–136 constructs it in exactly their original order. No prepared normal form, KAM conclusion, torus existence, positive-measure assertion or downstream bound is assumed as input.

`finalRadius` is the minimum of the preliminary positive radius and `((2*(pgLoss+1))⁻¹)^2`, as required by the design. `lower d` proves `pgLoss>0`; the preliminary `rstar` specification proves positivity and both upper bounds. All remain data-only. The additional shrinking is explicit in the design and does not alter the frozen quantifiers. No reliance on the totalized value of an inverse, logarithm, real power or measure conversion occurs outside its proved domain.

For `S=kset d r mu hadm (pgD0 d r mu\B)`, `strictness` supplies sigma compactness of the surviving parameters and the three measure conclusions. `cell_transfer` supplies measurability and cylinder inclusion. For every point in S the same action J and the same whole torus range remain in S (Main:82–84); deleting parameters deletes whole tori. `PGFamilySpec` is a proved witness specification selected through `torus_conv`, not a new input premise.

The frequency is exactly `freq/(2*pi)` once. Membership in `pgD0` already gives the two-scale predicate for that scaled frequency. Positivity of both gamma scales follows from `k0>0`, `r>0`, and `mu>0`; `pgTau=a+b+1>a+b` gives the frozen exponent condition. No second period conversion occurs. Generic `blockFast` and `blockSlow` reduce to the frozen real `fast` and `slow`; taking the maximum C preserves both inequalities, using `mu>0` for the slow bound.

For the measure lower bound, set `x=1-C*sqrt r` and `y=1-(pgLoss+1/2)*sqrt r`. Since `C≥pgLoss+1` and `sqrt r>0`, x<y. Cell mass is finite by boundedness and nonzero by its positive `toReal`. If x≤0, `ofReal x=0` and survivor positivity proves the claim. If x>0, strict monotonicity of `ofReal` and multiplication by finite nonzero cell mass gives the result. Thus ENNReal truncation does not hide an invalid strict inequality at zero or infinity.

### Supplemental inherited Strictness inventory

These declarations occur in the full three-dot diff. Each theorem/instance was included in the axiom probe; the module is included in kernel replay. The signed `strictness` telescope equals its shared signature after whitespace normalization. This supplements, rather than supersedes, its separately assigned P5-ST audit.

| Declaration (Strictness line) | Verdict | Role / reason |
|---|---|---|
| `stParam` (42) | PASS | Unique torus parameter on the raw union; zero off the union, classified below. |
| `stParam_eq` (47) | PASS | Parameter identity follows from the produced family's injectivity. |
| `stParam_preimage` (58) | PASS | Exact parameter preimage identity restricted to the raw union. |
| `stSigma_inter_closed` (72) | PASS | Sigma compactness under closed intersection. |
| `stParam_measurable` (78) | PASS | Closed preimages split into sigma compact raw union and the off-union zero case. |
| `stMeasure` (103) | PASS | Pushforward of volume restricted to the output representative. |
| `stCell_ne_top` (107) | PASS | Finite cell volume from disc formula and bounded V. |
| `stRep_ne_top` (112) | PASS | Cell-transfer equality and finite target cell. |
| `stMeasure_finite` (121) | PASS | Finite restricted measure and finite pushforward; proved instance, not assumed difficulty. |
| `stMeasure_apply` (127) | PASS | Measurable pushforward formula with exact representative. |
| `st_mass` (135) | PASS | Cell mass is `(2*pi)^n` times parameter mass. |
| `stMeasure_compl_D0` (141) | PASS | Restricted mass has no support outside D0. |
| `stMeasure_inter_D0` (147) | PASS | Exact intersection/support identity. |
| `st_mass_real` (152) | PASS | Real form of the mass formula. |
| `st_add` (159) | PASS | Literal countable additivity for disjoint sigma compact parameter subsets. |
| `st_slice_rep_null` (169) | PASS | Hyperplane nullity, Lipschitz image and countable lattice translates. |
| `st_null` (189) | PASS | Cell-transfer form of coordinate-slice nullity. |
| `stMeasure_slice_null` (200) | PASS | Parameter-measure slice nullity. |
| `st_cut_value` (213) | PASS | Continuous finite-measure cut and two monotone endpoint limits imply IVT. |
| `stCell_toReal_pos` (258) | PASS | Positive finite V volume and positive disc factor. |
| `st_ivt` (265) | PASS | Cut mass realizes the minimum of half total mass and half square-root cell slack. |
| `strictness_aux` (328) | PASS | Half-space deletion, both sides sigma compact, exact cut mass. |
| `strictness` (360) | PASS | Real mass split proves survivor positivity, lower slack and strict upper bound; transferred back with finite-mass guards. |

## Definition classification and imports

No new definition in Main. In inherited Strictness, `stParam` is a total function with an explicit zero fallback **only outside** the raw union. The pushforward source is restricted to `outputRepresentative(D0)`, a subset of that union, and `stParam_eq` identifies the genuine parameter there. Its fallback is used solely to prove global measurability, and cannot manufacture mass or change a torus parameter on the measured support. `stMeasure` is the literal pushforward of that restricted volume; no fallback, dummy measure or assumed mass bound occurs. `stMeasure_finite` is a proved instance.

The consumed `kset` and `rawUnion` are whole-range unions; `physicalTorus` uses the proved chart and angle scaling; `pgFamily` chooses a witness of `torus_conv`; `finalRadius` has the literal signed minimum formula. All are intended objects on their carriers. The frozen definitions retain the original Hamiltonian `H0+mu*P`, rotation-invariant oscillator discs, physical fast-angle cell `[0,2*pi)`, original symplectic/dynamical torus predicate, and period-one torus frequency. None is replaced by a weaker local surrogate.

A recursive local-import traversal from Main found **354 KAM modules** and **zero provider or frozen-theorem modules**, including transitively. Only frozen definitions are imported. Thus no imported DRAFT_SORRY theorem, sealed theorem status exception, other provider or theorem-anchor cycle is involved. Repository declaration-site searches find each new Main short name only in Main. All three exports are under `KAM.Planetary`; no root declaration or harmful namespace shadow is introduced.

## Independent validation receipts

All Lean/Lake checks launched by this audit are serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`. The targeted build goes through the required gate. Lint is also run under `nice`, so its ABI Lean subprocess inherits that priority and thread setting. No source or build-resource override was used.

### Targeted build

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5main KAM.Planetary.PGAssembly.Main
[inp-gate] slot 1 acquired 22:32:00 for KAM.Planetary.PGAssembly.Main
Build completed successfully (9400 jobs).
exit 0
```

Lake replayed existing upstream lint/style/deprecation warnings and existing axiom informational messages. No Main warning was reported. This is a targeted overlay build, not a clean/rebuild-from-scratch command.

### Exact type, explicit seal body and axioms

Scratch file: `.lake/abi-scratch/P5MainAudit.lean`, importing the frozen theorem and Main. The exact requested comparison is:

```lean
example : type_of% @KAM.Planetary.properlyDegenerateKAM := @KAM.Planetary.main
```

A second declaration, `KAM.Planetary.prospectiveSeal`, copies the **complete** frozen telescope and conclusion under that fresh name; its entire proof is:

```lean
by exact KAM.Planetary.main ha hb V hV hVc hVb W hW hVW hboundary r0 mu0 B
  hr0 hmu0 hB H0 P P0 Omega beta hP hperiod hfreq hBNF htorsion hsymm
```

Every explicit binder is supplied exactly once, in frozen order; `{a b}` remain implicit. No frozen theorem or provider theorem is used in the proof term. The frozen import is only for comparing types, and the prospective proof's axiom list excludes `sorryAx` despite that scratch import.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5MainAudit.lean > /tmp/maud-p5main-1-probe-fixed.log 2>&1
exit 0
```

The corrected run has no errors or warnings. Its Main/seal axiom output is exactly:

```text
'KAM.Planetary.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.main_of_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ofReal_mul_lt_of_slack' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.prospectiveSeal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same invocation printed axioms for every inherited Strictness public theorem and its finite-measure instance (21 further declarations); **each** returned exactly `[propext, Classical.choice, Quot.sound]`. Full output is in the named log. There is no production provider export to probe or print: the empty stub is explicitly distinguished from the elaborated prospective seal.

Scratch-generation incident: the first run exited 1 because the auditor's initial textual extraction split at the named argument `(b := b)`, truncating the copied telescope. That run proved no prospective-seal receipt. The generator was corrected to split at the outer declaration assignment, the full literal comparisons were rerun, and the successful complete run above replaces that failed scratch run. No production file changed. The full Main telescope equals both frozen and signed text, not just a prefix.

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Provider.Planetary.ProperlyDegenerateKAM KAM.Planetary.PGAssembly.Main KAM.Planetary.PGAssembly.Strictness > /tmp/maud-p5main-1-kernel.log 2>&1
replaying KAM.Planetary.PGAssembly.Strictness
replaying KAM.Planetary.PGAssembly.Main
replaying KAM.Provider.Planetary.ProperlyDegenerateKAM
exit 0
```

This is one invocation. Replay of the empty stub establishes module integrity, not existence of a provider export; Main's actual proof exports are replayed by the same invocation.

### Static integrity

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output)
git diff --check inp...HEAD
(no output; exit 0)
```

Direct scans of both added modules find no forbidden proof escape, `EuclideanSpace`, heartbeat/recursion/synthesis override, line over 100 characters or file over 1500 lines. Main has 140 lines, maximum width 97; Strictness has 426 lines, maximum width 99. Copyright, `module`, public imports, module docstring and exposed public section are present. No reused Main public helper name or root shadow was found.

### Repository lint and ABI

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > /tmp/maud-p5main-1-lint.log 2>&1
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1051 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is the explicitly permitted generated-root exception, “KAM.lean is out of date”. Module checks, frozen-anchor guard and elaborated ABI hashes pass. The generated root was not regenerated or edited. No other hygiene failure was reported.

## Blueprint, source and documentation notes

No new suspected mathematical source erratum or Main deviation was found. The reviewed local blueprint main/order/measure clauses are faithfully implemented. The final-radius shrinking is the design's explicit separation of preliminary admissibility from final strictness; it does not change the theorem's dependency order.

Pre-existing source-contract issue retained: design audit 4, R4-S1, records that `blueprint-P/parts/p5-pg-assembly.tex:30` says the extension is “P~ = P at real points” without the constrained-cylinder guard; line 35's periodicity proof also requires a germ-overlap argument. Taken as agreement with arbitrary exterior total-function values, this is false, as the earlier audit's counterexample shows. The revised design restricts agreement to real points in the closed original cylinder. Main does not assert the false exterior agreement and uses the original frozen Hamiltonian through the proved torus-conversion interface. This is an already reported project-blueprint wording defect, not a newly verified paper erratum, and this audit makes no source correction.

Historical status text is stale: `docs/tracks/P/statement.md:3–4` says “Proposed, not approved, frozen or proved”; the frozen theorem's comment similarly says approval awaits. D20 and the manifest record owner approval. Neither historical comment changes the actual manifest state **DRAFT_SORRY**, and this audit does not edit it.

Uncertainties and limits: no independent rereading of the CP10/CP11 PDFs or re-audit of all upstream package proofs is claimed. The Main seal-key conclusion rests on the direct proof review, its exact interfaces, axiom checks and kernel replay recorded here. The separately assigned Strictness audit remains distinct. Production provider implementation and manifest sealing are later integration steps, outside this report-only task.

## Final integrity and handoff

During the audit the external `inp` ref advanced to `18c2a1317acb2ee9a314d1ad8f2ab2ef840a428f`. The original comparison SHA is pinned at the top of this report. A final `git diff --stat inp...HEAD` still reports exactly the same Main/Strictness additions (566 lines total), but now emits `warning: inp...HEAD: multiple merge bases, using b8f993d23d231733c86a70ab03dc9b362a45f1ea`. The final protected-path comparison emits that same merge-base warning and no diff. Explicit comparison against the original pinned inp SHA independently retains the same two-file inventory. HEAD and the Main SHA256 remain unchanged.

Final `git diff --check` exits 0 with no output. The report has balanced code fences, no trailing whitespace and a terminal newline. `.lake/abi-scratch/P5MainAudit.lean` was deleted after all checks completed. The existing untracked handoff is untouched; the only repository file created by this audit is `/root/code/KAM-inp-p5main/docs/tracks/P/audits/P5-MAIN-audit-1.md`. No tracked source, frozen file, manifest, generated file, signature source or git state was changed.

**Disposition:** PASS WITH NOTES for P5-MAIN / the prospective `properlyDegenerateKAM` seal. Zero blocking findings in the audited Main slice. Integration still needs to populate P5-PROV with the verified exact wrapper and perform the separately controlled seal; this report does neither. No new suspected source errata, proof deviations or unresolved Main uncertainties.

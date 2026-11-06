Audited commit: `4841de21312a29329fcfcc557f3fa3f7eacdfea9` (initial HEAD); SHA256: `KAM/EffectiveStability/Tube/Engine/BrChunk.lean=d5edc286a7f357f285e556c7d5a4a046150848694d0ccf920e899a578bc717c6`; `scripts/sjsu/ledger/br.py=47849d775477e6f76c427d6c1e830474661cea87180cafa71c72ef945159dcbf`; `scripts/sjsu/ledger/bracket.py=6c2b1854be6c717bfb13311b6682f51577fb94fcf690c2c1e75bcec327448536`; `scripts/sjsu/ledger/emit_h.py=30c0d9470c270ce00f471fda26e6aaf8cf48b0b0233778db6aaaae826f9be50e`; `scripts/sjsu/ledger/ledger.py=4b40de84baa54e401c9dfd4818d580477583d41a9ae7a8f9175ab2c9de2f0425`; `scripts/sjsu/ledger/packing.py=2e3a09bce1efaf950c12496882030dee13bb96980ac5b21e1a3b0d309078b655`; `scripts/sjsu/ledger/poly.py=fac11b4a8375786278dd98b9259d8b843f16e31d28a7fe282f222cac8d81071a`; `scripts/sjsu/ledger/produce.py=bea3c18465b0e6b5064028abb37b051a82329d18ea1e66560e340540b943d8c8`.

# N7d / N7-Engine part 4 — audit 1

**PASS WITH NOTES.** The generic chunk theorem is sound and supplies exactly the kept-coefficient conclusion of `Engine/Bracket.brAll_sound`. The emitter requires kernel proofs of actual chunk checks, complete coverage and the total budget; it does not trust a Python-computed bracket norm, float witness or chunk count. Notes concern missing reproducibility inputs and inaccurate documentation. This is a review of the eight first-line files, not acceptance of the generated production ledger, a numerical eta, or the T2-CONF theorem.

## Scope and snapshot

Read the launch, AUDIT-PKG brief, WORKER-RULES, N7 brief, DRAFT handoff, preceding three package audits, AGENTS, PLAN and DECISIONS, and the requested phase-1/ApproxIntegral context. The launch expressly says part 4 is not yet in the handoff; the commit and actual code control this review. Method: focused tier-2 audit, statement/proof pass, producer acceptance trace, separate adversarial checks, then hygiene. No repair was authorized or made. No subagent was used.

The initial HEAD was the requested commit. Other workers subsequently advanced HEAD to `13ba620812f620c0876641a612d6cd1388c37b7d`; its only source difference from the launch commit is the context-module rename `Regroup.monOf_apply` to `Regroup.monOf_apply_triple`. That rename was already present as another worker's uncommitted change on entry. No audited file changed. The build/probes therefore certify the first-line package bytes in this explicitly identified dependency context, rather than claiming a pristine checkout of the launch commit.

Supporting reads of `Bracket`, `Regroup`, `Witness`, `Check/BracketBound` and the input-loader portion of `fobs.py` establish contracts/dependencies only. A dry read of generated `Br/P0.lean` and `Br/Q0.lean` confirms the emitted shape; neither was built. No producer was imported or executed, and no generated `Ledger/**` module was built. Only this report was created/edited. Lean probes used stdin to respect the user's stricter report-only instruction instead of creating the brief's scratch file. Build-cache effects are from the expressly requested validation.

## Chunk proof and exact consumption

At the frozen snapshot, `BrChunk:25` defines `chunk l m k = (l.drop (m*k)).take m`. `chunk_succ` shifts exactly one block. `sum_chunks` (`32–47`) proves equality of the original sum and all block sums under `l.length ≤ m*n`, by decomposing `l` into `take m ++ drop m`. This is a partition by positions, not a set-membership argument: duplicate entries keep their multiplicities. For positive m, position i belongs to block `i/m` at offset `i%m`; the coverage inequality puts that block below n. A short last block and extra empty blocks are safe. With m=0 or n=0 the same inequality forces l empty. No term can be omitted by supplying too few chunks.

`brCheckC` (`61–63`) checks the actual chunk of the actual `brList`; the producer cannot substitute a different chunk list. `brChunks_sound` (`66–81`) first applies `sum_filter_mon` to identify the full filtered coefficient with `brList`, then `sum_chunks`, then the triangle inequality over block sums. Each block is bounded by `brl_sound`. `mem_of_mem_chunk` and `mem_brList` supply the operand memberships; `hin` identifies H membership. No per-term triangle estimate replaces cancellation within a chunk.

The `Hl.Nodup` premise matters: regrouping selects one candidate H index per tuple, so repeated H indices must be excluded. The finite F list may contain duplicates, whose contributions are preserved on both sides. The monomial guards in `Regroup` prevent natural-subtraction underflow. Zero coefficients vanish explicitly in the regrouping application.

`BrPOk` (`85–88`) contains exactly three obligations: coverage, every required chunk check, and the rational sum of chunk claims at most the total claim. It contains no analytic coefficient estimate. `brAllC_sound` (`91–107`) obtains those obligations at `(p 0,p 1,p 2)` from `mdeg p ≤ L`, invokes the chunk theorem, rewrites `monOf_triple`, and casts the rational total comparison. Its conclusion is literally the RHS/LHS of `Bracket.brAll_sound` (`328–336`), with the same F/H data, scales, evaluation maps, phi and G triple.

This is the `hG` required by `Check/BracketBound.reducedBracket_bound_of_drop:284–285`, after `mem_truncSet_iff` and `G p = (sjsuG j (p 0,p 1,p 2) : ℝ)`. The emitter performs exactly this conversion at `br.py:466–479`. `muF` is definitionally `fun e => monOf e.1`; no changed monomial convention or norm is involved. The stdin composition probe below checks the complete coefficient type by directly applying `brAllC_sound`. Actual production source-identification, hcert, remainder/decomposition and tail obligations of BracketBound remain separate.

All four supporting theorems also pass: `chunk_succ` (exact shift), `sum_chunks` (complete sum equality), `abs_list_sum_le_map` (triangle inequality), and `mem_of_mem_chunk` (sublist membership). No new theorem concerns Complex.arg, zero-action polar differentiability, flow existence or confinement.

## Premise audit

These are generic checker implications, not manifest-bound source theorems. SOURCE below means the numerical/structural contract explicitly required by the launch and N7 checker design. Each named logical binder is accounted for; STANDING/RULED/EXCESS counts are zero.

| Binder | Classification and meaning |
|---|---|
| `brChunks_sound.hlen` | SOURCE: decidable full-list coverage. |
| `brChunks_sound.hall` | SOURCE: finite per-chunk Boolean checks for all k<n. |
| `brChunks_sound.hnd` | SOURCE: decidable H-index uniqueness. |
| `brChunks_sound.hin` | SOURCE: exact membership specification, proved for emitted brInH. |
| `brChunks_sound.hD` | SOURCE: representation certificates, expanded below. |
| `brChunks_sound.hS0` | SOURCE: equality of semantic strides. |
| `brChunks_sound.hb0` | SOURCE: equality of literal digit widths. |
| `brAllC_sound.hall` | SOURCE: finite family of BrPOk, expanded into coverage/checks/total comparison above. |
| `brAllC_sound.hnd` | SOURCE: H-index uniqueness. |
| `brAllC_sound.hin` | SOURCE: exact H membership. |
| `brAllC_sound.hD` | SOURCE: the same representation certificates below. |
| `brAllC_sound.hS0` | SOURCE: semantic stride equality. |
| `brAllC_sound.hb0` | SOURCE: literal digit-width equality. |
| `brAllC_sound.hp` | SOURCE: requested degree range. |

For `brChunks_sound`, each of `D,Ca,Cb,pp,Fl,Hl,inH,P0,p,m,n,G,w₀,φ` is TYPING (14); the seven logical binders above are SOURCE (7). For `brAllC_sound`, each of `D,Ca,Cb,pp,Fl,Hl,inH,P0,L,m,nOf,Gc,G,w₀,p,φ` is TYPING (16); its seven logical binders are SOURCE (7). The generic list lemmas have only type/list/function/index data and, where applicable, a coverage or membership premise.

`BrD.Ok` is expanded from `Bracket:56–75`, not accepted on its name alone:

| Field | Checked content |
|---|---|
| `hb` | Positive plain digit width. |
| `hbd` | Positive derivative digit width. |
| `hw` | Equal packing widths. |
| `hS` | Equal strides. |
| `fok` | Every plain F literal passes ok. |
| `fl` | F decoded list, C, parity and q equal the sparse operand's. |
| `dfok` | Every F derivative literal passes ok. |
| `dfl` | Its decoded list equals dlist, C is unchanged, parity flips, q is unchanged. |
| `hok` | Every H literal passes ok and exact symmetry check. |
| `dhok` | Every H derivative literal passes ok. |
| `dhl` | Its decoded list equals dlist with the same C, flipped parity and unchanged q. |

These are representation identities, not bracket bounds. `BrD.ok_of` produces them from the emitted fCheck/dCheck/ok/symDigOk checks. Thus no final estimate is hidden in hD. `hin` is not supplied by Python fiat either: `br.py:400–409` emits a Lean proof using two finite membership checks and `mem_monsUpTo`.

## Producer acceptance trace

| File | Review result |
|---|---|
| `packing.py` | Compact offset digits and whitening supply candidate literals. Mantissa bounds, layout/decoder guards and semantic attachment are checked again in Lean. Python slots/l1 calculations are not proof evidence. `up` uses integer ceiling arithmetic on Fraction. |
| `poly.py` | Active mul uses exact flint integer-polynomial multiplication, with the odd/odd sign. Fixed-width WPY packing is used by the Python mirror's conv_raw, not as an unchecked Lean assertion. Any bad candidate product/budget must still pass the Lean packed checks. |
| `produce.py` | Inputs, products, common rational scale, multipliers, rounding discrepancies, error budgets and norm claims use integers/Fraction. Float FFT/sqrt at 269–290 supplies candidate witnesses only. The float-derived sigma0 at 414 is adjusted by an exact square comparison (415–416), then checked again by Lean sqrtCheck. No convergence or approximation claim is accepted merely from the float construction. |
| `ledger.py` | Computes parameter records and some producer-side mirror checks. Skipping mirrors changes no emitted Lean proof requirement. See documentation note N2. |
| `emit_h.py` | Emits exact rational data and whitened literals, then `decide +kernel` proofs of tIn, pBase, every required power/U/V/h check. Assembly identifies finite index lists in Lean and applies TCerts_of, PCerts_of, VCerts_of and HCert_of. sjsu_hIdx_ne also checks nonemptiness rather than assuming it. |
| `br.py` | Reconstructs brList order (axis, sorted F entries, kind, shift), chunks it, computes dyadic upper claims and emits one actual brCheckC proof per chunk. Q assembly at 439–448 separately kernel-checks brN, the full length and total rational claim; every k<n is discharged by the corresponding brp theorem. Missing or reordered Python terms cannot bypass these checks. |
| `bracket.py` | Diagnostic calculation only. Its float CLI thresholds can choose different pruned/rounded observable data, and its JSON output converts estimates to floats. It emits no Lean certificate and is not read as an accepted bound by br.py/emit_h.py. It explicitly reports eta_wo_tails; see the boundary below. |

`br.py:78–98` agrees with Regroup's ordering and guards. For kind=false the coefficients are s_a and -s_2; for kind=true they are -t_a and t_2. Independently, these are the four terms in `(∂u_a F-∂u_2 F)∂phi_a H - ∂phi_a F(∂u_a H-∂u_2 H)`. For s=(2,3,4), t=(5,6,7), axes a=0,1 give pairs `(2,-5),(-4,7)` and `(3,-6),(-4,7)` before evaluating the derivative factors. Derivatives obey d cos(k·phi)=-k_a sin(k·phi), d(-sin(k·phi))=-k_a cos(k·phi); the parity flip and signs in br.py:54–62 match. There is no 2*pi in these radian-angle expressions.

The bracket checker recomputes its own Q, integer c, products, overflow bounds and packed l1 on each exact chunk. br.py's Gc is only a proposed dyadic bound. `brCheckL` rechecks the product scale equation, `2*BX < 2^w`, l1 guards and `|Q|*l1P ≤ Gc`. Defaults in lookup tables do not supply proofs; they are subjected to the same checks. Too-small chunk counts fail coverage, negative empty-chunk budgets fail `0≤Gc`, and too-small total G fails the separate rational comparison. Extra chunks are empty and contribute nonnegative budgets.

For the H witnesses, `Witness.sqrtCheck:54–62` checks residual/value/derivative errors, positive sigma0, sigma0^2 below the true B lower majorant, the W lower bound and the final error formulas. emit_h includes pBase and the whole power chain; it does not merely insert the Python-computed error into a theorem premise. Input checks compare the exact emitted T/B rationals to the actual decoded literals. Output checks compare actual packed combinations to actual output literals. Wrong rounding, float seeds, scales or mantissas can cause rejection or larger error claims, not an accepted stronger bound.

**Scope of the accepted bound:** the emitted Br results concern the literal model H_t; H.Main's certificates concern the finite Horner functions built from emitted Tdat/Bdat. Identifying those functions with the approved SJSU Hamiltonian and centre is a separate source bridge. Acceptance of arbitrary self-consistent input data does not establish that identification. The source bridge is not audited or claimed complete here. Likewise N7 part 4 does not by itself include the final model-error/tail/face assembly. `bracket.py:9,159–162` explicitly leaves tails out (`tails: TODO`, `eta_wo_tails`). Its JSON eta and T_years are not a certificate for the full reducedBracket or physical confinement.

## Findings and refutation dispositions

**N1 — Reproducibility gap, not a kernel soundness shortcut.** Locations: `produce.py:247`, `bracket.py:44`, and supporting `fobs.py:40`; quotes: `.drafts/g2/data/literal-v1.json`, `.drafts/g2/data/F-v1.json`. Both are ignored/untracked (`git ls-files` returns neither; git check-ignore lists both). A checkout plus the seven audited Python files cannot reproduce these runs without separately obtaining those inputs. The output manifests at `emit_h.py:483` and `br.py:511` hash emitted modules, not the input files or run configuration. Refutation attempt: traced all emitted proof statements and their assembly; the Lean checks re-verify bounds for the emitted literal data, and the F literal itself is the chosen observable. Thus missing raw input provenance does not introduce a false theorem about those literals. Conversely, that re-verification does not reconstruct missing inputs or automatically prove their physical-source identity. Disposition: confirmed nonblocking reproducibility note for this conditional producer review; production reproducibility/source closure is withheld. Suggested fix: archive/hash both JSON inputs, hw.json, commands/configuration including BR_MCH and dependency versions, then record the separately checked model/centre bridges.

For later recovery, the currently present inputs hash to:

```text
F-v1.json       40cf26e2a1f669a36cd13d86891f18620089f04c2e3a198afdb03f6670d1c825
literal-v1.json 95b841cee81ef862a7bc7631b28c84eb387e04cb1505e8cc105fd2ce9b33306e
```

These hashes identify local inputs only; this auditor did not regenerate them or establish their provenance.

**N2 — Mirror documentation overclaims its coverage.** `ledger.py:6–8` says “re-runs EVERY kernel Bool check”, naming inputCheck, sqrtCheck, invCheck and pBase; `emit_h.py:4–5` says it “re-runs the kernel mirror ... aborts on any failure”. In fact `ledger.build:212–290` mirrors U/V/H/power products and copies the sqrt/inverse records at 288–289; it does not run the named base/input checks. Moreover `LEDGER_NOMIRROR=1` makes litCheck and combCheck return True (`ledger.py:185–204`). Refutation attempt: checked both entry points and searched the complete mirror implementation for the listed checks. The H emitter still emits pBase, tIn and other kernel proofs, and the DRAFT handoff discloses the full-run mirror bypass. Therefore this is inaccurate diagnostic documentation, not a bypass of Lean verification. Disposition: confirmed, nonblocking. Suggested fix: enumerate the actual default mirror subset, document NOMIRROR in the module/CLI descriptions, and describe kernel acceptance as the required gate in both modes.

**N3 — Nonexistent API name in the chunk module docstring.** `BrChunk.lean:16` quotes `brChunksAll_sound`; the exported theorem at 91 is `brAllC_sound`. Refutation attempt: complete declaration/name scan and comparison with the emitter call at `br.py:478` show the emitter uses the correct name. Disposition: confirmed documentation-only note. Suggested fix: change the docstring reference. The same docstring's factor-2–3 cancellation claim (16–17), also repeated in br.py, is an empirical claim not established by these theorems and was not measured in this audit; label it as such when recording production measurements.

No suspected mathematical defect in a pinned external source was found. No mathematical or source deviation was introduced. These findings are notes; there is no surviving in-scope soundness blocker.

## Verification receipts

Exactly one targeted build:

```text
.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Engine.BrChunk
exit 0
Build completed successfully (2949 jobs).
```

This was a warm/cached build with dependency-warning replay, not a clean-build performance experiment. The warning replay concerns dependencies (deprecated names, unused tactics/arguments and a deprecated import); no warning or default-heartbeat failure was attributed to BrChunk. The prescribed wrapper supplies flock serialization, nice 5, a 6 GB memory cap and LEAN_NUM_THREADS=2; it was not changed. There was no direct Lean/Lake call, clean, broad build, resource override or requested Mathlib rebuild.

The axiom command was `.drafts/g2/g2lake env lean --stdin`, with `import KAM.EffectiveStability.Tube.Engine.BrChunk` followed by `#print axioms` for every theorem declared in the module. Exit 0; complete output:

```text
'KAM.EffectiveStability.Tube.chunk_succ' depends on axioms: [propext]
'KAM.EffectiveStability.Tube.sum_chunks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.Tube.abs_list_sum_le_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.Tube.mem_of_mem_chunk' depends on axioms: [propext]
'KAM.EffectiveStability.Tube.brChunks_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.Tube.brAllC_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A second `.drafts/g2/g2lake env lean --stdin` returned exit 0 with no diagnostics. It copied the complete `brAll_sound` conclusion with the chunk-check premises and proved it by `brAllC_sound hall hnd hin hD w₀ hS0 hb0 p hp φ`. Its six `decide +kernel` examples checked duplicate-preserving first chunks, a partial last chunk, an extra empty chunk, rejection of insufficient coverage, and rejection of a nonempty list with m=0 or n=0. A seventh example applies `sum_chunks` to an empty list with m=0,n=4. No generated module was imported.

Independent Python arithmetic, written inline and importing no producer, checked the position partition for all list lengths 0..40, m=0..10 and n=0..44 satisfying coverage. Output:

```text
INDEPENDENT_CHUNK_POSITION_PARTITION_PASS 15949
INDEPENDENT_REJECT_SHORT_COVERAGE True
```

The same read-only inspection parsed all seven Python files with ast.parse without importing/executing them. All eight audited files matched `git show 4841de213:<path>` byte-for-byte. Line counts are BrChunk 111; br 534; bracket 170; emit_h 503; ledger 308; packing 145; poly 135; produce 517. BrChunk has the required copyright/module/public import/docstring/exposed public section, no line over 100 characters, and no forbidden declaration, proof escape, option or EuclideanSpace. Its import is a core Engine module, with no provider/draft/application-root import.

Ran `PYTHONDONTWRITEBYTECODE=1 .drafts/g2/lint_noabi.sh` once, to completion: **exit 1**. Its complete diagnostic/test output, apart from unittest progress dots, was:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean, KAMSJSU/EffectiveStability/SJSU/Check.lean, KAMSJSU/EffectiveStability/SJSU/Confinement.lean, KAMSJSU/EffectiveStability/SJSU/Ecc.lean, KAMSJSU/EffectiveStability/SJSU/Ham.lean, KAMSJSU/EffectiveStability/SJSU/Initial.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/Br/Top0.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/Br/Top1.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/Br/Top2.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/F.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/H/Top0.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/H/Top1.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/H/Top2.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/Top.lean, KAMSJSU/EffectiveStability/SJSU/Model.lean, KAMSJSU/EffectiveStability/SJSU/Obs.lean, KAMSJSU.lean, KAMSJSU/EffectiveStability.lean)
check_lean_modules: PASS (18629 Lean files, 0 comparator configurations)
----------------------------------------------------------------------
Ran 29 tests in 4.158s

OK
----------------------------------------------------------------------
Ran 8 tests in 0.008s

OK
FROZEN-ANCHOR GUARD OK
```

The only reported failure is stale generated roots, including the not-yet-landed application data. Those roots are protected by AGENTS rule 10 and the user's report-only restriction; they were not regenerated. Repository lint is **not green**, despite the passing module check, both test suites and frozen-anchor guard. `abi_hashes` was skipped under WORKER-RULES' explicit lint amendment; the full `scripts/lint_sources.sh` was not run because it invokes Lake outside g2lake.

At final integrity verification HEAD was `4afebe84d4cd0fd012de56b2d559855f926c85e1`. Relative to the launch commit it adds the context-helper rename already described, one row in `docs/explorations/sjsu-g2-decisions.md`, and the separately owned N5a-2 HtBridgeInst files/handoff. Those instance files were present as untracked files on entry and were committed by another worker during this audit; they remain outside this verdict. None of these commits changes any of the eight audited files. The first-line manifest was checked against both current bytes and `git show 4841de213:<path>`: `REPORT_MANIFEST_AND_COMMIT_MATCH_PASS 8`. The scoped tracked diff is empty. The report passes the whitespace check. Supporting context hashes: `Engine/Bracket.lean=21e298afbb0f0501f8cad73b25fdc9b218838c388d8b9e5634cff9c96a7b1a01`; `Engine/Regroup.lean=99fc281664b6312899b12c117e9d079afe3f84cd9452abaa58e884e77c75bffe`; `Check/BracketBound.lean=9b02ad2504627e8819edd158440c36cf6aee01f1dff2fca06efbda5bab7bdf1e`. The dry-read samples were `Br/P0.lean=00890445b534700fccfb89906b11363880f85d2e62c136c4254fe91c034ee9e3` and `Br/Q0.lean=ffd53b7bd272ca801dbebf5862a0ff0fb87adb37618d854889a5d2f07f91b794`; these identify sampled text, not accepted generated proofs.

## Closeout

All six theorem statements/proofs, chunk-coverage and consumer-type checks, all seven producer files, the required targeted build and every theorem's axiom query are reviewed. Notes N1–N3 have explicit refutation dispositions and suggested fixes; none was repaired. The one lint run has exited and its non-green result is retained. No audit command remains running. The sole authored workspace change is this report; other workers' existing/generated files and concurrent commits were left alone. Production execution, generated-kernel acceptance, measured cancellation loss, source-instance closure, full eta and final confinement are not certified by this scoped PASS WITH NOTES.

READY g2-audit-n7d-1

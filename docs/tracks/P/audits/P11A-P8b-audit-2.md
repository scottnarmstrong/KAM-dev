# P11A-P8b independent audit 2

Verdict: **FAIL for unconditional literal completion of `stepP:p11:pr-in`; PASS for the helper proofs as stated.** Audit 1's substantive missing G0-hat normalization/logarithmic bound is now **CLOSED** by `PreparedJetsG0`. Its constant-scope finding remains **OPEN as a source/graph contract ambiguity**, not a demonstrated false Lean theorem. A single constant uniform over unbounded derivative orders is not certified. The finite-order interpretation needed by the displayed consumers is supported by the estimates, with explicit order factors retained.

No frozen anchor or provider is implemented by this package, so an anchor seal-ready verdict is N/A. No finding concerns the expressly deferred pr-b/pr-c/pr-d work or the separately audited PreparedData.

## Frozen inputs and scope

Audit date: 2026-10-29. Worktree: `/root/code/KAM-inp-p11ap8b`.

- HEAD: `1c8abd7064954ab709e312aee99b44ae230df071`.
- Observed inp: `8dc8bedc37b2b4dad2163b79fbcf35ff51fdffdb`.
- `git diff inp...HEAD` contains 4042 lines over 18 files. It includes inherited P7 work, PreparedData, the two requested modules, the new G0 repair, and handoff/audit documents. The full diff was mechanically inventoried; proof review is restricted to the assigned slice.
- Git warns: `warning: inp...HEAD: multiple merge bases, using a2464f937a8b578ae414ec08331359284ec94a78`. `git merge-base --all inp HEAD` also returns `3a1ff30bf4f0de6b17be19a7234a99b727d000a7`. The requested three-dot comparison was used.
- Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the common package brief, local handoff and audit 1, track-P statement, design node table/Appendix A, blueprint pr-in and its consumers, graph pr-in, and supporting analytic/data specifications.
- The user's exact report destination overrides the brief's default MAIN-worktree destination. Only this report is changed; temporary evidence is confined to `.lake/abi-scratch/` and removed.
- Primary scope remains PreparedCauchy and PreparedJets. PreparedJetsG0 is assessed explicitly as supplemental repair evidence at current HEAD; it is not silently attributed to either original file. Those two original files are byte-identical to audit 1's `7023f944` revision. If the handoff's two-file scope is enforced literally, its missing G0 export remains absent there; the G0 closure below requires including this new third module.
- No new declarations in these three modules are SIGNED. Name searches in the design and `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` find none of the 22 exports. Exact provider/frozen-type and seal-body probes are therefore N/A, rather than replaced by self-type checks.

SHA256 snapshot:

| Input | SHA256 |
|---|---|
| KAM/Planetary/Preparation/PreparedCauchy.lean | `60ded550c754637ca03a2eac47ce5c45086f0742dffca7245e9277459a0b3bad` |
| KAM/Planetary/Preparation/PreparedJets.lean | `97ed93228384378fc30c8599a0ccb0508e7fca37b294f702bf69b490269de8c4` |
| KAM/Planetary/Preparation/PreparedJetsG0.lean | `a34c9e8c7a09d65041bfa96da28a3181810c1c5c3b5f68c2ba409863d8be6941` |
| docs/tracks/P/design/P11A-LEAN-DESIGN.md | `98caf2698430baf58bbf7da612810dce8ffd0b8d1db04536e2720a9a1dceeccd` |
| docs/graph/P/DEPGRAPH.md | `af1e7f1103c30f46915b6561618bb5c45b8d8c01b007cf9d4712c375119891e9` |
| blueprint-P/parts/p11-cp09-preparation.tex | `4c0e2dfefb50b1e06581e069a55846d25e0e4697a8826514ac699bbb83efb41f` |

Method: focused, refute-first correspondence/proof audit. Discovery, attempted refutation, and hygiene were separate passes. I independently re-read the code and source rather than adopting audit 1's verdict. No subagent review or fresh audit of the pinned CP09 PDF is claimed. Imported analytic infrastructure is inspected at points of use, not re-certified source by source.

## Findings and attempted refutations

### F1 from audit 1 — CLOSED by the supplemental G0 module

Blueprint `blueprint-P/parts/p11-cp09-preparation.tex:208` states
`|d_J^beta G0-hat| <= c MF beta! (4/s1)^|beta| <= c ell^((tau0+1)|beta|)`.
PreparedJets:554 originally supplied only the prefactor `MF + eta1(eps)`.

PreparedJetsG0:57 now proves `exists K >= 1, forall eps > 0, eps*MF <= exp(-1) -> MF + eta1(eps) <= K*MF`. K is chosen before eps, Fast and derivative indices. Its proof uses the established eta1 estimate, `MF >= 1`, and the independently proved numeric inequality `eps*log(1/eps)^p <= (2*p)^p` for `p>0`, `0<eps<=1` (line 33). This bound is coarse but valid and requires no further threshold shrink.

Line 84 applies it to the actual `p11PolarAverage Fast.G`, with factorial and radius exactly `beta!*(4/s1)^|beta|`. Line 114 proves the logarithmic form for that same object. The constant in the latter is chosen after beta but before eps, Fast, J and rho. It equals `K*MF*beta!*(4*k)^|beta|`, not a constant depending on eps. This is a genuine proof of the previously unpaid normalization; it does not replace G0-hat by C.C or assume the desired estimate.

Object identification is supported by SlowData:63-65, the h0 identity in `P11SlowSpecOf`. The J domain and s1/4 Cauchy radius match; the rho disc `norm rho < pi*(rz/2)^2` is larger than the later working disc. No conclusion-shaped premise was introduced.

### F2 from audit 1 — OPEN contract-scope discrepancy; blocks literal all-order certification

At the frozen snapshot, graph `docs/graph/P/DEPGRAPH.md:20623` says
`arbitrary J-multi-indices alpha,beta and rho-multi-index gamma`;
line 20624 suppresses the derivative-order constants in (ii)/(iii), and line 20625 says `CONSTANT_SCOPE: none`. Design:392 repeats the suppressed form. Blueprint:208 displays alpha! in the sharp Z estimate but drops it in the final logarithmic expression.

The exports honestly retain:

- PreparedJets:101-113, g2: `c*(4/c0)^|alpha|*4^|gamma|` in addition to alpha! gamma! and the required eps/log powers.
- PreparedJets:275-288, Z: `alpha!*c*(1+k)*(4*k)^|alpha|` in addition to the required eps/log powers.
- PreparedJetsG0:114-124, G0: `forall beta, exists c`, before eps, rather than one c before all beta.

Attempted refutation: the source is naturally usable for each fixed order, and its consumers at blueprint:209-211 use only finitely many orders bounded in terms of mu. For that reading the explicit factors can be absorbed into constants depending on the cutoff, fixed before eps. Thus this is NOT evidence that the source's intended estimates or the Lean proofs are false. `CONSTANT_SCOPE: none` is underspecified; it is not itself a positive statement of all-order uniformity.

Nevertheless, the handoff requires literal conclusion matching, and neither the graph nor design explicitly settles which dependence is allowed. No ruling resolving that ambiguity was located. PreparedJetsG0:20-21 asserts in a module comment that the source constant may depend on derivative orders; that assertion is implementation commentary, not an owner/orchestrator amendment of the graph. This audit cannot silently make that amendment. Under a single-c, all-order reading, the exported conclusions do not match. Under the fixed-order reading, the estimates have the requisite eps-uniform strength.

Closeout criterion: record the intended derivative-order dependence in the controlling source/graph contract (or provide an authorized bounded-order contract), then assess its exact requested exports. No requirement to prove an implausible unbounded-order uniform Cauchy bound is imposed. The current FAIL is for unconditional literal node closure while this scope is unresolved; it is not a kernel failure or a demand to finish deferred consumers.

## Declaration ledger

All public names below have prefix `KAM.Planetary.`. PASS means sound as stated. Node coverage is assessed separately above.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| pr-in overall | combined exports | FAIL | F1 closed with third module; F2 prevents unconditional literal contract match. |
| Coordinate Cauchy | p11PolyStep_iterate_bound (PreparedCauchy:31) | PASS | Circle Cauchy on an included closed coordinate disc. |
| Coordinate runs | p11PolyRuns_bound (PreparedCauchy:72) | PASS | Reverse-list induction; Nodup keeps each frozen coordinate distinct. |
| Polydisc | p11PartialVec_norm_le_poly (PreparedCauchy:120) | PASS | Fixed-order partials/runs agree; products give exact coordinate factorials and radii. |
| pr-in(iii) sharp | p11_prin_g2_jet (PreparedJets:51) | PASS | Correct object, mixed s2/4 and eps/4 radii, alpha! gamma!, eps^3 bound. |
| pr-in(iii) log | p11_prin_g2_jet_log (PreparedJets:101) | PASS WITH NOTES | Exact eps^3/eps^|gamma| and log exponent; explicit order factors, F2. |
| K1 bound | p11_prin_K1_le (PreparedJets:158) | PASS | MF >= 1 controls the logarithm. |
| s1 reciprocal | p11_prin_s1_inv (PreparedJets:170) | PASS | Data-dependent k before eps, log^(tau+1). |
| alpha1 reciprocal | p11_prin_alpha1_inv (PreparedJets:190) | PASS | Data-dependent k before eps, log^tau. |
| d1 reciprocal | p11_prin_d1_inv (PreparedJets:214) | PASS | Inverse minimum bounded by sum; log >= 1. |
| eta1 growth | p11_prin_eta1_le (PreparedJets:244) | PASS | eps log^(2*tau+1), with k before eps. |
| pr-in(ii) | p11_prin_Z_jet (PreparedJets:275) | PASS WITH NOTES | Transforms genuine upstream Z derivative bound; F2. |
| C coefficient size | p11_prin_C_bound (PreparedJets:328) | PASS | Fast mean at zero, normalized torus average. |
| C holomorphy | p11_prin_C_diff (PreparedJets:367) | PASS | Recovers C.C from actual h0 identity on fixed rho slice. |
| C sharp jets | p11_prin_C_jet (PreparedJets:444) | PASS | Cauchy on s2/4; concerns C.C only. |
| C log jets | p11_prin_C_jet_log (PreparedJets:474) | PASS | Explicit factorial and radius-lower-bound factors. |
| F bound | p11_prin_F_bound (PreparedJets:521) | PASS | Removes denominator using coth^n >= 1. |
| Fast mean | p11_prin_fastMean_bound (PreparedJets:532) | PASS | Domain inclusion and norm of normalized average. |
| G0 intermediate | p11_prin_G0_jet (PreparedJets:554) | PASS | Polar-average holomorphy/bound and s1/4 Cauchy. |
| Numeric log bound | p11_prin_eps_log_le (PreparedJetsG0:33) | PASS | Positive real powers; eps <= 1 controls reciprocal square root. |
| MF normalization | p11_prin_MF_eta1_le (PreparedJetsG0:57) | PASS | F1's exact formerly unpaid bridge, uniformly in eps. |
| pr-in(i) MF form | p11_prin_G0_jet_MF (PreparedJetsG0:84) | PASS | K before all eps and derivative indices; actual G0-hat. |
| pr-in(i) log form | p11_prin_G0_jet_log (PreparedJetsG0:114) | PASS WITH NOTES | Actual G0-hat, c before eps but after beta; F2 scope explicit. |
| Private domain/product helpers | p11Box_isOpen_aux; prin_prod_append; prin_poly_prod (PreparedJets:33,39,43) | PASS | Open finite polydisc and exact Fin.append product identities. |
| Private analytic helpers | prin_coth_ge_one; prin_slice_differentiable (PreparedJets:322,358) | PASS | Positive sinh/cosh inequality; affine slice differentiability. |

Polydisc proof check: the center fixes the coordinates already differentiated; the unused coordinates remain in their closed discs. Each new coordinate circle stays in U by hcl. The reverse-run induction applies holomorphy of the prior derivative on U; positivity of every R justifies all divisions. Conversion from the signed fixed-order partial definition uses the exact run identity, without assuming mixed-derivative commutation. The g2 rho disc fits because `5*eps/4 + eps/4 = 3*eps/2 < pi*eps/2`; J uses strict inner center distance plus closed s2/4 radius. Zero orders and empty products are included.

## Definitions, premises and imports

There are **no new def/abbrev/structure declarations** in any of the three reviewed modules: definition classification N/A. All new objects in proofs are local abbreviations for the specified radii, logarithms, products and constants; no fallback-valued exported object exists.

| Premise family | Classification / source |
|---|---|
| n, finite-dimensional Pi carriers, points, multi-indices | TYPING; ambient types remain Fin n -> C or R. |
| P11SecularSpec D C | STANDING/source holomorphic-chart data; expanded in Holomorphic:73ff. |
| P11FastSpec C eps Fast | SOURCE, avg-fast result; expanded Fast:43ff, including G holomorphy and mean-error estimate. |
| P11SlowSpecOf C Fast nu eps c A | SOURCE, avg-slow result; expanded SlowData:54ff. The Z derivative bound used in (ii) is an explicit upstream source conclusion, not a new hidden assumption. |
| eps>0; eps*MF<=exp(-1); nu>=1; c>=0; positive radii | SOURCE numeric range/constant conditions. In standalone generic Cauchy helpers, holomorphy, inclusion and sup bound are their defining analytic premises. |
| norm rho, norm J-J0 constraints; 2*pi*eps < pi*rz^2/16 | SOURCE domains / numeric eps-smallness. |
| eps<=1 in eps_log_le | SOURCE numeric premise, proved from the existing range before normalization uses it. |

No new conclusion-shaped hypothesis, instance or bundled field is introduced. These are parametric helpers consuming source specifications, not claims to have newly constructed those specifications. Existing `P11SlowSpec` unfolds to the parametric spec; its producer is outside this slice. In particular no produced slow-averaging result is promoted solely because these helpers compile.

Recursive local import traversal from PreparedJetsG0 reaches 375 KAM modules, including 64 frozen modules. Every frozen import is manifested as a SEALED definition. No provider, DRAFT_SORRY theorem, or frozen theorem is imported. No provider seal is applicable. All exports stay inside KAM.Planetary; a repository declaration-name search found no reused public helper short names or harmful root shadows.

## Independent verification

All Lean-related commands ran sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5`. No resource-budget overrides, clean, update, cache fetch, or package edits were used.

1. Targeted compile gate (includes the original two modules as dependencies):

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap8b KAM.Planetary.Preparation.PreparedJetsG0
```

Exit 0. Output begins `[inp-gate] slot 1 acquired 01:54:33 for KAM.Planetary.Preparation.PreparedJetsG0` and ends `Build completed successfully (9421 jobs).` Lake replayed cached dependency warnings (unused variables/simp arguments and deprecated names). The reviewed PreparedJets warnings are at 159, 349, 351, 363, 435 and 534; none is an elaboration or resource failure. This was a targeted cached build, not a clean library rebuild.

2. Scratch axiom probe: import PreparedJetsG0, then `#print axioms KAM.Planetary.<name>` for every public theorem in the ledger (22 total).

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP8bAudit2.lean
```

Exit 0. Complete theorem output:

```
'KAM.Planetary.p11PolyStep_iterate_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolyRuns_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PartialVec_norm_le_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_g2_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_g2_jet_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_K1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_s1_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_alpha1_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_d1_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_eta1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_Z_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_C_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_C_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_C_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_C_jet_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_F_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_fastMean_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_G0_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_eps_log_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_MF_eta1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_G0_jet_MF' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_G0_jet_log' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The probe is reproducible by scanning each reviewed file with `^theorem (\w+)` in file order and writing those 22 print commands after the import. Private helper closures are covered by their uses in these exported proofs.

3. Single kernel replay invocation:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.PreparedCauchy KAM.Planetary.Preparation.PreparedJets KAM.Planetary.Preparation.PreparedJetsG0
```

Exit 0; complete output:

```
replaying KAM.Planetary.Preparation.PreparedJetsG0
replaying KAM.Planetary.Preparation.PreparedJets
replaying KAM.Planetary.Preparation.PreparedCauchy
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1; complete output:

```
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1194 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole failure is the generated-root exception explicitly allowed by the brief. KAM.lean was not regenerated. All other source-lint checks passed.

5. Protected-path and whitespace checks:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit 0, no diff/whitespace diagnostics, only the multiple-merge-base warning quoted above. `git diff 7023f944 HEAD -- KAM/Planetary/Preparation/PreparedCauchy.lean KAM/Planetary/Preparation/PreparedJets.lean` is empty.

Module/size inventory: PreparedCauchy 137 lines, max 98 characters; PreparedJets 605 lines, max 99; PreparedJetsG0 155 lines, max 96. All have copyright, module, public imports, module docstring, public noncomputable section. No proof escape, forbidden ambient carrier or resource override was found.

## Closeout, suspected defects and limitations

All 22 public statements and five private helpers are classified. The original G0 normalization gap is closed at current HEAD when the new G0 module is included. The literal derivative-order constant contract remains unresolved; no mathematical counterexample to the intended fixed-order statement is claimed. This source/graph ambiguity is the suspected defect to carry to the orchestrator, with the exact quoted anchors under F2. No defect in a pinned publication was established.

No production, frozen, manifest, generated-root, graph, signature, source or prior report was edited. No pr-b/pr-c/pr-d, PreparedData body, frozen headline or downstream consumer proof is certified. The report is complete even though the audited node has not received unconditional literal closure.

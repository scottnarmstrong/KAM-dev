# T18 independent package audit 1

**Overall: FAIL under the handoff's literal unsigned-export contract (F1).** The implemented estimates are mathematically faithful, compile, and have clean axiom closure. The failure concerns omitted source clauses in the node-named exports `as_in`, `as_pi`, and `as_c`; it does not assert a false Lean theorem. `as_ent`: PASS WITH NOTES. No frozen anchor is sealed by this infrastructure package.

## Scope and immutable inputs

Tier 2, independent refute-first source/package audit, 2026-10-28. Worktree and report are `/root/code/KAM-inp-p11c-t18`; the user's exact output path overrides the generic brief's MAIN-worktree destination. Only this report is a lasting edit. Temporary probes/logs were confined to `.lake/abi-scratch/` and removed. No source repair, git mutation, root regeneration, frozen edit, or manifest edit was performed.

Snapshot v1: HEAD `0b7c10a700ade312a6c5882d5a3baa8c7b0a055a`; integration ref `inp` at `ce5bc0c09a78b36777a59cdb8b93c5e544d380e6`. `git diff inp...HEAD` warns of multiple merge bases and selects `a73d2767362222d4a6d0610ce6bf6be553301a4e`; the other merge base is `980388b435b56c1a548f7c9771a8f4c62033aba7`. The full comparison was inspected, including inherited seals, generated-root additions, graph status updates and provider wrappers. These are not silently attributed to T18.

T18 itself is the nine-commit range `f67bed9b..HEAD`: exactly ten new files, 1,169 lines. The scope is ONLY the facade and its nine submodules. T4/T6/T12/T13 are imported inputs, not independently re-audited packages. Read authority: AGENTS.md, PLAN, DECISIONS, the package audit brief, T18-handoff.md:46, design row T18 and node table, P11C design audit 1, Track P statement, graph records, and blueprint Part 11b. The standalone signature has no `as_in/as_pi/as_c/as_ent` declarations; signature-identity/provider-seal probes are therefore N/A, not successful seal checks.

### SHA-256 manifest

| File (under `KAM/Planetary/PlanarTorsion/`) | Lines | SHA-256 |
|---|---:|---|
| `AsymptoticEntries.lean` | 33 | `58b3c16ffe84a4022600b968ab9f7a67280d32677cfb6c24c3f26d025d13658e` |
| `AsymptoticEntries/Calculus.lean` | 97 | `b9d5a807fe4f63c37a053d6781dd103853db550c06a29f05f121596f47d661c7` |
| `AsymptoticEntries/CoeffEq.lean` | 137 | `b14c15c3405d84534b16943a991fc0b6ea1096d39f47591088214ba171e3dae3` |
| `AsymptoticEntries/Coeffs.lean` | 125 | `ff478c4a344647e3abd39e32d2d1c187ceb58bcfc648d3b32b3a8dedd065022a` |
| `AsymptoticEntries/Entries.lean` | 115 | `ef087be72749365b81f2e817122fa235442988e232cf825a4c13221016acf44d` |
| `AsymptoticEntries/EntryBounds.lean` | 149 | `57a5142aa9d3984c0d0a5eb36f778ac91c5b85610d1a0bb3d4ffa9125df43c37` |
| `AsymptoticEntries/Inputs.lean` | 198 | `bc32f6b73b922fa68bc8293fbabc66c5ef649356e813b63e2e5e5c2f7a62051b` |
| `AsymptoticEntries/Leading.lean` | 121 | `d65a48a256852c728a376a415d6830fcecac889b829cb68501379f31d5b5b4c5` |
| `AsymptoticEntries/Pair.lean` | 51 | `ec8d9e3bbd0637ade79c9974f6bcac304ac58ea1d196b6a80531532f5d374164` |
| `AsymptoticEntries/Projector.lean` | 143 | `982f44387c6ca604505a9df1f0aab35f0e979ef68c665341bc76c88081748daf` |

| Authority | SHA-256 |
|---|---|
| `docs/tracks/P/design/P11C-LEAN-DESIGN.md` | `8693b4c33b78a6d52c251999b15e08fc68d588b9250e2e4bbe3e64b4510a6437` |
| `docs/tracks/P/design/DESIGN-P11C-design-audit-1.md` | `b6da04d8b43c384d2a479e88c1a20642aee11b53f81f840f8f1d0bbc9944dba7` |
| `docs/graph/P/DEPGRAPH.md` | `dad2bca68bd1a99f5f79d4d1481f518914ca492a12593718d6e9622e9a7b2582` |
| `blueprint-P/parts/p11b-planar-torsion.tex` | `f8ce70a3460c855e1e04ea1a8d39c7a32a550f38b8097ca993a6a17efe012bf1` |
| `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` | `6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7` |

## Findings and attempted refutations

### F1 — source-facing export completeness: FAIL; survives the literal-contract check

The controlling handoff at line 46 says: “an UNSIGNED export named after a graph node must state that node's literal conclusion.” This is stronger than merely allowing the slice's mathematics to be distributed among helpers. The design has not signed narrower T18 exports. The discrepancies are:

1. **`as_in`**, Inputs.lean:124–135, versus DEPGRAPH.md:31313 and blueprint `p11b-planar-torsion.tex`:240–242. The source conclusion begins “a=(3/8)G m_1 m_2 alpha^2(1+O(alpha^2)), b=(15/32)G m_1 m_2 alpha^3(1+O(alpha^2))”. The exported conjunction contains only the three Q estimates, eventual negative Delta, and its relative comparison with Q11. Neither scalar expansion is a conjunct. In particular, a size bound for Q12 is not the stated leading expansion for the scalar b.
2. **`as_pi`**, Projector.lean:76–87, versus DEPGRAPH.md:31342 and blueprint:243. The source explicitly includes “pi_12=-Q_12/R”. The export contains bounds, nonnegativity, trace and Big-O statements, but not this signed identity. `p11cAe_proj_exact` at Projector.lean:26–34 proves the identity separately and is used in the proof at line 107; it is not a conclusion of `as_pi`.
3. **`as_c`**, Coeffs.lean:62–74, versus DEPGRAPH.md:31370 and blueprint:244–245. The source conclusion includes the six raw pair-coefficient combinations, starting “p_1-A/4=-(3/32)alpha^2(1+O(alpha^2))”, before dividing by the action powers. The export contains only the six resulting c estimates. Helpers `p11cAe_X0`, `p11cAe_X1`, `p11cAe_p3`, `p11cAe_X3`, `p11cAe_X4`, `p11cAe_X5` supply those raw claims separately.

**Adversarial check:** searched all 65 public declarations, checked the separate helper surfaces and their uses, and independently elaborated the two scalar expansions and eventual projector identity from the existing helpers. The probe also used `fail_if_success exact as_in p hp` at the first scalar target and `fail_if_success exact as_pi p hp` at the signed-identity target, followed by successful reconstructed proofs. Thus the omission is not unpaid analytic work or an axiom problem. This refutes an allegation of missing mathematical ingredients; it does not refute the stated literal-export mismatch. Source-equivalent absolute error notation is accepted: F1 is about absent clauses, not spelling `1+O` as subtraction.

**Repair criterion (not applied):** export each full graph-node conclusion under its node name, assembling the already proved pieces with only `p` and `hp`, or obtain an explicit amended scope/signature that authorizes the narrower names. Do not silently mark the present narrower exports as the entire literal nodes. This finding has no claim that downstream T19 cannot use the current estimates.

### Notes

- **N1 — inherited protected-path differences.** The prescribed `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**: two secular-box proof-body seals, their two manifest state changes, and 27 generated-root import additions. The seal history is commit `b8f993d2`; the root regeneration is `74ed24b5`; the manifest change log records the seals. `git diff f67bed9b..HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. Therefore the broad brief's empty-diff test fails literally, while T18 itself obeys protected-path ownership. This audit does not re-certify those inherited seals.
- **N2 — warnings.** The targeted build exits 0 but emits warnings. Scoped examples: Calculus.lean:33 (unused binder), Inputs.lean:37,48,60,73 (unused simp arguments), CoeffEq.lean:28,52 (unused binders) and :48,59,77,88,123,132 (unused simp arguments), Projector.lean:40,44, and Entries.lean:64,77,89–90. Upstream replay warnings also occur. No warning suppression was introduced. Reported separately from the allowed generated-root lint exception.
- **N3 — scope of constants.** Every Big-O is after fixing the full physical datum `p`. The package makes no mass-ratio-only uniformity assertion. T19 owns normalized uniformity, determinant, and homogeneity (design:224–225,264); none is certified here. No extra premise is introduced to obtain an estimate.

## Graph-node ledger

All names below are in `KAM.Planetary`; source nodes have prefix `stepP:p11b:`.

| Node | Declaration and location | Verdict | Source comparison |
|---|---|---|---|
| `as-in` | `as_in`, Inputs:124 | FAIL (F1); estimates PASS | Q11 coefficient −3Gm2/(8√κ), exponent 3/2, error 7/2; Q22 coefficient −3Gm1/(8√κ), exponent 2, error 4; Q12 order 11/4; Delta eventually negative and relative error order 1/2. Scalar input expansions omitted from named export. |
| `as-pi` | `as_pi`, Projector:76 | FAIL (F1); estimates PASS | Correct absolute-ratio inequality, 0≤pi22≤Q12²/Delta², trace, orders 5/4 and 5/2. Signed identity is a separate helper. |
| `as-c` | `as_c`, Coeffs:62 | FAIL (F1); estimates PASS | c1,c2,c3 leading coefficients 3m2/(32m0m1), −3m1/(8m0m2), −9/(16m0), orders 1,2,3/2 with errors 3,4,7/2; c4,c5,c6 orders 7/2,9/4,11/4. Raw combinations are separate helpers. |
| `as-ent` | `as_ent`, Entries:32 | PASS WITH NOTES (N2–N3) | beta00−8c1 and beta01−4c3 order 7/2; beta11−8c2 order 4; all three final leading limits with errors 3,7/2,4. Intermediate a,d,b statements are the same claims divided by 8,8,4. |

For `as_ent`, the intermediate relative correction orders are 5/2,2,2: divide the displayed absolute corrections by c1,c2,c3, whose nonzero leading coefficients and eventual comparison follow from `hp` and `as_c`. The final beta00 error is O(alpha³), since c1 itself has relative error O(alpha²); it must not be described as a final relative O(alpha^(5/2)) error. All filters are `𝓝[>] 0`, definitionally `nhdsWithin 0 (Ioi 0)`, and powers with fractional exponents are real powers. Index 0 is physical planet 1, index 1 is planet 2; coefficient indices 0..5 are c1..c6. No determinant node is assigned to T18 alone.

## Binder and definition audit

This expanded table applies separately to each of the four main exports; all binders are explicit, in the order `p`, `hp`.

| Export | Expanded input | Bin | Authority |
|---|---|---|---|
| `as_in` | `p : PlanarData` | TYPING | Setting.lean:31–34; fixed physical data |
| `as_in` | `hp.1 : 0 < p.G` | STANDING | blueprint:231, positive G |
| `as_in` | `hp.2.1 : 0 < p.m0` | STANDING | blueprint:231, positive central mass |
| `as_in` | `hp.2.2 0 : 0 < p.m 0` | STANDING | blueprint:231, positive first planet mass |
| `as_in` | `hp.2.2 1 : 0 < p.m 1` | STANDING | blueprint:231, positive second planet mass |
| `as_pi` | `p : PlanarData` | TYPING | Setting.lean:31–34; fixed physical data |
| `as_pi` | `hp.1 : 0 < p.G` | STANDING | blueprint:231, positive G |
| `as_pi` | `hp.2.1 : 0 < p.m0` | STANDING | blueprint:231, positive central mass |
| `as_pi` | `hp.2.2 0 : 0 < p.m 0` | STANDING | blueprint:231, positive first planet mass |
| `as_pi` | `hp.2.2 1 : 0 < p.m 1` | STANDING | blueprint:231, positive second planet mass |
| `as_c` | `p : PlanarData` | TYPING | Setting.lean:31–34; fixed physical data |
| `as_c` | `hp.1 : 0 < p.G` | STANDING | blueprint:231, positive G |
| `as_c` | `hp.2.1 : 0 < p.m0` | STANDING | blueprint:231, positive central mass |
| `as_c` | `hp.2.2 0 : 0 < p.m 0` | STANDING | blueprint:231, positive first planet mass |
| `as_c` | `hp.2.2 1 : 0 < p.m 1` | STANDING | blueprint:231, positive second planet mass |
| `as_ent` | `p : PlanarData` | TYPING | Setting.lean:31–34; fixed physical data |
| `as_ent` | `hp.1 : 0 < p.G` | STANDING | blueprint:231, positive G |
| `as_ent` | `hp.2.1 : 0 < p.m0` | STANDING | blueprint:231, positive central mass |
| `as_ent` | `hp.2.2 0 : 0 < p.m 0` | STANDING | blueprint:231, positive first planet mass |
| `as_ent` | `hp.2.2 1 : 0 < p.m 1` | STANDING | blueprint:231, positive second planet mass |

Per export: TYPING=1, STANDING=4, SOURCE=0 additional binders, RULED=0, EXCESS=0. Total: 4,16,0,0,0 respectively. `PlanarData.Valid` is exactly the positivity conjunction above (Setting:36), not a hidden asymptotic or spectral assumption. There are no instance binders hiding a proof obligation. Quantified alpha is inside each Big-O/eventual assertion; its constants and threshold can depend on p but not alpha.

**New definitions/abbreviations/structures: none.** All 65 declarations are theorems. Local `set`/`have` bindings name existing expressions. The body/carrier/well-definedness/characterization/choice-independence definition tests are N/A for new definitions. Imported meaning-bearing objects were checked at use: `PlanarData.actions` is m_i sqrt(kappa a_i), `kappa=G*m0`; Q is the exact Laplace formula; sigma uses the sorted sqrt discriminant; the projector is `(sigma0-sigma1)⁻¹ • (Q-sigma1*Id)`; coefficients use the six literal action denominators; beta is the polynomial `beta_def` evaluated on those coefficients and that projector. No replacement objects or off-source fallback definitions are added. Positive alpha sufficiently below 1 lies in the axis cone; positivity/lower bounds are proved before inversion.

The transitive project import scan visits 213 modules, no provider, no frozen theorem, and 58 frozen definitions, all manifest state SEALED. The main source-facing frozen conventions checked include `Phase` (Pi coordinate pairs), `fixedHamiltonian`, normalized `secularAverage` with physical 2pi angular integration, and oscillator actions `(p²+q²)/2`. The axiom checks below cover imported proof closure; this is not a fresh mathematical audit of all upstream providers or definitions.

## Public helper ledger

Each helper is a distinctly named auxiliary result, not a substitute for a source node. Conditional Big-O/analytic/arithmetic hypotheses here are the hypotheses of the abstract helper being proved; the main proof supplies them from actual earlier lemmas. Main exports assume none of them. All rows pass local statement/proof and axiom checks; F1 only affects the named graph exports above. Locations use snapshot v1; paths are relative to `AsymptoticEntries/`.

| Source node served | Declaration | Location | Verdict / role |
|---|---|---|---|
| `as-in/as-pi/as-c/as-ent` | `p11cAe_pos` | `Calculus.lean:23` | PASS; power-product/division calculus or proved lower-bound transfer |
| `as-in/as-pi/as-c/as-ent` | `p11cAe_lt_one` | `Calculus.lean:25` | PASS; power-product/division calculus or proved lower-bound transfer |
| `as-in/as-pi/as-c/as-ent` | `p11cAe_mul` | `Calculus.lean:29` | PASS; power-product/division calculus or proved lower-bound transfer |
| `as-in/as-pi/as-c/as-ent` | `p11cAe_const_mul` | `Calculus.lean:36` | PASS; power-product/division calculus or proved lower-bound transfer |
| `as-in/as-pi/as-c/as-ent` | `p11cAe_div` | `Calculus.lean:41` | PASS; power-product/division calculus or proved lower-bound transfer |
| `as-in/as-pi/as-c/as-ent` | `p11cAe_natPow` | `Calculus.lean:51` | PASS; power-product/division calculus or proved lower-bound transfer |
| `as-in/as-pi/as-c/as-ent` | `p11cAe_sqrt` | `Calculus.lean:55` | PASS; power-product/division calculus or proved lower-bound transfer |
| `as-in/as-pi/as-c/as-ent` | `p11cAe_lower` | `Calculus.lean:60` | PASS; power-product/division calculus or proved lower-bound transfer |
| `as-c` | `p11cAe_act0` | `CoeffEq.lean:28` | PASS; exact action/physical coefficient identity; constants precede alpha |
| `as-c` | `p11cAe_act1` | `CoeffEq.lean:33` | PASS; exact action/physical coefficient identity; constants precede alpha |
| `as-c` | `p11cAe_sqrt_rpow` | `CoeffEq.lean:37` | PASS; exact action/physical coefficient identity; constants precede alpha |
| `as-c` | `p11cAe_c0_eq` | `CoeffEq.lean:41` | PASS; exact action/physical coefficient identity; constants precede alpha |
| `as-c` | `p11cAe_c1_eq` | `CoeffEq.lean:52` | PASS; exact action/physical coefficient identity; constants precede alpha |
| `as-c` | `p11cAe_act_mul` | `CoeffEq.lean:63` | PASS; exact action/physical coefficient identity; constants precede alpha |
| `as-c` | `p11cAe_c2_eq` | `CoeffEq.lean:71` | PASS; exact action/physical coefficient identity; constants precede alpha |
| `as-c` | `p11cAe_c3_eq` | `CoeffEq.lean:82` | PASS; exact action/physical coefficient identity; constants precede alpha |
| `as-c` | `p11cAe_den` | `CoeffEq.lean:93` | PASS; exact action/physical coefficient identity; constants precede alpha |
| `as-c` | `p11cAe_c_rpow` | `CoeffEq.lean:107` | PASS; exact action/physical coefficient identity; constants precede alpha |
| `as-c` | `p11cAe_c4_eq` | `CoeffEq.lean:117` | PASS; exact action/physical coefficient identity; constants precede alpha |
| `as-c` | `p11cAe_c5_eq` | `CoeffEq.lean:126` | PASS; exact action/physical coefficient identity; constants precede alpha |
| `as-c` | `p11cAe_X0` | `Coeffs.lean:29` | PASS; raw pair-combination asymptotic |
| `as-c` | `p11cAe_X1` | `Coeffs.lean:36` | PASS; raw pair-combination asymptotic |
| `as-c` | `p11cAe_X3` | `Coeffs.lean:41` | PASS; raw pair-combination asymptotic |
| `as-c` | `p11cAe_A6` | `Coeffs.lean:44` | PASS; raw pair-combination asymptotic |
| `as-c` | `p11cAe_A7` | `Coeffs.lean:47` | PASS; raw pair-combination asymptotic |
| `as-c` | `p11cAe_A1` | `Coeffs.lean:50` | PASS; raw pair-combination asymptotic |
| `as-c` | `p11cAe_X4` | `Coeffs.lean:53` | PASS; raw pair-combination asymptotic |
| `as-c` | `p11cAe_X5` | `Coeffs.lean:57` | PASS; raw pair-combination asymptotic |
| `as-ent` | `p11cAe_mono3` | `EntryBounds.lean:27` | PASS; abstract monomial or entry-error estimate |
| `as-ent` | `p11cAe_entA` | `EntryBounds.lean:58` | PASS; abstract monomial or entry-error estimate |
| `as-ent` | `p11cAe_entE` | `EntryBounds.lean:85` | PASS; abstract monomial or entry-error estimate |
| `as-ent` | `p11cAe_entB` | `EntryBounds.lean:112` | PASS; abstract monomial or entry-error estimate |
| `as-in` | `p11cAe_Q00` | `Inputs.lean:29` | PASS; exact Q formula or lower-bound/leading-order bookkeeping |
| `as-in` | `p11cAe_Q11` | `Inputs.lean:42` | PASS; exact Q formula or lower-bound/leading-order bookkeeping |
| `as-in` | `p11cAe_Q01` | `Inputs.lean:52` | PASS; exact Q formula or lower-bound/leading-order bookkeeping |
| `as-in` | `p11cAe_id` | `Inputs.lean:81` | PASS; exact Q formula or lower-bound/leading-order bookkeeping |
| `as-in` | `p11cAe_sqrt_isBigO` | `Inputs.lean:84` | PASS; exact Q formula or lower-bound/leading-order bookkeeping |
| `as-in` | `p11cAe_rpow_isBigO_of_lower` | `Inputs.lean:87` | PASS; exact Q formula or lower-bound/leading-order bookkeeping |
| `as-in` | `p11cAe_lead_isBigO` | `Inputs.lean:96` | PASS; exact Q formula or lower-bound/leading-order bookkeeping |
| `as-in` | `p11cAe_b1_lead` | `Inputs.lean:101` | PASS; exact Q formula or lower-bound/leading-order bookkeeping |
| `as-in` | `p11cAe_b2_lead` | `Inputs.lean:105` | PASS; exact Q formula or lower-bound/leading-order bookkeeping |
| `as-in` | `p11cAe_lead_isBigO'` | `Inputs.lean:109` | PASS; exact Q formula or lower-bound/leading-order bookkeeping |
| `as-in` | `p11cAe_congr_exp` | `Inputs.lean:115` | PASS; exact Q formula or lower-bound/leading-order bookkeeping |
| `as-in` | `p11cAe_rpow_three_half` | `Inputs.lean:119` | PASS; exact Q formula or lower-bound/leading-order bookkeeping |
| `as-in/as-c` | `p11cAe_npow_le` | `Leading.lean:25` | PASS; explicit jet/Laplace leading term or polynomial-power comparison |
| `as-in/as-c` | `p11cAe_pair_lead` | `Leading.lean:34` | PASS; explicit jet/Laplace leading term or polynomial-power comparison |
| `as-in/as-c` | `p11cAe_A` | `Leading.lean:44` | PASS; explicit jet/Laplace leading term or polynomial-power comparison |
| `as-in/as-c` | `p11cAe_B` | `Leading.lean:50` | PASS; explicit jet/Laplace leading term or polynomial-power comparison |
| `as-in/as-c` | `p11cAe_p1` | `Leading.lean:57` | PASS; explicit jet/Laplace leading term or polynomial-power comparison |
| `as-in/as-c` | `p11cAe_p2` | `Leading.lean:63` | PASS; explicit jet/Laplace leading term or polynomial-power comparison |
| `as-in/as-c` | `p11cAe_p3` | `Leading.lean:69` | PASS; explicit jet/Laplace leading term or polynomial-power comparison |
| `as-in/as-c` | `p11cAe_p4` | `Leading.lean:75` | PASS; explicit jet/Laplace leading term or polynomial-power comparison |
| `as-in/as-c` | `p11cAe_p5` | `Leading.lean:81` | PASS; explicit jet/Laplace leading term or polynomial-power comparison |
| `as-in/as-c` | `p11cAe_p6` | `Leading.lean:88` | PASS; explicit jet/Laplace leading term or polynomial-power comparison |
| `as-in/as-c` | `p11cAe_b1` | `Leading.lean:96` | PASS; explicit jet/Laplace leading term or polynomial-power comparison |
| `as-in/as-c` | `p11cAe_b2` | `Leading.lean:108` | PASS; explicit jet/Laplace leading term or polynomial-power comparison |
| `as-in/as-c` | `p11cAe_rpow_isBigO` | `Pair.lean:26` | PASS; pair-jet remainder or power comparison |
| `as-in/as-c` | `p11cAe_pow_mul_isBigO` | `Pair.lean:35` | PASS; pair-jet remainder or power comparison |
| `as-in/as-c` | `p11cAe_pair` | `Pair.lean:43` | PASS; pair-jet remainder or power comparison |
| `as-pi` | `p11cAe_proj_exact` | `Projector.lean:26` | PASS; exact projector identity or eventual Delta lower bound |
| `as-pi` | `p11cAe_delta_lower` | `Projector.lean:59` | PASS; exact projector identity or eventual Delta lower bound |

Proof review: Pair obtains analytic remainders from T4's `p11c_comp_vanishes` and bounds them near zero. Leading keeps the actual jet coefficients and uses quadratic consistency to recover the two Laplace expansions. Inputs cancels only positive mass/action denominators, proves a dominating negative Q11 term, and controls inverse Q11 before the Delta ratio. Projector proves R>0 and R≥|Delta| before cross multiplication, then uses orders 11/4−3/2=5/4 and twice 5/4=5/2. CoeffEq tracks alpha powers 1,0,1/2,3/4,1/4 in the action denominators. EntryBounds checks each monomial's exponent by arithmetic; Entries supplies all eight Big-O premises using `as_c`/`as_pi` and expands the actual beta polynomial with u=1−v. No circular dependency, changed sign convention, non-Pi norm, output-shaped premise in a main theorem, or renamed missing main result was found.

## Independent verification

All Lean/Lake commands below were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No clean, update, cache fetch, package mutation or full-library rebuild was run.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t18 KAM.Planetary.PlanarTorsion.AsymptoticEntries
```

Exit 0. Output included `[inp-gate] slot 2 acquired 23:33:30` and `Build completed successfully (9259 jobs).` Warnings are disclosed in N2; this is not a warning-free receipt.

2. Lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1; exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1067 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is precisely the generated-root exception permitted by the brief. The root was not regenerated.

3. Axioms and export applications:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T18-probe.lean
```

Exit 0. The probe imports the facade, issues `#print axioms KAM.Planetary.<name>` for all 65 distinct public theorems, checks four full-type applications of the actual exports, and independently proves the two omitted scalar expansions and eventual projector identity. Every one of the 65 axiom outputs is exactly `[propext, Classical.choice, Quot.sound]`. In particular:

```text
'KAM.Planetary.as_in' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.as_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.as_c' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.as_ent' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Probe-only warnings: the two scalar reconstructions do not need hp (they follow from universal Laplace expansion helpers). No error, sorryAx or project axiom occurs. The probe and output are removed after transcription. Reproduction: enumerate `^theorem ([\w']+)` in the nine submodules, prepend `#print axioms KAM.Planetary.`, and import the facade; preserve apostrophes in theorem names.

4. Kernel replay, a single invocation over all ten scoped modules:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.AsymptoticEntries KAM.Planetary.PlanarTorsion.AsymptoticEntries.Pair KAM.Planetary.PlanarTorsion.AsymptoticEntries.Calculus KAM.Planetary.PlanarTorsion.AsymptoticEntries.Leading KAM.Planetary.PlanarTorsion.AsymptoticEntries.CoeffEq KAM.Planetary.PlanarTorsion.AsymptoticEntries.EntryBounds KAM.Planetary.PlanarTorsion.AsymptoticEntries.Inputs KAM.Planetary.PlanarTorsion.AsymptoticEntries.Projector KAM.Planetary.PlanarTorsion.AsymptoticEntries.Coeffs KAM.Planetary.PlanarTorsion.AsymptoticEntries.Entries
```

Exit 0. Exact scoped replay output (the invocation also checks the imported environment):

```text
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Calculus
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.CoeffEq
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Entries
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Coeffs
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Leading
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Pair
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Inputs
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.EntryBounds
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Projector
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries
```

5. Mechanical source and ownership checks:

- `git diff --check inp...HEAD`: exit 0 (only the disclosed multiple-merge-base warning).
- Scoped forbidden-token/override scan: zero `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, or `set_option` matches.
- Every file has copyright, `module`, public imports, module docstring and public section. Maximum file size 198 lines; maximum line width 100 Unicode characters. No definition body exposure issue arises because the package defines no objects.
- Source declaration-name scan over KAM finds each of the 65 short names exactly once (including `p11cAe_lead_isBigO'`); all 61 helpers are `p11cAe_` names in namespace `KAM.Planetary`. No root namespace declaration, instance, notation, or harmful shadowing is introduced.
- T18 protected-path delta is empty; broad three-dot protected-path delta is not (N1).

### Minimal reproduction of the source-clause refutation check

The following is part of the successful disposable probe (with the facade imported and `KAM.Planetary Set Filter Asymptotics Real` opened). It demonstrates both the narrower node export and the available mathematical repair ingredient:

```lean
example (p : PlanarData) (hp : p.Valid) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, p11c_projector p ![a, 1] 0 1 = -p11c_Q p ![a, 1] 0 1 /
      √((p11c_Q p ![a, 1] 0 0 - p11c_Q p ![a, 1] 1 1)^2 + 4*p11c_Q p ![a, 1] 0 1^2) := by
  fail_if_success exact as_pi p hp
  filter_upwards [(as_in p hp).2.2.2.1] with a ha
  exact (p11cAe_proj_exact p ha).1
```

For the first scalar clause the successful proof takes
`(p11cAe_mul p11cAe_id p11cAe_b1).const_mul_left (p.G * p.m 0 * p.m 1 / 4)`,
converts the comparison exponent `1+3` to `4`, and uses `ring` under positive alpha.
The second uses `p11cAe_b2`, exponent `1+4=5`, and the same scalar multiplier.
These checks certify the missing expansions with remainders O(alpha^4) and O(alpha^5),
respectively. They do not modify or strengthen the existing package export types.

## Errata, limits and closeout

No new suspected pinned-source or blueprint mathematical defect was found. Inherited CP11 B.6 erratum and earlier global-frame/angle-lift issues are not newly resolved or changed by T18. The blueprint, graph and signature were checked as local pinned artifacts; no fresh audit of CP11's PDF or of all upstream physical-attachment proofs was attempted. Full signed T19, uniform mass-ratio constants, determinant/homogeneity, torsion and physical theorem closure remain outside this audit.

Permission/decision log: followed the user's report-only path, scoped inspection and serialized build authorization; applied the handoff's stricter unsigned-export rule; accepted only the brief's explicit stale-root exception; left all proposed repairs unapplied. No additional approval was required. The report is complete as an audit even though the literal export-contract finding remains open. Before a package PASS under this brief, F1 must be closed or the narrower API expressly authorized. All 65 declarations and all four scoped nodes are classified; no unclassified mathematical finding is promoted to a blocker.

# SO-R1 independent audit 1

Verdict: **PASS WITH NOTES** for SO-R1, including all five signed declarations. No Lean correctness defect or unpaid analytic premise was found. Notes concern inaccurate handoff prose, superseded design numbers, and the generated-root lint exception. This is parameter infrastructure, not a lunar certificate, barrier theorem, or frozen-anchor seal.

## Scope and authority

Audited `/root/code/KAM-inp-sor1`, HEAD `defa4b8d5efc113087f8890148d21f81a45c1828`, against `inp` at `6cc8c0e509fe0f60c41c49ebe065a4a595cb4973`, using the full `git diff inp...HEAD`. Read AGENTS.md, PLAN, DECISIONS, the package-audit brief, SO-R1 handoff and producer brief, signed `SOSignaturesLunar.lean` §I.4, the SO design §6 and Appendix I.4, O5, CONSTANTS-STUDY §2.2/§4, and SO-GEN2-rotated-frame-candidates. There is no SO frozen anchor or SO `statement.md` for this package; the signed design is its statement authority. The relevant imported frozen definitions were inspected.

The full diff has six added files: LunarParams, the SO-R1 handoffs, and inherited SO-GRAPH implementation/tests/handoff. Commits `02ff5ed3` and `defa4b8d` are R1; the graph files come from the parent branch. They were read and included in the build, theorem-axiom checks and kernel replay, but this report's signed-interface verdict concerns R1. No SO-GRAPH seal or separate signature audit is asserted.

The requested worktree report path overrides the generic brief's instruction to put reports in `/root/code/KAM-inp`. Only this report and temporary `.lake/abi-scratch/SOR1Audit.lean` were written in the repository; no state-changing git command was used.

## Declaration review

Names in this table have prefix `KAM.SpinOrbit.`. The source file is `KAM/SpinOrbit/LunarParams.lean`.

| Node / location | Declaration | Verdict | Reason |
|---|---|---|---|
| Signed I.4, line 26 | `lunarR1TimeScale` | PASS | Exact signed name, type and body; `237/125`. |
| Signed I.4, line 28 | `lunarR1Scalar` | PASS | Exact signed name, type and body; `1 + 1/10^6`. |
| Signed I.4, line 31 | `lunarR1Kappa` | PASS | Exact signed name, type and body; `c/s`. |
| Signed I.4, line 34 | `lunarR1` | PASS | Exact signed name, binders, type and all fields. |
| Signed I.4, line 52 | `lunarR1Kappa_div` | PASS | Exact signed theorem header; kernel proof of `κ/42 = 316000/7000007`. |
| Static helper, line 59 | `lunarR1StaticCore` | PASS | Faithful dimension-2 parameter sub-conjunction; see below. |
| Static helper, line 65 | `lunarR1_staticCore_zero` | PASS | Kernel decision for zero budgets. |
| Static helper, line 69 | `lunarR1_staticCore` | PASS | Stronger than nonnegative-budget request: core independent of both budgets. |
| Static helper, line 73 | `lunarR1_err_nonneg` | PASS | Source premise `0 ≤ err` pays exactly the omitted error conjunct. |
| Static helper, line 78 | `lunarR1_staticCore_gen2` | PASS | Literal budgets `41/10^79 = 4.1e-78`, `79/10^79 = 7.9e-78`; both above the reported budgets. |
| Smallness, line 87 | `lunarR1_smallness_C1` | PASS | Checker's strict C1 inequality at `1/10^75`. |
| Smallness, line 94 | `lunarR1_smallness_C1_fails` | PASS | Same strict inequality false at `1/10^74`; nonvacuous. |
| Displacement, line 102 | `lunarR1_smallness_C2` | PASS | Checker's C2 inequality, `err=1/10^75`, `disp=1/10^39`. |
| Box helper, line 110 | `lunarR1Box` | PASS | Rational center/radius enclosure for all rational `a,b`; nonnegative radii. |
| Ray margins, line 116 | `lunarR1_rayMargins` | PASS | Both exact boxes, both positive lower bounds and both margin inequalities. |
| Norm helper, line 126 | `lunarR1Box_normLo` | PASS | Explicit first-coordinate bound is necessary and sufficient for the max reduction; distinct conditional helper, not a substituted source theorem. |

The four signed definition blocks, including their intervening docstrings, compare byte-for-byte equal to the signed draft. The theorem header also compares byte-for-byte equal; its design `sorry` body is replaced by `decide +kernel`, as required. All five declarations are in the signed namespace `KAM.SpinOrbit`. A fresh namespace copy of the signed block elaborated with theorem body `by exact KAM.SpinOrbit.lunarR1Kappa_div`; `type_of%` and `rfl` examples checked the theorem type and each definition against the originals. There are no explicit theorem binders requiring seal-body arguments. Provider/frozen-anchor matching is otherwise inapplicable: this package supplies neither a provider nor a new frozen theorem.

## Definitions and mathematical checks

Every new R1 definition is an intended total object on its entire carrier:

- `lunarR1TimeScale`, `lunarR1Scalar`, `lunarR1Kappa`: exact rational constants, nonzero denominators.
- `lunarR1 err disp`: pure rational parameter record, preserving both supplied budgets exactly. Negative inputs remain negative; no fallback conceals a failed check. Validity is established only by the relevant predicates.
- `lunarR1StaticCore`: a Bool predicate, not a proof-bearing bundle or replacement checker. At `n=2`, `2 ≤ n` is true and `n ≤ tau+1` becomes `2 ≤ tau+1`. All fifteen nontrivial retained parameter conjuncts match `checkStatic` verbatim, with no weakened inequality. `0 ≤ err` is separately proved; shapes, weight equality/validity, pi enclosure and frequency-box/margin checks are deliberately outside this helper. Displacement positivity is not a `checkStatic` conjunct. This does not prove a whole certificate passes.
- `lunarR1Box a b`: center `κ((a+b·2.236068)/3118−1)`, radius `κ|b|/(3118·10^6)`, second coordinate `(κ,0)`. No indexing/default fallback occurs in R1.

All parameters match the latest signed Revision 6 package: `tau=1`, `rho=1/70`, `rhoInf=1/70000`, all four majorants `1987/1000`, `mu=1/160`, `gamma=gammaBar=κ/42=c/(42s)`, `sigmaOmega=2`, `nuRay=1/10^6`, `s=1+1/10^6`, `E0=0`, `c=237/125`. O5 fixes the rotated route and widths/margin; the later measured Revision 6 fixes the revised majorants and time scale. The older constants-study table is not byte-identical to Revision 6 (see documentation findings).

The C1/C2 expressions use the landed `isoC1Q`/`isoC2Q` with exactly the argument order, dimension, powers, inequality direction and strictness used by `checkSmallness` (`KAM/Certificate/Defs.lean`, definition `checkSmallness`). An audit `rfl` example confirmed the expansion of `checkSmallness`. No different mirror or reimplemented constant is used. These are separate conjunct checks at chosen budgets, not a claim that `checkTorusCertificate` passes.

Exact rational values were evaluated by Lean in the scratch probe; decimal summaries below were computed from those numerator/denominator pairs:

| Quantity | Independently checked value |
|---|---:|
| `gamma^4 rho^4 / isoC1Q` | `2.1424798055294127e-75` |
| Its base-10 logarithm | `-74.66908326293498` |
| `isoC2Q / (gamma^2 rho^2)` | `1.16403215894492e35` |
| Its base-10 logarithm | `35.065964978818506` |
| C1 ratio at `4.03e-78` | `0.0018809978930019254` (headroom `531.6327`) |
| C1 ratio at `7.84e-78` | `0.003659311037502505` (headroom `273.2755`) |
| Minimum disp at those budgets | `4.691049600548027e-43`, `9.126012126128172e-43` |

Thus the threshold is the checker's, and the passing/failing decade tests bracket it correctly. The decimal logarithm is a numerical summary, not an additional Lean theorem.

The audit additionally proved in the scratch probe `2236067/10^6 ≤ sqrt 5 ≤ 2236069/10^6` using nonnegativity and `(sqrt 5)^2=5`, verified `checkAlgBox` by kernel decision for both coefficient lists, and applied `algFreq_encloses` with `lunarRotFreqMinus_eq` / `lunarRotFreqPlus_eq`. Both full `FreqEncloses` propositions elaborated. Consequently these boxes contain the exact frequencies, not merely rounded versions. The retained signed R1 file itself does not export those enclosure theorems; consumers must establish their own actual certificate-box relation.

No conclusion-shaped analytic premise or hidden instance supplies a hard step. `lunarR1Box_normLo` is explicitly a conditional max-arithmetic helper; the two concrete ray margins are independently decided without its hypothesis.

## Full-diff inherited files

`Graph/Cert.lean` defines `KAM.Certificate.SoGraphCert`, `soGraphMonoModel`, `soGraphActionModel`, `checkSoGraph`. These are data, exact denotation models and a Bool checker respectively. The DK entry `(0,0)` and action entry `0` are the intended components; `getD` defaults follow the total embedding denotation and are enclosed by the existing model theorems, not assumed to be valid certificate shapes. The negative action model pays the upper bound by `checkRealLowerBound_sound`. `SoGraphCert` bundles data only.

Its eight public theorems (`norm_fst_apply_sub_le`, `norm_snd_apply_sub_le`, `realPt_one_zero`, `soGraph_deriv_transfer`, `checkSoGraph_sound`, `soGraph_exactTorus`, `soBarrier_of_cert`, `soRotBarrier_of_cert`) were read and pass the expanded hygiene checks. The open-strip derivative transfer uses every `0<delta<rho` and a midpoint contradiction to obtain the endpoint bound. `soGraph_exactTorus` uses the black box's displacement on that same strip, transfers values in the product/Pi max norm, and scales the Diophantine constant by positive `sinf`. Both barrier routes call the landed theorems.

`Tests/GraphCert.lean` defines eight explicitly scoped toy data objects (`graphToyW`, `graphToyPi`, `graphToyCfg`, `graphToyCos`, `graphToyK`, `graphToyParams`, `graphToyBase`, `graphToy`). Its defaults are meaningful for the fields read by the graph-only check; the module expressly disclaims full-certificate validity. Four public tests (`graphTest_pass`, `graphTest_mono_fail`, `graphTest_range_fail`, `graphTest_margin_fail`) pass kernel replay and exhibit acceptance and three rejection modes. These inherited test fixtures are not lunar SO-DATA placeholders.

## Validation receipts

All Lean/Lake commands were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`. No heartbeat, recursion-depth or synthesis override was used. No clean, update, cache regeneration, protected-file write, or `.lake/packages` edit was performed.

Build command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sor1 KAM.SpinOrbit.LunarParams KAM.SpinOrbit.RotFreq KAM.SpinOrbit.Graph.Cert KAM.SpinOrbit.Tests.GraphCert
```

Exit 0: `Build completed successfully (3333 jobs).` Existing replayed modules emit unused-section-variable warnings; no warning was attributed to LunarParams. Log during audit: `/tmp/maud-sor1-build.log`.

Probe command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOR1Audit.lean
```

Final exit 0, no errors. Earlier scratch-only iterations fixed explicit rational endpoint casts and a multiline `#eval` layout; these were probe construction errors, not package errors or default-heartbeat failures. Final probe checked signed definitions/type/application, checker expansion, both exact box enclosures and rational threshold values. Probe removed after validation.

The probe issued `#print axioms` for every new public theorem in all three added Lean modules. Exact output for R1:

```text
'KAM.SpinOrbit.lunarR1Kappa_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_staticCore_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_staticCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_err_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_staticCore_gen2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_smallness_C1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_smallness_C1_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_smallness_C2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1_rayMargins' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1Box_normLo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All eight inherited graph theorems and all four graph tests likewise printed `[propext, Classical.choice, Quot.sound]`: 22 theorem receipts total. There are ten R1 theorems, not eleven. No `sorryAx` or additional axiom appears.

Kernel command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.LunarParams KAM.SpinOrbit.Graph.Cert KAM.SpinOrbit.Tests.GraphCert
```

Exit 0. Complete output:

```text
replaying KAM.SpinOrbit.Tests.GraphCert
replaying KAM.SpinOrbit.Graph.Cert
replaying KAM.SpinOrbit.LunarParams
```

Short-name command:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sor1 KAM.SpinOrbit.LunarParams
```

Exit 0: `short-name check OK (no reused public short name)`.

R1's transitive KAM import closure has 99 modules, no provider and no frozen theorem; all 19 frozen imports are manifest `SEALED` definitions. This was checked recursively from source imports against each manifest `path`/`state`, not inferred from a successful build.

All three added Lean files have the required copyright, `module`, public imports, module docstring and public section. R1's unfolding definitions are exposed. Line counts: R1 134, Graph/Cert 255, graph tests 92. Forbidden proof escapes and resource overrides were also checked by repository lint.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. `git diff --check inp...HEAD` exits 0.

Lint command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, with this complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1382 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The only failure is the generated `KAM.lean` staleness explicitly permitted by the audit brief. Module checks, forbidden-token checks, line limits, frozen-anchor guard and all 144 ABI hashes pass. The generated root was left untouched as required.

## Documentation defects / errata candidates

1. **Handoff numerical headroom, not a theorem defect.** `docs/tracks/SO/audits/SO-R1-handoff.md:25-26` says “4.03e-78 is 10^{-3.73} of threshold (×~5300), 7.84e-78 is ×~2700.” The independently evaluated threshold gives `10^-2.72561`, ×531.63 and ×273.28 respectively. The ratios are ten times larger than that prose suggests. The duplicate `.drafts/handoff-SO-R1.md` has the same issue. The Lean checks and the design §6 ratios `1.9e-3 / 3.7e-3` are correct.
2. **Overbroad box statement.** Handoff line 34 says “Any box whose second entry is (κ, 0) gives L = κ.” That gives `L ≥ κ`; equality also needs every other coordinate lower contribution ≤ κ. For example a first entry `(3κ,0)` gives `L=3κ`. The Lean theorem at LunarParams:126-128 correctly includes the needed hypothesis; both concrete boxes satisfy it. No theorem repair is required.
3. **Theorem count.** Handoff line 45 says “All eleven theorems”. There are ten; all ten were independently checked.
4. **Superseded values still presented as O5 R1.** `docs/tracks/SO/design/SO-LEAN-DESIGN.md:121` says “M = σK = σB = σT = 39/20” and “lunarR1TimeScale = 7/4”. CONSTANTS-STUDY:201 retains the same original R1 row. The later design row at :97, §6 at :499-507 and signed Appendix I.4 use `1987/1000`, `237/125` and explicitly identify the old numbers as Revision 5 projections. Thus a literal claim that all these documents have the same exact numbers is false. Current Lean follows the controlling signed Revision 6 text and the prompt's explicit numbers. Label the old O5 row as historical; preserve the study's projection context. This is documentation drift, not a pinned mathematical-source erratum or unauthorized parameter change by the prover.

No suspected defect in an external pinned mathematical source was found. No introduced source deviation, weakened signed declaration, placeholder, unproved R1 theorem, or whole-certificate conclusion was found. Remaining work is SO-DATA's concrete certificate construction and checks; it is outside this parameter package.

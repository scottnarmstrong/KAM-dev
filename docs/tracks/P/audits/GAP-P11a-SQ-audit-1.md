# GAP-P11a-SQ independent audit 1

Verdict: **PASS** for the five assigned graph nodes and the auxiliary exponent lemma.
No frozen anchor is supplied or sealed by this package; “seal-ready” is therefore not applicable.
This is a scoped graph-export/package audit, not closure of P-G, P-PLANAR, P-FIXED, or another
campaign theorem. Generated-root staleness is permitted by the audit brief and explicitly excluded
as a finding by the handoff ruling.

Audited HEAD: `c22444905131b11455b9081f4c2c7971d849a5a3`.
Comparison ref `inp`: `02f1bcd96b3681d37a276e77c2ec795dbece6ae4`.
The full `git diff inp...HEAD` consists of three new Lean modules, 272 lines total:

- `KAM/Planetary/WeakKAM/ScheduleNodes.lean` (90 lines).
- `KAM/Planetary/Quantitative/TheoremNodes.lean` (78 lines).
- `KAM/Planetary/Quantitative/KamInputNodes.lean` (104 lines).

Authority read: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local
`docs/tracks/P/audits/GAP-P11a-SQ-handoff.md` including AUDIT FOCUS and the 02:30/02:40 rulings,
`docs/tracks/P/statement.md`, the relevant P11A/B/C design mappings, and the second gap plan
`/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P2.md` sections 2 and 6.
The user’s exact local report path overrides the generic brief’s main-worktree destination.

## Literal node comparison

Every named NODE record was read in full, including SOURCE_HYPOTHESES,
SOURCE_QUANTIFIERS, SOURCE_CONCLUSION and its cited blueprint text. All names in the table
are in `KAM.Planetary`.

| Graph node / auxiliary | Declaration and locator | Verdict | Literal conclusion and premise audit |
|---|---|---|---|
| `bpP:p11a:sel-data` | `sel_data_gamma`, `TheoremNodes.lean:33` | PASS | Graph `DEPGRAPH.md:24305`; blueprint `p11a3-iteration-selection.tex:32–40`. Exports `2 * selectionGamma d = p11GammaStar ... d.loss` with `m=N`, the same rho, mu, beta, max diameter, theta, M and tau in `p11CDio`, plus the requested inequality. Source scalar/Hamiltonian hypotheses are packaged by the existing `SelectionData`; no gamma bound is assumed. Existing standing-data and perturbation definitions supply the definition-node part; the new export supplies its asserted property, exactly as the ruling requests. No perturbation-dependent gamma is introduced. |
| `stepP:p11a:fe-supp` | `fe_supp`, `ScheduleNodes.lean:30` | PASS | Graph `DEPGRAPH.md:25000`; blueprint `p11a3-iteration-selection.tex:156–167`. For every `j < nu`, exports the closed max-distance theta/(2 sqrt N) support inclusion, its Euclidean theta/2 consequence, inclusion in the Euclidean theta-thickening, that thickening’s inclusion in the real points of the complex 2 theta collar, and support inclusion in the open stage collar. `SelectionExtensionChain` is the parent lemma’s source nested nonempty compact prefix and holomorphic/real/bounded increments, not a dependency’s conclusion. Its fields are inspected at `WeakKAM/Schedule.lean:227–240`. The support bound is the explicit source premise; nesting is composed inside the proof via `selectionChain_antitone`. Positivity of t0 and nonnegative tau are schedule premises. K_theta subset V is proved rather than assumed. |
| `stepP:p11a:qt-order` | `qt_order`, `TheoremNodes.lean:46` | PASS | Graph `DEPGRAPH.md:28230`; blueprint `p11a5-quantitative-theorem.tex:93`. From `d.Valid` alone proves positive gamma, admissible threshold, volume K and max diameter, and Euclidean K_theta subset the real 2 theta collar. Omitting h, f and the perturbation bound strengthens the mathematical claim. The source sentence that the input does not mention any conclusion is a metamathematical hygiene assertion: inspection of `Valid` and `QuantitativeInput` verifies it; it is not an omitted mathematical proposition. |
| `stepP:p11a:qt-reduce` | `qt_reduce`, `TheoremNodes.lean:63` | PASS | Graph `DEPGRAPH.md:28258`; blueprint `p11a5-quantitative-theorem.tex:95`. From `d.Valid` and `QuantitativeInput d h f`, constructs ds and m0 internally. Exports ds.h=h, exact numerical-data correspondence, actual derivative supremum <= m0, the perturbation package for every positive epsilon bounding f, gamma equality, and the minorant <= selection threshold. Thus the reduction output is constructed, not an extra premise. `qbcOfSelection ds m0=d` identifies m0 with the supplied upper bound; `selectionAdmissible ds` uses the actual supremum. This is the source’s actual-M0 reduction in the delivered representation. No eps_f or smallness premise is needed, so the export is stronger in that respect. |
| `bpP:p11:kam-input` | `kam_input`, `KamInputNodes.lean:41` | PASS | Graph `DEPGRAPH.md:19325`; blueprint `p11-cp09-preparation.tex:24–38`. Specializes N=n+n and rho=2, with the source numerical validity and A1–A4. Chooses gamma, threshold and cDelta before h, f and eps_f. Returns one family carrying K1–K4, including the literal compactness/measure, lattice-torus/Diophantine, displacement, injectivity, Borel-image and 2^(-2N) measure clauses. K5 quantifies c_star before varying beta and proves the required exponent identity. K6 quantifies its constants before beta and eps_f. Nonnegativity of eps_f is derived from the bound on f at a real point in the nonempty domain. No selected torus, Diophantine vector, Lipschitz estimate or iteration output is an input. |
| K5 auxiliary | `kam_input_B0`, `KamInputNodes.lean:31` | PASS | Under numerical validity and rho=2 proves `p11c_B0 d = mu*(mu+1)+2`. Uses mu>=1 to select the correct max branch. N is arbitrary, so this helper is stronger than the even-dimensional consumer needs. |

For fe-supp, the parent source at lines 156–157 explicitly supplies the chain assumptions;
the shortened graph hypothesis line does not repeat them. No prohibited assumption of a proved
dependency’s output was found. The holomorphic increment fields are unused by this geometric
step but are source hypotheses, not invented restrictions.

K2 was checked by unfolding the existing `IsLatticeTorus` definition
(`Hamiltonian/Transport.lean:44–54`): real analyticity, range/differentiability, primary lattice
law, injectivity modulo the integer lattice, injective differential, Lagrangian property and
the literal `HasDerivAt` orbit equation are all present. `IsDiophantine` carries the source gamma
and tau. The ambient Pi and product norms are max norms. `actionNbhd` uses strict complex
max-distance, whereas `selectionThick` and the displayed thickening in `qt_order` use closed
Euclidean distance. The proof explicitly pays the sqrt N conversion and uses theta < 2 theta.

K5 and K6 use record replacement `{d with beta := b}`. The lower bounds hold for every b in
`(0,min(1,M)]`, after a single choice of constants. `weak_kam_quantitative` chooses cDelta
before K, beta, M, M0, h and f; `kam_input` uses that witness. Its proof chooses kappa_D=1/2
and a_D=G0. These equalities are proof witnesses, not extra equations in the exported type;
the assigned kam-input source requires existence of positive kappa_D and nonnegative a_D,
which the type states. No source-required uniformity is lost.

## Signatures, definitions and completeness

All six exports are UNSIGNED additions under the explicit gap-programme ruling. None claims
to replace an existing SIGNED declaration; no existing signature or implementation was changed.
Frozen/provider type-equality and frozen seal-body probes are **not applicable**: there is no
provider export and no target frozen anchor in this slice.

There are **no new def, abbrev, structure, instance or notation declarations** to classify.
The imported carriers were inspected for their use here: `SelectionData` contains source
standing inputs, `SelectionPerturbation` contains source perturbation assumptions,
`SelectionSchedule` contains raw formula parameters, `SelectionExtensionChain` contains the
source prefix assumptions, `QuantitativeData.Valid` contains numerical/geometric restrictions,
`QuantitativeInput` contains A1–A4, and `QuantitativeFamily` is an output-only bundle.
`qbcOfSelection` copies the numerical fields and replaces only M0 by its supplied bound;
`selectionM₀` is the derivative supremum. No new junk-value or fallback definition occurs.
The frozen action-neighborhood, strip, frequency-map and real-Hamiltonian definitions were
also read to check domains, carrier and Hamiltonian identity.

The current ruling narrows the original gap-plan module assignments to exactly these five
nodes. Each is exported, and all six new public theorems are audited above. The previously
closed sp-1 through sp-5, qt-zero, qt-iter and qt-k5 are explicitly skipped by the handoff/ruling;
they are not unpaid items of this audit slice. P11A maps kam-input to the upstream quantitative
assembly consumed by Preparation/Wrapper; P11B maps sel-data and fe-supp to the standing-data
and finite-extension components; P11C maps qt-order and qt-reduce to Q6. The new leaf modules
make those particular obligations available without changing their earlier SIGNED parents.
This audit does not certify unrelated nodes of those larger modules/designs.

## Independent validation

All Lean-related invocations were serial within this audit, with `LEAN_NUM_THREADS=1` and
`nice -n 5`; the build gate itself applies nice. No budget override, clean, update or cache-fetch
command was used. Scratch files were confined to `.lake/abi-scratch/` and removed after checks.

Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-g11sq KAM.Planetary.WeakKAM.ScheduleNodes \
  KAM.Planetary.Quantitative.TheoremNodes KAM.Planetary.Quantitative.KamInputNodes
```

Exit 0. Gate output: `[inp-gate] slot 2 acquired 02:50:02 ...`.
Final output: `Build completed successfully (9253 jobs).`
Lake replayed warnings from existing dependency modules (unused variables/simp arguments and
deprecated names); these are not source changes in the three audited files.

Kernel replay, one invocation:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Planetary.WeakKAM.ScheduleNodes KAM.Planetary.Quantitative.TheoremNodes \
  KAM.Planetary.Quantitative.KamInputNodes
```

Exit 0; complete output:

```text
replaying KAM.Planetary.Quantitative.KamInputNodes
replaying KAM.Planetary.Quantitative.TheoremNodes
replaying KAM.Planetary.WeakKAM.ScheduleNodes
```

A scratch probe imported the three modules and ran `#print axioms` for every new public
theorem. Command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-g11sq-1-axioms.lean
```

Exit 0; complete output:

```text
'KAM.Planetary.fe_supp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sel_data_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qt_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qt_reduce' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.kam_input_B0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.kam_input' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely for the permitted generated-root staleness. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1218 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The current independent count is 1218; the handoff's older receipt says 1217.
No forbidden-token, resource-override, EuclideanSpace, overlength or module-format diagnostic
was emitted. The generated root was left untouched as required.

Static and protected-path checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty output.
- `git diff --check inp...HEAD` and `git diff --check`: exit 0, empty output.
- Maximum Unicode line lengths: ScheduleNodes 97, TheoremNodes 95, KamInputNodes 100.
  All files are below 1500 lines and carry the required copyright, module declaration,
  public imports, module docstring and public section.
- All six declaration short names occur exactly once among KAM declaration headers;
  no reused public helper name or harmful root shadow was introduced.
- Recursive KAM import scan: 207 KAM modules, zero providers, 26 frozen modules,
  all 26 manifest entries of kind definition and state SEALED. No frozen theorem,
  DRAFT_SORRY anchor or provider is imported in that closure.

## Uncertainties, source defects and deviations

No suspected blueprint/source defect, frozen-statement defect, or introduced mathematical
deviation was found in the assigned slice. The qt-order metamathematical sentence is verified
by premise inspection rather than encoded as a Lean proposition. Existing full-system and
physical-transfer obligations in the track statement remain outside this infrastructure audit.
No protected or generated file was edited, no git state-changing command was used, and the only
repository artifact written by this auditor is this report.

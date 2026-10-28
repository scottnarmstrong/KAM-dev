# Q5 independent package audit 1

Date: 2026-10-28. Audited worktree: `/root/code/KAM-inp-p11c-q5`.
Scope: only `KAM/Planetary/Quantitative/Zero.lean` at HEAD
`ec3da98b92fb1857a209775259027622d7347a19`.
Comparison branch at initial inspection: `inp`, `a81e8d4215d2f99f8c148dd4ca24915a17ca95b5`.

## Verdict

**PASS WITH NOTES — Q5 zero-case slice complete.** No mathematical, signature, premise, carrier,
norm or node-completeness defect found. The sole validation note is the permitted stale generated
`KAM.lean`; Q5 has no frozen anchor to seal.

Q5 is a helper package with no provider export or frozen theorem anchor. Provider/frozen-type and
seal-body probes are therefore inapplicable. The analogous exact-signature application is checked
against the standalone design declaration under a fresh name. This audit certifies the scoped zero
case only; it does not close the positive-perturbation theorem or P-G/P-PLANAR/P-FIXED.

Authority: user instructions and `Q5-handoff.md` AUDIT FOCUS; `AGENTS.md`, `docs/PLAN.md`,
`docs/DECISIONS.md`; `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`;
`P11C-LEAN-DESIGN.md` decisions 1–3, upstream rows U1/U11a1, node table L72–85, Q5/Q0 package
rows L195–196; `DESIGN-P11C-design-audit-1.md`; standalone
`/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` L240–246;
`blueprint-P/parts/p11a5-quantitative-theorem.tex` L59–91 and the corresponding graph contracts;
track P statement conventions and the relevant frozen definitions. The explicit user report path
supersedes the generic brief's instruction to write into MAIN.

`git diff inp...HEAD --stat` shows exactly one file, 366 insertions in Zero.lean.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
The pre-existing untracked handoff is preserved. Only this report is a lasting audit edit.

## Nodes and completeness

All declarations below are in `KAM.Planetary`. Lines refer to Zero.lean.

| Node | Declaration / proof fragment | Verdict | Literal conclusion and evidence |
|---|---|---|---|
| `bpP:p11a:zero-case` | `zero_case` L330; `p11c_zeroGood` L154 | PASS | Existential family for the actual zero-perturbation Hamiltonian; exact good set, torus and frequency equalities. All family fields constructed. |
| `stepP:p11a:zc-set` | `p11c_zero_good` L242 | PASS | Compact H0 and measure loss, in equivalent ENNReal addition form; `power_law` at m=N and 2 gamma, with exact constant identification. |
| `stepP:p11a:zc-tori` | `p11c_zero_lattice` L289, derivative/field helpers, `zero_case` L334–360 | PASS | Real analyticity, domain, lattice winding, injective derivative, Lagrangian pullback, actual global HasDerivAt equation; gamma-Diophantine output and zero displacement. Evaluation is identity in (theta,b) coordinates, equivalently swap in (b,theta). |
| `bpP:p11a:sec-q-thm#data` (shared ownership row Q1/Q5) | imported `QuantitativeData`, `.NumericalValid`, `.Valid`, `QuantitativeInput` | PASS | The explicit Q0/Q1 ownership split supplies these existing definitions; Q5 neither duplicates nor assumes an output family. |

The step labels are local proof fragments by the design's explicit convention. No exported theorem
pretends to establish a full node while stating only an auxiliary bound. In particular the lattice
helper states the exact lattice-torus predicate; the rest of zc-tori is in the family assembly.
Although `QuantitativeFamily.cell_lower` requests only the general factor 2^(-2N), the zero-case
output also fixes the torus to `(theta,b)`. Thus its image is exactly `unitCube N × H0`, its measure
is exactly `volume H0`, and evaluation is injective. Fresh scratch examples check the exact measure
and injectivity identities, beyond the weaker family-field bound. The torus itself is injective by
its first projection. The family equality is stronger than merely saying displacement is zero.
There is no missing Q5 node; the positive-size assembly and physical interface belong to Q6/Q7.

## Declaration-by-declaration review

| Declaration | Line | Verdict | Statement / source correspondence |
|---|---:|---|---|
| `p11c_zero_isOpen_nbhd` | 32 | PASS | Arbitrary complex action neighborhood is a union of open balls; no positivity premise needed. |
| `p11c_zero_contDiffOn_freq` | 40 | PASS | Holomorphy on open U gives smooth real frequency on the real preimage; actual fderiv, no assumed smoothness output. |
| `p11c_zero_contDiffAt_scalar` | 52 | PASS | Smooth frequency gives smooth scalar finite sum raised to rho; includes all natural rho. |
| `p11c_zero_euclid_iter` | 61 | PASS | Derivative of the singleton-valued scalar embedding has Euclidean norm equal to scalar absolute value, for every order. |
| `p11c_zero_diam_pos` | 77 | PASS | Positive-volume compact K in positive dimension has positive max diameter. |
| `p11c_zero_patch` | 88 | PASS | Constructs the actual upstream patch with K unchanged, open real preimage V and v=vartheta. Euclidean thickening is contained in the strict complex max neighborhood of radius 2*vartheta. |
| `p11c_zero_dioHyp` | 104 | PASS | Derives every upstream D1–D3 field from A1–A3; equality of scalar norms preserves diagonal finite type and full tuple operator bounds. Difference is identically zero. |
| `p11c_zeroGood` | 154 | PASS | Literal source H0; definition classified below. |
| `p11c_zero_cDio_pos` | 157 | PASS | Proves positivity of all real-power factors, diameter and summation denominator under NumericalValid. |
| `p11c_zero_gamma_pos` | 177 | PASS | Positive minimum defining gamma; division uses proven positive cDio. |
| `p11c_zero_two_gamma` | 188 | PASS | Exact 2*gamma=gammaStar identity for all data; no domain assumptions hidden. |
| `p11c_zero_cDio_eq` | 194 | PASS | Literal equality to upstream p11CDio with n=m=N, same max diameter and thickness. |
| `p11c_zero_small` | 199 | PASS | Strict (sqrt N * 2 gamma)^rho < beta/4; proves the reciprocal-power cancellation with positive beta and rho. |
| `p11c_zero_good_eq` | 232 | PASS | Upstream power-law good set equals frozen-IsDiophantine H0; real rpow_neg keeps the same l1 divisor. |
| `p11c_zero_good` | 242 | PASS | Full zc-set compactness and measure loss, under weaker NumericalValid rather than full Valid. |
| `p11c_zero_hasFDeriv` | 266 | PASS | Actual derivative of Re h composed with action projection; holomorphy guards total fderiv. |
| `p11c_zero_vectorField` | 281 | PASS | Frozen Hamiltonian field equals (frequencyMap h b,0) on the real slice. |
| `p11c_zero_lattice` | 289 | PASS | All L1–L6 clauses for the unperturbed torus; applies field equality at theta+t*omega as required. |
| `p11c_zero_image` | 325 | PASS | Literal identity-image equality on every subset of Phase N, stronger than the unit-cell specialization. |
| `zero_case` | 330 | PASS | Exact signature, including d.Valid and arbitrary cDelta; constructs all outputs without additional premises. |

Appendix A is byte-identical to the standalone signature file.
The planned theorem header is **byte-identical** to standalone signature L243–246 up to the proof
body. The planned definition, including its body, is **byte-identical** to L240–241. The other
18 declarations are distinctly named proof helpers, absent from the standalone signature rather
than changed versions of any planned export. They introduce no replacement theorem. No reused
public helper short name was found by declaration search across the other KAM files. Everything
is inside `namespace KAM.Planetary`; no root shadow or new instance is introduced.

Premise review: N/types and d/h/cDelta are typing/source data. `hd : d.Valid` is explicitly present
in the signature, not an added premise. Its use only through `hd.1 : d.NumericalValid` is confirmed
at L334. The unused tau>N-1 and beta<=1 remain on the public theorem, exactly as specified.
`hh : QuantitativeInput d h 0` expands to A1–A4 analytic, reality, periodicity, finite-type and
norm premises. In particular it does not contain an assumed torus, measure bound, or iteration.
Unused A4 bounds do not weaken the conclusion. The helper assumptions about holomorphy,
smoothness and patch identifications are discharged before use; none replaces a source result.

## Definition classification and upstream use

The only new definition is `p11c_zeroGood` L154–155. BODY_MATCH: OK; PUBLIC_CARRIER: OK;
WELL_DEFINEDNESS: N/A_LITERAL; CHARACTERIZATION: literal membership by reduction;
CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS. It is the subset of the original real K whose
actual frequency satisfies frozen `IsDiophantine (2*gamma) tau`. No choice, junk branch, fallback,
rescaled measure, or changed norm appears. It is meaningful on its whole declared carrier,
including invalid data; compactness and quantitative properties are asserted only under the
stated source premises. `QuantitativeInput` and `QuantitativeFamily` remain imported Q0 objects.

U11a1: `p11c_zero_patch` retains K, Euclidean thickening and max diameter. The holomorphic-to-smooth
bridge supplies regularity on the open real preimage. `p11c_zero_euclid_iter` explicitly reconciles
the singleton-vector and scalar derivatives; `le_index_def` supplies the amount bound from diagonal
directions, whereas the size bound uses all independently chosen tuple directions. The D3 diagonal
bound is proved for the actual zero difference. No diagonal/operator norm substitution occurs.
`power_law` is consumed with exactly 2*gamma, and its constants and good set are identified by
proved equalities, not renamed copies.

U1: the existing `IsLatticeTorus` and `unitCube` are imported via Q0. The torus, derivative,
lattice, symplectic form and field all use the original objects and period-one convention.
The generic union lemmas are unnecessary for this identity evaluation: direct product
measurability/volume and compactness prove their required specialized conclusions. This is the
explicit direct zero-case route in blueprint L67, not an unpaid generic transport application.

## Independent validation

All audit Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`
(build niceness supplied by the required gate wrapper). No resource-budget override was used.

1. Command:

   `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-q5 KAM.Planetary.Quantitative.Zero`

   **Exit 0.** Output: `[inp-gate] slot 3 acquired 18:46:07 for KAM.Planetary.Quantitative.Zero`;
   `Build completed successfully (9118 jobs).` Replayed unused-variable warnings only, in
   Hamiltonian/Algebra L146 (`hc`), Chart L193 (`hc`), Diophantine L124 (`hγ`), Transport L55
   (`hc`), WeakMeasure/Stability L302 (`hn`), L304 (`hK`), L403 (`hn`), and DividedDifference
   L96 (`hab`). No warning in Zero.lean.

2. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Q5Audit.lean` — **exit 0**.
   The fresh theorem used the exact standalone signature header with body
   `by exact zero_case d hd h hh cDelta`; an additional
   `example : type_of% @q5_audit_signature := @zero_case` passed. The literal-definition rfl
   example, evaluation injectivity, and exact cell-volume example also passed.
   Complete axiom-query output (all 19 new public theorems plus the definition):

```text
'KAM.Planetary.p11c_zeroGood' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_isOpen_nbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_contDiffOn_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_contDiffAt_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_euclid_iter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_diam_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_patch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_dioHyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_cDio_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_gamma_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_two_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_cDio_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_good_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_hasFDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_vectorField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_zero_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.zero_case' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Quantitative.Zero`
   — **exit 0**. This single invocation names the sole new lemma module; no provider exists.
   Complete output:

```text
replaying KAM.Planetary.Quantitative.Zero
```

4. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` — **exit 1**, solely the explicitly allowed generated-root exception.
   Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (880 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

5. Final report trailing-whitespace/conflict-marker scan and
   `git diff --check inp...HEAD` / `git diff --check -- docs/tracks/P/audits/Q5-audit-1.md`
   — **exit 0**, no findings. All audit-owned scratch files were removed.


Static checks: 366 lines, maximum line length **99** characters; proper copyright, `module`,
public imports, module documentation and `@[expose] public noncomputable section`. Forbidden-token
search finds no sorry/admit/axiom/unsafe/opaque/resource overrides/EuclideanSpace. No production
file, frozen file, manifest, generated root or README was edited. `git diff --check inp...HEAD`
exits 0. Import closure contains **72** project modules, no provider, and **24** frozen definitions,
all manifest state **SEALED**; no frozen theorem or DRAFT_SORRY anchor is reachable.

Provenance SHA-256:

| Input | SHA-256 |
|---|---|
| Zero.lean | `f0b2d12ebdd9c553cfc1178c4367aaa7bed2364ffcedbf8334b54d5cf0a0564a` |
| Standalone P11CSignatures.lean | `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079` |
| P11C-LEAN-DESIGN.md | `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36` |

## Findings, uncertainty, suspected errata and deviations

No new mathematical blueprint or pinned-source defect was found in the Q5 slice. No frozen
statement looked wrong. No source PDF was needed to replace the explicit blueprint authority,
and no independent PDF erratum claim is made. The inherited P11C design audit's graph snapshot
hash and unrelated module-DAG notes do not change the Q5 signatures or route. The shared data
node's older Q1/Q5 ownership wording is resolved by the explicit preceding Q0 package row.
No auditor-introduced source deviation or production repair occurred.

The only validation note is the explicitly permitted stale generated root: the new public module
is not yet listed in KAM.lean. The orchestrator can regenerate it on integration; audit instructions
forbid doing so here. No check remains pending. There is no default-heartbeat design signal.
The report is the sole lasting audit-created file; the existing handoff remains untouched.

# SO-GRAPH independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-sograph`.
Audited HEAD: `e9e1db35d1b8740db8a8a70cb0cefb96f5b443ca`.
Comparison: `git diff inp...HEAD`; inp at inspection was
`6cc8c0e509fe0f60c41c49ebe065a4a595cb4973`, merge base
`302963ff1dda8363f983a5e10f3b24c9f0ba38cb`.

## Verdict

**FAIL for exact signed API compliance (F1). Mathematical implementation: PASS.**
The only blocking finding is a namespace deviation in two signed declarations.
The checker soundness, open-strip Cauchy transfer, exact-torus construction, both
barrier routes, targeted build, axiom checks and kernel replay pass independently.
The expected generated-root lint exception is recorded below.

| Signed endpoint / anchor | Verdict | Scope |
| --- | --- | --- |
| `KAM.SpinOrbit.SoGraphCert` | FAIL | Signed qualified name absent; implemented as `KAM.Certificate.SoGraphCert`. |
| `KAM.SpinOrbit.checkSoGraph` | FAIL | Signed qualified name absent; implemented as `KAM.Certificate.checkSoGraph`. |
| `KAM.SpinOrbit.soBarrier_of_cert` | FAIL for exact signed contract; proof PASS | Header text agrees, but its certificate binder resolves to the relocated carrier. |
| `KAM.SpinOrbit.soRotBarrier_of_cert` | FAIL for exact signed contract; proof PASS | Same carrier discrepancy; rotated-frame mathematics passes. |
| Frozen provider / seal | N/A | This diff adds no provider and seals no frozen anchor. No seal-readiness claim is made. |

F1 should be resolved by restoring the signed namespace, or by an explicit reviewed
signature amendment covering the carrier, checker and downstream consumers. The
handoff's namespace statement is disclosure, not evidence of such an amendment.
No implementation was changed during this audit.

## Authority and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the requested
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the full
`docs/tracks/SO/audits/SO-GRAPH-handoff.md`, including AUDIT FOCUS.
The user's exact report destination overrides the generic brief's main-worktree
output instruction. This report is in the package worktree at the requested
absolute path.

SO's controlling mathematical statements here are the signed draft
`/root/code/KAM-inp/.drafts/design/SOSignaturesLunar.lean` §I.5, the local
`docs/tracks/SO/design/SO-LEAN-DESIGN.md` §6 (especially lines 556–570), and
`docs/campaign/design/SPIN-ORBIT-PLAN.md` including O5. There is no
`docs/tracks/SO/statement.md` in this checkout and the package has no new I/N/P
blueprint node or frozen theorem. The inherited I-G1 bridge is
`KAM.Iso.Apost.g1_explicit` (`bpI:p2:g1`), used by landed certificate soundness;
it is not re-proved or newly sealed here.

The entire three-dot diff consists of:

- `KAM/SpinOrbit/Graph/Cert.lean`: 255 added lines.
- `KAM/SpinOrbit/Tests/GraphCert.lean`: 92 added lines.
- `docs/tracks/SO/audits/SO-GRAPH-handoff.md`: 71 added lines.

## F1 — signed declarations have moved namespace

The signed draft opens `namespace KAM.SpinOrbit` at line 237 and does not close
it until line 538. At lines 397–409 it declares:

```lean
structure SoGraphCert (α : Type) where
  base : TorusCertificate 2 α
  -- the signed numerical and SOS fields follow

def checkSoGraph {α : Type} [CertArith α] (g : SoGraphCert α) : Bool := sorry
```

Thus the signed names are `KAM.SpinOrbit.SoGraphCert` and
`KAM.SpinOrbit.checkSoGraph`. In `KAM/SpinOrbit/Graph/Cert.lean:30` the namespace
is instead `KAM.Certificate`; the declarations are at lines 39 and 65. There
is no compatibility declaration at the signed names. A fresh negative probe,
importing only the production module, produced:

```text
.lake/abi-scratch/SoGraphSignedNames.lean:2:7: error(lean.unknownIdentifier): Unknown identifier `KAM.SpinOrbit.SoGraphCert`
.lake/abi-scratch/SoGraphSignedNames.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `KAM.SpinOrbit.checkSoGraph`
```

Command: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean
.lake/abi-scratch/SoGraphSignedNames.lean`; exit 1, as expected for this refutation.
The production barrier statements at lines 218 and 238 use the relocated
certificate type through `open KAM.Certificate`; consequently unqualified header
text equality alone does not establish equality with the signed qualified API.

Independent Python extraction confirmed all four textual comparisons:

```text
soBarrier_of_cert header byte equality: True
soRotBarrier_of_cert header byte equality: True
SoGraphCert structure byte equality: True
checkSoGraph header byte equality: True
```

For theorems and checker, the comparison stops before `:=`; the draft deliberately
has placeholder bodies. The structure comparison includes all ten fields and
their order. These results establish textual fidelity but do not erase F1.

## Declaration-by-declaration review

In this table, `C` means `KAM.Certificate`, `S` means `KAM.SpinOrbit`, `Cert`
means `KAM/SpinOrbit/Graph/Cert.lean`, and `Tests` means
`KAM/SpinOrbit/Tests/GraphCert.lean`. PASS is for the indicated mathematical
obligation; F1 remains an independent package blocker.

| Node / location | Lean declaration | Verdict | Reason |
| --- | --- | --- | --- |
| §I.5 data, Cert:39 | `C.SoGraphCert` | FAIL API; data PASS | Exact signed fields; namespace differs (F1). |
| §6 derivative model, Cert:54 | `C.soGraphMonoModel` | PASS | Degree-zero model of DK angle row 0, column 0. |
| §6 action model, Cert:59 | `C.soGraphActionModel` | PASS | Degree-zero model of action coordinate 0, with matching denotation defaults. |
| §I.5 checker, Cert:65 | `C.checkSoGraph` | FAIL API; algorithm PASS | Three paid SOS checks and strict rational margin; F1. |
| Norm projection, Cert:80 | `S.norm_fst_apply_sub_le` | PASS | First coordinate is bounded by the Pi norm and product max norm. |
| Norm projection, Cert:84 | `S.norm_snd_apply_sub_le` | PASS | Same estimate for action coordinate. |
| Direction identity, Cert:88 | `S.realPt_one_zero` | PASS | Exactly the unit vector in coordinate 0. |
| §6 Cauchy transfer, Cert:93 | `S.soGraph_deriv_transfer` | PASS | Full open-strip displacement gives `abs(derivative difference) * ρ ≤ d`. |
| §6 checker contract, Cert:136 | `S.checkSoGraph_sound` | PASS | Exact real derivative lower bound, action lower/upper bounds, and strict margin. |
| §6 black-box transfer, Cert:165 | `S.soGraph_exactTorus` | PASS | Exact invariant torus, scaled Diophantine margin, positive monotonicity and widened band. |
| §I.5 original endpoint, Cert:218 | `S.soBarrier_of_cert` | FAIL signed contract; proof PASS | Calls the landed original-frame theorem with exactly its hypotheses; F1 affects certificate binder. |
| §I.5 rotated endpoint, Cert:238 | `S.soRotBarrier_of_cert` | FAIL signed contract; proof PASS | Calls the landed rotated theorem after identifying the scaled Hamiltonian; F1. |
| Fixture, Tests:28 | `C.graphToyW` | PASS | Exact rational weight data, not a proof of weight validity. |
| Fixture, Tests:30 | `C.graphToyPi` | PASS | Exact finite π-enclosure candidate. |
| Fixture, Tests:32 | `C.graphToyCfg` | PASS | Finite model configuration with empty advice. |
| Fixture, Tests:35 | `C.graphToyCos` | PASS | Represents the advertised constant plus cosine via conjugate half coefficients. |
| Fixture, Tests:37 | `C.graphToyK` | PASS | Correct degree -1 angle displacement and degree 0 action component. |
| Fixture, Tests:40 | `C.graphToyParams` | PASS | Total rational record parameterized by displacement; not asserted statically valid. |
| Fixture, Tests:44 | `C.graphToyBase` | PASS | Explicit graph-only toy certificate; unrelated torus fields are placeholders. |
| Fixture, Tests:62 | `C.graphToy` | PASS | Total graph fixture with independent displacement, monotonicity and band inputs. |
| Positive computation, Tests:74 | `C.graphTest_pass` | PASS | `decide +kernel` checks the advertised graph fixture. |
| Fail-closed computation, Tests:78 | `C.graphTest_mono_fail` | PASS | Rejects the tightened derivative bound. |
| Fail-closed computation, Tests:82 | `C.graphTest_range_fail` | PASS | Separately rejects tightened lower and upper action bounds. |
| Fail-closed computation, Tests:88 | `C.graphTest_margin_fail` | PASS | Rejects displacement 1/200 against margin 1/250. |

## Definition classification and defaults

`SoGraphCert` is untrusted finite data: the base certificate, six rational bounds
and centres, and three polynomial witnesses. No field asserts monotonicity,
invariance, existence of a barrier, or any other conclusion.

`soGraphMonoModel` and `soGraphActionModel` are concrete enclosure algorithms,
not mathematical objects defined by choosing a proof witness. `checkSoGraph` is
a Boolean algorithm, reducible in the kernel, whose soundness requires the
explicit lawful-arithmetic, weight and π premises. It is deliberately an
additional graph check, not a replacement for `checkTorusCertificate`.

All eight test definitions are total finite fixture constructors. In particular
`graphToyBase` is only a carrier of the fields read by this check; no theorem
claims that it passes the torus checker or produces a physical lunar barrier.
There are no new abbrevs, implicit existence choices or proof-valued structure
fields in either new file.

Default reads are harmless on the whole denoted carrier:

- `CertEmbedding.eval` (`Embedding.lean:38–44`) and `actionAt` (:58) use the same
  exponent `actionDeg.getD 0 0` and the same optional action component as the new
  action model. A missing action is the mathematical zero function; a missing
  exponent means degree zero in both denotation and model.
- `realCompModel_encloses` (`Expr/ComposeModels.lean:260`) holds for every option
  and integer degree; it proves the `none` case using `zeroModel_encloses`.
  The final `toDeg` retains a certified error radius through valid weight and π
  bounds. No input-list shape premise is omitted.
- The derivative matrix is built with shape 4 by 2 by `dkModels` and `buildMat`.
  Its (0,0) entry exists; `buildMat_entry` and `dkModels_encloses` prove this
  identification. `modelMatrixEntry`'s missing-entry zero fallback is not taken
  here. The angle derivative includes the affine identity derivative, rather
  than only the periodic displacement derivative.

## Analytic and consumer checks

At `Cert:146–153`, `dkModels_encloses` is specialized to row `Sum.inl 0` and
column 0. Unfolding `tangentMat_apply` and `sumVec_apply` identifies exactly
`(fderiv ℂ g.base.K θ (Pi.single 0 1)).1 0`; `realPt_one_zero` identifies its
real direction. The action enclosure denotes exactly `(g.base.K θ).2 0`.

All three branches use the landed `checkRealLowerBound_sound`
(`KAM/Certificate/Positivity.lean:121`), not an unpaid SOS implication. The
upper action bound applies it to `negM` with centres and targets `-pHi₀`,
`-pHi`, then reverses the sign. The checker bounds the full residual
`(f + f*) - 2gg* - 2m₀` by `2(m₀ - m)`, so the residual is paid. Advice under
`cfgLow`, including product key `[7]`, is subject to the landed checked-product
contract; it contributes no mathematical assumption here.

The frozen `complexStrip` is open (`abs Im θᵢ < ρ`). The new Cauchy proof applies
the coordinate estimate to the holomorphic difference on that exact strip, for
every `0 < δ < ρ`; real points lie in `T_(ρ-δ)`. It proves `D*δ ≤ d` where D is
the absolute real derivative difference. To obtain `D*ρ ≤ d`, it assumes the
opposite, obtains `D > 0` and `0 ≤ d/D < ρ`, and uses the admissible midpoint
`δ = (d/D + ρ)/2`, a contradiction. This is a valid limiting argument without
assuming differentiability or displacement bounds on the boundary. Nonnegativity
of d follows from the displacement bound at a real point. The product/Pi max
norm projections introduce no factor 2 or dimension factor.

`CertifiedTorus` (`KAM/Certificate/Defs.lean:356–371`) supplies holomorphy and
`norm(Kinf-K) ≤ disp` on the same `T_rhoInf`, as well as `1 < sinf`. Static
soundness supplies `rhoInf > 0` and `γ > 0`. Therefore the rational strict
margin gives `m = mono - disp/rhoInf > 0`; value displacement gives exactly
`[pLo-disp, pHi+disp]`. There is no hidden strip shrink or change of norm.

`isDiophantine_smul_scale` gives `(sinf*γ, tau)`-Diophantinity of `sinf • ωstar`
from `sinf > 0`. Since `sinf > 1` and `γ > 0`, its new margin is indeed greater
than γ. No weakening back to γ is needed: the landed barrier theorem accepts
any positive margin and receives exactly `sinf*γ` and its positivity proof.

The original route rewrites `g.base.H` to `soHC` using `hham` and
`soHamExpr_eval`. The rotated route rewrites it to
`(soRotHamExprScaled c).eval` using `hham`, keeping `hc0 : 0 < c`. Both supply
all the landed exact-torus theorem's premises with no new hypothesis. The
rotated consumer in `Graph/Rot.lean:103` already rescales time, identifies the
clock and invokes `SoGraph.torus_of_rot`, then `soBarrier_of_torus`; neither
landed theorem is restated in this diff. The output is the original physical
`SoBarrier` with continuity, both periodicities, physical invariance, and the
advertised action band.

The two imported arithmetic classes are representation laws, not bundled hard
analytic premises. No conclusion-shaped hypothesis was found. The only geometric
hypotheses in the new Cauchy helper are discharged from the black box and the
entire finite embedding before either public endpoint is used.

## Independent checks

All auditor Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and
`nice -n 5`; no clean, update, cache download or package mutation was performed.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sograph KAM.SpinOrbit.Graph.Cert KAM.SpinOrbit.Tests.GraphCert
```

Exit 0. Output included:

```text
[inp-gate] slot 2 acquired 21:56:22 for KAM.SpinOrbit.Graph.Cert KAM.SpinOrbit.Tests.GraphCert
Build completed successfully (3325 jobs).
```

Replayed warnings were confined to existing `KAM.ODE.Exit`,
`KAM.Certificate.Expr.Basic`, `KAM.Certificate.Arith.PiHigh`,
`KAM.Certificate.Sound.Static`, and `KAM.Certificate.Sound.Ham`; no warning was
reported in either new module.

### Signed-header and explicit-binder probes

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SoGraphAudit.lean
```

Exit 0. The scratch file imported the test module, opened the relevant namespaces,
and copied both signed theorem headers under fresh names. Bodies were exactly:

```lean
by exact soBarrier_of_cert g hham hc hg hω hdio
by exact soRotBarrier_of_cert g hc0 hham hc hg hω hdio
```

For each, `example : type_of% @<production theorem> := @<fresh theorem>` also
elaborated. These probes check binder order and conclusion at the actual imported
carrier; they are not claimed to prove namespace equality with the draft. The
separate fully qualified negative probe establishes F1. Provider/frozen type and
seal-body probes are otherwise inapplicable because this is unfrozen helper code.

### Axioms

The same probe ran `#print axioms` for every new public theorem. Exact output:

```text
'KAM.SpinOrbit.norm_fst_apply_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.norm_snd_apply_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.realPt_one_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soGraph_deriv_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.checkSoGraph_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soGraph_exactTorus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soBarrier_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotBarrier_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.graphTest_pass' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.graphTest_mono_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.graphTest_range_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.graphTest_margin_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` or additional axiom occurs.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.Graph.Cert KAM.SpinOrbit.Tests.GraphCert
```

Exit 0; exact output:

```text
replaying KAM.SpinOrbit.Tests.GraphCert
replaying KAM.SpinOrbit.Graph.Cert
```

### Lint and static hygiene

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the generated root, explicitly permitted by the audit brief.
Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1381 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module check, frozen-anchor guard and all 144 ABI hashes pass. The generated
`KAM.lean` was left untouched as required. No other lint failure was emitted.

Static masked-code scans of the two new modules found no forbidden proof escape,
resource override, or banned ambient carrier. Both have copyright and author
headers, `module`, public imports, module docstrings and public sections. The
production noncomputable section is `@[expose]`. Line counts and maximum widths:
255 / 100 for Cert, 92 / 94 for Tests. Both are below the 1500-line cap.

A recursive source import walk found 167 KAM modules and 20 frozen modules,
all manifest state SEALED. They are frozen definitions, not DRAFT_SORRY theorem
imports. No provider import or DRAFT_SORRY anchor occurs in the closure. In
particular the certificate uses the proved implementation `g1_explicit`, not an
unproved frozen theorem. The main-result axiom probes independently support this.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit 0 with empty output. The full three-dot diff was inspected, rather than
only the working-tree diff. Only this report is a persistent auditor change;
scratch probes and audit logs were removed after incorporation into this report.

## Errata, deviations and remaining scope

- **F1 (blocking implementation/API deviation):** the two signed qualified names
  were moved, as documented above. The signed draft and local design Appendix A
  both place them in `KAM.SpinOrbit`. No owner or orchestrator ruling authorizing
  that move was found in the inspected authorities. This is not a suspected
  mathematical source erratum.
- **Documentation note:** `KAM/SpinOrbit/Graph/Cert.lean:22` says
  “(`soGraph_transfer`)”, but the actual split is `soGraph_deriv_transfer` plus
  `soGraph_exactTorus`. No declaration with that documented name is added. This
  is a minor stale locator, with no effect on the proof.
- No mathematical contradiction with the SO design, frozen definitions or
  inherited I-G1 statement was found. No suspected pinned-source mathematical
  erratum was identified in this package's scope.
- `cfgLow` is sound and is the configuration actually used for all three SOS
  checks; certificate generation must supply suitable advice there. This is
  an implementation constraint, not an unpaid analytic hypothesis.
- The graph-only toy computations do not validate a full torus certificate or
  supply lunar data. Concrete lower/upper lunar certificates, kernel passing
  checks, their O1 window inequalities and final 3.3% confinement remain outside
  this package. A passing abstract implication does not discharge those tasks.

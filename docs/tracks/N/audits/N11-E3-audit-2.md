# N11-E3 independent package audit 2 (delta)

Overall verdict: **PASS WITH NOTES** for the Domain/Hessian package. Round-1 **F1 and F2 are CLOSED**.
The companions establish the literal missing source conclusions using source premises. All eleven signed
declarations and their proof bodies are preserved. The notes concern the brief-permitted stale generated root and nonblocking warning diagnostics.

**N-PARTIAL-CONVEX is not seal-ready on this evidence.** E3 is a supporting package, not its provider;
`KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean:79` still has `by sorry`, and its manifest
state is `DRAFT_SORRY`. No anchor sealing, downstream consumer closure or campaign theorem closure is claimed.

## Scope and pins

Audit date: 2026-10-28. Exact worktree/report destination: `/root/code/KAM-inp-n11e3` /
`docs/tracks/N/audits/N11-E3-audit-2.md`. The user's explicit destination overrides the brief's generic
main-worktree destination. Production verdict scope is only `KAM/Nekhoroshev/Partial/{Domain,Hessian}.lean`.

Read the external `inp-audit-package.md`, AGENTS, PLAN, DECISIONS, AUDIT FOCUS and both prover handoffs,
Round 1, the design and its two design audits, track-N statement, the actual frozen partial-convex anchor,
source predicates and field/domain definitions, and the relevant p11c blueprint and graph contracts.
The earlier design audits approve interfaces; their verdicts do not substitute for this proof audit.

| Input | Current revision / SHA-256 |
|---|---|
| Audited HEAD | `84e511163f4bbd50cfe5d965a3c1fe92021f0a67` |
| Round-1 baseline | `16d8b40d` |
| Comparison `inp` at first explicit resolution | `b5e58ec5e766134ead4e306f3ed3c4dc0da81acd` |
| Domain.lean | `61d5493eb2a25d69df7151141ca3342dabb8d28283f3e0fcfdaa8b5f8743641f` |
| Hessian.lean | `9cd2b320c1e287b1838923656229d5ee681f92bf584c173d3dd68dfdaa5f1cc4` |
| External N11Signatures.lean | `a87a457f07c997e6a922e3f3ada6bf8f3e82195761a6f7109fabeef80f08ef04` |

Inspected the requested `git diff inp...HEAD`, including upstream Setting/Coordinates as context;
its scope is six added files, 2054 insertions (the two context modules, Domain/Hessian, audit 1 and handoff).
Git reports multiple merge bases and selects `be6fc7b01267bd5d16506ff11a84c1f7b93cc791`; the other is
`9d16b3127c8a9fe9af335c5b64874bd29f32ebd8`. The literal requested three-dot comparison was retained.
No upstream N11-A/B audit verdict is reissued.

The independent delta `git diff 16d8b40d HEAD` is exactly **523 insertions and 5 deletions**, confined to
Domain/Hessian. The deleted line in Domain's module docstring is replaced by the companion descriptions;
the four Hessian deletions are its old module-docstring description. **No deleted line is a signed
statement or proof.** Comment/whitespace-normalized extraction independently finds all eleven signed
statements AND bodies unchanged. All eleven headers match the current external signatures exactly
modulo whitespace, including binder names/order and full let-conclusions; all six definition bodies match.
The external signature-file hash differs from Round 1's recorded hash; the scoped declarations were
compared afresh, rather than assuming file-wide identity.

## Disposition of the failures

### F1: dm-field slow transport and physical analyticity — CLOSED

Literal authority: `blueprint-N/parts/p11c-partial-stability.tex:138,142` says the physical converted
Hamiltonian “is real analytic” and “rescaling” turns weight “2π into c”; graph
`docs/graph/N/DEPGRAPH.md:18292` requires the holomorphic-real restriction and that weight transport.

`domain_field_scaled` (Domain:702–768) has exactly the signed `domain_field` source premises:
PartialData, positive μ and R, the chosen frozen sign, Ic in G, R≤r0, d≤ρ, and the actual frozen
IsPartialPerturbation. It proves λ>0, `b.c * b.lam^2 = 2π`, openness of the physical domain, exact
`z ∈ b.realDom R ↔ slowScaleReal b.lam z ∈ physicalDomain ...`, the field identity at **weight b.c**,
and the ExtOrbit/physical IsSolutionIn equivalence. Here `b.c = 2π/b.lam^2` by the imported definition,
not an unrelated weight satisfying an assumed equation. Both q and p are scaled, fast variables are fixed.
The sign σ is retained in the physical field, so no unproved positive-sign selection is smuggled in.

The chain rule at Domain:471–541 uses an invertible continuous linear scaling. Mathlib's
`ContinuousLinearEquiv.comp_right_fderiv` is unconditional, including the totalized non-differentiable
case, so its use for arbitrary K does not conceal a differentiability assumption. Multiplying the
slow derivative factor λ by the coordinate factor λ gives `λ²c = 2π`; the fast components are unchanged.
The proof at Domain:731–746 first uses an eventual equality on the OPEN real domain to remove the
indicator in the actual `realHamiltonianExt`, then transports its derivative. This avoids differentiating
an unrestricted substitute for the guarded Hamiltonian. The domain equivalence is proved componentwise
in the max norm, using λR=w and the same existential slow centre; it remains correct for empty S.
Orbit transport uses two-sided HasDerivAt, in both directions via the inverse scaling, on any supplied
set J. This is stronger than requiring an interval, and neither supplies nor assumes orbit existence.

`domain_physical_analytic` (Domain:781–858) proves the global identity
`σ * converted H w = Re F(extCx w)`, an OPEN complex Ω containing every real physical point, holomorphy
of the actual F on Ω, and **AnalyticOnNhd ℝ (converted H)** on the physical set. Its premises are the
same source premises; no physical analyticity or field identity is assumed. Ω is the intersection of
the fast action tube with the inverse-scaled complex block domain. Holomorphy of signedF follows from
`blockPert ∘ slowScale λ⁻¹`, with inverse cancellation; holomorphy of signedH comes from PartialData.hol.
The real analytic conclusion uses the proved holomorphic-to-analytic theorem, scalar restriction,
real inclusion and real projection; σ²=1 recovers the unsigned converted H. Since the displayed F is
σ times the unsigned h1+f1 globally, multiplying its holomorphic representation by σ also gives the
literal unsigned representation in the source. No continuation across a boundary is used.

Adversarial recheck: tried the wrong-weight and scalar-pullback-only interpretations, the indicator
boundary, sign −1 and empty-core cases. The exported field identity, positivity, open-domain argument
and exact orbit/domain equivalences address these cases. No F1 clause remains unpaid in this slice.

### F2: real derivatives, real symmetric Hessian and frequency — CLOSED

Literal authority: `blueprint-N/parts/p11c-partial-stability.tex:126` and graph
`docs/graph/N/DEPGRAPH.md:18979–18988`: “the real derivatives ... are restrictions of the complex
derivatives; Q(I)=D^2 h_R(I)=Q_C(I), symmetric and real, and omega(I) is the real gradient”.

`realPart_derivs_real` (Hessian:140–194) assumes only an open Ω, holomorphy of h on Ω, reality of its
values on Ω's real slice, membership of the chosen real I, and real test vectors u,v. It exports:
first derivative imaginary part zero; equality of that COMPLEX derivative with the inclusion of
D h_R(I)[u]; second derivative imaginary part zero; equality of the COMPLEX Hessian with the inclusion
of D² h_R(I)[u,v]; and symmetry of both real and complex Hessians on real vectors. These are complex
equalities, not merely equalities after applying Re. Basis specialization gives exactly the real
symmetric matrix Q_C=Q. Universal real vectors establish restriction of the whole bilinear map.

The source bundle supplies these premises on the FULL open actionNbhd G′ ρ through `a.hol` and
`a.real`; no centred-ball integrability, Hessian bound or definite-sign premise is added. The probe
instantiates that exact source bundle and checks the basis-frequency equality with the actual frozen
`KAM.frequencyMap`, whose definition is D h_R evaluated on each coordinate vector. Thus the generic
companion pays the node on its full source domain, rather than on a smaller block ball only.

The proof differentiates the locally zero imaginary part (Hessian:107–135), repeats the argument for
the holomorphic first derivative evaluated on a real vector, then uses the already proved real-part
bridge and Schwarz symmetry from local C² regularity. The local real neighbourhood comes from
openness and continuous real inclusion. It does not assume derivative reality or symmetry.
Adversarial recheck: h(z)=i*z₀², which invalidated the Round-1 inference, now fails the actual
function-value reality hypothesis on an open real slice. That hypothesis is exactly the source one.

## Node/declaration ledger

Names are under KAM.Nekhoroshev; D/H are Domain/Hessian. PASS is a package/source verdict.

| Node / declaration | Locator | Verdict | Reason |
|---|---|---|---|
| block-setting / block_setting | D44 | PASS | Same literal block geometry and inner core. |
| perturbation pair / signedH | D46 | PASS | Same σh/(2π) on the whole carrier. |
| perturbation pair / signedF | D48 | PASS | Same original P, period conversion and σμ/(2π). |
| slowScale | D53 | PASS | Same complex scaling of both slow coordinates. |
| block-setting / blockPert | D56 | PASS | Same fixed-block pullback. |
| physicalDomain | D61 | PASS | Same max-norm existential physical tube. |
| dm-field / domain_field | D118 | PASS | Unchanged signed physical field identity. |
| polyNbhd_realBall_subset | D150 | PASS | Unchanged source collar inclusion. |
| dm-pts | D202, D373 | PASS | Original frozen complex tube, holomorphy, reality and periodicity. |
| dm-norm / domain | D373 | PASS | Unchanged class and coth(πs)^n μ/(2π) bound. |
| slowScaleReal | D441 | PASS | Literal real scaling as a continuous linear map. |
| dm-field / domain_field_scaled | D702 | PASS | Weight b.c, actual guarded field, domains and orbit transport. |
| dm-field / domain_physical_analytic | D781 | PASS | Actual converted H analytic; open holomorphic representation. |
| realPart_hessian_apply | H64 | PASS | Unchanged general real-part bridge; does not pretend to prove reality. |
| real-hessian / realPart_derivs_real | H140 | PASS | Literal complex=real derivative equalities, reality and symmetry. |
| FastConvex.toRealFastConvex | H255 | PASS | Unchanged real-slice upper bound with same M. |
| hs-op / hessian_at_sign | H222, H334 | PASS | Unchanged operator bound, selected sign, same m1/M1. |
| hessian / hessian | H428 | PASS | Same single global sign and frequency lower bound. |
| domain, whole assigned node | D373/D118/D702/D781 + Hessian | PASS | Round-1 analytic, norm and convex clauses plus repaired field/analytic clauses. |

## Definition classification and hygiene

The delta adds just public `slowScaleReal` and private `slowEquiv`, no abbrev, structure or instance.
`slowScaleReal` is the literal real map `(θ;I,q,p) ↦ (θ;I,λq,λp)` for every real λ, including zero;
no guard or fallback. `slowEquiv` packages that map with inverse scaling only under λ≠0, a typing
requirement for invertibility, proved from λ>0 in its source uses. Both bodies are exposed by the
module's `@[expose] public noncomputable section`. No public definition changes its meaning off a domain.

Retained definitions: block_setting is the literal fixed block; signedH/signedF are global scalar
multiples/evaluations of the originals; slowScale is the complex coordinate multiplication;
blockPert is its literal pullback; physicalDomain is the existential open tube; private blockLift
regroups the actual coordinates with fast angles multiplied by 2π. No artificial junk-value argument
enters any proof. The inherited `realHamiltonianExt` indicator is handled locally, as described above.

Independent static checks:

```text
Domain lines 862; over100 []
Hessian lines 451; over100 []
Domain forbidden code matches []
Hessian forbidden code matches []
IMPORT CLOSURE 88; PROVIDER/FROZEN THEOREM []
```

Forbidden-code scan excludes comments and checks sorry/admit/axiom/unsafe/opaque/EuclideanSpace and
all set_option commands. Both files satisfy the copyright/module/import/docstring/public-section
format and the 1500-line cap. No resource override or warning suppression was introduced.
All six public helper short names (`slowScaleReal`, `domain_field_scaled`, `domain_physical_analytic`,
`realPart_derivs_real`, `polyNbhd_realBall_subset`, `realPart_hessian_apply`) each have exactly one
public declaration across KAM. Every added public name is inside KAM.Nekhoroshev; the sole new import
is non-public KAM.Strip.AnalyticTaylor. No root shadow, new global instance, provider or frozen-theorem
import was found. The 88-module KAM import closure was walked afresh, including that analytic import.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` has no diff (only the documented
merge-base warning). `git diff --check` exits 0. No production, frozen, manifest, generated file or git
state was edited. Scratch probes are restricted to `.lake/abi-scratch/` and removed after checking.

## Verification

All Lean/Lake checks below are serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No clean,
cache fetch, update, root regeneration, full-library rebuild or resource-budget override was run.

### Targeted compile gate — PASS (exit 0)

```sh
LEAN_NUM_THREADS=1 nice -n 5 \
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-n11e3 \
  KAM.Nekhoroshev.Partial.Domain KAM.Nekhoroshev.Partial.Hessian
```

Decisive output:

```text
[inp-gate] slot 1 acquired 21:05:38 for KAM.Nekhoroshev.Partial.Domain KAM.Nekhoroshev.Partial.Hessian
⚠ [3241/3242] Replayed KAM.Nekhoroshev.Partial.Domain
Build completed successfully (3242 jobs).
```

The gate waited for a free slot, as expected. These include cached/replayed jobs, not a clean build.
Domain warnings: D114:76 unused `Fin.append_left`; D119:5/42/59/72 unused hμ/hIc/hR/hRR;
D120:5 unused hd; D121:51 unused hP. These are retained Round-1 warnings, with shifted locators;
hσ is used and is not warned about. **Three additional delta warnings** are D489:10 and D501:10
unused `Pi.single_apply`, and D538:47 unused `Fin.append_left`. This corrects the Round-2 handoff's
claim that there are no new warnings. They are nonblocking proof-cleanup diagnostics, not resource
failures. No audited Hessian warning appeared. Other replayed warnings are inherited Gradient:168
and Coordinates:118–236 (unused variables/simp/tactics, unnecessary sequencing, unreachable tactics).

### Exact signed types/bodies, source instantiation and axioms — PASS (exit 0)

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11E3Audit2.lean
```

The scratch probe copies all six signed definition bodies and proves full-function equality by rfl.
It copies all five signed theorem statements under fresh names, closes them with the production exports,
and checks their complete polymorphic types in BOTH directions using `type_of%`. The full let-binders
of domain/domain_field are preserved. No placeholder proof from the external signature file is imported.
An initial scratch-generation error truncated those two statements at their first let assignment;
that probe failed, was corrected, and the complete probe above then exited 0. No production change was needed.
The final probe has four harmless tactic-style warning diagnostics at scratch lines 79 and 101.

The additional source-instantiation example proves, for arbitrary I in the full actionNbhd G′ ρ and
coordinate i, that the complex derivative of a.h on the included real basis vector is exactly the
complex inclusion of `KAM.frequencyMap a.h I i`. It uses only the open action tube, a.hol, a.real and
realPart_derivs_real, with no additional integrability or reality-of-derivative premise.

Complete axiom output (every public theorem in both audited modules):

```text
'KAM.Nekhoroshev.domain_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.polyNbhd_realBall_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.domain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.domain_field_scaled' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.domain_physical_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.realPart_hessian_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.realPart_derivs_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.FastConvex.toRealFastConvex' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.hessian_at_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.hessian' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only propext, Classical.choice and Quot.sound occur; no sorryAx or other nonstandard axiom.

### Kernel replay — PASS (exit 0)

After the probe completed, one invocation:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Nekhoroshev.Partial.Domain KAM.Nekhoroshev.Partial.Hessian
```

Complete output:

```text
replaying KAM.Nekhoroshev.Partial.Hessian
replaying KAM.Nekhoroshev.Partial.Domain
```

### Source lint — PASS WITH NOTES (exit 1, permitted exception only)

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (899 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The brief expressly permits the stale generated KAM.lean line. No other lint failure occurred.
The generated root was left untouched; the module, frozen-anchor and ABI checks passed independently.

## Suspected source defects, deviations and limits

No new suspected blueprint or pinned-source defect was found; there is no source text to correct.
The Round-1 F1/F2 implementation omissions have been paid by distinct companions, preserving the signed
interfaces. No frozen hypothesis, quantifier, sign, norm, field, normalizer, domain or graph contract
was silently changed. Domain's new non-public analytic import is appropriate and acyclic.

The Round-2 handoff says “no new warnings beyond the pre-existing unused-variable warnings”; the three
new unused-simp warnings listed above make that receipt inaccurate. This is a handoff discrepancy,
not a false source theorem or a blocking proof defect. The original handoff's hσ-unused claim is also
incorrect, as already observed in Round 1. No production repair was made during this audit.

Provider/frozen-type and seal-body probes are inapplicable to E3's helper-only delivery. Exact signed
types, literal companion conclusions, all public-theorem axioms and kernel replay were checked instead.
The frozen partial-convex theorem remains unsealed. Upstream packages, future consumers and the full
campaign theorem require their own evidence.

## Final artifact checks

Removed N11E3Audit2.lean and its three scratch logs after recording the outputs. The only persistent
worktree change is this exact report path. Final git diff --check passes; the untracked report also
passes git diff --no-index --check against /dev/null with no whitespace diagnostics (exit 1 means a new
file diff), and its trailing-whitespace list is empty. Protected-path comparison remains empty.
HEAD and the two audited file hashes are unchanged. The live inp branch advanced during the audit to
`e262c35780384516b9eb2b21264c361a52841ef9`; both merge bases and the requested three-dot file diff remain
unchanged. No state-changing git operation occurred.

Disposition: accept N11-E3's Domain/Hessian slice with the documented hygiene notes; close audit-1
F1/F2. This is package completion evidence, with no assertion that N-PARTIAL-CONVEX is seal-ready.

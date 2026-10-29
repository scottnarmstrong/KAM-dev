# P13-C independent package audit 1

Audit date: 2026-10-29. Worktree: `/root/code/KAM-inp-fx13c`.
HEAD: `e0a53043c829925330f36786539b6755686c4e9e`.
Comparison ref `inp`: `747706c70a08f2e1e2610dd82dc38cbdfeed2bfd`.

**Verdict: PASS WITH NOTES for the authorized parametric P13-C package.**
For the sole anchor `KAM.Planetary.fixedSunPlanetaryKAM`: **PASS WITH NOTES for conditional assembly; not yet seal-ready**. Its manifest state remains `DRAFT_SORRY`.
The three conditional exports have precisely the approved wrapper premise and the intended signed conclusions. No additional mathematical premise, weakened conclusion, altered constant dependence, or proof escape was found. This audit does not discharge the wrapper or the Part 11 K1–K6 chain.

The explicit overnight ruling at `P13-C-handoff.md:41` authorizes exactly one universally quantified signed wrapper premise and defers the unconditional names to integration. It supersedes the design's original wrapper-delivery assignment gate (`P1213-LEAN-DESIGN.md:68,238`) for this conditional package only. The missing unconditional exports are therefore not findings. An unconditional provider and seal still require a proved signed wrapper. The draft frozen theorem is used only for its type in an isolated probe, never to prove the audited results.

## Scope and authority

Read AGENTS, PLAN, DECISIONS, the requested package brief, handoff/AUDIT FOCUS, Track P's statement (especially P-FIXED), P1213 design/node table, current signed P11A/P1213 declarations, Part 13 blueprint and graph packet, frozen anchor and physical predicates, and the consumed Working/Tube/Assembly interfaces and proofs. The previous P6-5 audit records a scoped PASS WITH NOTES; its physical assembly theorem was independently inspected here and its axioms checked again.

The full `git diff inp...HEAD` contains exactly the three requested Lean files: General (76 lines), Main (59 lines), and the provider (54 lines in its final form; 39 lines added). No inherited source changes complicate attribution. The user's explicit absolute report path overrides the brief's generic main-worktree destination. Only this report is added; scratch probes/logs are removed after validation. No source, generated file, frozen file, manifest, or git state was changed.

## Declaration and node results

Names in the table use `FA = KAM.Planetary.FixedAssembly`, `PR = KAM.Provider.Planetary`. PASS rows refer to the approved conditional scope.

| Node / declaration | Lean locator | Verdict | Reason |
|---|---|---|---|
| `bpP:p13:n-general` / `FA.n_general_of_wrapper` | General:33–70 | PASS | Signed `n_general` telescope/conclusion after exactly `hw`; canonical let-bound d,D retained for every n≥2. |
| `stepP:p13:ng-const` | General:46–65 | PASS | Injectivity follows from strict ordering; `axisData_canonical` proves positive gap and bounds. d=gap/2, D=2·axisMax+gap depend only on a. `hw P` selects eps0 before eps. |
| `stepP:p13:ng-wrap` | General:60–66 | PASS | P contains exactly original physical data/proofs; wrapper supplies the measurable positive finite set in the literal physical tube, plus whole torus witnesses. Conditional on the approved hw. |
| `stepP:p13:ng-phys` | General:67–70 | PASS | Actual P6-5 `fixedKolmogorovSet_of_tube`, at gamma=axisGap a and A=axisMax a. p11Zeta P is definitionally tubeRadius eta (axisGap a); only witness equality orientation is reversed. |
| `bpP:p13:fixed` / `FA.fixed_of_wrapper` | Main:32–53 | PASS | Exact signed `fixed` conclusion and original data telescope after hw; all witnesses precede eps. |
| `stepP:p13:fx-split` | Main:49 | PASS | `hn.eq_or_lt` gives n=2 or 2<n. |
| `stepP:p13:fx-2` | Main:50 | PASS | Dependent substitution followed by actual `FA.n2`; hsep instantiated at 0<1. This branch does not use hw. |
| `stepP:p13:fx-n` | Main:51–53 | PASS | Conditional general theorem, with its canonical d,D existentially packaged for the exact signed consumer. The unused hlt is harmless: general route works already for n≥2. |
| `PR.fixedSunPlanetaryKAM_of_wrapper` | Provider:33–50 | PASS | Direct application of fixed_of_wrapper. After hw, exact frozen type and explicit-binder body both elaborate. |
| Frozen P-FIXED anchor | Frozen/Planetary/Theorems/FixedSunPlanetaryKAM:46 | PASS WITH NOTES | Conditional assembly accepted; unconditional provider/wrapper integration and sealing remain outstanding. |

Every node assigned to these modules by the design table is implemented inside the enclosing proof, under the authorized wrapper assumption where applicable. These are conditional implementations, not unconditional PROVED receipts for the graph. No unsigned export claims a stronger graph conclusion. The existential signed `fixed` interface deliberately packages the canonical general witnesses, and its only new consumer, the provider, requires exactly that interface.

## Definition classification and premises

There are no new public `def`, `abbrev`, `structure`, instances, notation, or root declarations in the diff. The local lets d,D denote the canonical tube constants, and local P is a literal `P11Physical` record with G,m0,m,a,eta and proofs from the theorem's original hypotheses. It has no hidden conclusion field or fallback.

The consumed `P11Physical` fields are physical data and sign/order/dimension proofs. `p11Zeta` is the same finite-set infimum radius as `tubeRadius eta (axisGap a)`, not a chosen substitute. The physical assembly theorem constructs the unchanged frozen measurable-set, tube, invariant-torus, collision, all-time fixed-law, and Sun-at-origin pair-bound clauses. No totalized singular value is used to evade a collision obligation: tube geometry supplies collision exclusion. No uniform-in-eps Diophantine constant is introduced or required.

All three hw binders are text-identical modulo whitespace. The probe derives `AuditWrapper` directly from `P11ASignatures.lean:1196–1203` and proves its equality to the literal binder by rfl. The remaining telescope/conclusions agree with `P1213Signatures.lean:330–356` and the frozen theorem. The conditional names remain distinct from the source-facing names.

## Validation

All Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No resource override, clean, update, cache fetch, or dependency edit was used.

Targeted gate:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-fx13c KAM.Planetary.FixedAssembly.General KAM.Planetary.FixedAssembly.Main KAM.Provider.Planetary.FixedSunPlanetaryKAM
[inp-gate] slot 2 acquired 03:58:33 for KAM.Planetary.FixedAssembly.General KAM.Planetary.FixedAssembly.Main KAM.Provider.Planetary.FixedSunPlanetaryKAM
Build completed successfully (9649 jobs).
exit 0
```

The build replayed inherited dependency warnings (unused variables and existing axiom diagnostics); no warning or error was attributed to the three audited files.

Exact signature/explicit-body/axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P13CAudit.lean
exit 0
'KAM.Planetary.FixedAssembly.n_general_of_wrapper' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.FixedAssembly.fixed_of_wrapper' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.fixedSunPlanetaryKAM_of_wrapper' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.FixedAssembly.n2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fixedKolmogorovSet_of_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The exact-type check quantifies dimension before instantiating the provider's hw, since the provider's implicit n precedes hw. It does not use the frozen theorem as a proof term. The final example is a fresh copy of the frozen declaration with all explicit binders passed in order, after hw.

Kernel replay, one invocation:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Provider.Planetary.FixedSunPlanetaryKAM KAM.Planetary.FixedAssembly.General KAM.Planetary.FixedAssembly.Main
replaying KAM.Planetary.FixedAssembly.Main
replaying KAM.Planetary.FixedAssembly.General
replaying KAM.Provider.Planetary.FixedSunPlanetaryKAM
exit 0
```

Repository lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1248 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only lint failure is the stale generated root, explicitly permitted by the audit brief. It was not regenerated. All substantive module/frozen/ABI checks passed.

Static/source integrity:

- `git diff --check inp...HEAD`: exit 0, empty output.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty output.
- No forbidden code token, EuclideanSpace, heartbeat/recursion/synthesis override, reused public HELPER short name, or harmful root shadow in the changed modules.
- Module headers, copyright, docstrings, public imports/sections present. File lengths 76/59/54; maximum Unicode line lengths 94/90/100, all within limits.
- Provider direct imports: Mathlib, frozen FixedKolmogorovSet Def, FixedAssembly.Main. Mathlib is a library import, not another project dependency.
- Recursive project-import traversal finds only one frozen theorem dependency: `ProperlyDegenerateKAM`, manifest `SEALED`. No imported `DRAFT_SORRY` theorem. Its sealed anchor may import its own provider; the new provider never bypasses that anchor.
- Reverse provider import search (`rg --no-ignore`, to include ignored frozen paths) finds only `KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.lean:24`. No production consumer bypasses quarantine.

## Suspected defects, deviations, and limits

No new suspected mathematical, blueprint, or pinned-source defect found in this slice; no erratum is proposed. Existing source concerns elsewhere are not adjudicated here. The earlier canonical-constant interface concern is absent from the current signed n_general and implementation.

The sole material deviation is the explicitly authorized conditional wrapper form (`P13-C-handoff.md:41`: “ONE extra hypothesis hw that must be exactly the signed ... wrapper statement ... universally quantified over n and D, nothing else”). The probe confirms that exact scope. `docs/tracks/P/statement.md:264–266` still describes an unconditional target; the present helpers do not replace it. The Part 11 K1–K6 delivery gate and general wrapper proof remain outside this package's closure. No unconditional sealing is authorized by these checks alone.

## Reproducible signature probe

The following temporary probe was used and then deleted:

```lean
import KAM.Frozen.Planetary.Theorems.FixedSunPlanetaryKAM
import KAM.Provider.Planetary.FixedSunPlanetaryKAM
open Set Real MeasureTheory Function KAM KAM.Kepler KAM.Planetary

abbrev AuditWrapper : Prop := ∀ {n : ℕ} (D : P11Physical n),
∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps, 0 < eps → eps < eps0 →
      ∃ S : Set (Phase (n*2)), MeasurableSet S ∧ 0 < volume S ∧ volume S < ⊤ ∧
        S ⊆ circularTube D.G D.m0 D.m D.a (p11Zeta D) ∧
        ∀ z ∈ S, ∃ w : P11Vec (n*2), ∃ K : P11Vec (n*2) → Phase (n*2),
          ∃ theta0, z=K theta0 ∧ Set.range K ⊆ S ∧
            IsPhysicalTorus (fixedHamiltonian D.G D.m0 D.m eps) w K
example : AuditWrapper = (∀ {n : ℕ} (D : P11Physical n),
      ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), MeasurableSet S ∧ 0 < volume S ∧ volume S < ⊤ ∧
          S ⊆ circularTube D.G D.m0 D.m D.a (p11Zeta D) ∧
          ∀ z ∈ S, ∃ w : P11Vec (n * 2), ∃ K : P11Vec (n * 2) → Phase (n * 2),
            ∃ theta0, z = K theta0 ∧ Set.range K ⊆ S ∧
              IsPhysicalTorus (fixedHamiltonian D.G D.m0 D.m eps) w K) := rfl

example (hw : AuditWrapper) {n : ℕ} (hn : 2 ≤ n)
    (G m0 : ℝ) (m a : Fin n → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : ∀ i j, i < j → a i < a j)
    (eta : ℝ) (heta : 0 < eta) :
    let d := tubeD (axisGap a)
    let D := tubeBigD (axisGap a) (axisMax a)
    ∃ eps0 : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          FixedKolmogorovSet G m0 m a eps eta d D S  :=
  FixedAssembly.n_general_of_wrapper hw hn G m0 m a hG hm0 hm ha hsep eta heta

example (hw : AuditWrapper) {n : ℕ} (hn : 2 ≤ n)
    (G m0 : ℝ) (m a : Fin n → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : ∀ i j, i < j → a i < a j)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ eps0 d D : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          FixedKolmogorovSet G m0 m a eps eta d D S  :=
  FixedAssembly.fixed_of_wrapper hw hn G m0 m a hG hm0 hm ha hsep eta heta

example (hw : AuditWrapper) : type_of% @KAM.Planetary.fixedSunPlanetaryKAM :=
  fun {n} => @KAM.Provider.Planetary.fixedSunPlanetaryKAM_of_wrapper n hw

example (hw : AuditWrapper) {n : ℕ} (hn : 2 ≤ n)
    (G m0 : ℝ) (m a : Fin n → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : ∀ i j, i < j → a i < a j)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ eps0 d D : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          FixedKolmogorovSet G m0 m a eps eta d D S  := by
  exact KAM.Provider.Planetary.fixedSunPlanetaryKAM_of_wrapper hw hn G m0 m a hG hm0 hm ha hsep eta heta

#print axioms KAM.Planetary.FixedAssembly.n_general_of_wrapper

#print axioms KAM.Planetary.FixedAssembly.fixed_of_wrapper

#print axioms KAM.Provider.Planetary.fixedSunPlanetaryKAM_of_wrapper

#print axioms KAM.Planetary.FixedAssembly.n2

#print axioms KAM.Planetary.fixedKolmogorovSet_of_tube
```

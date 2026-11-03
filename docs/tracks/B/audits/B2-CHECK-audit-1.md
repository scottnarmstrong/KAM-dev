# B2-CHECK independent audit 1

Verdict: **PASS WITH NOTES** for `KAM.EffectiveStability.checkOscStep_sound` and the B2-CHECK package. No blocking defect found. This is ordinary Track B infrastructure under OD-B7; there is no frozen anchor or provider to declare seal-ready. The notes concern the scope of the checker and its origin-only smoke example.

## Scope and authority

Audited worktree: `/root/code/KAM-inp-b2check`.
HEAD: `9f97b14506c7a08c24fa74370b8f590b221e5674`.
Comparison ref `inp`: `5595de37ca9e0a1efa85151a359b5c3966ed9e36`.
Merge base: `4d9d56ed0c2d98fbd80679223c571a04af95cba3`.
Initial working tree was clean. Reviewed `git diff inp...HEAD`: precisely 198 added lines in `KAM/EffectiveStability/OscillatorCheck.lean` and 50 added lines in `docs/tracks/B/audits/B2-CHECK-handoff.md`.

Read AGENTS.md, PLAN, DECISIONS, the generic package-audit brief, the B2-CHECK handoff and AUDIT FOCUS, the B2-CHECK and B1-common implementation briefs, Track B SPEC, FREEZE-PROPOSAL and OWNER-DECISIONS, and program-b-plan §3.1 at `/root/code/KAM/docs/explorations/program-b-plan.md:300–340`. Compared the actual B2-STEP theorem, polynomial carriers, dimension predicate and rational majorant definitions; inspected the frozen oscillator action, real Hamiltonian field and symplectic form definitions. The existing STEP audit was contextual evidence, not substituted for current checks.

The package-specific Track B focus governs the generic I/N/P template: unrelated I/N/P anchors and blueprint nodes are not implemented here. OD-B7 records the B2 extension under overnight D71; the local DECISIONS snapshot ends at D70. No exact-text freeze approval is inferred. The user's explicit report destination in this worktree overrides the generic brief's main-worktree destination.

## Declaration review

All declarations below are in `KAM.EffectiveStability`; line numbers refer to `KAM/EffectiveStability/OscillatorCheck.lean`. Every new named public declaration is listed. Generated structure constructor/projections have only the data types displayed in the structure.

| Node / line | Declaration | Verdict | Reason |
|---|---|---|---|
| Certificate data / 26 | `OscStepCert` | PASS | Four finite rational polynomials, natural Lie length, six rational scalars and four rational lists; no Prop fields, instances or analytic witnesses. Dimension is deliberately phantom. |
| Dimension check / 59 | `cartFitsB` | PASS | Checks both exponent-list suffixes starting at n, for every monomial. Missing exponents mean zero. |
| Dimension soundness / 73 | `cartFitsB_sound` | PASS | Recovers both zero-exponent conditions for every k ≥ n, including k outside the list length. Exactly the existing `CartFits` predicate. |
| Tail majorant / 80 | `OscStepCert.Bmaj` | PASS | Exact rational `cartSupBound (cartAdPow χ L H)` on two identical length-n replicate lists of ρ. |
| Executable check / 84 | `checkOscStep` | PASS | Total finite Bool conjunction over data; all scalar arithmetic is rational. Complete premise correspondence below. |
| Dynamics / 103 | `checkOscStep_sound` | PASS | Only acceptance and initial-box hypotheses beyond data and initial point. Supplies the full STEP conclusion with the specified casts and charts. |
| Smoke data / 166 | `harmonicCert` | PASS | Exactly the stated one-dimensional harmonic data, including ε=0, η=[0], T=1. |
| Kernel acceptance / 184 | `harmonicCert_check` | PASS | `by decide +kernel`; kernel replay succeeds; no native evaluation axiom. |
| Smoke consequence / 187 | `harmonicCert_zeroDrift` | PASS WITH NOTES | Applies soundness and extracts zero drift. Its hypothesis I(w₀)≤0 restricts this smoke instance to the origin; it does not exercise positive-action dynamics. |

The private `getD_zero_of_drop` (line 62) splits in-range/out-of-range indices and correctly converts suffix membership into zero-default lookup equality.

## Premise and conclusion fidelity

Every non-data premise of `oscillatorStep_confinement` is either checked or discharged by the chosen interpretation of data. The initial-box premise is intentionally retained for each initial point, exactly as requested.

| STEP premise | CHECK representation / proof |
|---|---|
| `hH hχ hN hP` | Four `cartFitsB` guards; four uses of `cartFitsB_sound`. |
| `hA hL hid` | `cartActOnly Nact`, `decide (1 ≤ L)`, exact `cartEqCheck (cartLieSum χ H L) (cartAdd (cartActSubst Nact) P)`. |
| `hδ hδc hε0 hε` | Rational `0<δ`, `0<δc`, `0≤ε`, `ε≤1/2`; faithful rational-to-real casts. |
| `ρl hρl` | `List.replicate n c.ρ`; every `Fin n` lookup is proved equal to c.ρ. |
| `hq hp` | Both coordinate derivative majorants on those same replicate lists; upper bound εδ. |
| `hεb hT` | Rational `0<εb`, `0≤T`. |
| `rl r hrl` | `rl=c.r`, `r i=(c.r.getD i 0 : ℝ)`; compatibility is reflexivity. |
| `hr0 hdom1` | `0≤r_i`, `2(b_i+εb)≤r_i²`, with precisely the same index i. |
| `hdom2 hdom3` | `r_i+δ<ρ`, `r_i+δc+δ/2<ρ`. |
| `hη` | `0≤η_i`. |
| `hdrift` | `cartSupBound (cartBracket (cartAction i) P) r r ≤ η_i − 2 r_i Bmaj / (L! δc)`, wholly in ℚ before casting. |
| `hmargin` | Strict `a_i+Tη_i<b_i`. |
| `w₀ hw₀` | Arbitrary initial point; precisely `oscillatorAction w₀.2 w₀.1 j ≤ (a.getD j 0 : ℝ)`. |

Every indexed guard ranges over `List.range n`; soundness uses `hall i i.2` for `i : Fin n`. Projection order was checked against all nine per-coordinate clauses. There is no omitted endpoint or off-by-one index. The rational drift inequality is transported with `Rat.cast_le`, then `simp [OscStepCert.Bmaj]`; this preserves subtraction, multiplication, factorial coercion, division, both radius lists and the factor 2. Acceptance implies L≥1 and δc>0, so the total rational division at rejected inputs cannot create a zero-denominator accepted certificate.

The conclusion retains T₁>T, the actual polynomial Hamiltonian's physical solution starting at `stepChart χ ρ w₀`, its equation throughout `Ioo (-T₁) T₁`, uniqueness against every solution on an order-connected interval containing zero, chart recovery, and both action bounds for every |t|≤T. Coordinate order is q first, p second, with action `(p²+q²)/2`. No trajectory or analytic bound is assumed in the certificate. The final application of STEP elaborates exactly against this conclusion; a separate copied-interface probe also elaborated with `checkOscStep_sound c hc w₀ hw₀`.

## Definition classification and scope notes

All five new data/definition declarations have their intended bodies on the whole carrier. `cartFitsB`, `Bmaj` and `checkOscStep` are finite computations; `harmonicCert` is concrete data; `OscStepCert` is data only. A computable wrapper of `checkOscStep` compiled and ran despite the surrounding `noncomputable section`. No proof field, oracle or hidden typeclass carries a hard step.

List totalization is explicitly part of this interface: missing entries of a, b, η and r are zero. Extra entries do not alter the `Fin n` interpretation; out-of-dimension polynomial exponents are separately rejected. Empty a is therefore a legitimate all-zero initial bound, not malformed certificate data. Negative or otherwise unusable data are rejected where the corresponding STEP guard requires it. No additional positivity of ρ is silently inserted; for positive dimension it follows from the checked domain bounds, while n=0 is allowed by the existing theorem.

The checker handles one Cartesian polynomial generator and its chart-coordinate initial set. It does not implement the entire proposed §3.1 interface for multiple generators, parameter boxes, original-coordinate initial-region inclusion or displacement certificates. These are scope limits already fixed by the B2-CHECK brief, not weakened conclusions of this package.

## Verification

Every Lean/Lake invocation below, including lint's ABI subprocess, used this outer prefix:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

Invocations were serialized. The build additionally uses the prescribed gate (which itself applies `nice -n 5`). No budget overrides, broad rebuild, cache fetching or package mutation was requested.

Targeted build, prefix followed by:

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b2check KAM.EffectiveStability.OscillatorCheck
```

Exit 0, no warnings:

```text
[inp-gate] slot 1 acquired 01:39:05 for KAM.EffectiveStability.OscillatorCheck
Build completed successfully (2985 jobs).
```

Probe, prefix followed by:

```sh
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/B2CheckAudit.lean
```

Final exit 0, no errors or warnings. Computation output, in order:

```text
true
false
true
false
false
false
true
false
false
```

These are: the computable harmonic checker; exponent outside dimension; zero-padded valid exponent lists; harmonic data with L=0; δc=0; η=[−1]; a=[]; r=[]; and H with a nonzero exponent outside dimension. The temporary first probe run failed because its record updates omitted `(n := 1)` for the phantom dimension and its unnamed section lacked an `end`; corrected only the scratch probe and reran successfully. These were probe errors, not package failures.

Exact axiom output for all four new public theorems and the copied-interface probe:

```text
'KAM.EffectiveStability.cartFitsB_sound' depends on axioms: [propext, Quot.sound]
'KAM.EffectiveStability.checkOscStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.harmonicCert_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.harmonicCert_zeroDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
'B2CheckAudit.copied_interface' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, prefix followed by:

```sh
lake env leanchecker --verbose KAM.EffectiveStability.OscillatorCheck
```

Exit 0:

```text
replaying KAM.EffectiveStability.OscillatorCheck
```

This covers the only new Lean module, including the kernel acceptance proof. No `native_decide` or `ofReduceBool` occurs in the source or axiom lists. The handoff's 77.7 ms kernel elaboration timing was not independently remeasured; fresh build/replay/axioms establish acceptance without relying on that timing.

Lint, prefix followed by `sh scripts/lint_sources.sh`:

LINT_PENDING

Short-name command:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b2check KAM.EffectiveStability.OscillatorCheck
```

Exit 0: `short-name check OK (no reused public short name)`.

Static checks: 198 lines; over-100-character lines `[]`; forbidden token/resource-option scan `[]`. Copyright, `module`, public import, module docstring and exposed public section are present. Carriers are Fin-function products; no `EuclideanSpace`. Source import traversal reaches 74 local KAM modules, including 20 frozen definition modules, zero frozen theorem modules, zero providers and zero application modules. No DRAFT_SORRY theorem or quarantined provider dependency is introduced.

`git diff --check inp...HEAD` exits 0, empty output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md KAM/Root lakefile.lean` exits 0, empty output. Frozen-type and seal-body probes are inapplicable: this package has neither a frozen anchor nor a provider.

## Errata, deviations and disposition

No new suspected blueprint or pinned-source defect found; no source-paper theorem is newly transcribed here. No deviation from the scoped B2-CHECK signature or data contract was found. No heartbeat or memory-limit design signal occurred. The smoke limitation and broader program scope are recorded above; inherited analytic dependencies were not reproved as part of this checker audit.

Only this report was added to repository sources. Audit scratch probes were removed after verification. No state-changing git command was used; protected/generated files were left untouched.

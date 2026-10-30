# Handoff: LOCK-GRAPH (track SO part 3, D45)

Branch `inp-lockgraph`, worktree `/root/code/KAM-inp-lockgraph`.

## Files (all new)

| file | lines | content |
|---|---:|---|
| `KAM/SpinOrbit/Lock/Graph.lean` | 375 | `lockRealPt`, `hasDerivAt_line_shift`, `lockBarrier_of_exact_torus`, `LockGraphCert`, `re_action_pos_of_nonvanishingOn`, `lockBarrier_of_certified` (engine-generic core), `lockBarrier_of_certV2` (signed) |
| `KAM/SpinOrbit/Lock/Graph/Angle.lean` | 142 | `LockAngle` (monotone torus angle) and its inverse `lockInv` (spec, apply, continuity, shift laws), `sub_int_of_periodic` |
| `KAM/SpinOrbit/Lock/Graph/Bridge.lean` | 166 | `ofRealPt`, `fderiv_ofRealPt`, `lockHamExpr_eval_ofRealPt`, `differentiableAt_lockHamExpr`, `fderiv_lockHamExpr_ofRealPt`, `hamiltonianVectorFieldℂ_lockHamExpr_ofRealPt`, `lockToPhysicalR_congr`, `arg_lockW_lockToPhysicalR` |

No landed file is changed. `KAM.lean` / `KAM/Root/*` not touched (see checks).

## Signed declarations

- `LockGraphCert` — exactly as signed (`graph : SoGraphCert α`, `Ω`, `cs`, `κ : ℚ`).
- `lockBarrier_of_certV2` — statement verbatim from `SOLockSignatures.lean` §7. Proof: 6 lines from the core.

## Approach

**Core `lockBarrier_of_exact_torus`** (an exact torus `K∞` of `κ · lockHamExpr Ω cs` ⇒ `LockBarrier`); the
invariance is produced, never assumed:

1. **Unscaled frequency** (audit 2 finding 4): `invarianceError_const_mul` gives invariance for
   `lockHamExpr` at `(s∞/κ) ω*`; `isDiophantine_smul_scale` moves the Diophantine condition.
2. **Clock rigidity**: `clock_frequency` with `D = lockCertRegion` and `lockHamExpr_clock` gives
   `(s∞/κ) ω*₁ = 1` and `φ = θ₁ + c₀`. This needs `K∞(strip) ⊆ {Re I > 0}`; see below.
3. **The real torus solves `X_K`**: `hamiltonianVectorFieldℂ_lockHamExpr_ofRealPt` (from `lockHamExpr_eval`,
   `lockToRotC_ofReal`, `lockHamiltonianR_eq`, and a general line-derivative lemma `fderiv_ofRealPt`).
   **Its physical image solves `soField`**: chain rule plus `lock_conjugacy` (`I ≥ lo > 0` on the real torus).
4. **Graph** `I = P(α, φ) = I(lockInv(α, φ − c₀), φ − c₀)`, where `lockInv` inverts the angle `α(x, y)` (monotone:
   `∂_{θ₀} α ≥ m > 0`, `α(x+1,y) = α+1`). It is continuous and periodic, with bounds `[lo, hi]`.
5. **Invariance**: for a solution through a graph point `x₀`, use `lockToPhysicalR_surj` (with `lockToPhysicalR_congr`,
   since `Φ` ignores `J̃`) to find the torus point with image `x₀`. The physical image of its torus orbit solves
   `soField`, so `gen_uniqueness` identifies it with the solution. Every point of that orbit lies on the graph:
   - `libAction_lockToPhysicalR` gives `libAction = I`;
   - `arg_lockW_lockToPhysicalR` gives `arg(lockW)/2π = α − k` with `k ∈ ℤ`
     (`Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod`);
   - so `P` agrees by periodicity in `α`.

**Engine-generic core `lockBarrier_of_certified`**. Hypotheses:

- the signed ones (`hΩ`, `hκ`, `hham`, `hlo`, `hg`, `hdio`);
- `hs : checkStatic g.graph.base = true`;
- `hnv : g.graph.base.ham.NonvanishingOn g.graph.base.D`;
- `hT : CertifiedTorus g.graph.base ωstar`, the soundness conclusion of ANY certifier.

The graph transfer (Cauchy, `disp`) follows `soGraph_exactTorus_of_certified` and reuses `checkSoGraph_sound` and
`soGraph_deriv_transfer`. A future route such as `routeAV2P` needs only a ~6-line wrapper like
`lockBarrier_of_certV2`. That wrapper takes `hs` and `hnv` from `landedBase`, via `checkHamBounds_sound`.

**Design point: why `hnv` is needed (not in the design text).** `clock_frequency` requires
`∀ θ ∈ strip ρ∞, K∞ θ ∈ D` with `∂_{J̃} H = 1` on `D`. `lockHamExpr_clock` holds only on `Re I > 0`, and the real
torus bound `I ≥ lo` says nothing off the reals. The proof takes it from the certificate:

- `CertifiedTorus` gives `ball(K∞ θ, μ/2) ⊆ c.D`, and `checkStatic` gives `μ > 0`;
- the `.sqrt` arm of `NonvanishingOn` on `c.D` for the first square root of `lockHamExpr` (operand `(1/Ω) I/π`)
  gives `Re I > 0` on `c.D` (`re_action_pos_of_nonvanishingOn`).

`hnv` is a fact every base check establishes (`BaseFacts.hH.1`). It is a typing/certificate fact, not a
conclusion-shaped hypothesis. The signed `lockBarrier_of_certV2` needs no extra hypothesis.

## Checks (exact)

- **Gated build:** `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-lockgraph KAM.SpinOrbit.Lock.Graph`
  → `Build completed successfully (3546 jobs).` No warning in the three new files. The remaining warnings are in
  landed upstream files only (`ODE/Exit`, `Certificate/*`, `Sharp2/*`). A direct
  `lake env lean KAM/SpinOrbit/Lock/Graph.lean` gives rc=0 with no output.
- **`scripts/lint_sources.sh`:**
  - `check_lean_modules: PASS (1682 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`,
    `ABI HASHES OK (158 frozen declarations)`, no line over 100 characters.
  - One item remains: `KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/SpinOrbit.lean)`
    (exit 1). Rule 10 forbids editing `KAM.lean` / `KAM/Root/*`, so I left this for the orchestrator's regeneration
    commit, as with LOCK-COORDS-C (`e78c95b4`).
- **`main_shortname_check.py /root/code/KAM-inp-lockgraph KAM.SpinOrbit.Lock.Graph KAM.SpinOrbit.Lock.Graph.Angle KAM.SpinOrbit.Lock.Graph.Bridge`**
  → `short-name check OK (no reused public short name)`. The first run flagged `Angle`, `Angle.inv`, … and I
  renamed them to `LockAngle`, `lockInv_*`.
- **`#print axioms`** (scratch file deleted):
  - `lockBarrier_of_certV2`: `[propext, Classical.choice, Quot.sound]`;
  - `lockBarrier_of_certified`: same;
  - `lockBarrier_of_exact_torus`: same.
- No `sorry`, `axiom` or heartbeat options. Every file is under 400 lines.

## Uncertainties / design signals

- No heartbeat problems. Every proof elaborates at default settings.
- `Lock/Graph/Angle.lean` duplicates about 90 lines of the flow-free part of `SoGraph.Torus` (`Graph/Inverse.lean`).
  The landed structure bundles the rotational flow fields, so it cannot be reused for the librational flow. A later
  refactor could make `SoGraph.Torus` extend `LockAngle`. I did not touch the landed file.
- The engine-generic core takes `hnv` and `hs` besides `CertifiedTorus` (rationale above). If the orchestrator wants
  the core to take only `CertifiedTorus`, the alternative is a compactness argument (positivity of `Re I` on a
  thinner strip by uniform continuity and periodicity). That alternative is more Lean for no gain.

## Suspected errata / deviations

- **Design SO-LOCK §3** ("clock rigidity") does not mention that `clock_frequency` needs the whole complex strip
  inside `Re I > 0`. The implementation supplies this from `CertifiedTorus` (ball ⊆ `D`) and the sqrt
  `NonvanishingOn` arm. This is a design omission, not a source erratum.
- No other deviation. The signed statements are unchanged.

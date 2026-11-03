# B4-TSTEP independent package audit 1

Audit date: 2026-11-03. Audited HEAD `17bc288ac7e69b2c0afba19c97b38b662a1d2ae9` (including prover `d65c286bb`), against `inp` = `8f9a0aea60b4c4d72761dae0528d80077897a6e0`, using `git diff inp...HEAD`.

## Verdict and scope

**FINAL VERDICT: PASS WITH NOTES** for `torusStep_confinement` and the B4-TSTEP package. All four targeted builds, the two signature/conclusion probes, all 13 public-theorem axiom checks, and kernel replay passed. Lint has only the explicitly permitted stale-generated-root exception. The notes concern rational representation of b, guarded totalized charts, and the narrow smoke export; there is no blocking mathematical finding. This package implements the ordinary Track B theorem `KAM.EffectiveStability.torusStep_confinement`; there is no B4 frozen anchor or provider to seal. Frozen/provider type equality and frozen-body sealing checks are therefore not applicable. The explicit user report path overrides the generic I/N/P brief's main-worktree destination.

The controlling contract is the B4-TSTEP brief, B1-common brief, and handoff AUDIT FOCUS, together with B SPEC, FREEZE-PROPOSAL, OWNER-DECISIONS OD-B11/B12, and program-b-plan §2.2 and §3.2. Read AGENTS, PLAN, DECISIONS and the common I/N/P audit/prover briefs. Inspected the B2-STEP analogue, B1-T implementation and the relevant FT, TorusDomain, RealFlow, Cauchy and Canonical APIs; blueprint-N `bpN:p5:setting`, `flow`, `lie-derivative`, `taylor` supply the reused conventions. The local DECISIONS ends at D70; D71 is the packet's overnight status, not evidence of exact-text freeze approval. No unrelated I/N/P headline is claimed.

Only four Lean files are new in the diff: TorusStep.lean and TorusStep/{Remainder,Drift,Smoke}.lean; the other changed file is the handoff. All are inspected. No repository source was edited by this audit.

## Declaration review

Names below are in `KAM.EffectiveStability`. Every public declaration is listed; the private helper is included for completeness.

| Contract / node | Declaration | Verdict | Reason |
|---|---|---|---|
| Strip conversion | `strip_le_log_lam` | PASS | Derives `σ ≤ log lam/(2π)` from the stated rational majorant checks and `σ ≥ 0`. |
| Finite remainder | `torusRem` | PASS | Exact difference of the actual complex time-one pullback and the finite Lie sum. |
| Real restriction | `ftEvalC_realInclusion₂` | PASS | Unconditional real/complex polynomial evaluation identity. |
| Real restriction | `ftEvalC_realInclusion₂_im` | PASS | Imaginary part vanishes at every real point. |
| FT majorant | `norm_ftEvalC_le_of_strip` | PASS | Applies FT bound with the same geometric strip, carrier, and action radii. |
| Small field | `smallField_of_ftBounds` | PASS | Proves the scaled field bound from both finite derivative majorants; does not assume it in the main theorem. |
| Half-interior regularity | `differentiableOn_torusRem` | PASS | Flow holomorphy and entire FT evaluation imply remainder holomorphy. |
| Taylor remainder | `norm_torusRem_le` | PASS | Order `L` bracket bound along the actual flow, integral Taylor weight, denominator `L!`. |
| Real remainder | `torusRem_realInclusion₂` | PASS | Real-flow compatibility at real half-interior points; sign and truncation match. |
| Actions-only check | `ftActOnly` | PASS | Exact Boolean test for zero frequencies, zero `e`, zero sine coefficient. Sufficient, not a completeness claim. |
| Padded list support | private `getD_zero_of_all` | PASS | Missing frequency entries default to zero; every actual entry is checked. |
| Angle independence | `ftEvalR_actOnly` | PASS | Holds on the whole evaluation carrier, without an unnecessary `FTFits Nact` premise. |
| Exact split | `torusRemainder_eq` | PASS | `ftEqCheck` soundness, additivity and angle independence give the required equality. |
| Drift receiver | `torusDrift_le` | PASS | Local equality before differentiation; polynomial radius `b`, Cauchy radius `δc`, bound `B/(L! δc)`. |
| Actual chart | `torusChart` | PASS WITH NOTES | Exact inherited real time-one map; dynamical interpretation is guarded by the proved interior/SmallField conditions. |
| Inverse chart | `torusChartInv` | PASS WITH NOTES | Exact inherited time-minus-one map; inverse property is proved on the chart domain, not globally. |
| B4 one-generator soundness | `torusStep_confinement` | PASS WITH NOTES | B1-T conclusion recovered in full; finite-data interface qualification below. |
| Integrable test data | `torusSmokeH` | PASS | Exactly `J₀²/2` when evaluated in dimension one. |
| Smoke | `torusStepSmoke_zeroDrift` | PASS WITH NOTES | Instantiates the actual main theorem with checked data; its exported conclusion retains only zero drift, not the ODE/uniqueness clauses. |

No helper is substituted for a stronger source result. Helpers taking `SmallField` or interior membership are distinctly named intermediate results, and the final theorem derives these hypotheses from its finite checks.

## Focus trace

1. **Premises and conclusion.** Main theorem lines 51–72 contain typing (`FTFits`), exact Boolean equality/actions-only tests, finite lists, real vectors/scalars and explicit equalities/inequalities. None assumes a flow, remainder, chart property or confinement conclusion. The initial point premise is the prescribed initial box. No implicit instance or bundled field hides an analytic proof obligation. OD-B12 explicitly puts homological solving/divisor diagnostics outside soundness. Lines 73–85 retain B1-T existence past both endpoints, physical Hamiltonian ODE, agreement with every competing solution on every order-connected interval containing zero, chart-image identity, drift and action-size bounds. The scratch probe independently substitutes `V = univ`, `H = ftEvalR H`, `Ψ = torusChart`, `Ψinv = torusChartInv` into the B1-T conclusion and applies the main theorem.

2. **Strip conversion.** Remainder.lean:37–52 proves `2πσ ≤ 2πub σ = x`, `exp(x) ≤ 1/(1-x) ≤ lam`, positivity of `lam`, then takes the logarithm. Main derives `σ ≥ 0` from `0 < σ' < σ`. `norm_ftEvalC_le_of_strip` uses `|Im φ_i| < σ ≤ log lam/(2π)` and `‖J_i‖ < ρ`; the same outer strip bounds the generator derivatives and the order-L bracket along the trajectory. There is no coefficient-radius/geometric-radius substitution or missing `2π`.

3. **Chart and periodicity.** Main:93–124 places the enlarged cylinder in the full gauge interior, hence the half interior. Real-flow regularity, symplecticity and the negative-time inverse supply B1-T chart premises. Both χ and H are lattice-periodic by FT semantics. `comp_realFlow_angleShift` gives periodicity of `H ∘ Ψ`; translation leaves the action projection unchanged, so subtracting `N(J)` preserves periodicity of R (main:125–133). This is enough for B1-T periodic continuation on lifted angles.

4. **Drift.** Remainder:116–147 uses `taylor_lie`, with trajectories remaining in the outer strip and `ftEvalC_adPow_complex`, to prove `‖Rem‖ ≤ B/L!`. Drift:66–80 gives `H ∘ Ψ - N = P + Re(Rem ∘ ι)` on the real half interior. At x, that interior is open, so Drift:104–117 proves an eventual equality and transfers its derivative. `abs_fderiv_ftEvalR_le` bounds the P derivative using `bl`, whose entries are exactly `b`; no replacement by the larger r occurs. The closed Cauchy polydisc is contained in the half interior by `δc + σ'/2 < σ` and `r_i + δc + ρ'/2 < ρ`, with `|x_J| ≤ b ≤ r`. `abs_fderiv_realPart_fst_le` gives `(B/L!)/δc = B/(L! δc)`. The triangle inequality and hdrift finish. No oscillator bracket factor `2r_j` belongs to this single angle derivative.

5. **Deviations.** Dropping `FTFits Nact` is a strict improvement: angle independence and smooth evaluation do not require it, and no norm/bracket bound is applied to Nact. `x ≥ 0` is derived from positivity of σ and πub. `b_i + ρ' < ρ` follows from hdom1 and εb > 0. Adding `bl`/hbl resolves the list interface of `ftAngleDriftBound`; it does force b to be rationally representable when n > 0. This is compatible with the brief's finite-data/rational-majorant implementation, but the handoff's blanket “all weakening/clarifying, none strengthen premises” must not be read as a theorem for every arbitrary real b without that representation. No unsupported analytic premise was added. The real-valued hx/hlam are explicit arithmetic inequalities, not automatic executable checks on arbitrary reals.

6. **Smoke scope.** Smoke:28–58 uses n=1, H=Nact=`J₀²/2`, χ=P=0, L=1, σ=1/10, σ'=δc=1/20, ρ=5, ρ'=1, ε=0, b=1, r=2, a=η=0, εb=T=1, lam=3 and πub=`ftPiUB`. Boolean identities are kernel-decided; scalar inequalities use norm_num. This exercises the main theorem but is a zero-initial-action, zero-generator example; it supplies no nonzero-tail or nontrivial normalization test. Its weaker export is documented, not used to stand in for main soundness.

## Definition classification and totality

All five new definitions have exposed bodies in public noncomputable sections. No new abbrev or structure is introduced.

- `ftActOnly`: exact finite recognizer on every `FTPoly`; its conservative `e=0`, `s=0` syntax excludes some extensionally action-only expressions, as specified. It does not falsely accept angle dependence.
- `torusSmokeH`: literal finite polynomial data; whole-carrier semantics inherited from FT evaluation.
- `torusRem`: literal pullback-minus-Lie-sum definition on every complex point. The Lie-tail interpretation and bound apply only on the stated half interior under SmallField.
- `torusChart`, `torusChartInv`: literal specializations of existing realFlow. The inherited `Canonical.flow` chooses a solution on [-1,1] if one exists and defaults to the initial point otherwise (Canonical/Flow.lean:51–54). These are totalized maps, not globally asserted solutions or global mutual inverses. Every dynamical consumer here has the interior and small-field guards that ensure existence, realness and uniqueness, so no proof relies on the fallback.

## Verification receipts

All Lean/Lake/replay calls in these receipts were serialized, with no overlapping audit Lean process, under this exact prefix (the gate itself also applies `nice -n 5`):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

### Targeted builds

For each MODULE in the following table, separately and in order, the exact command was the prefix above followed by:

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b4tstep MODULE
```

| MODULE | Gate output | Build output | Exit |
|---|---|---|---|
| `KAM.EffectiveStability.TorusStep.Remainder` | `[inp-gate] slot 1 acquired 02:46:30 for KAM.EffectiveStability.TorusStep.Remainder` | `Build completed successfully (2964 jobs).` | 0 |
| `KAM.EffectiveStability.TorusStep.Drift` | `[inp-gate] slot 1 acquired 02:46:56 for KAM.EffectiveStability.TorusStep.Drift` | `Build completed successfully (2969 jobs).` | 0 |
| `KAM.EffectiveStability.TorusStep` | `[inp-gate] slot 1 acquired 02:47:12 for KAM.EffectiveStability.TorusStep` | `Build completed successfully (2993 jobs).` | 0 |
| `KAM.EffectiveStability.TorusStep.Smoke` | `[inp-gate] slot 2 acquired 02:47:27 for KAM.EffectiveStability.TorusStep.Smoke` | `Build completed successfully (2994 jobs).` | 0 |

No warnings from any target. These are targeted import-closure job counts, not requests to build the root or certificate applications. An earlier independent Remainder build also exited 0 with 2964 jobs.

### Signature, conclusion and axioms

Prefix above, followed by:

```sh
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/B4TstepAudit.lean
```

Exit **0**, no errors or warnings. The scratch imported `KAM.EffectiveStability.TorusStep.Smoke`. It checked (a) a fresh declaration with the complete main signature, supplied by the main theorem with all 38 explicit binders in order, and (b) a fresh declaration whose conclusion was extracted independently from `torus_confinement` and specialized as described in focus item 1. Thus the second check does not merely copy the package's conclusion. Frozen/provider matching remains inapplicable because none is part of this package.

Exact output of all 13 `#print axioms` commands:

```text
'KAM.EffectiveStability.torusStep_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.ftEvalR_actOnly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusRemainder_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusDrift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.strip_le_log_lam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.ftEvalC_realInclusion₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.ftEvalC_realInclusion₂_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_ftEvalC_le_of_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.smallField_of_ftBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.differentiableOn_torusRem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_torusRem_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusRem_realInclusion₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusStepSmoke_zeroDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

Prefix above, followed by this single invocation:

```sh
lake env leanchecker --verbose KAM.EffectiveStability.TorusStep.Remainder KAM.EffectiveStability.TorusStep.Drift KAM.EffectiveStability.TorusStep KAM.EffectiveStability.TorusStep.Smoke
```

Exit **0**. Exact output:

```text
replaying KAM.EffectiveStability.TorusStep
replaying KAM.EffectiveStability.TorusStep.Smoke
replaying KAM.EffectiveStability.TorusStep.Drift
replaying KAM.EffectiveStability.TorusStep.Remainder
```

### Lint

Prefix above, followed by `sh scripts/lint_sources.sh`. Exit **1**, solely for the expected generated-root staleness; accepted under audit brief hygiene item 5. Exact completed-run output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (4533 Lean files, 0 comparator configurations)
.........................
----------------------------------------------------------------------
Ran 25 tests in 3.717s

OK
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (314 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

No root regeneration was performed. Application anchors were file-hash checked only, as the lint explicitly reports; this audit makes no new application-build claim. An initial unwrapped lint attempt was stopped before its ABI Lean phase and superseded by this completed capped run.

### Widths, modules, names and protected paths

Exact source scan command:

```sh
python3 - <<'PYCODE'
from pathlib import Path
import re
fs=[Path('KAM/EffectiveStability/TorusStep.lean'),*sorted(Path('KAM/EffectiveStability/TorusStep').glob('*.lean'))]
for f in fs:
 s=f.read_text()
 print(f'{f}: lines={len(s.splitlines())}, width={max(map(len,s.splitlines()))}')
 assert len(s.splitlines())<=1500
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace|set_option)\b',s)
 assert all(t in s for t in ['Copyright','\nmodule\n','public import','/-!','@[expose] public noncomputable section'])
b=[(str(f),i) for f in fs for i,l in enumerate(f.read_text().splitlines(),1) if len(l)>100]
print('width violations:',b)
assert not b
print('module headers and banned-token scan: PASS')
PYCODE
```

Exit 0; exact output:

```text
KAM/EffectiveStability/TorusStep.lean: lines=139, width=98
KAM/EffectiveStability/TorusStep/Drift.lean: lines=130, width=98
KAM/EffectiveStability/TorusStep/Remainder.lean: lines=167, width=99
KAM/EffectiveStability/TorusStep/Smoke.lean: lines=58, width=100
width violations: []
module headers and banned-token scan: PASS
```

Exact naming command:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b4tstep KAM.EffectiveStability.TorusStep.Remainder KAM.EffectiveStability.TorusStep.Drift KAM.EffectiveStability.TorusStep KAM.EffectiveStability.TorusStep.Smoke
```

Exit 0: `short-name check OK (no reused public short name)`.

`git diff --check inp...HEAD` exited 0 with no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md lakefile.lean` exited 0 with no output. A recursive source import traversal from Smoke found 82 KAM modules and **no provider or frozen theorem import**, so there is no imported DRAFT_SORRY/SEALED theorem state to resolve in this closure. Frozen definitions of HamiltonianVectorField, SymplecticForm and oscillatorAction were inspected. Scratch probe deleted after successful checking; final worktree status contains only the requested untracked report.


## Errata, uncertainties and audit deviations

No suspected pinned-paper or blueprint mathematical defect was established. This is a package proof/contract audit using the local plan and reused blueprint nodes, not a fresh audit of GLS17/CL20/Pos93 PDFs. The newly introduced wording qualification about bl is at handoff:36–39 (quoted above), not a source-paper erratum. The inherited flow's default outside the valid domain and the narrow smoke export are explicit scope notes, not closure of stronger claims. No Lean implementation deviation was introduced by this audit; the exact user-specified worktree destination was followed. Scratch probes are removed after checking; no state-changing git command, source repair, root regeneration or manifest edit is performed.

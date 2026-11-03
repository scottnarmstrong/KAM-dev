# B2-STEP independent package audit 1

Verdict: **PASS WITH NOTES** for `KAM.EffectiveStability.oscillatorStep_confinement` and its one-generator soundness chain. No blocking mathematical defect found. There is **no frozen anchor or provider export** in B2-STEP; this is acceptance of ordinary Track B infrastructure, not a seal authorization or closure of an I/N/P anchor.

## Scope and authority

Worktree: `/root/code/KAM-inp-b2step`. Audited HEAD: `d1785b505f8fb647a49ce89693883dc7e9f108e6`.
Comparison `inp`: `cf4f25b6024d29837da39af09d1c0dfe5dcd8b0c`; merge base: `a5c88d4209eeb6d3813076a9c78afc49158cd4d0`.
Initial working tree was clean. Comparison used `git diff inp...HEAD`, as requested.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the generic package-audit brief, B2-STEP handoff/AUDIT FOCUS, `/root/code/KAM-inp-b1/.drafts/B/brief-B2-STEP.md`, `brief-B1-common.md`, Track B SPEC, FREEZE-PROPOSAL and OWNER-DECISIONS, program-b-plan §3.1–3.2 at `/root/code/KAM/docs/explorations/program-b-plan.md:300–420`, and the applicable shared blueprint-N Part 5 setting/flow/Taylor statements. Inspected the frozen real/complex Hamiltonian field, symplectic form and oscillator action definitions, the existing B1-E consumer and the domain, polynomial, real-flow, Cauchy and Taylor APIs used by the package.

The handoff's Track B focus governs in place of unrelated I/N/P anchor/blueprint checklists. B2 is unfrozen under recorded OD-B7; the local DECISIONS snapshot ends at D70, so D71 is treated as the packet's recorded overnight status, not independently verified exact-text freeze approval. The user's exact worktree report destination overrides the generic brief's main-worktree destination.

The triple-dot diff has 12 paths: five new B2-STEP proof modules, the Poly facade, inherited ChartChain, and five Track B documentation/metadata files. The STEP implementation paths are byte-identical between implementation commit `4e0cba8e3` and audited HEAD, including after merge `73141b1cb`. ChartChain is inherited B2-COMPOSE infrastructure with its own audit; it is not imported by STEP and is not independently re-audited here. The facade retains its correct public import of Poly.Lie. No protected path changes occur in `git diff inp...HEAD`.

## Declaration review

All names below are in `KAM.EffectiveStability`; `CartPoly.` is written explicitly. Each row covers one new public declaration. Locations are in the audited worktree.

| Node / file:line | Declaration | Verdict | Reason |
|---|---|---|---|
| Finite Lie sum, Poly/Lie:30 | `CartPoly.cartLieSum` | PASS | Exact rational factorial weights, indices `j < L`, iterated bracket in the existing source convention. |
| Poly/Lie:35 | `CartPoly.cartLieSum_succ` | PASS | Appends precisely the order-L term. |
| Poly/Lie:40 | `CartPoly.cartEval_lieSum` | PASS | Unconditional evaluation identity in any commutative ℚ-algebra; stronger scalar scope than required. |
| Poly/Lie:49 | `CartPoly.cartFits_lieSum` | PASS | Preserves dimension typing of both inputs. |
| Poly/Lie:54 | `CartPoly.cartEval_lieSum_complex` | PASS | Exactly matches analytic `adPow`, including sign and factorial; Fits premises are typing data. |
| Action substitution, Poly/Lie:67 | `CartPoly.cartPow` | PASS | Ordinary polynomial powers, constant one at exponent zero. |
| Poly/Lie:71 | `CartPoly.cartEval_pow` | PASS | Evaluation commutes with powers over the whole carrier. |
| Poly/Lie:78 | `CartPoly.cartActProd` | PASS | Finite product of action powers; empty product one, missing exponent zero. |
| Poly/Lie:82 | `CartPoly.cartEval_actProd` | PASS | Product evaluation identity, no hidden dimension restriction. |
| Poly/Lie:90 | `CartPoly.cartActSubst` | PASS WITH NOTES | Correct substitution on the explicitly checked action-only input carrier; see totalization classification below. |
| Poly/Lie:94 | `CartPoly.cartActOnly` | PASS | Bool checks every p-exponent equals zero. |
| Poly/Lie:96 | `CartPoly.cartGetD_eq_zero_of_all` | PASS | Includes absent list indices via zero default. |
| Poly/Lie:106 | `CartPoly.getD_b_of_actOnly` | PASS | Extracts the checked p-exponent condition for every monomial/index. |
| Poly/Lie:110 | `CartPoly.prod_range_eq_fin` | PASS | General monoid product equality with explicit unit factors outside both ranges; no analytic assumption. |
| Poly/Lie:121 | `CartPoly.cartEval_actSubst_mono` | PASS | Requires exactly zero p-exponents and no q-exponents outside dimension n. |
| Poly/Lie:140 | `CartPoly.cartEval_actSubst` | PASS | Checked substitution evaluates at complex/formal actions in any commutative ℚ-algebra; stronger than required. |
| Poly/Lie:161 | `CartPoly.cartEval_actSubst_real` | PASS | Identifies `(p²+q²)/2` with the frozen `oscillatorAction z.2 z.1`. |
| Remainder:39 | `stepRem` | PASS | Exact complex flow pullback minus finite Lie sum. |
| Remainder:43 | `differentiableOn_cartEval` | PASS | Rational polynomial holomorphic on arbitrary U. |
| Remainder:47 | `cartEval_realInclusion₂` | PASS | Exact rational-coefficient reality bridge. |
| Remainder:53 | `cartEval_realInclusion₂_im` | PASS | Imaginary part vanishes at every real point. |
| Remainder:59 | `smallField_of_supBound` | PASS | Derives SmallField from finite majorants; does not assume the flow or field bound as a main-theorem premise. |
| Remainder:83 | `differentiableOn_stepRem` | PASS | Holomorphy on the half gauge interior, from the existing small-field flow theorem. |
| Remainder:96 | `norm_stepRem_le` | PASS | Taylor integral bound B/L!, with B paid on the actual trajectory in Ω. |
| Remainder:130 | `stepRem_realInclusion₂` | PASS | Actual real-flow pullback; no projection of a non-real trajectory used without proof. |
| Drift:34 | `differentiableAt_realPart` | PASS | Scalar restriction and real inclusion chain rule at an interior point. |
| Drift:44 | `chartRemainder_eq` | PASS | Exact Bool identity yields R = P + Re Rem∘ι on the real half interior. |
| Drift:62 | `stepDrift_le` | PASS | Local derivative splitting, polynomial majorant, and closed-disc Cauchy estimate yield the required η bound. |
| OscillatorStep:38 | `stepChart` | PASS | Actual real time-one flow of χ on the stated polydisc. |
| OscillatorStep:43 | `stepChartInv` | PASS | Real time-minus-one flow; inverse claim used only on the proved interior. |
| OscillatorStep:49 | `oscillatorStep_confinement` | PASS | Requested source-premise list and complete B1-E conclusion for V = univ, physical polynomial H, specified charts. |
| Smoke:29 | `stepSmoke_zeroDrift` | PASS WITH NOTES | Genuinely applies the main theorem with checked harmonic-oscillator data; its initial action bound zero restricts this smoke instance to the origin. |

Poly.lean is an import-only facade with no new declaration. Smoke's `smoke_supBound_zero` is private and proves the literal empty-polynomial majorant identity. The three anonymous examples in Poly/Lie use `decide +kernel` on the specified finite identities.

## Premises, conclusion and remainder chain

1. **Main premise inventory.** `hH,hχ,hN,hP` are CartFits typing facts. `hA,hid` are exact Bool checks. `hL`, positivity/sign/smallness, domain and time-margin hypotheses are scalar inequalities. `hρl,hrl` type the rational lists as real radii. `hq,hp,hdrift` are inequalities involving explicit finite rational majorants. `hw₀` is the required initial action-box membership. No premise mentions a trajectory, flow, remainder, chart, canonicality, confinement or an unproved analytic estimate. Real-valued radii and margins are allowed by the explicit brief: this theorem is a soundness interface, not a single executable `checkNormalForm` implementation over arbitrary real inputs.

2. **Exact conclusion.** An independent scratch theorem retained every main-theorem binder and replaced its conclusion with the complete text extracted from `oscillator_confinement`, substituting only V = univ, H = cartEval H, Ψ = stepChart χ ρ, Ψinv = stepChartInv χ ρ. Its body applied `oscillatorStep_confinement` to exactly all explicit binders in order. It elaborated with no warnings. This preserves T₁ > T, initial physical point, HasDerivAt on the full open interval, uniqueness against every solution on every order-connected I containing zero, chart-image identity, both drift and level bounds, and endpoints |t| = T. The univ membership clauses are retained.

3. **Exact algebra and reality.** `cartAdPow χ (j+1) H = {cartAdPow χ j H, χ}`, matching differentiation along Xχ, not the opposite sign. `cartEval_lieSum_complex` matches the Taylor sum term for term. `chartRemainder_eq` uses `cartEval_eq_of_eqCheck hid`, the action-only substitution lemma and `stepRem_realInclusion₂`. Rational coefficients supply reality for χ, H and the finite Lie sum. The resulting identity holds on an open real neighborhood of x; Drift:88–110 uses eventual equality before taking fderiv, rather than differentiating an identity known only on a closed stopped region.

4. **Outer remainder bound.** In Remainder:105–124, `taylor_lie` is applied with Ω₁ = Ω = cpolyOpen ρ, u = cartEval H and order L ≥ 1. `flow_mem_cpolyOpen` supplies the trajectory premise for every |t| ≤ 1. For 0 ≤ t ≤ 1, `cartEval_adPow_complex` and `cartFits_adPow` identify the analytic L-th bracket with the checked polynomial; `hρl` supplies the coordinate majorant bounds at the trajectory point. Thus B bounds the actual L-th bracket there and the integral remainder has norm ≤ B/L! throughout the half interior. No first-omitted-term approximation or infinite-series assertion is used.

5. **Derivative invoice.** At x in oscClosed b, `2 b_i ≤ r_i²` and `r_i ≥ 0` give |q_i|,|p_i| ≤ r_i. `hdom3` embeds the entire closed complex δc-polydisc about ιx into the open half gauge interior. Holomorphy and the just-proved B/L! bound apply on that disc, so Cauchy pays `(abs q_j + abs p_j) B/(L! δc) ≤ 2 r_j B/(L! δc)`. Drift:121–126 obtains nonnegativity of this derivative majorant from the norm bound at the disc center and δc > 0, without assuming positivity of a potentially malformed bound. The polynomial action bracket is bounded by `cartSupBound ... rl rl` using hrl. Triangle inequality followed by hdrift gives ≤ η_j exactly once.

6. **Chart/domain obligations.** `hdom1` gives osc(b+εb) inside realInterior 1 via the coordinate radius bridge; `hdom2` provides the strict chart margin. Interior monotonicity supplies realInterior 1/2 for smoothness and symplecticity; the stronger interior 1 is retained when invoking the inverse theorem. Positivity of εb derives `2 b ≤ r²` for the stopped set. `hdom3` is separately used for the Cauchy discs; it is not confused with hdom2. Global polynomial smoothness and smoothness of the actual flow give differentiability of R on osc(b+εb); the normal part is a polynomial composition. All B1-E analytic premises are derived before its final application. No positive dimension, positive a/b, or global chart-inverse hypothesis is silently needed.

7. **Smoke.** Smoke:43–54 directly calls `oscillatorStep_confinement` with n=1, χ=[], H=cartAction 0, Nact=cartQVar 0, P=[], L=1, ρ=5, δ=δc=1, ε=0, a=0, b=1, η=0, εb=T=1, ρl=[5], rl=[2]. The Bool checks use `decide +kernel`; zero majorants and scalar margins are proved explicitly. The bound extracted at Smoke:56–58 is the theorem's endpoint-inclusive drift clause. Nonemptiness holds (w₀=0), but this particular smoke does not exercise a nonzero orbit or nonzero Lie tail; neither is claimed by its statement.

## Definition classification

There are eight new explicit definitions and no new abbrev/structure. `cartLieSum`, `cartPow`, `cartActProd` are ordinary total finite polynomial operations with correct empty/zero cases; the sum also makes sense for L=0, although the analytic remainder theorem correctly requires L≥1. `cartActOnly` is an executable exact exponent test. `cartActSubst` always computes the polynomial formed from q-exponents and coefficients, discarding p-exponents. Outside the action-only guard this amounts formally to setting p=1 while replacing q by actions; it is **not** advertised or used as the evaluation Nact(I,0) there. Every semantic use at Nact(I,0) requires `cartActOnly Nact = true`, and every dimensional comparison requires CartFits. Thus no proof relies on a junk value off the valid input carrier.

`stepRem`, `stepChart` and `stepChartInv` are literal compositions/differences using the existing totalized complex flow and real restriction. The inherited flow selects a genuine solution when available and otherwise returns its initial point. On every domain used by this proof, SmallField plus the proved interior membership supplies existence, and the real-flow bridge supplies reality/inverses. The fallback is never used to obtain a flow, derivative or inverse conclusion. There is no global assertion of invertibility outside the certified domain. All bodies are exposed by the module's `@[expose] public noncomputable section`.

## Validation

Every Lean/Lake invocation was serial and wrapped in:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

The build driver additionally runs `nice -n 5 lake build`. No heartbeat, recursion or synthesis-budget override was introduced. No clean, update, cache-get, root regeneration or library-wide build was run.

### Targeted builds

Prefix above, then each command separately:

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b2step KAM.EffectiveStability.OscillatorStep.Smoke
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b2step KAM.EffectiveStability.Poly
```

Both exit 0, no warnings. Exact output:

```text
[inp-gate] slot 1 acquired 01:20:42 for KAM.EffectiveStability.OscillatorStep.Smoke
Build completed successfully (2985 jobs).
[inp-gate] slot 1 acquired 01:21:06 for KAM.EffectiveStability.Poly
Build completed successfully (2890 jobs).
```

The Smoke target includes all five new STEP modules; the second target checks the edited public facade.

### Conclusion and axiom probe

Prefix above, then:

```sh
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/B2StepAudit.lean
```

Exit 0, no errors or warnings. In addition to the copied-conclusion probe described above, this printed axioms of **all 24 new named public theorems** listed in the declaration table. Exact axiom sets:

- `CartPoly.cartGetD_eq_zero_of_all`, `CartPoly.getD_b_of_actOnly`: `[propext, Quot.sound]`.
- Every other new public theorem in the table, including `oscillatorStep_confinement`, `stepSmoke_zeroDrift` and the independent `B2StepAudit.recovered_conclusion`: `[propext, Classical.choice, Quot.sound]`.

For example the exact main output was:

```text
'KAM.EffectiveStability.oscillatorStep_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.stepSmoke_zeroDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
'B2StepAudit.recovered_conclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Provider=frozen-type and frozen seal-body probes are inapplicable because neither exists in this package. The independent consumer-conclusion probe checks the applicable requested interface instead.

### Kernel replay

Prefix above, then one invocation:

```sh
lake env leanchecker --verbose KAM.EffectiveStability.Poly.Lie KAM.EffectiveStability.OscillatorStep.Remainder KAM.EffectiveStability.OscillatorStep.Drift KAM.EffectiveStability.OscillatorStep KAM.EffectiveStability.OscillatorStep.Smoke KAM.EffectiveStability.Poly
```

Exit 0. Exact output:

```text
replaying KAM.EffectiveStability.Poly.Deriv
replaying KAM.EffectiveStability.Poly.Bracket
replaying KAM.EffectiveStability.Poly.Basic
replaying KAM.EffectiveStability.Poly.Bound
replaying KAM.EffectiveStability.Poly
replaying KAM.EffectiveStability.OscillatorStep.Smoke
replaying KAM.EffectiveStability.OscillatorStep
replaying KAM.EffectiveStability.OscillatorStep.Drift
replaying KAM.EffectiveStability.OscillatorStep.Remainder
replaying KAM.EffectiveStability.Poly.Lie
```

### Lint and static checks

Prefix above, then `sh scripts/lint_sources.sh`:

LINT_RESULT_PENDING

Short-name check:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b2step KAM.EffectiveStability.Poly.Lie KAM.EffectiveStability.OscillatorStep.Remainder KAM.EffectiveStability.OscillatorStep.Drift KAM.EffectiveStability.OscillatorStep KAM.EffectiveStability.OscillatorStep.Smoke KAM.EffectiveStability.Poly
```

Exact output: `short-name check OK (no reused public short name)`; checker completed successfully. A subsequent unrelated exploratory rg in the same shell returned 2 for a nonexistent blueprint glob; the actual blueprint file was then read at `blueprint-N/parts/p5-canonical-maps.tex`. That rg failure is not a Lean/checker failure.

Python width/line-count/forbidden-token scan over the six STEP paths returned no overlong lines and no forbidden tokens. Line counts: Poly/Lie 188, Remainder 145, Drift 142, OscillatorStep 121, Smoke 60, Poly facade 23. All have copyright, `module`, public imports, module docstring and public section; definitions have expose. Carriers are the required Fin-function products; no EuclideanSpace or local resource override. `git diff --check inp...HEAD` exits 0 with empty output.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md KAM/Root lakefile.lean` exits 0 with empty output. This is the required triple-dot comparison, not the different direct comparison to the newer inp tip. Recursive source import traversal reaches 20 frozen **definition** modules, zero frozen theorem modules and zero providers. There is no DRAFT_SORRY dependency, application import or new provider-quarantine exception.

## Notes, uncertainties, errata and deviations

No new suspected blueprint or pinned-source defect was found. Program-b-plan's Lie formula with m=L−1 agrees with the exact Taylor remainder; its Cartesian tail charge `w_j E(1/δq_j+1/δp_j)` becomes precisely `2 r_j B/(L! δc)`. The sign, max-norm gauge, real coordinate order and frozen action normalization agree throughout. No source-paper theorem is newly transcribed here; this audit does not reopen already-audited B1/B2 dependencies or certify unrelated blueprint nodes.

The handoff's deviations are justified: rational lists plus typing equalities reflect the existing majorant API; the Bool action-only guard is executable; using complex `taylor_lie` directly supplies the outer-domain remainder needed by Cauchy; hL is the source Taylor guard. The action-only substitution's off-guard behavior and origin-only smoke limitation are recorded above. The theorem proves one-generator Cartesian-polynomial soundness; multiple generators, parameter-box uniformity, inverse displacement/initial-region certificates and a complete executable checker remain outside this package's explicit contract.

The handoff's 187-line count for Poly/Lie is a minor documentation discrepancy: audited source has 188 lines, comfortably below the cap. Its Poly facade width rewrap is present. Nothing in Frozen/manifest was repaired or reinterpreted. Only this report was added to the repository; scratch probes are removed after verification. No state-changing git command was used.

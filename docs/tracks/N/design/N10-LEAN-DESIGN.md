# Lean design for blueprint-N Part 10: N-HEAD-C assembly

Design v1, 2026-10-28, branch `inp-design-n10`. Planning evidence only: no proofs, frozen changes,
or sealing. Authority: DESIGN-N10.md, DESIGN-COMMON.md, current frozen N-HEAD-C, and the reviewed graph.
Format/reuse model: PART145-LEAN-DESIGN.md and its two audits (including their Data ownership correction).

## Decisions

1. Reuse `KAM.Nekhoroshev.HeadParams`, `.Pos`, `HeadHyp`, all existing constants and `centralSet`.
   No second Hamiltonian, frequency, Hessian, analytic membership or solution representation is introduced.
2. Use Part 9 in its **period-one, geometric-width** normalization: input `(mu,B,ell,r0,s/2)` and
   perturbation bound `epsPrime = coth(pi*s/4)^n * epsilon`. The existing Part 1 tilde formulas remain
   upstream facts; cancel their positive `2*pi` factors when needed. Do not scale time or the final orbit.
3. Prove concrete conversion lemmas independently of Part 9's pending setting carrier. The not-yet-delivered
   upstream `setting`, `omega0`, `thm1` interfaces below are reconciliation ports, never added premises.
   `cf_branch` is our concrete specialization to be proved using those ports, not an assumed stability theorem.
4. Keep the stopped theorem: the orbit need not stay in the smaller tube. Its total field is the frozen
   `hamiltonianVectorField (realHamiltonian h f)`. Prove confinement first, then use Part 3 continuation/glue.
5. Constants are functions of the seven data alone; choose them before `h,f,epsilon,theta0,I0`.
   The unspecified holomorphic size bound in `IsAnalyticIntegrable` never enters any chosen constant.
6. The provider namespace is exactly `KAM.Provider.Nekhoroshev`, as the anchor actually imports it.
   The provider path is `KAM/Provider/Nekhoroshev/QuasiConvexNekhoroshevComplexBound.lean`.
   This is the existing track-specific specialization of the generic provider rule.

## Carriers and standing structures

All unqualified names here are in `KAM.Nekhoroshev`, except `KAM.Weighted.*`, `KAM.Canonical.RealOn`
and the explicit provider namespace. Angles precede actions. Real coordinates are `Fin n → ℝ`, complex
coordinates `Fin n → ℂ`, Fourier modes `Fin n → ℤ`. Pi/Prod norms remain the existing max norms;
`euclid` is the existing scalar function, never an ambient norm instance.

| Blueprint quantity | Exact Lean object / new definition | Consumer |
|---|---|---|
| Seven data | `HeadParams n`, fields `R s M m Mc wmin`; `HeadParams.Pos` | constants, all packages |
| (H1)–(H5) | `HeadHyp p h`, existing conjunction of the frozen predicates | `hc_h`, `hc_qc`, `hc_exc`, `hc_time` |
| ODE standing assumptions | `Data n p.R p.s epsilon h f` (owned by Interfaces/Setting) | `ODE.confinement_glue`, `ODE.uniqueness_closed` |
| `P` in the weighted domains | `centralSet n p.R`, already the complex image of the closed real max ball | all tube/class bounds |
| `V`, `U`, `W` | `Weighted.polyNbhd (centralSet n p.R) p.r0`, its preimage under `realInclusion n`, `univ ×ˢ U` | Part 9 reconciliation |
| `s1,F1,epsilon1,R0,epsilon'` | new `HeadParams.s1 F1 eps1 R0 epsPrime` | numeric dictionary, Part 9 |
| `rho,tau` | new `HeadParams.rho p epsilon`, `.tau p epsilon` | closed action ball and time window |
| Choice of four constants | `choice p = (p.C,p.T,p.c,p.eps0)` | quantifier order; no choice from h |
| Weighted estimate | existing `Weighted.InClass`, `Canonical.RealOn`, `Weighted.WBound` | class, reality, summability and size |

`HeadParams.expo n = 1/(2*(n:ℝ))`. `eps1 = mu*r0^2/(2^10*A^(2*n))`, `R0 = r0/A`,
`s1 = s/2`, `epsStar = 2*pi*eps1`, `F = 2*pi*F1`.
`rho = C*epsilon^expo`, `tau = T*exp(c*epsilon^(-expo))`.
All definitions are exposed; no new structures, global instances or unproved equality bridges.

## Complete node-to-declaration map

Locators below are in `blueprint-N/parts/p10-assembly.tex`, except the explicitly marked frozen-root statement. `S/P` give statement/proof line intervals;
`—` means a definition or external fact. Every scoped graph node appears once. Proof-step nodes map to
an actual enclosing declaration or named helper, not to independent assumed lemmas. The names of the
seven main result/definition nodes use the required snake_case convention.

| Graph node | S / P lines | Declaration and exact reuse / proof obligation |
|---|---|---|
| `bpN:p10:ext-rpow` | 18–19 / — | Mathlib `Real.rpow_le_rpow`, `Real.mul_rpow`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.pow_rpow_inv_natCast`, `Real.rpow_neg`, `Real.exp_le_exp`; no new declaration |
| `bpN:p10:choice` | 27–34 / — | `choice`, `HeadParams.s1 F1 eps1 R0 epsPrime rho tau`; reuse existing HeadParams fields |
| `bpN:p10:choice-props` | 36–46 / 47–55 | `choice_props`, `cp_dict`, `cp_rad`, `cp_size` together are clauses (a)–(d) |
| `stepN:p10:cp-ab` | 48–48 / 48–48 | `choice_props`: `const_pos`, `const_eps0`, `const_size`, `HeadParams.two_mu_le_B` and four `r0_le_*` lemmas |
| `stepN:p10:cp-dict` | 50–50 / 50–50 | `cp_dict`: definitions, positivity from `const_pos`, `const_eps0`; cancel `2*pi` |
| `stepN:p10:cp-rad` | 52–52 / 52–52 | `cp_rad`: `cp_dict`, exact `const_conclusion`, `Real.mul_rpow`, `Real.rpow_neg` |
| `stepN:p10:cp-size` | 54–54 / 54–54 | `cp_size`: `const_eps0`, `HeadParams.C_pos`, `T_pos`, `Real.rpow_le_rpow`, `Real.rpow_pos_of_pos`, `Real.exp_pos` |
| `bpN:p10:hypotheses-check` | 59–73 / 74–90 | `hypotheses_check` plus `hc_tubes`, `hc_exc`, `hc_time`, `head_time_prefactor`, `head_field_locality`; assemble pending Part 9 `setting` locally |
| `stepN:p10:hc-tubes` | 75–75 / 75–75 | `hc_tubes`: `const_tubes`, `ball_subset_realActionDomain`, `centralSet`; no norm change |
| `stepN:p10:hc-h` | 77–77 / 77–77 | `hc_h`: `hessian_convert`, (H1), `hc_tubes`, `HeadParams.q_pos`; Euclidean operator bound `n*Mc ≤ B` |
| `stepN:p10:hc-qc` | 79–79 / 79–79 | `hc_qc`: `qc_convert` restricted using `hc_tubes`; (d) radius from `choice_props` |
| `stepN:p10:hc-f` | 81–81 / 81–81 | `hc_f`: exact `const_perturbation` first conjunct, frozen holomorphy/periodicity/reality clauses, `hc_tubes` |
| `stepN:p10:hc-setting` | 83–83 / 83–83 | local construction in `cf_branch`, fed by `hypotheses_check`, `choice_props`, `hc_tubes`; reconcile `setting` |
| `stepN:p10:hc-exc` | 85–85 / 85–85 | `hc_exc`: `const_exceptional`, `frequencyMap_tildeh`, `tilde_hypotheses`, positive `2*pi` cancellation; or (H3) directly |
| `stepN:p10:hc-time` | 87–87 / 87–87 | `hc_time` + `head_time_prefactor`: `const_time`/`const_time_arith` with scaling canceled; upstream `omega0` supplies actual maximum |
| `stepN:p10:hc-field` | 89–89 / 89–89 | `head_field_locality`: openness of `polyNbhd` and real preimage, `Filter.EventuallyEq.fderiv_eq`; values from `holo_real_b` |
| `bpN:p10:confinement` | 94–98 / 99–107 | `confinement`: `cf_branch`, `cp_rad`, `HeadParams.T_pos`, nonnegative `rho` |
| `stepN:p10:cf-setting` | 100–100 / 100–100 | local Part 9 setting construction in `cf_branch` from `hypotheses_check`; same data, no stability assumption |
| `stepN:p10:cf-orbit` | 102–102 / 102–102 | `cf_orbit`: unpack frozen `IsSolutionOn`; initial projection from `hy0`; `hc_tubes` gives membership in P |
| `stepN:p10:cf-branch` | 104–104 / 104–104 | `cf_branch`: pending `thm1` branch (a), `hc_exc`, `omega0`, `hc_time`, `head_time_prefactor`, `head_field_locality` |
| `stepN:p10:cf-trans` | 106–106 / 106–106 | local arithmetic inside `confinement`: `cp_rad`, `T > 0`, `exp_pos`; radius `rho/2 ≤ rho`, time `tau ≤ 2*T*exp(...)` |
| `bpN:p10:existence` | 111–114 / 115–123 | `existence`: `ODE.confinement_glue` with `rho,tau`, using `confinement`, `cp_size`, `ex_ball` |
| `stepN:p10:ex-rho` | 116–116 / 116–116 | `cp_size` used in `existence`; positivity of real powers and exponential |
| `stepN:p10:ex-ball` | 118–118 / 118–118 | `ex_ball`: triangle inequality, `norm I0 < R/2`, `rho ≤ R/4`; strict bound `< 3*R/4 < R` |
| `stepN:p10:ex-apriori` | 120–120 / 120–120 | local lambda to `ODE.confinement_glue` inside `existence`; invoke `confinement` for every open OrdConnected J containing 0 |
| `stepN:p10:ex-glue` | 122–122 / 122–122 | `existence`: exact `ODE.confinement_glue`; construct `Data` from `hp.hR hp.hs hh.1 hf` |
| `bpN:p10:uniqueness` | 125–129 / 130–134 | `uniqueness`: exact `ODE.uniqueness_closed` after time restriction, including L=0 |
| `stepN:p10:un-restrict` | 131–131 / 131–131 | `head_solution_restrict`: directly restrict frozen predicate; same pointwise two-sided derivative |
| `stepN:p10:un-apply` | 133–133 / 133–133 | local application in `uniqueness`: `ODE.uniqueness_closed hd isOpen_ball hUs hy hzRestricted hy0` |
| `bpN:p10:head` | 138–142 / 143–155 | `head` (fixed explicit constants), then exact `KAM.Provider.Nekhoroshev.quasiConvex_nekhoroshev_complexBound` |
| `stepN:p10:hd-order` | 144–144 / 144–144 | `choice` and the outer telescope of the provider; no proposition asserting functional independence |
| `stepN:p10:hd-const` | 146–146 / 146–146 | `choice_props` used in provider before introducing h/f/epsilon |
| `stepN:p10:hd-univ` | 148–148 / 148–148 | local introductions in `head`; construct exact `HeadHyp` conjunction, apply `hypotheses_check` through `existence` |
| `stepN:p10:hd-abc` | 150–150 / 150–150 | local invocation of `existence` in `head`; choose its z once |
| `stepN:p10:hd-d` | 152–152 / 152–152 | local invocation of `uniqueness` in `head` for that same z and every L/y |
| `stepN:p10:hd-dep` | 154–154 / 154–154 | provider telescope and `choice p`: constants unchanged across `existence` and `uniqueness`; z remains existential |
| `bpN:p0:head` | p0-conventions.tex 204–237 / p10-assembly.tex 143–155 | Frozen root, exact `KAM.Provider.Nekhoroshev.quasiConvex_nekhoroshev_complexBound` telescope in Appendix A; anchor remains read-only |

All 36 Part 10 statement-source nodes and the Part 0 root whose proof source is Part 10 are covered.

## Reuse and upstream interface (to reconcile)

Existing source names below were inspected in this checkout. The signatures import built interfaces,
not Part 9 or any draft anchor. Part 3's source is implemented here, but its specialization olean is
absent in the shared signature snapshot. It is a source-verified dependency, not a successful import receipt.
The older Part 3 signatures nested `Data` under `ODE`; PART145 and its audits correct ownership to
`KAM.Nekhoroshev.Data`. Production `ODE/Specialization.lean` already uses that single existing type.

| Owner/node | Exact upstream declaration | Inputs we supply / output consumed |
|---|---|---|
| Part 1 constants | `const_pos`, `const_eps0`, `const_size`, `const_conclusion`, `HeadParams.r0_le_half_s`, `r0_le_R_div_eight`, `r0_le_ell_div`, `r0_le_wmin_div` | `1 ≤ n`, p, hp; positivity, margin, minimum entries and exact powers |
| Part 1 analytic | `const_tubes`, `const_hyp`, `const_perturbation`, `const_exceptional`, `const_time` | p/hp, exact `HeadHyp`, perturbation membership; tube/norm/frequency estimates. `const_hyp`, exceptional/time are tilde-normalized; cancel scaling explicitly |
| Part 1 direct unscaled route | `hessian_convert`, `qc_convert`, `partials`, `ball_subset_realActionDomain`, `holo_real_b` | same frozen data; unscaled Euclidean Hessian/QC, frequency upper bound, field/value identification |
| Part 4/5 carriers | `KAM.Weighted.polyNbhd`, `Dom`, `InClass`, `WBound`, `isOpen_polyNbhd`; `KAM.Canonical.RealOn` | exact existing total f and frozen real inclusion; no recreated Fourier norm |
| Part 9 `bpN:p9:setting` (pending) | `KAM.Nekhoroshev.setting` (name convention; carrier not yet fixed) | n≥2, real P represented by centralSet, r0,s1>0, 0<mu≤B, ell>0; holomorphy/reality, Euclidean complex Hessian bound B, conic QC, r0≤ell/(2B), class/reality and finite weighted norm. Need bridge to the embedded-real centralSet if the eventual carrier takes a real P |
| Part 9 `bpN:p9:omega0` (pending) | `KAM.Nekhoroshev.omega0` | that setting, I0∈P; maximum of euclid(frequencyMap h) on euclid(I−I0)≤R0, ball inclusion, attainment. `hc_exc` gives positive lower bound; `hc_time` gives upper bound √n*M. Need exposed spec/attainment access, not a guessed local definition |
| Part 9 `bpN:p9:thm1` (pending) | `KAM.Nekhoroshev.thm1` | same setting; P nonempty; 0<epsPrime≤eps1 and WBound; total F agrees on W; OrdConnected J∋0, HasDerivAt y (F(y t)) t; initial I0∈P. Consume branch (a) when euclid(omega I0)≥mu*r0/8: tube membership and max displacement ≤R0/2*(epsPrime/eps1)^a for time ≤A²*s1/Omega0*exp(pi*s1/(3√n)*(eps1/epsPrime)^a). No prior tube confinement |
| Part 3 glue | `KAM.Nekhoroshev.ODE.confinement_glue` | exact `Data`; U=actionBall n R; IsOpen U; U⊆ball 0 (R+s); tau,rho>0; closedBall I0 rho⊆U; every open OrdConnected J∋0 and source solution → confinement. Returns initial/solution/confinement plus comparison uniqueness |
| Part 3 uniqueness | `KAM.Nekhoroshev.ODE.uniqueness_closed` | same Data, open U and containment; both solutions on Icc(−L,L) and common value at 0. Returns EqOn; no confinement, QC or dimensional premise |

The three Part 9 rows are **not** full invented signatures. Until their delivered design is reconciled,
package N10-3 depends on these precise mathematical outputs. A mismatch is reported, never repaired by
assuming `cf_branch` or adding an orbit-confinement hypothesis. N Parts 6–7 are transitive dependencies
of `thm1`; this design neither copies nor changes their delivered interfaces.

## Conventions and departures

Period is 1, geometric strip width s, Fourier weight `exp(2*pi*s*|k|₁)`. Theorem 1 uses `s1=s/2`;
its time exponent retains the `sqrt n` loss. Real and complex domains remain distinct: solution action
set `actionBall n R`; QC/derivative hypotheses on `realActionDomain n R s`; frequency lower bound only
on `actionBall n R`; smaller tube U lies in `actionBall n (5*R/8)`.

| Departure | Reason / contract preservation |
|---|---|
| `hypotheses_check` is a conjunction of concrete clauses; geometric/exceptional/time/field clauses have separate signed helpers | Avoid inventing Part 9's pending carrier. Together the node table covers (a)–(h). Setting constructor and its type must be reconciled before implementation |
| `hc_h` uses explicit Euclidean matrix action instead of a second operator-norm instance | Equivalent finite-dimensional estimate; existing `complexHessian`, `euclid` retained |
| `hc_f` uses WBound and separate class/reality | Existing norm API includes summability; does not rely on a junk supremum value |
| `cf_branch` shortens T0 to uniform `2*T` | `hc_time`, `omega0`, `head_time_prefactor` prove 2*T≤T0. The resulting theorem is a concrete specialization, with no new hypothesis |
| `uniqueness` drops n≥3, QC, epsilon smallness and special tau | Strictly stronger and true from the analytic ODE data alone; source production `ODE.uniqueness_closed` proves precisely this strength. Distinct from any weakened source theorem |
| `head_field_locality` is a separately named conditional helper | Its premise is equality of Hamiltonian values on the open W, supplied by the definition of upstream H^R and `holo_real_b`; it never assumes equality of the vector fields or confinement |
| Provider fixed constants packed only after `head` | `head` strengthens the existential headline to the specified constants; provider retains the exact frozen type |
| All design theorem bodies are `sorry` in untracked .drafts only | Explicit DESIGN-COMMON exception for signature writing; no production proof escapes |

No new source premise or owner ruling is requested. No action/time rescaling, epsilon-zero extension,
Euclidean ambient carrier, or parallel frozen predicate is used.

## Blueprint issues and inherited source concerns

1. **Part 10 L9: “It adds no analysis”.** The proof still needs the local field identity on an open set,
   inherited holomorphy/reality/class membership and a maximum specification for Omega0. These are genuine
   interface obligations, made explicit above; the sentence is reasonable only as an assembly description.
2. **Part 10 L69: “Omega0 ... satisfies ... hence T0 ... ≥2T”.** The given bound √n*M suffices, but
   the existing Part 1 `const_time` is for the scaled frequency. Applying it verbatim would compare different
   Omega0 values. Cancellation or the direct `partials` route is mandatory. This is an interface hazard,
   not a false blueprint inequality.
3. **Inherited Pos93 p.190/p.204 radius condition:** blueprint Part 9 `errata` quotes “r0≤4l/m”.
   That condition alone does not imply the full-rank block requirement M*r0≤ell/2 (M/m unbounded).
   This route already uses r0≤ell/(2B), present in the frozen-data constants minimum. It is a disclosed
   strengthening of the source intermediate hypotheses, not a change of the frozen headline.
4. **Inherited norm adaptation, Pos93 p.192/p.202 and time exponent:** Part 9 `errata` quotes “it suffices
   to assume ||k||≤K”. The blueprint's max/l1 framework uses Ka=Kg/√n and the resulting exponent loses √n.
   This is an adaptation, not a claimed paper misprint. Part 10 already includes it in c.

Items 3–4 are inherited blueprint/source reports, **not independently rechecked against a pinned PDF in
this design task**. No new paper defect is asserted; do not reclassify them as verified errata. No
blueprint, graph or ledger is edited. No frozen defect was found. The freezing comment describing an
older “proposal” in the anchor is stale prose; the actual D20 frozen telescope is the authority.

## Modules, import DAG and prover packages

Every path below is exact for the proposed local modules; all sizes are estimates, below 1500 lines.
Part 9 imports below are ports to its eventual modules, not authorization to invent their APIs.

| Package / wave | Exact files and estimated lines | Inputs / output |
|---|---|---|
| N10-1 / 1 | `KAM/Nekhoroshev/Assembly/Choice.lean` (220) | `Interfaces/Constants`; choice defs, `choice_props`, `cp_dict`, `cp_rad`, `cp_size`, `head_time_prefactor` |
| N10-2 / 2 | `KAM/Nekhoroshev/Assembly/Hypotheses.lean` (350) | N10-1; `Interfaces/ConstantsAnalytic`, `Canonical/Setting`; hc_* and `hypotheses_check`, `head_field_locality` |
| N10-3 / 3 | `KAM/Nekhoroshev/Assembly/Confinement.lean` (250) | N10-2; reconciled Part 9 setting/omega0/thm1 modules; `cf_orbit`, `cf_branch`, `confinement` |
| N10-4 / 4 | `KAM/Nekhoroshev/Assembly/Existence.lean` (200) | N10-3; existing `KAM/Nekhoroshev/ODE/Specialization.lean`; `ex_ball`, `existence`, `head_solution_restrict`, `uniqueness` |
| N10-5 / 5 | `KAM/Nekhoroshev/Assembly/Headline.lean` (150); `KAM/Provider/Nekhoroshev/QuasiConvexNekhoroshevComplexBound.lean` (90) | N10-4 and N10-1; `head`, then exact provider. Package total 240 lines |

Each prover brief repeats all hard rules below and names inputs by declaration, not just by package.
Dependency direction (imports): Choice → Interfaces.Constants; Hypotheses → Choice +
Interfaces.ConstantsAnalytic + Canonical.Setting; Confinement → Hypotheses + reconciled Part 9 modules;
Existence → Confinement + ODE.Specialization; Headline → Existence; Provider → Headline.
No implementation module imports a provider or DRAFT_SORRY anchor. The provider imports no frozen theorem:
only sealed definitions transitively. The frozen anchor alone may import the provider at sealing.
Do not modify the generated root or README. Split any estimate/proof reaching default elaboration limits.

## Exact provider assembly

Appendix A ends with the literal frozen theorem telescope, copied from
`KAM/Frozen/Nekhoroshev/Theorems/QuasiConvexNekhoroshevComplexBound.lean`, changing only namespace/body.
No import of that anchor is used to type this declaration.

| Frozen binder/result | Assembly |
|---|---|
| implicit `{n}` and `hn : 3 ≤ n` | keep unchanged; derive `1 ≤ n` only for existing constants lemmas |
| implicit `{R s M m Mcomplex omegaMin}` | p := `HeadParams.mk R s M m Mcomplex omegaMin`; six numeric fields in exactly this order |
| `hR hs hM hm hMcomplex hωmin` | hp := `HeadParams.Pos.mk hR hs hM hm hMcomplex hωmin` |
| `∃ C T c epsilon0` | witnesses `p.C, p.T, p.c, p.eps0` before all h/f data |
| four strict positivity conjuncts, then margin | `choice_props hn p hp`, first five conjuncts; exponent unfolds definitionally |
| `∀ h f epsilon` followed by (H1)–(H5) | retain their order; build `HeadHyp p h` as the existing five-fold conjunction |
| perturbation / `0<epsilon` / `epsilon≤epsilon0` | pass untouched to `head` (and its `existence` call) |
| `∀ theta0 I0`, `I0∈actionBall n (R/2)` | pass untouched; no boundary or frequency condition is added at I0 |
| `∃ z`, initial condition, frozen solution, drift | `head hn p hp` gives one z via `existence`; unfold tau/rho, preserving Icc endpoints and two-sided derivatives |
| `∀ L y`, `0≤L`, `L≤tau`, common initial value, source solution | `uniqueness` for the same z; convert `y 0=(theta0,I0)` to `y 0=z 0` using its initial equality |
| `∀ t∈Icc(-L,L), y t=z t` | EqOn applied pointwise; includes L=0; no confinement of y is introduced |

A final provider proof can use `choice_props` and `head` directly; it must not introduce any
intermediate theorem conclusion as a premise. Required eventual axioms: only `propext`, `Classical.choice`,
`Quot.sound`. Current design `#print axioms` necessarily includes `sorryAx`; it is not proof closure.
Do not seal the anchor or edit manifest in this task.

## Validation and risks

The 254-line standalone signatures file is untracked at
`/root/code/KAM-inp/.drafts/design/N10Signatures.lean`; Appendix A is byte-identical. Every theorem proof
is `sorry`; definitions have actual bodies. All proposed production files are modules with copyright,
`module`, interface `public import`, module docstring, `@[expose] public noncomputable section` and final `end`.

Required gated command:
`/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-n10 .drafts/scratch/N10Signatures.lean`.
Exit 0, exactly 22 `declaration uses sorry` warnings and no other Lean diagnostics. An initial attempt to
import ODE.Specialization failed because its shared olean was absent; the revised signature import list
uses only built modules and does not redeclare the upstream ODE theorems. The untracked axioms probe is
separate and uses the same gate. Targeted build is replaced by this signature check as DESIGN-COMMON
and the user's explicit gate-only instruction require; no production Lean module is authored here.

`scripts/lint_sources.sh` also exits 0: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`,
`FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (144 frozen declarations)`. The ABI subprocess normally invokes
Lean directly, so a task-local PATH adapter routed its sole `lake env lean <file>` request through
`inp_sig_check.sh`; no production script was edited. The gate restored the original PATH before invoking
Lean. Signature, axioms-probe and lint elaborations ran sequentially.

The separate gated `N10Axioms.lean` probe exits 0; both `KAM.Nekhoroshev.head` and the exact provider
signature print `[propext, sorryAx, Classical.choice, Quot.sound]`. This confirms the stubs are unpaid.
Mechanical checks pass: 37 graph nodes (36 Part 10 plus frozen root), literal frozen telescope inclusion,
byte-identical Appendix A/canonical signature/scratch copy, 22 sorry-only theorem bodies, module/import
policy and 254-line signature cap. Whitespace check is `git -C /root/code/KAM-inp-design-n10 diff --check`.

Risks: Part 9's concrete carrier/name delivery remains the main reconciliation gate; eventual imports
must be real built module paths before dispatching N10-3. `omega0` must expose attainment or an upper-bound
spec so a pointwise frequency bound bounds its maximum. The scaled/unscaled time calculation is a
separate signed helper. No branch may assume y stays in U. Reusing the full glue output could also supply
comparison uniqueness, but the separate uniqueness theorem keeps the blueprint path independently clear.

## Hard rules to repeat verbatim in every Lean brief

1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
   proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
3. **Every `.lean` file is a Lean module**: copyright comment, `module`, imports (`public import` for the
   interface), module docstring, `public section`. Expose (`@[expose]`) definitions whose bodies must unfold.
4. **No `axiom`, `admit`, `unsafe`, `opaque`; `sorry` only** as the manifest-bound body of a frozen statement in
   `KAM/Frozen/`. No recursion-depth or synthesis-heartbeat overrides either.
5. **Frozen files are read-only.** Never edit anything under `KAM/Frozen/` or `manifest/`. If a frozen
   declaration looks wrong, stop and report; never add a premise or substitute a helper.
6. **No conclusion-shaped hypotheses.** A theorem may assume only source premises, standing assumptions, typing
   data and explicit owner rulings. Conditional helpers get distinct names and never stand in for a source result.
7. **Ambient types:** `Fin n → ℝ`, `Fin n → ℂ`, Fourier indices `Fin n → ℤ`. Never `EuclideanSpace`.
8. **Builds:** one targeted `nice -n 5 lake build <Module>` at a time; never `lake clean`; never rebuild the
   library from scratch in a worktree (worktrees use a copy-on-write overlay on `main`'s build snapshot). A wait
   on the compile gate is expected, not a hang.
9. **Providers are quarantined.** `KAM/Provider/<Name>.lean` proves its frozen theorem as `KAM.Provider.<name>`;
   no module except the frozen anchor may import a provider or a `DRAFT_SORRY` anchor (the root file skips them).
10. **Never edit `README.md`** (generated) or `KAM.lean` (generated by `scripts/gen_root_imports.py`).
11. **Errata:** report every suspected defect in a pinned source (location, quoted text, why it is wrong) in your
    handoff; the orchestrator records it in `docs/errata/ledger.json`. Deviations you introduce are reported too.


## Appendix A. Exact signatures

SHA-256: `22021dd133e9ee9b787f52fae98bed1f544f960de5a83ec3ba891c62fb413bfe`.

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Interfaces.ConstantsAnalytic
public import KAM.Frozen.Nekhoroshev.Defs.IsSolutionOn
public import KAM.Frozen.Defs.RealHamiltonian
public import KAM.Canonical.Setting

/-!
# Part 10 assembly signatures

Design only. All theorem bodies are sorry. No draft anchor or provider is imported.
Part 9's not-yet-delivered setting is intentionally not redefined here; hc_* are
concrete conversion lemmas and cf_branch is the local specialization of thm1.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Nekhoroshev

variable {n : ℕ}

/-- Theorem-1 quantities, reusing the existing seven-data carrier and constants. -/
def HeadParams.s1 (p : HeadParams n) : ℝ := p.s / 2
def HeadParams.F1 (p : HeadParams n) : ℝ := KAM.Weighted.coth (Real.pi * p.s / 4) ^ n
def HeadParams.eps1 (p : HeadParams n) : ℝ := p.mu * p.r0 ^ 2 / (2 ^ 10 * p.A ^ (2 * n))
def HeadParams.R0 (p : HeadParams n) : ℝ := p.r0 / p.A
def HeadParams.epsPrime (p : HeadParams n) (ε : ℝ) : ℝ := p.F1 * ε
def HeadParams.tau (p : HeadParams n) (ε : ℝ) : ℝ :=
  p.T * Real.exp (p.c * ε ^ (-HeadParams.expo n))
def HeadParams.rho (p : HeadParams n) (ε : ℝ) : ℝ := p.C * ε ^ HeadParams.expo n

/-- choice: values are the already existing HeadParams constants, chosen before h and f. -/
def choice (p : HeadParams n) : ℝ × ℝ × ℝ × ℝ := (p.C, p.T, p.c, p.eps0)

/-- cp-ab and hd-const. -/
theorem choice_props (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) :
    0 < p.C ∧ 0 < p.T ∧ 0 < p.c ∧ 0 < p.eps0 ∧
    p.C * p.eps0 ^ HeadParams.expo n ≤ p.R / 4 ∧
    0 < p.mu ∧ p.mu ≤ p.B ∧ 22 ≤ p.A ∧
    p.r0 ≤ p.s / 2 ∧ p.r0 ≤ p.R / 8 ∧
    p.r0 ≤ p.ell / (2 * p.B) ∧ p.r0 ≤ 4 * p.wmin / p.mu := sorry

/-- cp-dict; no perturbation norm or smallness is assumed as a conclusion. -/
theorem cp_dict (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) (ε : ℝ) :
    p.epsStar = 2 * Real.pi * p.eps1 ∧ p.F = 2 * Real.pi * p.F1 ∧
    (p.epsPrime ε ≤ p.eps1 ↔ ε ≤ p.epsStar / p.F) ∧
    (0 < ε → ε ≤ p.eps0 → 0 < p.epsPrime ε ∧ p.epsPrime ε ≤ p.eps1) := sorry

/-- cp-rad: exact radius and exponential constants in period-one coordinates. -/
theorem cp_rad (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) {ε : ℝ} (hε : 0 < ε) :
    p.R0 / 2 * (p.epsPrime ε / p.eps1) ^ HeadParams.expo n = p.rho ε / 2 ∧
    Real.pi * p.s1 / (3 * Real.sqrt n) * (p.eps1 / p.epsPrime ε) ^ HeadParams.expo n =
      p.c * ε ^ (-HeadParams.expo n) := sorry

theorem cp_size (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) {ε : ℝ}
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) :
    0 < p.rho ε ∧ p.rho ε ≤ p.R / 4 ∧ 0 < p.tau ε := sorry

/-- hc-tubes: V is the existing max-norm polyNbhd, U is its real preimage. -/
theorem hc_tubes (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) :
    KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 ⊆ KAM.actionNbhd (actionBall n p.R) p.s ∧
    (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 →
      I ∈ actionBall n (5 * p.R / 8) ∧ I ∈ actionBall n p.R ∧ I ∈ realActionDomain n p.R p.s) ∧
    (centralSet n p.R).Nonempty ∧
    (∀ I ∈ actionBall n (p.R / 2), KAM.realInclusion n I ∈ centralSet n p.R) := sorry

/-- hc-h: Euclidean operator estimate, without installing a second norm instance. -/
theorem hc_h (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} (hh : HeadHyp p h) :
    DifferentiableOn ℂ h (KAM.Weighted.polyNbhd (centralSet n p.R) p.r0) ∧
    (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 →
      (h (KAM.realInclusion n I)).im = 0) ∧
    ∀ I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0, ∀ x : Fin n → ℂ,
      euclid (fun i => ∑ j, complexHessian h I i j * x j) ≤ p.B * euclid x := sorry

/-- hc-qc in the period-one normalization consumed by Part 9. -/
theorem hc_qc (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} (hh : HeadHyp p h) :
    ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 →
      ∀ ξ : Fin n → ℝ, |∑ i, KAM.frequencyMap h I i * ξ i| ≤ p.ell * euclid ξ →
        p.mu * euclid ξ ^ 2 ≤ fderiv ℝ (fderiv ℝ (realPart h)) I ξ ξ := sorry

/-- hc-f: class, reality and an actual summable weighted bound. -/
theorem hc_f (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) {ε : ℝ}
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hf : IsAnalyticPerturbation p.R p.s ε f) :
    KAM.Weighted.InClass (centralSet n p.R) p.r0 p.s1 f ∧
    KAM.Canonical.RealOn (KAM.Weighted.Dom n (centralSet n p.R) p.r0 p.s1) f ∧
    KAM.Weighted.WBound (centralSet n p.R) p.r0 p.s1 f (p.epsPrime ε) := sorry

/-- hc-exc: strict exclusion, retaining the frozen frequency lower bound on B(0,R). -/
theorem hc_exc (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} (hh : HeadHyp p h) :
    ∀ I₀ ∈ actionBall n (p.R / 2),
      p.mu * p.r0 / 8 < p.wmin ∧ p.wmin ≤ euclid (KAM.frequencyMap h I₀) := sorry

/-- hc-time: pointwise input for upstream omega0; no new definition of that maximum. -/
theorem hc_time (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} (hh : HeadHyp p h) :
    ∀ I₀ ∈ actionBall n (p.R / 2), ∀ I : Fin n → ℝ, euclid (I - I₀) ≤ p.R0 →
      euclid (KAM.frequencyMap h I) ≤ Real.sqrt n * p.M := sorry

/-- Conditional arithmetic helper: Omega is a scalar, not a supplied dynamical conclusion. -/
theorem head_time_prefactor (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {Ω : ℝ} (hΩ : 0 < Ω) (hΩM : Ω ≤ Real.sqrt n * p.M) :
    2 * p.T ≤ p.A ^ 2 * p.s1 / Ω := sorry

/-- Locality of the total frozen field. Hlocal is any extension of the same Hamiltonian on W. -/
theorem head_field_locality (p : HeadParams n)
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {Hlocal : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (heq : EqOn Hlocal (KAM.realHamiltonian h f)
      (univ ×ˢ (KAM.realInclusion n ⁻¹' KAM.Weighted.polyNbhd (centralSet n p.R) p.r0))) :
    EqOn (KAM.hamiltonianVectorField Hlocal) (KAM.hamiltonianVectorField (KAM.realHamiltonian h f))
      (univ ×ˢ (KAM.realInclusion n ⁻¹' KAM.Weighted.polyNbhd (centralSet n p.R) p.r0)) := sorry

/-- hypotheses-check: all concrete Part 9 analytic clauses; no guessed upstream setting carrier. -/
theorem hypotheses_check (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hh : HeadHyp p h) (hf : IsAnalyticPerturbation p.R p.s ε f)
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) :
    Data n p.R p.s ε h f ∧
    DifferentiableOn ℂ h (KAM.Weighted.polyNbhd (centralSet n p.R) p.r0) ∧
    (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 →
      (h (KAM.realInclusion n I)).im = 0) ∧
    (∀ I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0, ∀ x : Fin n → ℂ,
      euclid (fun i => ∑ j, complexHessian h I i j * x j) ≤ p.B * euclid x) ∧
    (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 →
      ∀ ξ : Fin n → ℝ, |∑ i, KAM.frequencyMap h I i * ξ i| ≤ p.ell * euclid ξ →
        p.mu * euclid ξ ^ 2 ≤ fderiv ℝ (fderiv ℝ (realPart h)) I ξ ξ) ∧
    KAM.Weighted.InClass (centralSet n p.R) p.r0 p.s1 f ∧
    KAM.Canonical.RealOn (KAM.Weighted.Dom n (centralSet n p.R) p.r0 p.s1) f ∧
    KAM.Weighted.WBound (centralSet n p.R) p.r0 p.s1 f (p.epsPrime ε) ∧
    0 < p.epsPrime ε ∧ p.epsPrime ε ≤ p.eps1 := sorry

/-- cf-orbit: extract a total-field solution; no confinement in the smaller tube is assumed. -/
theorem cf_orbit {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {U : Set (Fin n → ℝ)} {J : Set ℝ} {y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hy : IsSolutionOn H U J y) :
    ∀ t ∈ J, HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t := sorry

/-- Part 9 thm1(a) specialized to the concrete data, with the uniform shorter time. -/
theorem cf_branch (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hh : HeadHyp p h) (hf : IsAnalyticPerturbation p.R p.s ε f)
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) {θ₀ I₀ : Fin n → ℝ}
    (hI : I₀ ∈ actionBall n (p.R / 2)) {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hy0 : y 0 = (θ₀, I₀))
    (hy : IsSolutionOn (KAM.realHamiltonian h f) (actionBall n p.R) J y) :
    ∀ t ∈ J, |t| ≤ 2 * p.T * Real.exp
        (Real.pi * p.s1 / (3 * Real.sqrt n) * (p.eps1 / p.epsPrime ε) ^ HeadParams.expo n) →
      KAM.realInclusion n (y t).2 ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 ∧
      ‖(y t).2 - I₀‖ ≤ p.R0 / 2 * (p.epsPrime ε / p.eps1) ^ HeadParams.expo n := sorry

/-- confinement, including endpoints of any interval J containing 0. -/
theorem confinement (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hh : HeadHyp p h) (hf : IsAnalyticPerturbation p.R p.s ε f)
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) {θ₀ I₀ : Fin n → ℝ}
    (hI : I₀ ∈ actionBall n (p.R / 2)) {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hy0 : y 0 = (θ₀, I₀))
    (hy : IsSolutionOn (KAM.realHamiltonian h f) (actionBall n p.R) J y) :
    ∀ t ∈ J, |t| ≤ p.tau ε → ‖(y t).2 - I₀‖ ≤ p.rho ε := sorry

/-- ex-ball: closed max-norm action ball, strictly inside the solution domain. -/
theorem ex_ball (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) {ε : ℝ}
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) {I₀ : Fin n → ℝ}
    (hI : I₀ ∈ actionBall n (p.R / 2)) : closedBall I₀ (p.rho ε) ⊆ actionBall n p.R := sorry

theorem existence (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hh : HeadHyp p h) (hf : IsAnalyticPerturbation p.R p.s ε f)
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) (θ₀ I₀ : Fin n → ℝ)
    (hI : I₀ ∈ actionBall n (p.R / 2)) :
    ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = (θ₀, I₀) ∧
      IsSolutionOn (KAM.realHamiltonian h f) (actionBall n p.R) (Icc (-p.tau ε) (p.tau ε)) z ∧
      ∀ t : ℝ, |t| ≤ p.tau ε → ‖(z t).2 - I₀‖ ≤ p.rho ε := sorry

/-- un-restrict: restriction only in time; the derivative stays two-sided. -/
theorem head_solution_restrict {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {U : Set (Fin n → ℝ)} {τ L : ℝ} (hL : L ≤ τ)
    {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hz : IsSolutionOn H U (Icc (-τ) τ) z) :
    IsSolutionOn H U (Icc (-L) L) z := sorry

/-- Stronger than the blueprint: uniqueness uses just the analytic ODE data, any tau and L. -/
theorem uniqueness {R s ε τ : ℝ} {h : (Fin n → ℂ) → ℂ}
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hd : Data n R s ε h f)
    {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : IsSolutionOn (KAM.realHamiltonian h f) (actionBall n R) (Icc (-τ) τ) z)
    {L : ℝ} (hL : 0 ≤ L) (hLτ : L ≤ τ)
    {y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hy0 : y 0 = z 0)
    (hy : IsSolutionOn (KAM.realHamiltonian h f) (actionBall n R) (Icc (-L) L) y) :
    EqOn y z (Icc (-L) L) := sorry

/-- head with the specified constants, before existentially packaging them. -/
theorem head (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) :
    ∀ (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ε : ℝ),
      IsAnalyticIntegrable p.R p.s h → HasComplexHessianBound p.R p.s h p.Mc →
      (∀ I ∈ actionBall n p.R, p.wmin ≤ ‖KAM.frequencyMap h I‖) →
      IsStrictlyQuasiConvex (realActionDomain n p.R p.s) h p.m →
      HasDerivativeBounds (realActionDomain n p.R p.s) h p.M →
      IsAnalyticPerturbation p.R p.s ε f → 0 < ε → ε ≤ p.eps0 →
      ∀ θ₀ I₀ : Fin n → ℝ, I₀ ∈ actionBall n (p.R / 2) →
        ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = (θ₀, I₀) ∧
          IsSolutionOn (KAM.realHamiltonian h f) (actionBall n p.R)
            (Icc (-p.tau ε) (p.tau ε)) z ∧
          (∀ t : ℝ, |t| ≤ p.tau ε → ‖(z t).2 - I₀‖ ≤ p.rho ε) ∧
          (∀ (L : ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), 0 ≤ L → L ≤ p.tau ε →
            y 0 = (θ₀, I₀) → IsSolutionOn (KAM.realHamiltonian h f) (actionBall n p.R)
              (Icc (-L) L) y → ∀ t ∈ Icc (-L) L, y t = z t) := sorry

end KAM.Nekhoroshev

namespace KAM.Provider.Nekhoroshev

open KAM.Nekhoroshev

/-- Exact frozen telescope, copied without importing the DRAFT_SORRY theorem. -/
theorem quasiConvex_nekhoroshev_complexBound {n : ℕ} (hn : 3 ≤ n) {R s M m Mcomplex ωmin : ℝ}
    (hR : 0 < R) (hs : 0 < s) (hM : 0 < M) (hm : 0 < m)
    (hMcomplex : 0 < Mcomplex) (hωmin : 0 < ωmin) :
    ∃ C T c ε₀ : ℝ, 0 < C ∧ 0 < T ∧ 0 < c ∧ 0 < ε₀ ∧
      C * ε₀ ^ ((1 : ℝ) / (2 * (n : ℝ))) ≤ R / 4 ∧
      ∀ (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ε : ℝ),
        IsAnalyticIntegrable R s h →
        HasComplexHessianBound R s h Mcomplex →
        (∀ I ∈ actionBall n R, ωmin ≤ ‖KAM.frequencyMap h I‖) →
        IsStrictlyQuasiConvex (realActionDomain n R s) h m →
        HasDerivativeBounds (realActionDomain n R s) h M →
        IsAnalyticPerturbation R s ε f → 0 < ε → ε ≤ ε₀ →
        ∀ θ₀ I₀ : Fin n → ℝ, I₀ ∈ actionBall n (R / 2) →
          ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = (θ₀, I₀) ∧
            IsSolutionOn (KAM.realHamiltonian h f) (actionBall n R)
              (Set.Icc (- (T * Real.exp (c * ε ^ (- ((1 : ℝ) / (2 * (n : ℝ)))))))
                (T * Real.exp (c * ε ^ (- ((1 : ℝ) / (2 * (n : ℝ))))))) z ∧
            (∀ t : ℝ, |t| ≤ T * Real.exp (c * ε ^ (- ((1 : ℝ) / (2 * (n : ℝ))))) →
              ‖(z t).2 - I₀‖ ≤ C * ε ^ ((1 : ℝ) / (2 * (n : ℝ)))) ∧
            (∀ (L : ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), 0 ≤ L →
              L ≤ T * Real.exp (c * ε ^ (- ((1 : ℝ) / (2 * (n : ℝ))))) →
              y 0 = (θ₀, I₀) →
              IsSolutionOn (KAM.realHamiltonian h f) (actionBall n R)
                (Set.Icc (-L) L) y → ∀ t ∈ Set.Icc (-L) L, y t = z t) :=
  sorry

end KAM.Provider.Nekhoroshev

end
```

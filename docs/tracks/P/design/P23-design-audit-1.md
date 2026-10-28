# P23 Revision 3 independent design audit 1

Overall verdict: **PASS WITH NOTES**.

No blocking or major/medium signature defect was found in Revision 3. The nine-package plan is sufficient at the design level to recover the **unchanged** `osc_iter` from the existing core/class results and the proposed remainder/reality results. A fixture-free Lean probe independently checked that exact assembly. The estimates themselves remain unproved design obligations; neither this verdict nor successful elaboration closes the earlier package audit F1 or releases P23-15.

## Scope, authority and snapshot

The orchestrator's scope clarification controls: audit only `Revision 3 (oscillator Lie-series transfer)` and Appendix A.3, treating the original 861 signature lines as the previously audited interface. The new suffix has 15 theorem commands, four definitions and one premise structure. Existing carriers, frozen definitions, core results and the signed `osc_iter` were read to check applicability, without reopening the earlier full P23 audit.

Read the supplied AGENTS.md, local `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-design.md`, the design, the clarified handoff `/root/code/KAM-inp-p2313/.drafts/handoff-P23-13.md`, and `docs/tracks/P/audits/P23-13-audit-1.md`. The originally named `.drafts/handoff-P23.md` does not exist in this checkout; the later supplied P23-13 handoff resolves the relevant missing context. R3.8 contains a current receipt: the earlier R2 receipt is historical, not a discrepancy in the R3 signature inventory.

Audited HEAD: `ac48a764752f82d3ea3ea40f74bd549895a9dcd1`, branch `inp-design-p23r3`. `inp` was `5991245cabc06e69ec900cb6006b45f72cc85eb0` when recorded. The requested `git diff inp...HEAD` reports multiple merge bases and selects `f390de8f741ebb8dab2d17ff12ec7f7e5b6d4f46`; the design diff is exactly the 411-line R3 addendum. The wider diff also contains seven existing oscillator implementation modules and the preceding audit/handoff, which are context, not new R3 implementation claims.

Signature SHA256: `d067d47dbabfdf4913da3e2b76886eb29598f4502ad16318d328568d82380cd3`. The already present local scratch copy is byte-identical to the named shared file. The first 861 lines hash to `7d7dae4308ea9ec0ca763a2a21ce4b83280bdbb4b91d2c4f5e7567b71085e834`. Concatenating the two design Lean blocks reproduces the entire 1,131-line shared file byte for byte. No original signature was modified.

Primary statement/proof authorities checked directly:

- `blueprint-P/parts/p2-averaging.tex:167–196`: carriers, bracket, full inherited oscillator step and its four transfer steps.
- `blueprint-N/parts/p6-normal-form.tex:93–105`: the inherited step contract.
- `/root/code/KAM-inp/docs/graph/P/packets/P-p1p2.nodes.md`, records `bpP:p2:osc-iter`, `stepP:p2:oi-transfer`, `stepP:p2:oi-ratio`, `stepP:p2:oi-range`, `stepP:p2:oi-disp`.
- Part 2 lines 198–237 and the unchanged `osc_averaging`/`averaged_remainder`: immediate consumers.

## Findings

**N1 — Low, implementation-brief precision: qualify the homological module path.** R3.5's P23-13i row abbreviates its input as `NormalForm.Homological`. The actual production import is `KAM.Nekhoroshev.NormalForm.Homological`; its declarations are in namespace `KAM.NormalForm`. `OscillatorGen.lean:9` already imports the correct file. Proposed fix: use the full module path in the P23-13i brief/import list, while retaining `KAM.NormalForm.homological_param` as the declaration name. This is a documentation clarification, not a failed mathematical interface.

**N2 — Informational, release evidence: retain the proof boundary.** All 15 appended results have `sorry` bodies. The independently checked assembly uses those proposed results and consequently retains `sorryAx`. Proposed disposition: keep the explicit R3.6 full-contract proof audit gate for P23-13j/P23-15; do not mark `bpP:p2:osc-iter` proved from this design verdict. R3 already states this correctly. Full source lint also remains nonzero as recorded below.

No F-numbered failure was found; no corrected mathematical signature is required.

## Per-signature fidelity and applicability

All names in this table have prefix `KAM.Planetary`. Line numbers refer to the shared signature file. The helper hypotheses below are legitimate inputs to distinctly named generic estimates, discharged from the original step premises at their application; they are not new premises of `osc_iter`.

| Lean name / line | Blueprint obligation | Verdict | Reason |
|---|---|---|---|
| `osc_bound_const_mul`, 892 | `stepP:p2:oi-transfer` (weighted algebra) | PASS | Literal coefficient scalar multiplication and norm scaling. No class hypothesis is needed for this bound-only assertion: complex scalar multiplication commutes with the total integral defining coefficients. |
| `osc_bound_add`, 896 | `stepP:p2:oi-transfer` | PASS | Positive angle width and class premises provide integrability on the real angle cell; weighted triangle inequality at each parameter gives A+B. No exchange of sum and parameter supremum. |
| `osc_bound_tsum`, 901 | `stepP:p2:oi-transfer`, `stepP:p2:oi-ratio` | PASS | Summable nonnegative majorants control values on the entire open domain, permit coefficient interchange, holomorphic convergence and weighted tails. The pointwise total tsum is used only where convergence follows. |
| `osc_truncation_tail`, 912 | `stepP:p2:oi-transfer` (projection/tail) | PASS | Existing fast-angle truncation and exact `exp(-2*pi*K*sigma)` loss. K=0 is retained. |
| `osc_adjoint_bound`, 922 | `stepP:p2:oi-ratio` | PASS | Four positive losses and generator outer margins justify the factorial estimate below. The additional margin is a generic-helper premise supplied by the original generator domain in both planned applications. j=0 needs only restriction. |
| `osc_ratio_range`, 938 | `stepP:p2:oi-range` | PASS | Valid for every natural m, including 0. Exact q, eta and 16/9 inequalities; d>0 and Phi>=0 explicitly guard division/comparison. |
| `osc_trajectory_hat`, 949 | `stepP:p2:oi-range` | PASS | Same field and same one-loss flow domain O. V has a full loss of gauge room; displacement <=Phi/d<=1/4 puts every trajectory inside original-minus-7/4-loss. |
| `osc_lie_series`, 957 | `stepP:p2:oi-ratio` | PASS | Applies the adjoint estimate to u on O and generator on the original domain, obtaining a summable q-geometric bound on V, HasSum, class and weighted tails. |
| `osc_series_eq`, 970 | `stepP:p2:oi-transfer`, `stepP:p2:oi-range` | PASS | Taylor integral remainder on the actual O-flow tends to zero using the hatted ratio; no smaller-domain flow is substituted. |
| `osc_composition_t`, 978 | `stepP:p2:oi-transfer`, `stepP:p2:oi-ratio` | PASS | t in [-1,1] gives generator bound abs(t)*Phi and positive denominator. Time scaling follows by uniqueness on O, including t=0 and negative times. |
| `osc_composition_integral`, 988 | `stepP:p2:oi-transfer`, `stepP:p2:oi-ratio` | PASS | Joint continuity of v and Dv is an explicit generic-helper input, not an unproved step output assumption. Composition regularity follows from `flow_b`; weighted coefficient integration gives the stated uniform factor. |
| `osc_remainder_bound`, 1010 | `bpP:p2:osc-iter` quantitative clause | PASS | Original premises, same explicit Psi/gp/fp, exact Rsum and signed constant. No positivity of each Mj or nonemptiness of D added. |
| `osc_iter_reality`, 1041 | `bpP:p2:osc-iter` inherited conditional reality | PASS | Guards are exactly reality of H0, the sum g, and f on the original domain. Does not strengthen reality of g to reality of every gj. Same generator and actual map. |
| `osc_remainder_decomposition`, 1075 | `stepP:p2:oi-transfer` (transform identity) | PASS | Exact sign and convex-combination integrand; tail at Psi z. Concrete continuity and integrand bound are conclusions proved by this package. |
| `osc_generator_real`, 1113 | `stepP:p2:oi-transfer` (homological reality) | PASS | Source class/divisor/reality hypotheses imply real frequency at real actions. `homological_param` conclusion 10 supplies generator and zero-mode reality after flattening. No reality conclusion assumed. |

## Constants and domain checks

Write e=exp(1), b=1+m, d=min(rho*sigma,rhop*rhoq), and Phi=delta/(2*pi*alpha). Positive losses give d>0. The exact bracket coefficient at equal four-loss ratios is

```text
c_m = 2*(1/e + m).
```

For h>=1, divide all losses by h and apply the generator bound on its original outer domain. At the i-th bracket, each outer/inner ratio is at most 1/(h+1+i); the minimum product is d/h^2. Multiplication for i=0,...,h-1 gives

```text
norm(ad^h_phi u) <= (c_m*h^2/d)^h * h!/(2h)! * Phi^h*A.
norm(ad^h_phi u)/h! <= (c_m*e^2*Phi/(4*d))^h*A = q^h*A,
q = e*(1+e*m)*Phi/(2*d).
```

The second line uses `(2h)! >= (2h/e)^(2h)`. The h=0 term is the identity and is not obtained by dividing by h. Antisymmetry only changes a sign when the available bracket theorem puts the generator in the opposite slot.

Since e<4 and m>=0, `(1+e*m)/2 <= 2*(1+m)`, so

```text
0 <= q <= eta = 2*e*b*Phi/d <= e/8,
(16/9)*eta <= 2*e/9 < 1,
Phi/d <= 1/(16*b) <= 1/4.
```

The signatures retain the coarser signed eta; the sharper q is internal proof room. No unsupported ratio `2*b*Phi/d` is used.

Let O=original-minus-nu and V=original-minus-2nu. u is controlled on O, not on the original generator domain. For series identification, use middle widths O and losses 3nu/4 in `osc_adjoint_bound`. The generator margin condition holds because O+3nu/4 is inside the original domain. The target is original-minus-7nu/4, which contains the whole trajectory from V. Its minimum product is 9d/16, so the Taylor remainder is bounded by `((16/9)*q)^N*A`. It tends to zero. The generic `taylor_lie` needs only z in gaugeInterior(1/2); V is contained in the existing full-unit gauge interior, hence also in that half interior. O is kept literally fixed throughout.

## Remainder identity and bound

Set H0(z)=h(firstBlock z.2), xi(z)=coeff(oscFunction f)(oscPack z).2 0, T=oscTruncate K f, phi=oscGen K h f. The local homological identity is

```text
{phi,H0} = T-xi,  hence  {H0,phi} = xi-T.
```

Applying `taylor_poschel` on O with f0=g+T gives its integrand

```text
{(1-t)*{H0,phi} + g+T, phi}
  = {g+(1-t)*xi+t*T, phi} = v(t).
fp(z) = integral_0^1 v(t)(flow X_phi O t z) dt + (f-T)(Psi z),  z in V.
```

Both the sign and the point of evaluation of the tail are correct. Equality of functions on the open domain permits replacement inside the bracket by equality of their derivatives; the homological identity is available on that whole domain.

For each gj its signed four ratios give the bound `2*b*Phi/d*R_j*Mj` on O. The convex combination of xi and T has bound delta, because t in [0,1]; no factor two is lost. Thus `B=2*b*Phi/d*(Rsum+delta)`. The integral estimate and the composed Fourier tail give

```text
norm(fp)_V <= (1-eta)^(-1) * [B+exp(-2*pi*K*sigma)*delta]
 = (1-2*e*b*delta/(2*pi*alpha*d))^(-1)
   * [2*b/(2*pi*alpha*d)*(Rsum+delta)+exp(-2*pi*K*sigma)]*delta.
```

This is exactly the unchanged signed remainder bound. Denominator positivity follows before reciprocal comparisons. If D is nonempty, the positive widths let one evaluate each bound at a real base action with p=q=0 to derive Mj>=0, so the generic nonnegative majorants are supplied. If D is empty, all relevant oscillator domains/parameter sets are empty and the conclusions are vacuous, including a bound with a negative written majorant. This handles the potentially negative Mj without changing the original hypothesis list. Zero delta, K=0 and J=0 cause no division by delta or K.

## Definitions, frozen objects and decision B

Definition verdict: **PASS**.

| New object | Classification / check |
|---|---|
| `oscTruncate` | Existing `Weighted.truncate` pulled back by the existing pack/unpack equivalence; only n fast angles are Fourier-expanded. |
| `oscLieRatio` | Explicit numerical function. Uses are guarded by positive d. |
| `oscTheta` | Explicit numerical function with the unchanged signed constant. |
| `OscComposeData` | Expanded every field: hn, hm, twice-loss widths, generator class/bound, nonnegative bound and smallness. These are inputs to a generic composition estimate. At the step application all follow from source data plus the proved generator estimate. No flow, series identity, remainder or reality field. |
| `oscRemIntegrand` | Literal total bracket expression; theorem assertions use it only on open domains where the required holomorphic derivatives exist. |

No new global instance is proposed. The definitions do not exploit divergent sums, total-derivative defaults or the flow fallback to obtain conclusions. Positive strip width and weighted summability are present where analytic reconstruction/convergence is needed.

Frozen-object verdict: **PASS**. Read the frozen complex Hamiltonian field, real field, action neighbourhood, phase, fast/slow blocks and symplectic form. The oscillator phase is exactly `((theta,q),(I,p))`; all new dynamics use `KAM.hamiltonianVectorFieldℂ` itself, and reality uses the actual real inclusions and `Canonical.RealOn`. No parallel Hamiltonian field or replacement norm is introduced. `symplFormC` is the existing complexification of the frozen form. No new frozen theorem/solution predicate is being bridged or sealed by R3.

Decision B verdict: **PASS**. The weighted machinery already allows independent angle and parameter dimensions. On local balls in `oscParams`, that machinery applies with n angle coordinates and n+(m+m) parameters. The oscillator bracket and flow still live on canonical dimension n+m. Consequently N's paired-dimension *weighted composition estimates* are proof templates, while the arbitrary-gauge Taylor/flow theorems instantiate directly at dimension n+m. This distinction is respected. The direct integral transform is sufficient for the full signed step; a new oscillator `liftRemainder` series API is unnecessary for this consumer. No audited N implementation needs editing.

## Packages and consumers

Package verdict: **PASS**; all nine packages have assigned mathematical work and an acyclic order.

| Package / wave | Necessary output and dependency check |
|---|---|
| 13b / R1 | Scalar/additive/series algebra, truncation class and tail. Existing algebra/gen/parametric inputs suffice. |
| 13c / R2 | Four-loss adjoints and numerical ranges from 13b and the actual oscillator bracket. |
| 13d / R3 | Composition data and geometric Lie series from 13b/c. |
| 13e / R4 | Actual-flow trajectory, Taylor identification and time scaling from 13d, existing flow properties and Lie theorem. |
| 13f / R5 | Joint regularity and weighted integral estimate from 13e/parametric integration. Both integrand and phase-derivative continuity are accounted for. |
| 13g / R2 | Homological identity, convex integrand bound/continuity, exact remainder decomposition; independent of the series branch. |
| 13h / R6 | Same-flow integral/tail estimate and exact signed constant from 13f/g/d and the existing core. |
| 13i / R1 | Generator/zero-mode reality, then reality of gp/fp and the same flow. Independent of the series branch. |
| 13j / R7 | Conjunction assembly into unchanged `osc_iter` from existing core/class and 13h/i. |

Estimated new file lengths are 420, 470, 300, 480, 420, 500, 250, 300 and 140, totaling 3,280 lines. No planned file exceeds 1,500; optional splits remain within their owning packages. Keeping `OscillatorStep` below `OscillatorStepComplete`, and making P23-15 import the latter, avoids a facade cycle. No unowned analytic premise was found.

Consumer verdict: **PASS for this revision**. The proposed final result supplies the quantitative contraction, fp class, conditional reality and all preexisting flow/domain/displacement clauses on the same maps/remainders needed by `osc_averaging` and `averaged_remainder`. The finite-iteration schedule and its separate g/tail estimates remain P23-15's work; R3 neither weakens nor claims to prove them. Part 11's `stepP:p11:aa-same` is a separate anisotropic proof-transfer obligation using its own bracket; R3 does not claim its oscillator theorem is already a universally scaled replacement theorem for that different carrier.

## Independent Lean and hygiene checks

All Lean/lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No resource override, root build, clean/update/cache command or state-changing git command was used.

1. **Requested full signatures, run once:** from `/root/code/KAM-inp`,

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean /root/code/KAM-inp-design-p23r3/.drafts/scratch/P23Signatures.lean
   ```

   Exit 0. Exactly 48 warnings, all indicating that the declaration uses `sorry`; 15 belong to the appended suffix. No errors or other warnings. All six R3 axiom prints, including original `osc_iter`, report `[propext, sorryAx, Classical.choice, Quot.sound]`.

2. **Production-import applicability and assembly probe:** `.lake/abi-scratch/P23R3Audit.lean` imports `OscillatorStep`, `Canonical.Lie`, `Canonical.Adjoint` and `Weighted.Parametric`, adds only the exact R3 suffix, then copies the original `osc_iter` type under `audit_osc_iter`. It applies the existing core/class results and proposed bound/reality results without changing the type:

   ```lean
   dsimp only
   have hc := osc_iter_core hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
   have hfcl := osc_fp_class hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
   have hb := osc_remainder_bound hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
   have hr := osc_iter_reality hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
   dsimp only at hc hb hr
   rcases hc with ⟨c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14⟩
   exact ⟨c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,hfcl,hb,c14,hr⟩
   ```

   An initial invocation from the shared inp checkout failed at import because its `OscillatorStep.olean` is absent. Rerunning from `/root/code/KAM-inp-p2313`, where that object exists, exited 0 with only the 15 expected `sorry` warnings. All eight existing `Oscillator*.lean` source files in the audit checkout were compared byte for byte with that proof worktree and match. `audit_osc_iter` reports `[propext, sorryAx, Classical.choice, Quot.sound]`: this establishes exact interface assembly, not a proof of the new estimates.

   The same probe successfully `#check`ed `Real.exp_one_lt_d9`, `MeasureTheory.integral_const_mul`, `MeasureTheory.integral_add`, `HasSum.tsum_eq`, `summable_geometric_of_norm_lt_one`, `KAM.Canonical.factorial_ge`, `taylor_lie`, `taylor_poschel`, `KAM.NormalForm.homological_param`, `KAM.Weighted.holomorphic_parametric_integral`, `uniform_limit_holomorphic` and `OscFlowHyp.gauge_disp`. Their actual types match the uses discussed above: notably the integral theorem needs both joint continuity premises, the Taylor theorem accepts an arbitrary gauge/open set, and the homological theorem has independent parameter dimension.

3. **Source lint:** ran `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` in the audit worktree with a temporary PATH wrapper routing only its `lake` subprocess to the shared `/root/code/KAM-inp` build environment (the audit checkout has no `.lake/build`). The ABI scratch file remains the local absolute file generated by the lint script. Exit 1; literal output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (496 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   This is a failed full lint with successful component checks, not a zero-exit PASS. The generated root was not changed.

4. **Whitespace and scope:** `git diff --check` exited 0 before and after report creation; the report also has no trailing whitespace. Only this report is a persistent audit edit. Existing signature scratch files were reused without alteration; temporary ABI probes/wrapper are removed. There are no new production modules to target with `lake build`; R3.7 explicitly calls for signature elaboration rather than a library build for this Markdown-only design audit.

## Uncertainties, errata and deviations

Implementation effort and default-heartbeat behavior remain estimates. In particular, coefficient/integral interchange, the four-radius induction, local real restriction and negative-time rescaling still need actual proofs. The interfaces and mathematical derivations do not turn these tasks into assumptions.

No new pinned-paper defect was identified or verified in this scope; no fresh PDF check was performed. The inherited blueprint issue is quoted at `p2-averaging.tex:177`: the angular estimate uses `e(S_0-S)` while the stated margin is only `S-sigma<S_0`. That denominator can be nonpositive. R3.4 correctly retains the already identified target-width repair `S_0-S+sigma`, using the landed derivative result; it does not silently rely on the printed denominator. This is a carried blueprint report, not a newly verified CP10 erratum.

The disclosed design deviation is the direct `taylor_poschel` integral identity in place of a new oscillator full transform-series export. It preserves every clause consumed by the signed step and is acceptable. The audit itself changes no source, frozen declaration, manifest, generated root or README.

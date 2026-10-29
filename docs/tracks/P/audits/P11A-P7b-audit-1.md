# P11A-P7b independent package audit 1

Verdict: **PASS WITH NOTES for the P7b slice** at HEAD
`94d6bbcf33c48b029f8fdc513b27c68b37ee4e2a`.
No frozen anchor is delivered or seal-ready in this package. `avg_slow`, its signed wrappers,
nonresonance, (B2), and the canonical averaging/displacement conclusions remain P7c/P7d work.
This verdict concerns the delivered polar normalization and perturbation bounds only.

The report destination follows the user's explicit absolute-path instruction, overriding the
brief's generic instruction to write in the main inp checkout. No production source was edited.

## Authority and comparison

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief, the P7b focus and
P7 round-1 handoff, P11A design (especially rows 171-175 and statements 375-385),
blueprint-P/parts/p11-cp09-preparation.tex:170-184, track P statement, and the signed
`/root/code/KAM-inp/.drafts/design/P11ASignatures.lean:979-1039`.
Inspected all nine `KAM/Planetary/Preparation/SlowAverage*.lean` modules, with relevant
Fast/SlowData/SlowMean/PolarAverage/Cauchy dependencies. The frozen P-G theorem and its
secular-form definition provide surrounding context; this package does not implement that anchor.

`git diff inp...HEAD` is 22 files, 4033 insertions. It includes inherited P5/P7 round-1
modules and receipts outside this audit's explicitly restricted scope. Git reports:

```text
warning: inp...HEAD: multiple merge bases, using ce5bc0c09a78b36777a59cdb8b93c5e544d380e6
```

At comparison time inp was `3fcfb654e1e10a82cc4ab57401156fc446225ce1`.
The merge bases are `ce5bc0c09a78b36777a59cdb8b93c5e544d380e6` and
`798b999a67520b92bb55ebf904f9eee3541a1383`; this report records Git's selected base,
without silently replacing the requested comparison.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` has no diff output.
The pre-existing untracked P7b handoff was left untouched.

## Fidelity and consumer applicability

* `p11_slow_osc` quantifies `c, eps2` before eps and Fast. They depend only on the secular
  data (and ambient dimension); no nu dependence is needed. Its only premise is `hC`;
  Fast carries precisely `P11FastSpec`. There is no assumed oscillation or slow-divisor result.
* `p11_slow_osc_at` is a distinct conditional construction. Its rate premise is discharged
  in the main theorem at SlowAverage.lean:226,239 by `p11eta1_source_rate hC`.
  The live P5 definition is `p11d1 = min (p11s1 * sigma) (rz^2)` (Fast.lean:35),
  and the rate is `eta1 <= c1 eps log(1/eps)^(2 tau+1)` (Fast.lean:406).
  The helper's polar-output/identification premises come from `p11_slow_polar_out`,
  not from an unproved source assertion.
* The actual remainder is `p11Gbar = G - FastMean`, already the blueprint's **eps times gbar**
  (SlowMean.lean:20,125-126). Thus `Z = AR + AB` has exactly the intended normalization,
  with no missing or duplicated eps. `p11_slow_G_polar` uses
  `x_i^2+y_i^2=rho_i/pi`; the secular term is `Omega_i rho_i/(2 pi)`.
* `P11SlowOscSpec` supplies the signed P11SlowSpec identities 1-3 and Z holomorphy/jet
  clauses 4-5 literally, on a larger J box for the identities. Its extra Z sup bound
  `2^(2n)(MF/16+eta1)` is useful stronger output. The Z holomorphic domain is exactly
  `||J-J0||<s1/2`, `||rho||<pi rz^2/16`; the J-jet bound has all multi-indices,
  `alpha! (4/s1)^|alpha|`, and coefficient `c(eps+eta1)` on `D(J0,s1/4)` and
  `||rho-2 pi eps||<pi eps`.
* The construction uses the box `p11SlowAvgBox`, with radii `s1/4` and `pi eps`.
  The signed V uses `s2=min(s1/4,...)`, so V is contained in this box, and Vh is
  contained in V for the consumer's positive radii. Holomorphy, reality, identities,
  and WBound restrict directly. There is no need to assume a slow conclusion.
* The f2 sup bound on sigma/6 is `p11SlowC0 C c1 * eps^(5/2) log(1/eps)^(2 tau+1)`.
  The numeric helper explicitly absorbs the smaller eps^3 terms, using eps <= sqrt eps
  and log(1/eps) >= 1. The weighted conversion uses sigma/6 -> sigma/12 and the factor
  `(cosh(pi sigma/12)/sinh(pi sigma/12))^(n+n)`, exactly coth(pi sigma/12)^(2n).
* Reality uses h real from hC, G real from hF, and the actual real polar integral;
  it does not add a reality hypothesis on Omega. `p11_f1_periodic` derives theta
  periodicity from the fast lattice identity, working Hamiltonian identity, and F
  periodicity. Polar sin/cos periodicity gives zeta periodicity. Hence all 2n f2 angles
  are periodic, as required for the Fourier bound and later averaging.
* The main theorem takes `eps2=min(min(exp(-1)/MF,rz^2/129),eps1)` and
  `c=max 1 (max p11SlowCZ (coth-factor * p11SlowC0))`. All are independent of Fast and eps.
  This discharges `eps MF<=exp(-1)` and `128 eps<rz^2`. Increasing c preserves the
  supplied jet and weighted inequalities on positive eps. A scratch consumer probe
  checks the box inclusion and this constant enlargement.

## Coverage by graph node

| Node | Delivered result | Verdict | Scope |
|---|---|---|---|
| stepP:p11:as-osc | p11_slow_polar, p11_slow_key, p11_slow_osc_pointwise, p11_slow_Z_jets, p11_slow_f2_wbound, p11_slow_osc | PASS | Polar normalization, full jet estimate, oscillation and weighted f2 bound. |
| bpP:p11:avg-slow (a) | P11SlowOscSpec / p11_slow_osc | PASS | Exactly the assigned clause, with extra Z bound and larger action box. |
| stepP:p11:as-nr | none assigned | OUT OF SCOPE | P7c. |
| stepP:p11:as-b2 | none assigned | OUT OF SCOPE | P7c. |
| stepP:p11:as-concl | f2 weighted preparation only | OUT OF SCOPE for full node | Full g2/f3/mean/displacement result is not delivered here. |
| bpP:p11:avg-slow, signed wrappers | none | NOT SEALED | P7d; the assigned split expressly excludes assembly. |

All 68 declarations below are unsigned. None uses the exact signed name `avg_slow` or
`P11SlowSpec`, and no provider is supplied. Therefore frozen/provider type-equality and
seal-body probes are **not applicable**, rather than passed by a signature-only proxy.

## Per-declaration review

Names are in `KAM.Planetary`; file locators are relative to
`KAM/Planetary/Preparation/`. Every declaration was checked for its role, premises,
carrier, constants and conclusion. Generic conditional analysis helpers remain distinct
from the existential source output and are applied with proved premises.

| Node / role | Declaration (file:line) | Verdict | Reason / note |
|---|---|---|---|
| as-osc / def | `P11SlowOscSpec` (SlowAverage.lean:41) | PASS | Packages as-osc outputs; smallness and constants discharged from secular data. |
| as-osc / theorem | `p11_slow_osc_at` (SlowAverage.lean:80) | PASS | Packages as-osc outputs; smallness and constants discharged from secular data. |
| as-osc / theorem | `p11_slow_osc` (SlowAverage.lean:220) | PASS | Packages as-osc outputs; smallness and constants discharged from secular data. |
| as-osc / def | `p11RePos` (SlowAverageDom.lean:28) | PASS | Principal sqrt on Re rho > 0; polar domain, reality or lattice periodicity. |
| as-osc / theorem | `p11RePos_isOpen` (SlowAverageDom.lean:30) | PASS | Principal sqrt on Re rho > 0; polar domain, reality or lattice periodicity. |
| as-osc / theorem | `p11_sqrt_differentiableAt` (SlowAverageDom.lean:37) | PASS | Principal sqrt on Re rho > 0; polar domain, reality or lattice periodicity. |
| as-osc / theorem | `p11_polarC_differentiableOn` (SlowAverageDom.lean:42) | PASS | Principal sqrt on Re rho > 0; polar domain, reality or lattice periodicity. |
| as-osc / theorem | `p11_polarC_mem` (SlowAverageDom.lean:66) | PASS | Principal sqrt on Re rho > 0; polar domain, reality or lattice periodicity. |
| as-osc / theorem | `p11_polarC_real` (SlowAverageDom.lean:102) | PASS | Principal sqrt on Re rho > 0; polar domain, reality or lattice periodicity. |
| as-osc / theorem | `p11_natAdd_ne_castAdd` (SlowAverageDom.lean:136) | PASS | Principal sqrt on Re rho > 0; polar domain, reality or lattice periodicity. |
| as-osc / theorem | `p11_addNat_ne_castAdd` (SlowAverageDom.lean:140) | PASS | Principal sqrt on Re rho > 0; polar domain, reality or lattice periodicity. |
| as-osc / theorem | `p11_append_single` (SlowAverageDom.lean:145) | PASS | Principal sqrt on Re rho > 0; polar domain, reality or lattice periodicity. |
| as-osc / theorem | `p11_f1_periodic` (SlowAverageDom.lean:155) | PASS | Principal sqrt on Re rho > 0; polar domain, reality or lattice periodicity. |
| as-osc / def | `p11SlowAvgBox` (SlowAverageF2.lean:31) | PASS | Explicit slow box/data or oscillation-to-sup estimate; exponent 5/2 and log exponent 2 tau+1. |
| as-osc / def | `P11SlowPolarOut` (SlowAverageF2.lean:36) | PASS | Explicit slow box/data or oscillation-to-sup estimate; exponent 5/2 and log exponent 2 tau+1. |
| as-osc / theorem | `p11_slow_polar_out` (SlowAverageF2.lean:47) | PASS | Explicit slow box/data or oscillation-to-sup estimate; exponent 5/2 and log exponent 2 tau+1. |
| as-osc / def | `p11SlowZ` (SlowAverageF2.lean:54) | PASS | Explicit slow box/data or oscillation-to-sup estimate; exponent 5/2 and log exponent 2 tau+1. |
| as-osc / def | `p11SlowH0` (SlowAverageF2.lean:58) | PASS | Explicit slow box/data or oscillation-to-sup estimate; exponent 5/2 and log exponent 2 tau+1. |
| as-osc / def | `p11SlowF2` (SlowAverageF2.lean:63) | PASS | Explicit slow box/data or oscillation-to-sup estimate; exponent 5/2 and log exponent 2 tau+1. |
| as-osc / theorem | `p11SlowAvgBox_mem` (SlowAverageF2.lean:69) | PASS | Explicit slow box/data or oscillation-to-sup estimate; exponent 5/2 and log exponent 2 tau+1. |
| as-osc / def | `p11SlowC0` (SlowAverageF2.lean:100) | PASS | Explicit slow box/data or oscillation-to-sup estimate; exponent 5/2 and log exponent 2 tau+1. |
| as-osc / theorem | `p11_slow_f2_numeric` (SlowAverageF2.lean:106) | PASS | Explicit slow box/data or oscillation-to-sup estimate; exponent 5/2 and log exponent 2 tau+1. |
| as-osc / theorem | `p11_slow_f2_sup` (SlowAverageF2.lean:136) | PASS | Explicit slow box/data or oscillation-to-sup estimate; exponent 5/2 and log exponent 2 tau+1. |
| as-osc / def | `p11SlowCZ` (SlowAverageJet.lean:29) | PASS | Rho Cauchy bound and sharp J-multi-index estimate, radius s1/4. |
| as-osc / theorem | `p11SlowZ_append` (SlowAverageJet.lean:33) | PASS | Rho Cauchy bound and sharp J-multi-index estimate, radius s1/4. |
| as-osc / theorem | `p11_diffAt_rho` (SlowAverageJet.lean:39) | PASS | Rho Cauchy bound and sharp J-multi-index estimate, radius s1/4. |
| as-osc / theorem | `p11_slow_rho_bound` (SlowAverageJet.lean:48) | PASS | Rho Cauchy bound and sharp J-multi-index estimate, radius s1/4. |
| as-osc / theorem | `p11_slow_Z_jets` (SlowAverageJet.lean:138) | PASS | Rho Cauchy bound and sharp J-multi-index estimate, radius s1/4. |
| as-osc / theorem | `p11_sqrt_ofReal` (SlowAverageKey.lean:28) | PASS | Polar integral linearity/normalization and real-data average. |
| as-osc / theorem | `p11_polarPt_real` (SlowAverageKey.lean:36) | PASS | Polar integral linearity/normalization and real-data average. |
| as-osc / theorem | `p11_slow_avg_real` (SlowAverageKey.lean:53) | PASS | Polar integral linearity/normalization and real-data average. |
| as-osc / theorem | `p11PolarAverage_add_of` (SlowAverageKey.lean:83) | PASS | Polar integral linearity/normalization and real-data average. |
| as-osc / theorem | `p11PolarAverage_const_mul` (SlowAverageKey.lean:91) | PASS | Polar integral linearity/normalization and real-data average. |
| as-osc / theorem | `p11PolarAverage_sec` (SlowAverageKey.lean:98) | PASS | Polar integral linearity/normalization and real-data average. |
| as-osc / theorem | `p11_slow_key` (SlowAverageKey.lean:146) | PASS | Polar integral linearity/normalization and real-data average. |
| as-osc / def | `p11SlowJ` (SlowAverageOsc.lean:30) | PASS | Literal polar decomposition or order-one Schwarz oscillation estimate. |
| as-osc / def | `p11SlowR` (SlowAverageOsc.lean:33) | PASS | Literal polar decomposition or order-one Schwarz oscillation estimate. |
| as-osc / def | `p11PolPt` (SlowAverageOsc.lean:36) | PASS | Literal polar decomposition or order-one Schwarz oscillation estimate. |
| as-osc / def | `p11SlowSec` (SlowAverageOsc.lean:40) | PASS | Literal polar decomposition or order-one Schwarz oscillation estimate. |
| as-osc / theorem | `p11PolPt_fst` (SlowAverageOsc.lean:45) | PASS | Literal polar decomposition or order-one Schwarz oscillation estimate. |
| as-osc / theorem | `p11PolPt_snd` (SlowAverageOsc.lean:50) | PASS | Literal polar decomposition or order-one Schwarz oscillation estimate. |
| as-osc / theorem | `p11PolPt_norm_le` (SlowAverageOsc.lean:56) | PASS | Literal polar decomposition or order-one Schwarz oscillation estimate. |
| as-osc / theorem | `p11_slow_G_polar` (SlowAverageOsc.lean:93) | PASS | Literal polar decomposition or order-one Schwarz oscillation estimate. |
| as-osc / theorem | `p11_gbar_osc` (SlowAverageOsc.lean:124) | PASS | Literal polar decomposition or order-one Schwarz oscillation estimate. |
| as-osc / theorem | `p11_gbar_avg_osc` (SlowAverageOsc.lean:158) | PASS | Literal polar decomposition or order-one Schwarz oscillation estimate. |
| as-osc / theorem | `p11_slow_osc_pointwise` (SlowAverageOsc.lean:213) | PASS | Literal polar decomposition or order-one Schwarz oscillation estimate. |
| as-osc / theorem | `p11_slow_box_pt` (SlowAverageReal.lean:28) | PASS | Box membership or reality via the actual polar average of G. |
| as-osc / theorem | `p11_slow_secZ_eq` (SlowAverageReal.lean:43) | PASS | Box membership or reality via the actual polar average of G. |
| as-osc / theorem | `p11SlowJ_real` (SlowAverageReal.lean:54) | PASS | Box membership or reality via the actual polar average of G. |
| as-osc / theorem | `p11SlowR_real` (SlowAverageReal.lean:59) | PASS | Box membership or reality via the actual polar average of G. |
| as-osc / theorem | `p11_slow_PA_real` (SlowAverageReal.lean:64) | PASS | Box membership or reality via the actual polar average of G. |
| as-osc / theorem | `p11_slow_h0_real` (SlowAverageReal.lean:87) | PASS | Box membership or reality via the actual polar average of G. |
| as-osc / theorem | `p11_slow_f2_real` (SlowAverageReal.lean:110) | PASS | Box membership or reality via the actual polar average of G. |
| as-osc / theorem | `p11_slow_pt` (SlowAverageW.lean:26) | PASS | Joint holomorphy, full angle periodicity or sup-to-weighted conversion. |
| as-osc / theorem | `p11SlowJ_differentiable` (SlowAverageW.lean:47) | PASS | Joint holomorphy, full angle periodicity or sup-to-weighted conversion. |
| as-osc / theorem | `p11SlowR_differentiable` (SlowAverageW.lean:50) | PASS | Joint holomorphy, full angle periodicity or sup-to-weighted conversion. |
| as-osc / theorem | `p11SlowSec_differentiableOn` (SlowAverageW.lean:54) | PASS | Joint holomorphy, full angle periodicity or sup-to-weighted conversion. |
| as-osc / theorem | `p11_slow_f2_differentiableOn` (SlowAverageW.lean:82) | PASS | Joint holomorphy, full angle periodicity or sup-to-weighted conversion. |
| as-osc / theorem | `p11PolarC_shift_theta` (SlowAverageW.lean:118) | PASS | Joint holomorphy, full angle periodicity or sup-to-weighted conversion. |
| as-osc / theorem | `p11PolarC_shift_zeta` (SlowAverageW.lean:128) | PASS | Joint holomorphy, full angle periodicity or sup-to-weighted conversion. |
| as-osc / theorem | `p11_slow_f2_periodic` (SlowAverageW.lean:157) | PASS | Joint holomorphy, full angle periodicity or sup-to-weighted conversion. |
| as-osc / theorem | `p11_slow_f2_wbound` (SlowAverageW.lean:184) | PASS | Joint holomorphy, full angle periodicity or sup-to-weighted conversion. |
| as-osc / theorem | `p11eta1_pos` (SlowAverageZ.lean:31) | PASS | Polar averages from quartic jets and fast remainder; analytic Cauchy/jet helpers. |
| as-osc / theorem | `p11_gbar_data` (SlowAverageZ.lean:42) | PASS | Polar averages from quartic jets and fast remainder; analytic Cauchy/jet helpers. |
| as-osc / theorem | `p11_slow_polar` (SlowAverageZ.lean:62) | PASS | Polar averages from quartic jets and fast remainder; analytic Cauchy/jet helpers. |
| as-osc / theorem | `p11_rhoDeriv_differentiableOn` (SlowAverageZ.lean:121) | PASS | Polar averages from quartic jets and fast remainder; analytic Cauchy/jet helpers. |
| as-osc / theorem | `p11_rho_cauchy` (SlowAverageZ.lean:143) | PASS | Polar averages from quartic jets and fast remainder; analytic Cauchy/jet helpers. |
| as-osc / theorem | `p11_partial_rho_jet` (SlowAverageZ.lean:156) | PASS | Polar averages from quartic jets and fast remainder; analytic Cauchy/jet helpers. |

## Definition classification

There are 13 new definitions, no new structures or abbreviations.

| Definition | Classification |
|---|---|
| p11SlowJ, p11SlowR | Literal first/second action-block projections on the entire Pi carrier. |
| p11PolPt | Literal oscillator pair projected from the existing polar chart; no fallback. |
| p11SlowSec | Literal `C(J)+sum Omega(J) rho/(2 pi)` on the whole carrier. |
| p11RePos | Open right-half-plane condition for all oscillator actions. |
| p11SlowAvgBox | Literal product polydisc centered at `(J0,2 pi eps)`. Total set definition; no guarded junk. |
| P11SlowPolarOut | Output proposition collecting proved holomorphy, size and integral identifications. It is constructed existentially before consumption. |
| p11SlowZ | Sum of the two actual polar-average extensions, via the block projections. |
| p11SlowH0 | Literal integrable Hamiltonian `h+eps(sec+Z)`. |
| p11SlowF2 | Literal remaining perturbation `eps(G o Pi-sec-Z)+f1 o PolarC`. |
| p11SlowC0 | Explicit real estimate constant; positivity follows under standing data. |
| p11SlowCZ | Explicit real derivative constant depending only on C and n. |
| P11SlowOscSpec | Output conjunction; no extra axiom, hidden instance or assumed hard step. |

All are under `@[expose] public noncomputable section`. Globally total sqrt/integral/
fderiv operations are only used analytically with the proved domain, differentiability
and integrability conditions. The holomorphic AR/AB extensions come from polar_avg;
no theorem relies on their unspecified behavior outside the stated domain.

## Validation receipts

All audit Lean commands used `LEAN_NUM_THREADS=1` and `nice -n 5`, sequentially.
The targeted build command was:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap7b KAM.Planetary.Preparation.SlowAverage
```

Exit 0; output included:

```text
[inp-gate] slot 1 acquired 00:29:27 for KAM.Planetary.Preparation.SlowAverage
Build completed successfully (9350 jobs).
```

Build replay emitted existing unused-variable, deprecated-name, unused-simp and style
warnings in dependencies; no compilation failure or resource override.
The main module imports all eight other audited modules transitively.

Axiom probe (55 public theorems, not just the main export):

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P7bAxioms.lean
```

Exit 0. Exact output:

```text
'KAM.Planetary.p11_slow_osc_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_osc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11RePos_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_sqrt_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_polarC_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_polarC_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_polarC_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_natAdd_ne_castAdd' depends on axioms: [propext, Quot.sound]
'KAM.Planetary.p11_addNat_ne_castAdd' depends on axioms: [propext, Quot.sound]
'KAM.Planetary.p11_append_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_f1_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_polar_out' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowAvgBox_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_f2_numeric' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_f2_sup' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowZ_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_diffAt_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_rho_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_Z_jets' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_sqrt_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_polarPt_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_avg_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarAverage_add_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarAverage_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarAverage_sec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_key' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolPt_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolPt_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolPt_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_G_polar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_gbar_osc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_gbar_avg_osc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_osc_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_box_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_secZ_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowJ_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowR_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_PA_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_h0_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_f2_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowJ_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowR_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowSec_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_f2_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarC_shift_theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarC_shift_zeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_f2_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_f2_wbound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11eta1_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_gbar_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_polar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_rhoDeriv_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_rho_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_partial_rho_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, one invocation of all nine modules:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.SlowAverage KAM.Planetary.Preparation.SlowAverageDom KAM.Planetary.Preparation.SlowAverageF2 KAM.Planetary.Preparation.SlowAverageJet KAM.Planetary.Preparation.SlowAverageKey KAM.Planetary.Preparation.SlowAverageOsc KAM.Planetary.Preparation.SlowAverageReal KAM.Planetary.Preparation.SlowAverageW KAM.Planetary.Preparation.SlowAverageZ
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.Preparation.SlowAverageZ
replaying KAM.Planetary.Preparation.SlowAverageW
replaying KAM.Planetary.Preparation.SlowAverageReal
replaying KAM.Planetary.Preparation.SlowAverageOsc
replaying KAM.Planetary.Preparation.SlowAverageKey
replaying KAM.Planetary.Preparation.SlowAverageJet
replaying KAM.Planetary.Preparation.SlowAverageF2
replaying KAM.Planetary.Preparation.SlowAverageDom
replaying KAM.Planetary.Preparation.SlowAverage
```

Static checks:

* 55 theorems and 13 definitions (68 declarations), all in `KAM.Planetary`.
* File lengths, including comments: SlowAverage 248; Dom 202; F2 195; Jet 203;
  Key 194; Osc 310; Real 160; W 213; Z 171. All below 1500.
* Every scoped line is <=100 Unicode characters. All nine files have copyright,
  `module`, public imports, module docstring, and the public expose section.
* No scoped `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`,
  `set_option`, resource-limit override, new global instance or root shadow.
* A repository declaration-name scan found no reused public short names for any of
  the 68 exports. The rename to `p11SlowAvgBox` is present throughout the package.
* Recursive KAM-import closure of SlowAverage: 304 source modules, zero provider
  imports, zero frozen-theorem imports. Thus there is no DRAFT_SORRY theorem import
  and no imported frozen-theorem manifest state to excuse.

## Notes, deviations and suspected errata

No mathematical defect found in the assigned slice. No new suspected pinned-source
erratum was identified; the available blueprint and signed artifact suffice for this
scope, and this is not an independent re-audit of the full CP09 paper or the P5 proof.

1. The design node table at lines 171-175 maps all slow-stage nodes to the facade
   `Preparation/Slow`. The later explicit P7b/P7c/P7d split controls this audit.
   The facade has not yet imported the P7b main module. Import the delivered module
   directly until P7d integrates it; do not mark the full node or anchor complete.
2. SlowAverage.lean:78 and :216-219 mention graph steps `as-osc` and `as-concl`.
   The latter's literal design conclusion (design:384; blueprint:184) is
   “g_2 := g, f_3 := f_*; ... f^_0 = int f_2 = int f_1 ...” together with g2 and
   displacement estimates. P7b supplies f2 preparation only. This is a documentation/
   coverage-label caveat, not proof of that entire node.
3. SlowAverage.lean:16 says `Ẑ = A(R₄ + ε ḡ)` while several local comments call the
   already-scaled `p11Gbar` simply gbar. The actual definition is
   `p11Gbar = Fast.G - p11FastMean C.F`, explicitly documented as `ε ḡ` in
   SlowMean.lean:124. With that notation the source and implementation agree.
4. The source's coordinate mean-value oscillation bound is replaced by order-one
   radial Schwarz and a polar-average norm bound. This proves the same estimate,
   with explicit data-only constants. The AB Cauchy radius is pi rz^2/64 rather than
   the blueprint's pi rz^2/32; the larger resulting constant is absorbed in
   p11SlowCZ and leaves the signed derivative bound unchanged.
5. The larger J-box and extra Z sup bound are intentional stronger outputs, not
   changes to a signed declaration. Constant enlargement must be accompanied by
   the usual positive-eps/eta/log facts; these follow from the chosen threshold.
6. The handoff's default-heartbeat design signal was handled by splitting the
   real numerical estimate from the analytic sup proof. No override is present.

## Lint and final disposition

```sh
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely for the brief's permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1125 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The generated root was not changed. Module-format validation, frozen-anchor integrity,
and elaborated ABI hashes all passed. `git diff --check` also exited 0 with no output.

Consumer scratch probe:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P7bConsumer.lean
```

Final exit 0, no output. It independently proved the signed V-to-slow-average-box
inclusion and constant enlargement for P11SlowOscSpec, assuming the explicit numerical
facts `c<=d`, `0<=s1`, `0<=eps+eta1`, and nonnegative common epsilon/log factor.
The first draft of this audit-only probe omitted `0<=s1` and exited 1 at its positivity
tactic; adding that standing-data consequence made it pass. No production proof changed.

Audit-created scratch probes and logs were removed after transferring their receipts
here. Final working-tree status contains only this new report and the pre-existing
untracked P7b handoff. No state-changing Git command was used.

**Disposition:** P7b's assigned polar/oscillation slice passes, with the permitted stale-root
lint exception and scope/documentation notes above. No signed anchor is claimed closed.

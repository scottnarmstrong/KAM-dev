# Independent P11A-P5 package audit 1

**Overall: FAIL for complete blueprint/consumer delivery (F1); PASS WITH NOTES for the authorized signed parametric core.**
The five modules compile and kernel-replay, all 38 public theorems have only the permitted axioms,
and their signed declarations match. F1 is an upstream quantitative signature/interface defect,
not an unsound Lean proof: the signed squared minimum makes the advertised bound on `p11eta1`
false, and the slow-stage consumer uses that bound. `p11d1_le` suffices for the signed core,
but does not repair this consumer gap.

## Scope and authority

Audit snapshot: HEAD `c51ac53035e98f83b021bee42e37eb934a3af7d7`, branch `inp-p11ap5`;
comparison `inp` = `a2c95a9339a7bf00c88b45ff27058eaa6f5b3be9`.
Read AGENTS.md, PLAN.md, DECISIONS.md, the supplied package-audit brief, handoff including
21:50/22:46 rulings and AUDIT FOCUS, P11A design/node registry, design audits 1–3,
track P statement, relevant blueprint and oscillator API, P-FIXED frozen anchor and its
phase/set definitions. The explicit user destination overrides the generic brief's
main-worktree destination. Only this report persists as an audit edit.

Audited exactly `KAM/Planetary/Preparation/{Fast,FastBridge,FastDivisor,FastParams,LogBounds}.lean`.
The live amended signature file has SHA-256
`c4e40a3993bdc98e55db2c9221e370438d71e52a405ab8e5eb3b23a0218992fe`.
No provider or frozen theorem is delivered by this package. Frozen P-FIXED
`KAM.Planetary.fixedSunPlanetaryKAM` remains outside this parametric-core audit and is not
seal-ready by this receipt. The absence of signed `avg_fast` and `p11FastData` is expressly
allowed by the ruling and is **not** a finding.

| Target | Verdict | Scope |
|---|---|---|
| Signed definitions, `e4`, `avg_fast_of_spec` | PASS WITH NOTES | Correct authorized parametric core; N1 integration dependency, F1 quantitative limitation. |
| Full `bpP:p11:avg-fast` consumer interface | FAIL | F1: advertised eta asymptotic is false for the signed definition; no stronger exported bound. |
| P-FIXED frozen anchor | Not assessed for sealing | No provider/type/seal-body probe applies to these five infrastructure modules. |

## F1 — Signed `d1` is sufficient for the core but breaks the advertised eta rate

Exact locators: `Fast.lean:35–37`, `Fast.lean:159–176`, `Fast.lean:345–375`;
signatures `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean:781–783`;
blueprint `blueprint-P/parts/p11-cp09-preparation.tex:100,108,111,181–184`;
design registry `docs/tracks/P/design/P11A-LEAN-DESIGN.md:346,354,379`.

Signed text, copied verbatim:

```lean
def p11d1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) := min (p11s1 C eps*C.sigma) C.rz^2
```

An independent `rfl` probe confirms this is `(min (s1*sigma) rz)^2`. The blueprint's
parameter equation instead says `d_1 = min{s_1 sigma_F, r_z^2}`. On the proved carrier,
`0 < s1*sigma <= 1` and `rz > 0`, so `p11d1_le` correctly proves

```
0 < d_signed <= d_source := min (s1*sigma) (rz*rz).
```

Both uses in `fast_spec_at` are sound: S1 with smaller `d_signed` implies oscillator
smallness with `d_source`, and division by smaller positive `d_signed` gives a larger
permitted G-error bound. The proof actually obtains the stronger source-denominator
bound locally from `osc_averaging` before weakening it to the signed `p11eta1`.

However, blueprint line 108 says:
`eta_1(epsilon) <= c epsilon (log(1/epsilon))^(2 tau_0+1)`.
For every fixed positive admissible set of constants and sufficiently small epsilon,
write `K = K1`, so the active branches are

```
s1 = gamma/(4 L K^(tau+1)),
d_signed = (s1*sigma)^2,
alpha1*d_signed = gamma^3*sigma^2/(32*L^2) * K^(-(3*tau+2)),
p11eta1 = 6400*(1+n)*L^2*MF^2/(pi*gamma^3*sigma^2)
           * epsilon * K^(3*tau+2).
```

Since `K ~ (6/(pi*sigma))*log(1/epsilon)` and `tau > 0` (proved in `fast_consts`),
the ratio to `epsilon*log(1/epsilon)^(2*tau+1)` grows as a positive multiple of
`log(1/epsilon)^(tau+1)` and is unbounded. Thus this is a false scalar asymptotic
for the signed definition, not merely an omitted tactic proof or a threshold issue.
The source formula with `d_source` has the correct exponent `2*tau+1`.

This matters to an actual consumer: `stepP:p11:as-osc` at blueprint line 181 uses
`epsilon^2 + eta1*sqrt(epsilon)` to obtain the oscillation of order
`epsilon^(5/2)*log(1/epsilon)^(2*tau+1)`. The current signed `P11SlowSpec`
at signatures lines 986–987 fixes exactly that E exponent. A bound with exponent
`3*tau+2` cannot be substituted by shrinking epsilon while keeping the same epsilon
power and an epsilon-independent constant. The signed `P11FastSpec` exports only
the weakened bound by `p11eta1`; these modules export neither the source-denominator
G estimate nor the advertised smaller logarithmic bound.

Required disposition: version/correct the signed minimum, or export an additional
stronger bound on the same constructed/selected fast data and connect it to the
slow-stage consumer. The existing local stronger estimate makes the latter plausible;
it is not currently a public consumer contract. Do not silently change the signed
body, change logarithmic exponents, or classify the full node as complete from this
receipt. This finding refines handoff E2 and was not detected by the earlier
signature-design PASS receipts. It does not refute CP09 or the source's correctly
parenthesized parameter equation, nor does it refute existence of a better fast map.

## N1 — Reality amendment is exactly the needed source premise

`Fast.lean:180–182` defines `P11SecularHReal` as vanishing imaginary part of `C.h`
on real inclusions in the complex ball of radius `2*rC`. The amended signature's
second conjunct (lines 688–690) gives the same vanishing condition with
`norm(J-J0) < 2*rC`. A fresh probe proves the implication by `Metric.mem_ball`,
`dist_eq_norm`, linearity of real inclusion, and `KAM.norm_realInclusion`.
Thus it is exactly the added clause, with no conclusion-shaped assumption.

The checked-out dependency `Holomorphic.lean:79–80` still has only the real-part
formula; it predates the amendment. Consequently the current `hh` is explicit and
cannot simply be projected from this checkout's `hC`. This is the acknowledged
P2f integration dependency, not an additional P5 defect under the ruling. The
comments claiming the specification omits reality will need updating when that
amendment lands. No P2f delivery or physical wrapper is certified here.

## Node and public declaration ledger

All names below are in `KAM.Planetary`; module locators are under the audited directory.
Unsigned helpers state source assumptions, typing data, elementary dictionary facts or
explicit numerical conditions. None assumes the existence or bounds of the desired
averaging output. The full-node FAIL in F1 is separate from the valid individual Lean results.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| `sec-C#data` | `p11K1` (Fast:30) | PASS | Signed logarithmic cutoff; literal body. |
| `sec-C#data` | `p11Alpha1` (Fast:32) | PASS | Signed half-Diophantine divisor; literal body. |
| `sec-C#data` | `p11s1` (Fast:33) | PASS | Signed minimum radius; literal body. |
| `sec-C#data` | `p11d1` (Fast:35) | PASS WITH NOTES | Exact signed body and positivity/comparison proved; quantitative signature defect F1 below. |
| `sec-C#data` | `p11eta1` (Fast:36) | PASS WITH NOTES | Exact signed body; F1 blocks the advertised logarithmic estimate. |
| `sec-C#data` | `P11FastData` (Fast:38) | PASS | Signed data-only structure, no assumed conclusions. |
| `sec-C#data` | `P11FastSpec` (Fast:43) | PASS | Exact signed conjunction, including weighted spectator remainder and displacements. |
| `support` | `fast_consts` (Fast:83) | PASS | Extracts positivity/size from source specification; tau positive from n >= 2. |
| `support` | `p11K1_ge_one` (Fast:93) | PASS | Cutoff >= 1 with explicit positive-epsilon and epsilon MF <= exp(-1) guards. |
| `support` | `exp_p11K1` (Fast:103) | PASS | Exact exponential identity gives cubic final remainder. |
| `support` | `p11s1_pos` (Fast:114) | PASS | Positive radius on the actual small-epsilon carrier. |
| `support` | `p11s1_le` (Fast:123) | PASS | Global minimum comparison, no positivity needed. |
| `support` | `p11_budget` (Fast:125) | PASS | Oscillator budget >= 6 on the small-epsilon carrier. |
| `support` | `p11_sK` (Fast:133) | PASS | Finite-cutoff frequency variation bound with exact 1/4 factor. |
| `support` | `p11_alpha_le` (Fast:149) | PASS | Positive alpha and comparison with 3/4 gamma K^(-tau). |
| `support` | `p11d1_le` (Fast:159) | PASS | 0 < signed d <= min(s1 sigma, rz*rz); both uses have correct direction. |
| `support` | `P11SecularHReal` (Fast:180) | PASS WITH NOTES | Precisely amended signed reality clause after norm/isometry conversion; N1. |
| `support` | `zero_angle_mem` (Fast:185) | PASS | Domain membership after zeroing only fast angles; positive strip guard. |
| `af-concl` | `fast_spec_at` (Fast:204) | PASS | Actual oscillator averaging and all 15 output clauses; no assumed normal form. |
| `avg-fast (parametric core)` | `avg_fast_of_spec` (Fast:400) | PASS WITH NOTES | Authorized parametric version of signed avg_fast, exact conclusion; F1 affects consumer completeness. |
| `support` | `oscDom_eq_workingDom` (FastBridge:30) | PASS | Equality of whole carriers, with x=q, y=p and frozen phase order. |
| `support` | `p11Flat` (FastBridge:55) | PASS | Literal flat spectator parameter (J,y,x), no fallback. |
| `support` | `firstBlock_p11Flat` (FastBridge:57) | PASS | First block is J. |
| `support` | `p_p11Flat` (FastBridge:60) | PASS | Oscillator momentum block is y. |
| `support` | `q_p11Flat` (FastBridge:64) | PASS | Oscillator position block is x. |
| `support` | `p11_oscUnpack_flat` (FastBridge:68) | PASS | Unpacking yields (append theta x, append J y). |
| `support` | `oscPack_eq` (FastBridge:72) | PASS | Whole-carrier packing dictionary. |
| `support` | `realInclusion₂_append` (FastBridge:76) | PASS | Coordinatewise real inclusion respects concatenation. |
| `support` | `oscFunction_flat` (FastBridge:84) | PASS | Exact oscillator-function identity. |
| `support` | `coeff_zero_flat` (FastBridge:88) | PASS | Zero Fourier coefficient is epsilon times the actual torus average. |
| `support` | `spectator_coeff` (FastBridge:97) | PASS | Every Fourier mode agrees with the frozen-spectator function. |
| `support` | `spectator_wsummable` (FastBridge:105) | PASS | Weighted summability equivalence, not just a pointwise bound. |
| `support` | `spectator_wsum_eq` (FastBridge:111) | PASS | Exact weighted sum equality for every radius. |
| `support` | `oscBound_of_sup` (FastBridge:118) | PASS | Sup-to-weighted bound with coth(pi sigma-prime)^n, explicit strip margin. |
| `support` | `p11WorkingDom_mono` (FastBridge:137) | PASS | Coordinatewise monotonicity of all working radii. |
| `support` | `actionNbhd_sub_ball` (FastBridge:142) | PASS | Singleton action neighbourhood embeds in the required complex ball. |
| `support` | `p11_coth_pos` (FastBridge:151) | PASS | Positive coth for positive argument. |
| `af-apply` | `oscHyp_fast` (FastBridge:159) | PASS | Builds all OscHyp fields from literal source/typing and numerical premises. |
| `support` | `differentiableAt_append` (FastDivisor:30) | PASS | Generic concatenation differentiability on Pi carriers. |
| `support` | `omega_lipschitz` (FastDivisor:42) | PASS | Complex convex-ball mean value bound from first derivative of joint frequency. |
| `support` | `p11fd_norm_dotC_le` (FastDivisor:68) | PASS | l1 Fourier mode size times Pi max norm; no norm substitution. |
| `support` | `re_dotC_omega` (FastDivisor:78) | PASS | Restricts joint Diophantine condition to (k,0); real part gives norm lower bound. |
| `af-o1` | `fast_divisor` (FastDivisor:109) | PASS | Actual DivisorBound for every nonzero finite-cutoff mode; proof contains 3/4 bound. |
| `support` | `fast_rhs_lower` (FastParams:25) | PASS | Conservative polynomial lower bound for the squared signed minimum. |
| `af-o2` | `fast_small_eventually` (FastParams:66) | PASS | Uniform positive threshold, S1 and epsilon M <= exp(-1), via e4. |
| `e4` | `log_inv_ge_one` (LogBounds:22) | PASS | First clause of e4 node with exact (0,exp(-1)] guards. |
| `e4` | `e4` (LogBounds:30) | PASS | Exact signed real-exponent limit for a>0, b>=0, including b=0. |

The registry maps `sec-C#data`, `avg-fast`, `af-apply`, `af-o1`, `af-o2`, `af-concl`
and `e4` to this slice. The analytic averaging application, divisor estimate, eventual
smallness and signed output conjunction are all established. `af-o1` contains the
full intermediate 3/4 lower bound in its proof, although its export returns the
needed `DivisorBound`. `af-o2` supplies a uniform positive threshold and the budget
follows from `p11_budget`; the unnecessary blueprint phrase “largest value” is not
implemented as an extremal-threshold claim. The remaining completeness failure is F1.

## Definition classification and proof review

- `p11K1`, `p11Alpha1`, `p11s1`, `p11d1`, `p11eta1`: total explicit real expressions,
  identical to signed bodies; no choice or junk fallback. Division, log and rpow are
  totalized by the library outside admissible parameters, and every theorem using
  their intended analytic meaning supplies/proves positivity. `p11d1` has F1's
  source/signature discrepancy; no silent mathematical normalization was performed.
- `P11FastData`: data-only structure of map, G and remainder, with `Inhabited`;
  no unproved property is hidden in a field. The default instance is not used to
  discharge an existence or specification proof.
- `P11FastSpec`: exact signed predicate of holomorphy, injectivity, reality,
  symplecticity, lattice equivariance, mapping, Hamiltonian identity, sup/weighted
  remainder, G correction and displacement. It is an output, never a premise of
  the core existence construction.
- `p11Flat`: literal concatenation `(J,y,x)` on the entire carrier; exact inverse
  dictionary and all Fourier coefficients checked, without changing norms or order.
- `P11SecularHReal`: source reality predicate described in N1, no fallback.

`fast_spec_at` constructs G as epsilon-inverse times the actual averaged g at zero
fast angle. The inverse is justified by epsilon positivity; angle independence is
proved on the whole relevant domain. The remainder uses both weighted summability
and its weighted sum bound. The sup conversion retains `coth(pi*sigma)^n` and the
extra strip margin. All real/complex spaces use Pi max norms, Fourier indices use
integer Pi functions; no Euclidean carrier or hidden rescaling is substituted.
The oscillator and frozen symplectic forms have equivalent overall-sign preservation,
and the actual imported `symplFormC` is the one appearing in the signed conclusion.

## Independent checks

Every audit-owned Lean/Lake/checker invocation was serial, with `LEAN_NUM_THREADS=1`
and `nice -n 5`. Other worktrees have independent orchestrator jobs; none was launched
or modified by this audit. No clean/update/cache download or package edit occurred.

1. Targeted compile gate:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap5 KAM.Planetary.Preparation.Fast KAM.Planetary.Preparation.LogBounds
```

Exit **0**. Output includes `[inp-gate] slot 2 acquired 23:09:59` and
`Build completed successfully (9328 jobs).` Dependency warnings were unused-variable,
unused-simp/deprecation/style warnings; no sorry or heartbeat failure in the audited slice.
The build includes all five audited modules transitively.

2. Signed source and elaboration probes:

The seven contiguous signed data declarations in `Fast.lean:30–77` are identical to
signatures lines 776–822 after whitespace normalization. Literal signed expressions
for all five scalar definitions and `P11FastSpec` were copied into fresh definitions
and compared by `rfl`; the signed data structure's fields were copied and reconstructed.
The literal signed `e4` type was reproved by `e4 ha hb`. The signed `avg_fast` conclusion
was copied with only the authorized replacement of selected C by arbitrary specified C,
and closed by `avg_fast_of_spec hC hh`. Reality-clause conversion and squared-minimum
parse probes also elaborated. No signature draft or its sorry bodies was imported.

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP5Audit.lean
```

Exit **0**. Probe output: no errors/warnings; 38 axiom lines. Each of the 38 public theorem rows
in the ledger printed exactly `[propext, Classical.choice, Quot.sound]`, including
`e4`, `fast_divisor`, `fast_small_eventually`, `oscHyp_fast`, `fast_spec_at` and
`avg_fast_of_spec`. There is no `sorryAx` or unapproved axiom.

3. Single-invocation kernel replay:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.Fast KAM.Planetary.Preparation.FastBridge KAM.Planetary.Preparation.FastDivisor KAM.Planetary.Preparation.FastParams KAM.Planetary.Preparation.LogBounds
```

Exit **0**, output:

```text
replaying KAM.Planetary.Preparation.LogBounds
replaying KAM.Planetary.Preparation.FastParams
replaying KAM.Planetary.Preparation.FastDivisor
replaying KAM.Planetary.Preparation.FastBridge
replaying KAM.Planetary.Preparation.Fast
```

4. Source hygiene:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly permitted stale generated root. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1006 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

There is no over-100-column or other forbidden-source diagnostic in this receipt.
The generated root was not regenerated.

Static scans found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`
or option override in the five modules. All five have copyright, `module`, public
imports, module documentation and an exposed public section. Their respective
line counts/max Unicode columns are Fast 416/99, FastBridge 213/100,
FastDivisor 175/100, FastParams 143/98, LogBounds 52/95. Thus all fit the hard 1500-line
cap and the focus's 100-column rule. A repository-wide declaration-name search found
no reused public helper short name for any new declaration. All declarations remain
inside `KAM.Planetary`; no harmful root shadow was found.

A static traversal of all 282 reachable KAM modules found **zero provider modules
and zero frozen theorem modules**. Only frozen definitions are reachable, so no
DRAFT_SORRY theorem or provider is imported by the package.

5. Diff and integrity:

`git diff inp...HEAD` was taken as requested: 139 files, 23,576 insertions and 530
deletions, with a multiple-merge-base warning. Git chose
`4a6109378656730cc0b980bc99a04d661042ec0b`; the other merge base is
`4a5b757e944936d0ae6e9269a1170dc7098e4240`. The five audited files are additions;
their complete source/diff was reviewed. Other modules in the broad integration diff
were inventoried, not independently audited as P5.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**:
inherited generated-root additions and N-HEAD-C's complex-bound anchor seal/manifest
state change are present. These must not be represented as a clean protected-path
three-dot comparison. Attribution checks over all 15 commits with subject prefix
`P11A-P5:` show **no protected-path changes** in any package commit. The anchor seal
comes from `7c254d1a`; root regenerations include `4a5b757e`. There is no P5 frozen,
manifest, root or README mutation. The scope ruling permits auditing only the named
five files; this inherited history is retained as a note, not charged to their author.

`git diff --check`: exit **0**. The handoff was already untracked before this audit.
Final audit-owned scratch/probe files are deleted; no production file or git state
was changed. No commit was made.

## Errata, deviations and remaining uncertainty

- F1 is the concrete suspected design/signature defect, with quoted signed/source
  expressions and exact consumer locators above. It does not identify a defect in
  the pinned CP09 paper. Record it alongside handoff E2 without calling the signed
  eta rate established.
- N1's amended reality clause exactly supplies the explicit hh premise after the
  P2f integration. The amendment's physical construction remains outside this audit.
- The helper-module split and additional unsigned source/dictionary lemmas are
  transparent implementation deviations within the named five-file audit scope;
  none changes a signed body. Their combined size exceeds the design's rough
  500-line estimate but no file-size rule is violated.
- No heartbeat override or default-heartbeat failure occurred. No proof or definition
  defect was found in the authorized signed parametric core. Full consumer closure
  and any physical anchor seal remain unpaid for the reasons stated above.

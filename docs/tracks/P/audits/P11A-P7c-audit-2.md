# P11A-P7c independent package audit 2

Date: 2026-10-29 UTC. Worktree: `/root/code/KAM-inp-p11ap7c`.
Audited HEAD: `64ef7ba1c0803ab6393d221b73d1f7f1c01cad2b`.
Round 2 delta: `5b84c0bd..64ef7ba1` (26 insertions, 10 deletions).

## Verdict

**PASS WITH NOTES. F1 is resolved.** The unsigned as-nr export now establishes
both literal graph-node bounds, including the mixed `δ₀/2`, and the tightened
smallness is eventually supplied from source data. No signed statement changed.
No new finding blocks this parametric P7c slice. Round 1's N1/N2 remain: P7d must
assemble the common constants, full-domain MW bound, zero-mode estimate and
analytic inputs; `Slow.lean` remains an explicitly partial facade.

No frozen anchor or provider is delivered by this slice; provider/frozen-type and
seal-body tests are not applicable. This is not a certificate for `avg_slow`, its
signed wrappers, or a planetary headline. The package's as-concl result remains
conditional on its explicitly listed inputs.

## Authority, scope and comparison

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package-audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the package handoff and
its AUDIT FOCUS, audit 1, `.drafts/handoff-P11A-P7c.md` (including Round 2 fix),
the P7 round-1 handoff, the design's as-nr/as-b2/as-concl entries, the Track P
statement, and `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`'s slow spec.
Consulted `blueprint-P/parts/p11-cp09-preparation.tex:170–185` and the frozen
properly-degenerate headline, phase and complex-strip definitions for context.
The user's explicit report destination overrides the brief's generic destination.

Compared against `inp` with `git diff inp...HEAD`, including all five added Lean
files and the two audit/handoff documents. Current comparison: 7 files, 2017
insertions; `Slow.lean` is inherited and unchanged. The merge base is
`94d6bbcf33c48b029f8fdc513b27c68b37ee4e2a`. The shared `inp` ref moved from
`d26c97d9423611905bcd4fff7be60085e2e7e5cf` to
`a2464f937a8b578ae414ec08331359284ec94a78` during inspection; the seven-file
comparison remained unchanged. Unlike round 1's historical comparison, these
checks emitted no multiple-merge-base warning.

The authorized slice is exactly
`KAM/Planetary/Preparation/{SlowConclude,SlowDerivative,SlowDivisor,Slow,SlowRates,SlowSmall}.lean`.
The round-2 commit changes only `SlowDivisor.lean` and `SlowSmall.lean`.
`SlowConclude`, `SlowDerivative`, `SlowRates`, `Slow`, the inherited signed data
and the signature file are not changed by that commit. Unchanged semantic rows
below carry forward audit 1's scope; builds, kernel replay, axioms and static
hygiene were independently rerun for all six modules.

## F1 resolution and source-only smallness

Design `docs/tracks/P/design/P11A-LEAN-DESIGN.md:380` says:

> case k_1 != 0 ¦k.d h_0¦ >= delta_0/2 >= alpha_(1)

The blueprint at `blueprint-P/parts/p11-cp09-preparation.tex:182` likewise states
`≥ 1/2 δ₀ ≥ α_(1)` for sufficiently small ε. With `K = K₂`,
`δ₀ = C.gamma * K^(-C.tau)`, and
`R = min (s₁/4) (π r_z²/32)`, the actual exported type at
`SlowDivisor.lean:271–291` now states:

* pure slow: `ε * (3/4 * δ₀) ≤ ‖k·dh₀‖`, exactly
  `ε(δ₀ − δ₀/8 − δ₀/8)`;
* mixed: `δ₀/2 ≤ ‖k·dh₀‖`;
* the same domain, nonzero integer mode and total ℓ¹ cutoff as before.

The proof's pure-slow branch subtracts the Z derivative loss `δ₀/8` from the
`7δ₀/8` secular pairing. The mixed branch obtains `3δ₀/4` from `fast_divisor`
and subtracts at most `δ₀/4`, by the tightened `hMWs` at lines 283–284 and the
Cauchy calculation at lines 440–443. The resulting reverse-triangle bound is
`δ₀/2`, not the old `δ₀/4`. Using the slightly weaker intermediate fast bound
than the blueprint is harmless because the literal final bound is established.

`p11_slow_alpha1_le_half` at `SlowDivisor.lean:463` proves
`(γ/4) K^(-τ) ≤ γ K^(-τ)/2` for any nonnegative γ and positive K, with no τ
restriction. These premises follow from `fast_consts` and `slow_pos` for the
source data. It is an arithmetic companion, not a new source assumption.

`slow_R4_eventually` at `SlowSmall.lean:331–339` assumes only
`P11SecularSpec D C`, `1 ≤ nu`, and a fixed nonnegative numeric `MW`. It applies
`slow_R_eventually` with `2 * MW`, then divides the resulting inequality by two
using linear arithmetic. It has no divisor, averaging, or desired-smallness
hypothesis. Its pointwise conditions `0 < eps` and `eps * C.MF ≤ exp(-1)` are
supplied by `slow_base_eventually`. An independent Lean probe combined the two
lemmas to obtain the unconditional filter statement

```lean
∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0),
  eps * p11K2 C nu eps * MW ≤
    C.gamma * p11K2 C nu eps ^ (-C.tau) / 4 *
      min (p11s1 C eps / 4) (Real.pi * C.rz ^ 2 / 32)
```

from those three source/numeric premises only. The existing route is logarithmic
domination `e4`, with positive data constants and a shrinking s₁ estimate; no
conclusion-shaped hypothesis or theorem being assembled enters the route.
The threshold may depend on `C`, `nu`, `MW`, all fixed before ε.
This proves smallness for a chosen fixed MW, not the outstanding construction of
a uniform full-domain MW bound for the eventual P7d objects (N1).

A second part of the delta probe derived the exact old signed B1 expression from
the new export by splitting the two mode cases. It independently checked the
pure-slow expression with both explicit subtractions, the mixed `δ₀/2`, and the
last `α₁ ≤ δ₀/2` inequality. Another probe established eventual `α₂ ≤ α₁` from
`slow_base_eventually` and `slow_pos`. Thus the complete as-nr conclusion and the
existing `p11_slow_conclude` divisor input are compatible. A lexical reference
search found no in-repository caller needing repair.

## Declaration ledger

“Unchanged” refers to the round-2 delta, with audit 1's semantic assessment
retained. Every theorem below also has a fresh axiom check; all six modules have
fresh build and kernel checks. Locations are current line numbers.

| Node | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| as-nr inputs | `p11SlowW` (SlowDerivative.lean:32) | PASS | Unchanged literal definition; classification below. |
| as-nr inputs | `p11Jproj` (SlowDerivative.lean:38) | PASS | Unchanged literal definition; classification below. |
| as-nr inputs | `p11Jproj_apply` (SlowDerivative.lean:41) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr inputs | `p11Jproj_single_cast` (SlowDerivative.lean:44) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr inputs | `p11Jproj_single_nat` (SlowDerivative.lean:50) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr inputs | `hasFDerivAt_Jf` (SlowDerivative.lean:60) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr inputs | `fderiv_comp_Jf` (SlowDerivative.lean:66) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr inputs | `fderiv_slowW_nat` (SlowDerivative.lean:74) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr inputs | `p11dotC_split` (SlowDerivative.lean:128) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr inputs | `p11_slow_dotC_split` (SlowDerivative.lean:136) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr inputs | `p11_scalar_step_bound` (SlowDerivative.lean:177) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr inputs | `p11appR` (SlowDerivative.lean:205) | PASS | Unchanged literal definition; classification below. |
| as-nr inputs | `p11appR_apply` (SlowDerivative.lean:210) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr inputs | `p11Slow_append_eq_add` (SlowDerivative.lean:220) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr inputs | `p11appR_single` (SlowDerivative.lean:226) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr inputs | `fderiv_append_slice` (SlowDerivative.lean:241) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `p11SlowCenter` (SlowDivisor.lean:32) | PASS | Unchanged literal definition; classification below. |
| as-nr | `p11SlowBox` (SlowDivisor.lean:36) | PASS | Unchanged literal definition; classification below. |
| as-nr | `p11SlowZDom` (SlowDivisor.lean:40) | PASS | Unchanged literal definition; classification below. |
| as-nr | `p11SlowBox_isOpen` (SlowDivisor.lean:45) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `p11SlowZDom_isOpen` (SlowDivisor.lean:52) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `p11SlowBox_mem` (SlowDivisor.lean:58) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `norm_Jf_sub_le` (SlowDivisor.lean:67) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `norm_Rf_sub_le` (SlowDivisor.lean:72) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `modeSize_split` (SlowDivisor.lean:77) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `p11s2_spec` (SlowDivisor.lean:84) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `slowZDom_J_mem` (SlowDivisor.lean:101) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `slowW_differentiableOn` (SlowDivisor.lean:110) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `Omega_lipschitz` (SlowDivisor.lean:139) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `re_dotC_Omega` (SlowDivisor.lean:166) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `dotC_Omega_lower` (SlowDivisor.lean:204) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `p11_slow_divisor` (SlowDivisor.lean:271) | PASS | Changed: literal pure-slow 3εδ₀/4 and mixed δ₀/2; F1 resolved. |
| as-nr | `p11_slow_alpha1_le_half` (SlowDivisor.lean:463) | PASS | New: α₁ ≤ δ₀/2 under source-supplied signs. |
| as-nr | `p11PartialVec_zero` (SlowDivisor.lean:468) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `p11_drho_of_clause6` (SlowDivisor.lean:473) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr | `p11SlowBox_subset_avg` (SlowDivisor.lean:492) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-b2 / as-concl | `rpow_nat_mul'` (SlowRates.lean:25) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-b2 / as-concl | `rpow_mul_pos` (SlowRates.lean:30) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-b2 / as-concl | `eps_pow_five_half` (SlowRates.lean:33) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-b2 / as-concl | `eps_pow_three_half` (SlowRates.lean:38) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-b2 / as-concl | `lg_pow_one` (SlowRates.lean:42) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-b2 / as-concl | `lg_pow_two` (SlowRates.lean:46) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-b2 / as-concl | `slow_disp_rho` (SlowRates.lean:54) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-b2 / as-concl | `slow_disp_J` (SlowRates.lean:69) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-b2 / as-concl | `slow_disp_theta` (SlowRates.lean:83) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-b2 / as-concl | `slow_g_quad` (SlowRates.lean:97) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-b2 / as-concl | `slow_b2_eventually` (SlowRates.lean:119) | PASS | Unchanged; eventual literal B2 via e4. |
| as-nr smallness | `min_div_le_min` (SlowSmall.lean:29) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr smallness | `eventually_eps_log_le` (SlowSmall.lean:38) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr smallness | `p11s1_log_lower` (SlowSmall.lean:47) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr smallness | `p11s2_log_lower` (SlowSmall.lean:79) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr smallness | `small_arith_cz` (SlowSmall.lean:111) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr smallness | `small_arith_R` (SlowSmall.lean:140) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr smallness | `slow_log_ge_one` (SlowSmall.lean:159) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr smallness | `slow_pos` (SlowSmall.lean:165) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr smallness | `slow_pe_eventually` (SlowSmall.lean:188) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr smallness | `slow_cz_eventually` (SlowSmall.lean:214) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr smallness | `slow_R_eventually` (SlowSmall.lean:258) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr smallness | `slow_base_eventually` (SlowSmall.lean:317) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-nr smallness | `slow_R4_eventually` (SlowSmall.lean:331) | PASS | New: eventual δ₀/4 smallness from source data and fixed MW ≥ 0. |
| as-concl | `p11Box_half_subset` (SlowConclude.lean:33) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-concl | `p11_norm_le_of_wbound` (SlowConclude.lean:38) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-concl | `g_bound_arith` (SlowConclude.lean:55) | PASS | Unchanged; source, calculus, domain or arithmetic helper. |
| as-concl | `p11_slow_conclude` (SlowConclude.lean:66) | PASS WITH NOTES | Unchanged; signed tail freshly probed; explicit P7d inputs remain (N1). |
| avg-slow facade | `Slow.lean` (no declarations) | PASS WITH NOTES | Unchanged partial facade and header exception (N2). |

## Definition classification

Round 2 introduces no definition, abbrev, structure, or bundled hypothesis.
The six package definitions are unchanged:

| Definition | Whole-carrier meaning |
|---|---|
| `p11SlowW` | Literal `C(J) + Σ Ωᵢ(J)ρᵢ/(2π) + Z(I)`, with no branch/default. |
| `p11Jproj` | Continuous linear projection onto the first action block. |
| `p11appR` | Continuous linear embedding `ρ ↦ (0,ρ)`. |
| `p11SlowCenter` | Literal `(J₀, 2πε)` for every real ε. |
| `p11SlowBox` | Open rectangular box with radii s₂ and πε, possibly empty for nonpositive radii; positivity is supplied at use. |
| `p11SlowZDom` | The signed Z-domain's literal pair of strict norm inequalities. |

There is no junk branch or fallback used by a proof. Ambient vectors and modes
remain ordinary Pi types. No SIGNED declaration is introduced in these files.
The independently rebuilt signed-tail target was extracted from the signature
file, with only `A.h0/A.g2/A.f2/A.f3/A.Psi` replaced by the corresponding
parametric/existential variables and the explicit V/Vh/s/E lets supplied.

## Independent checks

All audit Lean/Lake invocations were serialized, with `LEAN_NUM_THREADS=1` and
`nice -n 5` (the build gate supplies nice). No resource override was used.

### Build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap7c KAM.Planetary.Preparation.SlowSmall KAM.Planetary.Preparation.SlowConclude KAM.Planetary.Preparation.Slow
```

Exit 0. Gate acquisition and final output:

```text
[inp-gate] slot 3 acquired 00:54:42 for KAM.Planetary.Preparation.SlowSmall KAM.Planetary.Preparation.SlowConclude KAM.Planetary.Preparation.Slow
Build completed successfully (9353 jobs).
```

The dependency closure includes SlowDerivative, SlowDivisor and SlowRates.
Warnings were deprecated names and unused variables/simp arguments, including
inherited dependencies; no sorry or heartbeat failure. Job totals include cached
dependency replay, not a clean rebuild.

### Independent delta and signed-tail probes

Run separately, each after the previous process exited:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P7cR2Delta.lean
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P7cR2Tail.lean
```

Both exit 0. Delta probe warnings were only deprecated `if_pos`/`if_neg` names.
The complete axiom output of these probes:

```text
'KAM.Planetary.audit_r2_literal_and_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.audit_r2_source_eventual' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.audit_r2_alpha_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.audit_r2_signed_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Axioms of all public theorems

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P7cR2Axioms.lean
```

Exit 0. Probe generated one `#print axioms` for each of the 58 public theorems
in the ledger. Complete output:

```text
'KAM.Planetary.p11Box_half_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_norm_le_of_wbound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.g_bound_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_conclude' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Jproj_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Jproj_single_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Jproj_single_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasFDerivAt_Jf' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_comp_Jf' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_slowW_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11dotC_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_dotC_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_scalar_step_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11appR_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Slow_append_eq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11appR_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_append_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowBox_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowZDom_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowBox_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_Jf_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_Rf_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.modeSize_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11s2_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slowZDom_J_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slowW_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Omega_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.re_dotC_Omega' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.dotC_Omega_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_divisor' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_alpha1_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PartialVec_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_drho_of_clause6' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowBox_subset_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rpow_nat_mul'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rpow_mul_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.eps_pow_five_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.eps_pow_three_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lg_pow_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lg_pow_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_disp_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_disp_J' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_disp_theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_g_quad' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_b2_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.min_div_le_min' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.eventually_eps_log_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11s1_log_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11s2_log_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.small_arith_cz' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.small_arith_R' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_log_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_pe_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_cz_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_R_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_base_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_R4_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.SlowConclude KAM.Planetary.Preparation.SlowDerivative KAM.Planetary.Preparation.SlowDivisor KAM.Planetary.Preparation.SlowRates KAM.Planetary.Preparation.SlowSmall KAM.Planetary.Preparation.Slow
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.Preparation.Slow
replaying KAM.Planetary.Preparation.SlowSmall
replaying KAM.Planetary.Preparation.SlowRates
replaying KAM.Planetary.Preparation.SlowDivisor
replaying KAM.Planetary.Preparation.SlowDerivative
replaying KAM.Planetary.Preparation.SlowConclude
```

### Lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly permitted stale generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1130 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module hygiene, the frozen-anchor guard and all 144 frozen ABI hashes pass.
The generated root was left untouched, as required by the audit brief.

### Static hygiene and protected paths

The package-wide lexical scan found no proof escape, resource option or
`EuclideanSpace` in code. No reused declaration short name among the package's
public helpers was found against other KAM Lean sources, including both newly
added helpers and the previously renamed `p11Slow_append_eq_add`. All package
declarations remain under `KAM.Planetary`; no root declaration was added.

| File | Lines | Maximum Unicode line width |
|---|---:|---:|
| SlowDerivative.lean | 262 | 98 |
| SlowDivisor.lean | 503 | 100 |
| SlowRates.lean | 167 | 99 |
| SlowSmall.lean | 344 | 98 |
| SlowConclude.lean | 271 | 100 |
| Slow.lean | 17 | 91 |

Every line is ≤100 characters, every file is below 1500 lines. The five
substantive modules have the required copyright, module, public imports,
docstring and exposed public section. The inherited declaration-free facade
still lacks a literal `public section` (round 1 N2); the module checker accepts it.

Transitive local-import traversal found 307 KAM modules, no provider and no
frozen theorem imports. All 58 frozen-definition files in that closure are
manifest-SEALED. No DRAFT_SORRY anchor enters the package.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit 0 with empty output. The report was also checked for whitespace errors.
No frozen/manifest/generated file is changed by this package diff.

## Remaining notes, errata and handoff boundary

* **N1 retained:** the split explicitly assigns P7d a uniform MW bound on the
  whole Z-domain, the `cf0 ε³` zero-mode estimate on the half box, analytic/reality/
  periodicity inputs, and selection of the common constant. None is discharged
  merely by the eventual arithmetic lemma. The actual P7b derivative-jet and
  weighted-bound exports remain compatible: the alpha=0 specialization supplies
  `hdZ`, and `p11SlowBox_subset_avg` restricts the larger averaging box. No new
  impossible premise was found. The stronger hMWs is now genuinely covered by
  `slow_R4_eventually`, replacing `slow_R_eventually` for P7d's assembly.
* **N2 retained:** `Slow.lean` exposes only the earlier P7 modules and declares
  itself PARTIAL. The unsigned conditional core, rather than a signed wrapper,
  is this package's authorized deliverable. The facade's public-section omission
  and the informal clause-number drift remain the harmless recorded exceptions.
* No new suspected mathematical-source or blueprint defect was established.
  F1 was an unsigned-export mismatch, now corrected. No pinned PDF verification
  is claimed by this local Lean/design delta audit.
* The deliberate change from δ₀/2 to δ₀/4 in the smallness premise is recorded,
  justified by source-only eventual smallness, and does not change a signed
  statement. No auditor-introduced mathematical deviation or production repair.

Only this report was written outside `.lake/abi-scratch/`. All audit probe files
and scratch logs were removed after recording their results. No state-changing
git command or generated-root regeneration was performed.

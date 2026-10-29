# P11A-P7c independent package audit 1

Audit date: 2026-10-29 UTC. Worktree: `/root/code/KAM-inp-p11ap7c`.
Audited HEAD: `33170ae3b6f445cc05ab3660a24ed9a396fcb97f`.

## Verdict

**FAIL under the AUDIT FOCUS literal graph-completeness requirement.** The mathematical
helpers pass the checked types, axiom checks and targeted builds, but the unsigned
`p11_slow_divisor` does not establish the design node's stronger mixed lower bound
`δ₀/2`. It establishes `δ₀/4`, exactly sufficient for the signed slow-spec B1 clause.
This is a statement/completeness finding, not evidence of an unsound Lean proof.
See F1 below. The conditional averaging and eventual-smallness results pass with
notes about their explicitly deferred P7d inputs.

No frozen anchor is implemented or proposed for sealing by this six-file slice;
provider/frozen-type and seal-body probes are therefore not applicable. In particular,
this audit does not certify `avg_slow`, its signed wrappers, or a planetary headline.

The six audited files are `KAM/Planetary/Preparation/{SlowConclude,SlowDerivative,
SlowDivisor,Slow,SlowRates,SlowSmall}.lean`. P5, P7 round 1 and P7b appear in the
three-dot diff as inherited dependencies; their source interfaces were consulted
for compatibility, without extending this package verdict to their proofs.

## Authority and comparison

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package-audit brief,
`docs/tracks/P/audits/P11A-P7c-handoff.md`, the P7 round-1 handoff,
`docs/tracks/P/design/P11A-LEAN-DESIGN.md`, the signed file
`/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, the Track P statement,
and `blueprint-P/parts/p11-cp09-preparation.tex:170–185`. Consulted the frozen
properly-degenerate headline and underlying phase/strip definitions for context.
The user's explicit absolute report path overrides the generic brief's main-worktree destination.

`git diff inp...HEAD` contains 27 files, 5564 insertions. Git warns:

```text
warning: inp...HEAD: multiple merge bases, using ce5bc0c09a78b36777a59cdb8b93c5e544d380e6
```

At initial comparison `inp` was `a20be6a42facf4d58164200dedf9a38b0e72cb7b`.
`git merge-base --all inp HEAD` returned
`ce5bc0c09a78b36777a59cdb8b93c5e544d380e6` and
`798b999a67520b92bb55ebf904f9eee3541a1383`.
The shared `inp` ref advanced during the audit (observed later at
`7e77845396885b8f953f902df45903b7c9a7f20a`); repeated three-dot diff/stat and
protected-path checks still chose the same base and returned the same 27-file diff.
The six-file slice was reviewed against the required three-dot diff and current sources.
The handoff was already untracked at audit start. No production source was edited.

## Findings and exact scope

### F1 — unsigned as-nr export is weaker than the literal design node

`docs/tracks/P/design/P11A-LEAN-DESIGN.md:380` states:

> case k_1 != 0 ¦k.d h_0¦ >= delta_0/2 >= alpha_(1)

The blueprint proof at `blueprint-P/parts/p11-cp09-preparation.tex:182` likewise
claims the intermediate mixed lower bound `δ₀/2` for sufficiently small ε.
`SlowDivisor.lean:269–292` exports only `(γ/4) K₂^(-τ)` in the mixed case.
Its actual proof uses the fast lower bound `3δ₀/4` (`:420–452`) and allows a
perturbation as large as `δ₀/2` through `hMWs` (`:283–284`, `:439–443`).
The resulting reverse-triangle estimate proves `δ₀/4`, as concluded at `:460`;
it does not prove the node's `δ₀/2`. The stronger mixed estimate is neither an
export nor an internal fact in this slice.

The signed spec at `P11ASignatures.lean:1003–1006` asks for `δ₀/4`, and that
consumer is satisfied. However, `p11_slow_divisor` is unsigned, explicitly labelled
`stepP:p11:as-nr`, and the focus only exempts SIGNED declarations from literal node
strength. Thus this cannot be silently accepted as the complete literal node.
Resolution requires establishing the stronger intermediate mixed bound under
appropriate eventual smallness, or an explicit ruling narrowing the unsigned node.
No claim is made that the blueprint bound itself is false. No signed statement
should be changed to address this finding.

### N1 — P7d inputs remain genuine assembly obligations

The 23:35 split assigns P7c the parametric steps 3–4. The following premises are
explicitly deferred by its handoff, rather than disguised as proved source results:

* `MW`, uniform in ε, bounding `p11SlowW` on the whole Z-domain;
* `cf0`, uniform in ε, bounding `‖coeff f2 I 0‖ ≤ cf0 ε³` on the half box;
* instantiation of holomorphy, reality, periodicity, B1/B2 and the common constant.

No incompatible or evidently impossible premise was found. A route to `MW` is
available from `P11SlowPolarOut`'s AR/AB bounds, eventual control of η₁, the secular
C/Ω bounds, and `s₁ ≤ rC`. This must bound the full Z-domain, not just V₂.
The `cf0` route is the zero mean of `G∘Π − polarAverage G`, followed by the
`P11FastSpec` bound `(ε MF)³` on `f1`. The cancellation and integral estimate are
not established by this six-file slice or an identified P7b export; they remain
unpaid P7d work. No unconditional as-concl/avg-slow closure is claimed here.

`SlowConclude.lean:61–65` calls the result clauses 9–28 and inputs clauses 8/24.
Those ordinal labels do not count the top-level conjunctions literally: the current
spec has six initial conjuncts, then the 20-conjunct tail proved by this helper
(with displacement components grouped at the end). The elaborated signed-tail
probe below avoids relying on these informal clause numbers.

### N2 — facade and harmless hygiene deviations

`Slow.lean:16` explicitly says `avg_slow_of_spec` is not proved; its imports at
`:8–11` do not expose the new P7c modules. Adding those imports and assembling
signed wrappers is explicitly assigned to P7d, so this is not an additional
missing deliverable of the authorized split. It must not be advertised as a complete
`Preparation/Slow` implementation.

The import-only facade has no `public section`, despite the literal AGENTS rule.
It defines no declarations, and the repository module checker accepts it. All five
substantive modules have the full header, public imports, docstring, exposed public
section, and ordinary Pi carriers. Record the facade exception; do not silently
claim every file literally contains a public section.

## Core proof and interface review

* Pure slow: `re_dotC_Omega` embeds `(0,k₂)` into the selected full Diophantine
  frequency and retains Ω/(2π). `Omega_lipschitz` uses the full frequency derivative
  bound. `dotC_Omega_lower` gives `7δ₀/8`; the Z error is at most `δ₀/8` **before**
  multiplying by ε. The proof therefore supports `3εδ₀/4`, stronger than its
  exported `εδ₀/4` target. No outgoing nonresonance conclusion is assumed.
* Mixed: `p11_slow_dotC_split` isolates the fast frequency and ε∂W. Cauchy uses
  `R = min(s₁/4, π rz²/32)` and an explicitly proved closed-ball inclusion in the
  Z-domain. Both blocks of ∂W, including the slow Ω term, are bounded together.
  F1 concerns strength, not omission of this term or a missing ε.
* B2: `slow_b2_eventually` works for arbitrary fixed `c0` (even negative), with
  positive a,γ and τ≥0. The reduced small quantity is
  `|c0| a^(τ+1) ε^(1/2) log(1/ε)^(3τ+2) → 0`.
  The κ identity/order and `α₂ ≤ α₁` are proved inside `p11_slow_conclude`.
* `p11_slow_conclude` invokes `aniso_avg` with E₀=`c0 ε^(5/2) ℓ^(2τ+1)`,
  not the larger bookkeeping E=`c ε^(5/2) ℓ^(2τ+1)`.
  With a=`3ν/(πs)`, s=`σ/12`, the g constant is
  `cf0 + 260 c0² a^τ/(π² γ s)`, the two action constants are
  `6 c0 a^τ/(π γ s)`, and the angle constant is `18 c0 a^τ/(π² γ)`.
  These expressions are independent of c. Once c dominates them, all remaining
  c-dependent smallness is imposed by shrinking ε. The existential witnesses may
  syntactically depend on the supplied proof arguments; the verified independence
  claim concerns these numerical constants, not a separate witness-independence theorem.
* Output domains, strip loss σ/12→σ/72, reality, symplecticity, lattice equivariance,
  injectivity, mapping, Hamiltonian identity and three displacement rates match
  the signed tail. `exp(-κ/6)=ε^ν` is proved with ε>0, not a formal log rewrite
  on an unrestricted carrier.
* P7b compatibility: `p11SlowW C Z = fun I => p11SlowSec C I + Z I`
  and `p11SlowH0 C eps Z = fun I => C.h (p11SlowJ I)+eps*p11SlowW C Z I`
  are definitionally the same expressions. `p11_slow_Z_jets`
  (`SlowAverageJet.lean:138`) matches `p11_drho_of_clause6` at α=0.
  Its stronger `128 ε < rz²` follows from `3 ε ≤ rz²/32` and ε>0.
  `p11_slow_f2_wbound` (`SlowAverageW.lean:184`) has the claimed larger box,
  width σ/12, and constant `coth(πσ/12)^(n+n) * p11SlowC0 C c1` after reassociation.
  `p11SlowBox_subset_avg` restricts it. The stronger-width holomorphy, periodicity
  and realness exports at `SlowAverageW.lean:82,157` and
  `SlowAverageReal.lean:87,110` restrict to the same domain. Their `64 ε < rz²`
  follows from the same base smallness. These are source-interface comparisons;
  P7b was not independently rebuilt or re-audited here.

## Declaration-by-declaration inventory

All names below are in `KAM.Planetary`. PASS here means the stated helper is
correct and suitable for its scoped use; it does not override the F1 graph verdict.

| Node/use | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| as-nr derivatives | `p11SlowW` (SlowDerivative.lean:32) | PASS | Intended total object; classification below. |
| as-nr derivatives | `p11Jproj` (SlowDerivative.lean:38) | PASS | Intended total object; classification below. |
| as-nr derivatives | `p11Jproj_apply` (SlowDerivative.lean:41) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr derivatives | `p11Jproj_single_cast` (SlowDerivative.lean:44) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr derivatives | `p11Jproj_single_nat` (SlowDerivative.lean:50) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr derivatives | `hasFDerivAt_Jf` (SlowDerivative.lean:60) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr derivatives | `fderiv_comp_Jf` (SlowDerivative.lean:66) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr derivatives | `fderiv_slowW_nat` (SlowDerivative.lean:74) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr derivatives | `p11dotC_split` (SlowDerivative.lean:128) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr derivatives | `p11_slow_dotC_split` (SlowDerivative.lean:136) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr derivatives | `p11_scalar_step_bound` (SlowDerivative.lean:177) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr derivatives | `p11appR` (SlowDerivative.lean:205) | PASS | Intended total object; classification below. |
| as-nr derivatives | `p11appR_apply` (SlowDerivative.lean:210) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr derivatives | `p11Slow_append_eq_add` (SlowDerivative.lean:220) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr derivatives | `p11appR_single` (SlowDerivative.lean:226) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr derivatives | `fderiv_append_slice` (SlowDerivative.lean:241) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `p11SlowCenter` (SlowDivisor.lean:32) | PASS | Intended total object; classification below. |
| as-nr / domain | `p11SlowBox` (SlowDivisor.lean:36) | PASS | Intended total object; classification below. |
| as-nr / domain | `p11SlowZDom` (SlowDivisor.lean:40) | PASS | Intended total object; classification below. |
| as-nr / domain | `p11SlowBox_isOpen` (SlowDivisor.lean:45) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `p11SlowZDom_isOpen` (SlowDivisor.lean:52) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `p11SlowBox_mem` (SlowDivisor.lean:58) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `norm_Jf_sub_le` (SlowDivisor.lean:67) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `norm_Rf_sub_le` (SlowDivisor.lean:72) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `modeSize_split` (SlowDivisor.lean:77) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `p11s2_spec` (SlowDivisor.lean:84) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `slowZDom_J_mem` (SlowDivisor.lean:101) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `slowW_differentiableOn` (SlowDivisor.lean:110) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `Omega_lipschitz` (SlowDivisor.lean:139) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `re_dotC_Omega` (SlowDivisor.lean:166) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `dotC_Omega_lower` (SlowDivisor.lean:204) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `p11_slow_divisor` (SlowDivisor.lean:269) | FAIL (node) / PASS (B1) | Signed B1 met; literal mixed δ₀/2 absent (F1). |
| as-nr / domain | `p11PartialVec_zero` (SlowDivisor.lean:462) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / domain | `p11_drho_of_clause6` (SlowDivisor.lean:467) | PASS | α=0 removes factorial/power costs; coordinate norm ≤ vector norm. |
| as-nr / domain | `p11SlowBox_subset_avg` (SlowDivisor.lean:486) | PASS | s₂≤s₁/4 restricts P7b exports. |
| as-b2 / as-concl rates | `rpow_nat_mul'` (SlowRates.lean:25) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-b2 / as-concl rates | `rpow_mul_pos` (SlowRates.lean:30) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-b2 / as-concl rates | `eps_pow_five_half` (SlowRates.lean:33) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-b2 / as-concl rates | `eps_pow_three_half` (SlowRates.lean:38) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-b2 / as-concl rates | `lg_pow_one` (SlowRates.lean:42) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-b2 / as-concl rates | `lg_pow_two` (SlowRates.lean:46) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-b2 / as-concl rates | `slow_disp_rho` (SlowRates.lean:54) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-b2 / as-concl rates | `slow_disp_J` (SlowRates.lean:69) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-b2 / as-concl rates | `slow_disp_theta` (SlowRates.lean:83) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-b2 / as-concl rates | `slow_g_quad` (SlowRates.lean:97) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-b2 / as-concl rates | `slow_b2_eventually` (SlowRates.lean:119) | PASS | Literal eventual B2; κ/order supplied in conclude. |
| as-nr / eventual smallness | `min_div_le_min` (SlowSmall.lean:29) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / eventual smallness | `eventually_eps_log_le` (SlowSmall.lean:38) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / eventual smallness | `p11s1_log_lower` (SlowSmall.lean:47) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / eventual smallness | `p11s2_log_lower` (SlowSmall.lean:79) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / eventual smallness | `small_arith_cz` (SlowSmall.lean:111) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / eventual smallness | `small_arith_R` (SlowSmall.lean:140) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / eventual smallness | `slow_log_ge_one` (SlowSmall.lean:159) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / eventual smallness | `slow_pos` (SlowSmall.lean:165) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / eventual smallness | `slow_pe_eventually` (SlowSmall.lean:188) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / eventual smallness | `slow_cz_eventually` (SlowSmall.lean:214) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / eventual smallness | `slow_R_eventually` (SlowSmall.lean:258) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-nr / eventual smallness | `slow_base_eventually` (SlowSmall.lean:317) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-concl | `p11Box_half_subset` (SlowConclude.lean:33) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-concl | `p11_norm_le_of_wbound` (SlowConclude.lean:38) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-concl | `g_bound_arith` (SlowConclude.lean:55) | PASS | Direct arithmetic, analytic or domain helper; no hidden output premise. |
| as-concl | `p11_slow_conclude` (SlowConclude.lean:66) | PASS WITH NOTES | Signed tail matches; cf0 and analytic inputs remain explicit (N1). |
| avg-slow facade | `Slow.lean` (no declarations) | PASS WITH NOTES | Explicit partial facade, assembly deferred to P7d. |

## Definition classification

| Definition | Classification on its whole carrier |
|---|---|
| `p11SlowW` | Literal secular bracket C(J)+ΣΩᵢ(J)ρᵢ/(2π)+Z(I); no branch/default. |
| `p11Jproj` | Continuous linear first-block projection on every Pi vector. |
| `p11appR` | Continuous linear embedding ρ↦(0,ρ) on every Pi vector. |
| `p11SlowCenter` | Literal center `(J₀,2πε)`; defined for every real ε. |
| `p11SlowBox` | Literal open rectangular box with s₂ and πε; may be empty for nonpositive radii, with positivity supplied at use. |
| `p11SlowZDom` | Literal product of the two norm inequalities in the signed Z-domain; no fallback. |

No new structure, abbrev, selected default value, or conclusion-bearing bundled field
occurs in the audited files. No SIGNED declaration is introduced in these six files;
the signed data definitions reside in inherited `SlowData.lean`. No root declaration
or reused public helper short name was found in a lexical comparison against all
other KAM Lean sources, including the renamed `p11Slow_append_eq_add`.

## Independent checks

Every Lean/Lake invocation in this audit was serialized, with `LEAN_NUM_THREADS=1`
and `nice -n 5` (the gate supplies nice for builds). No resource limit was raised.

### Targeted builds

Run separately, waiting for each exit before starting the next:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap7c KAM.Planetary.Preparation.SlowConclude
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap7c KAM.Planetary.Preparation.SlowSmall
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap7c KAM.Planetary.Preparation.Slow
```

All exit 0. Final output respectively:

```text
Build completed successfully (9351 jobs).
Build completed successfully (9339 jobs).
Build completed successfully (9342 jobs).
```

SlowConclude's dependency build covers SlowDerivative, SlowDivisor and SlowRates.
These are targeted cached-overlay builds; the job totals include dependency replay,
not a requested clean rebuild. Warnings include deprecated names and unused simp/
variable arguments in SlowDerivative (:158,238,254), SlowDivisor (:271,363,419),
SlowSmall (:112,141), SlowConclude (:44,55), plus inherited dependency warnings.
No sorry warning or default-heartbeat failure occurred.

### Signed-tail probe

`P7cTail.lean` copied the current theorem's parametric inputs, but independently
constructed the target conclusion from the signature file's literal tail beginning
`DifferentiableOn ℂ A.h0 V ∧ ...`. It replaced only A's fields by the existential
variables and supplied the same V/Vh/s/E lets. A fresh theorem with this independent
target was proved by applying `p11_slow_conclude` to the listed inputs.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P7cTail.lean
```

Exit 0. Output:

```text
'KAM.Planetary.audit_signed_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This verifies the tail's order and types, including the grouped displacement
conclusion. It does not instantiate P7d's outstanding inputs.

### Axioms of every new public theorem

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P7cAxioms.lean
```

Exit 0; 56 `#print axioms` commands, one per public theorem listed above.
The complete output was:

```text
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
'KAM.Planetary.p11Box_half_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_norm_le_of_wbound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.g_bound_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_conclude' depends on axioms: [propext, Classical.choice, Quot.sound]
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

### Lint and protected paths

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

The frozen-anchor guard and all 144 elaborated ABI hashes pass. The generated root
was not regenerated in this report-only audit.

Static scope checks: file lengths are SlowDerivative 262, SlowDivisor 497,
SlowRates 167, SlowSmall 334, SlowConclude 271, Slow 17. All lines are ≤100
Unicode characters; no file is near the 1500-line cap. No forbidden proof escape,
resource override or EuclideanSpace appears in this slice. Transitive local-import
traversal found 307 KAM modules, no provider, no frozen theorem, and 58 frozen
definitions, all manifest-SEALED. Thus no DRAFT_SORRY theorem enters this slice.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit 0, with no diff/check output except Git's multiple-merge-base warning
quoted above. No frozen/manifest/generated file was changed by this package diff.

## Errata, deviations and handoff boundary

No defect in a pinned mathematical source was established; the pinned PDF itself
was not needed for this Lean/design interface audit, and no PDF-verification claim
is made. F1 is a discrepancy between the literal design/blueprint intermediate
bound and the delivered unsigned export. N1's mean estimate and full-domain MW
bound remain explicit assembly work, not imported axioms or completed graph facts.
N2 records the facade's literal header-rule exception and incomplete import surface.
The informal clause-number drift is documentation only; the signed-tail probe
checks the actual conjunction. No auditor-introduced mathematical deviation.

Only this report was written outside `.lake/abi-scratch/`. Audit probes were removed
at completion. No git state-changing command, production-source repair, or frozen
statement edit was performed.

Audited HEAD (`git rev-parse HEAD`): `47103daf17581a9bc88fc6e562305c9fba2cae17`; SHA-256: `KAM/EffectiveStability/Tube/Check/TailMaj.lean`: `f65d17896c9f20e240d58f4730ef92ffef5b5cce1a23a2504242206c1469917a`; `KAM/EffectiveStability/Tube/Check/TailRem.lean`: `5ce8c77c351db7f9ed5cedc9ace1ddaf6beee4b75c45547dfce3a3daa4f501cc`; `KAM/EffectiveStability/Tube/Check/TailQ.lean`: `e85f7f214a3bbdaec0814f5c2e38d3441fa4d5c4abb00e0ced44293ea9aad209`; `KAM/EffectiveStability/Tube/Check/HSplit.lean`: `612421ddc60ed9abef5ef8d8581ce6854144aa2b30bea7f7db8504b83db33026`; `KAM/EffectiveStability/SJSU/Check/Tail/Rows.lean`: `3b535de982b52d7a2cb39503e19d8363e0b296b24ee7fd68877a4a67ab70ed8f`; `KAM/EffectiveStability/SJSU/Check/Tail/Tab.lean`: `09b68263a1da164af9de347fbdd9cccb328c709ba9b20673688e3d23a0f45f28`; `KAM/EffectiveStability/SJSU/Check/Tail/Tails.lean`: `cf4e0edbdf82ec3ffce3ac9e985147afe0b105a6bb59002db3d3c7474686a073`; `KAM/EffectiveStability/SJSU/Check/Tail/W1to6.lean`: `d82604cfe43abeb5cc7b76dc8d07a14822381e87f60777e402ac5dcf509e6430`; `KAM/EffectiveStability/SJSU/Check/Tail/W7.lean`: `1085abd84dfcbd292b3f3a4256222dee3c1428e8db11918b867923d86725fc6c`; `KAM/EffectiveStability/SJSU/Check/Tail/W8.lean`: `e580ff76092dcd6461e1a0370ed65b997a9c1a8c8cca1a34297e700e0de0d869`; `KAM/EffectiveStability/SJSU/Check/Tail/W9.lean`: `ba2c05555d067dc68d2aabee00952162e0d8972827e6e07cd913fc05bd5fed99`; `KAM/EffectiveStability/SJSU/Check/TailAcc.lean`: `3a77bd1d0e7b3a2a5cf0fcae6073ba0485915437b70d708c5b448a2249cafecf`; `KAM/EffectiveStability/SJSU/Check/TailCheck.lean`: `6a126d204b5cb9c0dcdeabfcac27d37a470ef51cc977b48bf7bde0a6142d28b0`; `KAM/EffectiveStability/SJSU/Check/TailData.lean`: `5443938c8fdaf995ef6c9e45bf60aa20edcd7ba055de080ebe507a8935758bb1`; `KAM/EffectiveStability/SJSU/Check/TailMain.lean`: `ef944efa6f99e8f5216ca756d4c22e6891578ae500536026d38034c777daa4dc`; `KAM/EffectiveStability/Tube/Check/BracketBound.lean`: `9b02ad2504627e8819edd158440c36cf6aee01f1dff2fca06efbda5bab7bdf1e`; `docs/explorations/sjsu-g2-handoffs/N5b-Assembly.md`: `437ea3d4fc6efb0ed5d8d7ff080d488c1722931ef1d574a1ccdd473b3e1a8501`.

# N9-Bracket (C), part 1 — audit 2

**Verdict: PASS WITH NOTES.** The remainder derivative budget and the generic assembly with the actual
`hTildeOf` satisfy this part's assigned mathematical targets. No incorrect remainder, power inequality,
missing derivative term, conclusion-shaped premise, vacuous premise, or proof escape was found.
Two minor documentation/module-format notes remain below. This is not certification of the final
`sjsu_hη`, `sjsu_hTη`, `sjsuEta`, or confinement theorem: those are outside this part and still need the
production ledger and coefficient-bridge attachment described in the handoff.

## Scope and integrity

Package commit: `f487cb1cec1ab7acec23431f363f104a27d3144a`. Initial live HEAD:
`80916aa6b05813dc4338e5aaf3af3ed41cbc3043`. The first line records live HEAD at report preparation and
SHA-256 of all 15 package Lean files plus the two files reviewed for audit-1 fixes.
All 17 paths equal their versions at the package commit, and their hashes remained unchanged throughout
the checks. Concurrent commits and unrelated untracked worker files were present in this shared tree.
They were neither audited as package deliverables nor changed here.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `.drafts/g2/WORKER-RULES.md`,
`.drafts/g2/AUDIT-PKG-brief.md`, `.drafts/g2/BRIEF-N9-Bracket.md`, the N9 handoff, and audit 1.
Read the required route, SR-4 and `ApproxIntegral` consumer, and traced the relevant N4 binomial,
N5a Hamiltonian/regularity, N6 balanced-sum and SJSU centre/degree interfaces. These dependency reads
establish applicability; they do not replace those packages' own audits.

Only this report and the protocol-required ignored scratch probes/logs under
`.drafts/g2/scratch/audit/` were written. No production edits, commits, branch changes, frozen or manifest
edits, generated-root updates, resource overrides, or direct Lean/Lake calls.

## Findings and verification of audit-1 fixes

1. **Minor literal module-format omission — `SJSU/Check/TailCheck.lean:21`.** The file ends with the
   facade docstring, quoted: “`denominators) and Tail/W1to6, W7, W8, W9 (integer row sums per degree).`”
   It contains the copyright header, `module`, public imports and module docstring, but no
   `public section`, which AGENTS rule 3 and the audit checklist explicitly request for every file.
   This import-only facade declares nothing, so no theorem becomes inaccessible and no proof is affected.
   Suggested fix: append an empty `public section` / `end`, or obtain an explicit facade exception.
   The repository module checker checks the module header and size; its success does not check this
   additional literal requirement.

2. **Minor residual handoff count — `docs/explorations/sjsu-g2-handoffs/N5b-Assembly.md:522`.** Quote:
   “`BracketBound.lean | 334`”. The current file has **335** lines: correcting “jointly smooth” split one
   line into two. Suggested fix: change the count to 335. Audit 1's substantive documentation requests
   are otherwise satisfied: `BracketBound.lean:30–31` now says “jointly differentiable”, the handoff
   inventory includes both `_of_drop` exports, and its axiom/check list includes both of them.

Paths in finding 1 are relative to `KAM/EffectiveStability/`. No suspected defect in a pinned
mathematical source, and no mathematical deviation introduced by this audit.

## Remainder identity and independent derivative accounting

For `s_j = n_j/2`, write

`P₉(u,φ) = Σ_{|m|≤9} hCoef(m,φ) u^m`,
`R(u,φ) = Σ_n T_n(φ) [Π_j(B_j(φ)+u_j)^{s_j} − binomTrunc(s,9,B(φ),u)]`.

The bracketed expression is exactly N4's `binomProdRem`, not a remainder of degree 8 or a rectangular
Taylor truncation. N5a's `hTildeOf_taylor` identifies `R = h̃ − P₉` globally by algebra.
`HSplit.lean:73` transfers that equality to `listObs` with the correct coefficient/monomial order.
Its list hypotheses require no repeated monomials, total degree at most `L`, and coverage of every
triple of total degree at most `L`, including the constant. They prevent omission of zero/default
coefficients. The Taylor degree `L=9` remains distinct from the bracket cutoff `L'=8`.
An independent scratch example checks this exact remainder identity for `sjsuHTilde sjsuB`.

Direct differentiation gives

`∂_{u_i} R = Σ_n T_n ∂_{u_i} binomProdRem`,
`∂_{φ_a} R = Σ_n [(∂_{φ_a}T_n) binomProdRem + T_n Σ_i (∂_{φ_a}B_i) ∂_{B_i}binomProdRem]`.

Both angle terms survive `TailRem.lean:117` and `TailMain.lean:133`. The first is bounded by
`|coef| (|k₀|+|k₁|)`, uniformly in either angle direction; the second by the three actual `sjsuBeta`
bounds. This produces **`Wp_d TT_{2d} + W_d TP_{2d}`**, not merely `W_d TP_{2d}`.
The action derivative uses **`W_d TU_{2d,i}`**. Regrouping by `rowExp` preserves list multiplicity;
it neither assumes cancellation nor sums a repeated exponent more than once without its rows.

N4 expands three factors into slots `0,…,10`: slots `0,…,9` are Taylor terms and slot 10 is the
entire one-variable remainder. `tailSum_fin3` / `tailQ` sum exactly tuples whose total slot index
exceeds 9. Thus the finite triple sum includes every product containing a one-variable remainder,
as well as products of Taylor terms of total degree above 9. It does not truncate an infinite
remainder at physical degree 30.

## Power bounds, rational tables and finite domains

`TailMaj.lean:34` proves, for `0<a≤b`, `s≥0`,

`max(a^(s-k),b^(s-k)) ≤ b^s/a^k`.

This handles negative `s-k`; monotonicity in the base is applied only to the nonnegative exponent
`s`. For the remainder interval `[bmin−r,bmax+r]`, `r<bmin` makes both endpoints positive, and
`(bmax+r)^s ≤ bmax^s ((bmax+r)/bmax)^9` follows from `s≤9` and a ratio at least 1.
The derivative hats correctly shift the denominator exponent rather than asserting `s−1≥0`.
At Taylor order 9 their remainder slots are:

- value: `|binom(s,10)| (r/(bmin−r))^10 ρ`;
- action: `|s| |binom(s−1,9)| r^9/(bmin−r)^10 ρ`;
- base/angle: `|s| |binom(s−1,10)| r^10/(bmin−r)^11 ρ`;

where `ρ=((bmax+r)/bmax)^9`, after factoring out `bmax^s`.
The Taylor slots use denominator powers `bmin^m`, and `bmin^(m+1)` for the base derivative.
At `m=0` the action multiplier is zero, so natural subtraction in `r^(m−1)` is harmless.
At `s=0` both derivative hats have the required zero factors.

`TailQ.lean:33–73` uses exact generalized binomial coefficients, including their signs before
absolute values, and proves each rational-to-real cast identity. The checks cover **all**
`0≤n_j≤K≤18`, all three action slots and `0≤m≤10`, including their boundaries. The list-accessor
zero defaults therefore cannot silently discard an accessed table entry.

The actual short-decimal box is kernel-attached to `sjsuBmin/sjsuBmax` by `sjsu_tail_box`, and those
bounds attach to `sjsuB(φ)` for every real `φ` through `sjsuB_bounds`. In particular
`r=2·10⁻⁶ < (0.0002627, 0.000619, 0.00002336) = bmin` coordinatewise.
The nonnegative upper square-root bounds are exactly
`hi=(19150,26980,5813)/10⁶`, with `bmax≤hi²`. `rpow_half_le_pow` proves
`bmax_j^(n_j/2)≤hi_j^n_j`; no unverified decimal approximation of a square root is used.
Rows in block `d` have both monomial degrees `d`, hence total exponent `K=2d≤18` and each
`s_j≤9`. The per-degree tail factors can consequently be pulled out with exactly the table index
`2d`, without assuming componentwise exponents equal the total exponent.

An independent Python `Fraction` reconstruction, reading the committed literal lists rather than
running their generator, passed **18,810** individual slot inequalities, **45** tail inequalities,
and **57** integer power-table entries. All inequality arithmetic was exact; floats were used only
for displaying the resulting budgets.

## Integer row sums and balanced summation

`Tail/Rows.lean:108` kernel-checks all entries `M_j^k`, `k=0,…,18`; `sjsuRowW_eq` proves the exact
rational identity with denominator

`Den_d = 10^sjsuE · sjsuN^(2d) · 10^(12d)`.

Indeed `rowCoef = c/(10^E N^(2d))` and `Π_j hi_j^(n_j)` has denominator
`(10⁶)^(Σ_j n_j)=10^(12d)`. Both monomial-degree premises are checked on the actual dense rows.
They also imply each power-table index is below 19, so `getD ... 0` cannot replace a required
positive power with zero. `sjsuDen_pos` justifies the direction of every denominator comparison.
The weighted numerator multiplies by `|k₀|+|k₁|` exactly once.

The kernel inequalities in `W1to6/W7/W8/W9` use N6's `treeSumQ 64`, whose `treeSumQ_eq` rewrites it
to the full `List.sum`. The depth-zero case still sums the residual list; the parameter 64 cannot
discard rows. `sjsu_block_le` then converts those integer sums into rational upper bounds for the
actual `sjsuHw d` rows. `sjsuHwAll_sum` covers blocks 1 through 9, with block 0 definitionally empty.
The row data and their repetitions are retained exactly. No generator output is trusted as proof.

The resulting exact rational budgets have decimal displays

`Ru ≈ (1.16532461315·10⁻¹⁵, 5.14681392856·10⁻¹⁶, 2.77768736677·10⁻¹³)`,
`Rp ≈ 1.11706863199·10⁻¹⁹`.

These agree with the handoff's rounded values. Its estimate for the final TAIL additionally uses
observable derivative ceilings from another package; no final η inequality is certified here.

## Joint differentiability, hypotheses and consumer boundary

`HSplit.lean:85` proves **joint** `DifferentiableAt ℝ R (u,φ)` by expressing `R` as `h̃−P_L`.
N5a supplies the joint derivative of `h̃` when `B+u>0`; every coefficient is differentiable when
`B>0`, and its product with the action monomial is jointly differentiable by composition and
multiplication. This proof uses neither a slice-to-joint implication nor the default zero
`fderiv` of a nondifferentiable function. The independent instance probe proves joint regularity on
the entire closed SJSU box using only `differentiable_sjsuB`, the centre bounds and `hu`.

`reducedBracket_hTilde_bound` (`HSplit.lean:105–139`) supplies this joint proof to the previously
audited `reducedBracket_bound_of_drop`. Its conclusion is the actual bracket with `hTildeOf`, with
`KEPT + D + ERR + TAIL`, including `Ru_a + Ru_2` in the action-difference term. `C1Close` supplies
differentiability of both the true and model coefficient functions. `hbr` is a coefficient identity,
not a bracket estimate; list coverage and uniqueness are independently checkable structural facts.
`hG` is a finite model coefficient-sum bound; `hDrop` is the explicit finite dropped model sum;
`hFd/hFp`, `hRu/hRp` are component derivative ceilings. None assumes the final bracket or rate
conclusion. `sjsu_hRem_bounds` has no certificate or derivative-budget premise: only `φ`, `u` and
the stated box condition.

The positivity requirements are usable by the consumer: `B_j+u_j≥bmin_j−r>0`, including negative
`u_j`, zero deviations and the closed-box boundary. Zero physical actions lie outside this tube,
so this local remainder argument makes no unsupported regularity claim there. Angles range over
`Fin 2 → ℝ`; no `Complex.arg` branch or periodicity premise is needed for these pointwise bounds.
The absolute-value accounting removes derivative signs without changing N2's bracket convention.

The handoff correctly leaves production `Ledger.H/Br`, the instance `Ht` bridge, complete Taylor-list
coverage, empty-coefficient certificates, the literal η arithmetic and confinement assembly as
remaining attachment work. No small-mode or conditional receipt was promoted to that closure.

## Verification

Every Lean/Lake command used `.drafts/g2/g2lake`, with its serial lock, 6 GB cap, nice level and
configured thread count unchanged. Exactly one targeted build was requested at a time.
All 15 builds exited 0; the following are the literal `Build completed successfully (… jobs).`
counts, in build order. Each row means `.drafts/g2/g2lake build <Module>` with the indicated prefix.

| Module suffix | Prefix | Jobs | Lines |
|---|---|---:|---:|
| `TailMaj` | `KAM.EffectiveStability.Tube.Check.` | 2321 | 222 |
| `TailRem` | same | 2336 | 284 |
| `TailQ` | same | 2338 | 112 |
| `HSplit` | same | 2957 | 143 |
| `Tail.Rows` | `KAM.EffectiveStability.SJSU.Check.` | 3158 | 199 |
| `Tail.Tab` | same | 2850 | 50 |
| `Tail.Tails` | same | 2852 | 89 |
| `Tail.W1to6` | same | 3159 | 66 |
| `Tail.W7` | same | 3159 | 31 |
| `Tail.W8` | same | 3159 | 31 |
| `Tail.W9` | same | 3159 | 31 |
| `TailAcc` | same | 2849 | 54 |
| `TailCheck` | same | 3166 | 21 |
| `TailData` | same | 800 | 430 |
| `TailMain` | same | 3171 | 260 |

Build log: `.drafts/g2/scratch/audit/N9BracketAudit2-builds.out`. Warnings are replayed dependency
warnings; none names an audited package module. All audited Lean files are below 1500 lines and
have no line above 100 characters. The comment-masked scan found no `sorry`, `admit`, `axiom`,
`unsafe`, `opaque`, `set_option`, `EuclideanSpace`, `native_decide` or `sorryAx` in the audited files.
Core imports remain in core; there is no provider, draft-anchor, application-root or generated-root
import. Definitions that must unfold have the exposed public section.

`.drafts/g2/g2lake env lean .drafts/g2/scratch/audit/N9BracketAudit2.lean` exited **0**, without
warnings or errors. It checks the exact SJSU remainder identity, joint instance differentiability,
the exact type of `sjsu_hRem_bounds`, and `#print axioms` of **all 84 new exported theorems**.
The allowed axiom sets are `[propext, Classical.choice, Quot.sound]` (82 declarations), `[propext]`
(`sjsuPw_ok`) and `[propext, Quot.sound]` (`sjsuHw_deg`). In particular `hRem_bounds_rows`,
`differentiableAt_hRem`, `reducedBracket_hTilde_bound` and `sjsu_hRem_bounds` all report exactly the
three standard axioms. No `sorryAx` or additional axiom. Earlier scratch attempts had a missing
import and an auditor name-extraction typo dropping trailing apostrophes; these were corrected in
the probe, with no production edit or resource override. Final output:
`.drafts/g2/scratch/audit/N9BracketAudit2-probe.out`.

`python3 .drafts/g2/scratch/audit/N9BracketAudit2-numeric.py` exited **0**:
`Exact Fraction slot inequalities: 18810 PASS; tail inequalities: 45 PASS`,
`Power entries: 57 PASS`. Output: `.drafts/g2/scratch/audit/N9BracketAudit2-numeric.out`.

`.drafts/g2/lint_noabi.sh` exited **1**. Its complete output is recorded in
`.drafts/g2/scratch/audit/N9BracketAudit2-lint.out`. Diagnostics are entirely outside the audited
package files:

- `Tube/Engine/Bracket.lean:21`: 101 characters;
- `Tube/Engine/Deriv.lean:135,172,210`: 111, 106, 101 characters;
- `Tube/Engine/Regroup.lean:195`: 101 characters;
- `KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean,
  KAMSJSU/EffectiveStability.lean)`.

The same run reports `check_lean_modules: PASS (18622 Lean files, 0 comparator configurations)`,
29 guard tests `OK`, 8 root-generator tests `OK`, and **`FROZEN-ANCHOR GUARD OK`**. The package itself
has no width diagnostic. The generated roots were left untouched, as required for this audit.
`abi_hashes` was **skipped**, following the worker rules' explicit 15:25 UTC amendment to use
`lint_noabi.sh` instead of `scripts/lint_sources.sh`; no ABI or full-library build is claimed.

No package elaboration/design failure occurred in these checks. The author's earlier OOM/depth
signals are documented in the handoff and addressed by module/statement splits, `treeSumQ` and
integer power tables, without options. No mathematical uncertainty was found in this part's
remainder and assembly; final production rate attachment remains outside this verdict.

READY g2-audit-n9b-2

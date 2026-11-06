Audited HEAD (`git rev-parse HEAD`, final integrity check): `d4e5745986a488e0a06636b19d32f348e63737d2`; package commit/initial HEAD: `498a8ccf60649b77142022de7f400395621e37fd`; SHA-256 `KAM/EffectiveStability/Tube/Check/BracketList.lean`: `fecebcfbfd261f72de2c6a5e2c21ee997b3ab9bc097aa3c29109306a0e29b858`; SHA-256 `KAM/EffectiveStability/Tube/Check/BracketBound.lean`: `fa587cc3bf5f31cbfa538d9105fe23c063907a87b8b026c7c472cf2f06a030a3`.

# N9-Bracket parts (A)+(B), audit 1

**Verdict: PASS WITH NOTES.** The generic identity and four-budget bound satisfy the brief. No
mathematical defect, vacuous premise, conclusion-shaped hypothesis, forbidden proof escape, or missing
joint-differentiability premise was found. Two documentation corrections are suggested below.
This verdict covers the two hashed files, including their additional `_of_drop` theorems. It does not
certify part (C), any production ledger, a numerical value of η, or T2-CONF closure.

## Inputs and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `.drafts/g2/WORKER-RULES.md`,
`.drafts/g2/AUDIT-PKG-brief.md`, `.drafts/g2/BRIEF-N9-Bracket.md`, and the N9 section of
`docs/explorations/sjsu-g2-handoffs/N5b-Assembly.md`. Also inspected the required route/gate documents,
`ApproxIntegral.lean`, and the relevant BTerm, ListObs, C1Close, N4/N5a and N7 interfaces. Dependencies
were read for applicability; their separate package audits are not replaced by this report.

Both package files equal the committed versions (`git diff 498a8ccf6 -- <both paths>` is empty).
Another worker advanced HEAD during the audit; both file hashes remained unchanged.
The package commit adds exactly these two Lean files and its handoff. Other workers' unrelated
untracked files and subsequent edits were present in the shared worktree; none was changed by this
audit. Audit writes are this report and the explicitly required ignored scratch probe/logs under
`.drafts/g2/scratch/audit/`. No commits, branch changes, generated-root edits, or frozen-file edits.

## Findings

1. **Minor documentation overstatement — `BracketBound.lean:30`.** Quote: “the models and `f` are
   jointly smooth.” The generic hypotheses establish differentiability, not smoothness (`ContDiff`).
   Arbitrary differentiable angle coefficients are allowed. The proof correctly needs and uses joint
   differentiability only. Suggested fix: replace “jointly smooth” with “jointly differentiable”.

2. **Stale handoff inventory — `docs/explorations/sjsu-g2-handoffs/N5b-Assembly.md:520`.** Quote:
   “`BracketBound.lean` | 246”. The committed file has 334 lines and additionally exports
   `abs_reducedBracket_listObs_le_of_drop` and `reducedBracket_bound_of_drop`. The handoff's axiom list
   at lines 592–594 also predates these additions. Suggested fix: update the count, inventory and
   check list. This audit checked both additional theorems, including their axioms.

Neither note changes the theorem statements or proofs. No suspected defect in a pinned mathematical
source and no mathematical deviation introduced by this audit.

## Independent bracket derivation and indices

Write `U_m(u) = ∏_{l=0}² u_l^{m_l}`, `D_a = ∂_{u_a} − ∂_{u_2}`, and take a single pair
`U_μ g(φ)`, `U_ν k(φ)`. Expanding N2's `D_a f ∂_{φ_a} h − ∂_{φ_a} f D_a h` gives:

| kind | shift | coefficient | monomial | angle factor |
|---|---|---|---|---|
| false | false | `+μ_a` | `μ+ν−e_a` | `g ∂_a k` |
| false | true | `−μ_2` | `μ+ν−e_2` | `g ∂_a k` |
| true | false | `−ν_a` | `μ+ν−e_a` | `(∂_a g) k` |
| true | true | `+ν_2` | `μ+ν−e_2` | `(∂_a g) k` |

This agrees with `BT.coef`, `BT.mon`, `BT.val`, and `bterms`, independently of the proof's expansion.
Here `a : Fin 2` is 0 or 1, `a.castSucc : Fin 3` preserves that value, and `2 : Fin 3` is the third
action. `bterms` includes each of the eight direction/kind/shift choices per list pair exactly once;
list duplicates retain their intended multiplicities. Hand sign checks: brackets of
`(u_0,sin φ_0)`, `(u_2,sin φ_0)`, `(sin φ_0,u_0)`, `(sin φ_0,u_2)` are respectively
`cos φ_0`, `−cos φ_0`, `−cos φ_0`, `cos φ_0`.

For a differentiated exponent `m_x > 0`, `(m−e_x)+n = m+n−e_x`; if `m_x = 0`, the multiplier is
zero. Thus natural subtraction never creates a spurious nonzero term. The argument involves no
division by `u_x` and holds at zero or negative actions. Empty lists and repeated terms are handled
by list sums. No argument lift or periodicity hypothesis is needed for this algebraic identity.

**(A):** `BracketList.lean:76–83` has the brief's exact quantified statement, carriers and conclusion
(the explicit `: Type*` annotations only spell out the type parameters). An independently copied
signature elaborated against `reducedBracket_listObs` in the scratch probe.

## Independent budget derivation

Set `M = listObs Hl ν k`, `δ_e = hc_e − k_e`, and `E = listObs Hl ν δ`. The decomposition is
`h = M + E + R`, so joint differentiability permits bracket additivity in the second argument.

* **KEPT/DROP:** group the model expansion by `p = b.mon μ ν`. The kept part is
  `Σ_{|p|≤L} U_p(u) Σ_{mon b=p} coef_b val_b(φ)`. Since `|U_p(u)| ≤ r^{|p|}`, its bound is
  `bracketKept L r G`. The complementary terms have `|mon b| > L`; the triangle inequality gives
  exactly `Σ_b |coef_b| r^{|mon b|} V_b`, the definition of `bracketDrop` at lines 127–130.
  `mem_truncSet_iff` identifies the truncation set with total degree, not coordinatewise degree.
  Every term lies in exactly one side; there is no omitted boundary or cancellation assumed in DROP.
* **ERR:** certificates give `|δ_e| ≤ e₀_e` and `|∂_a δ_e| ≤ e₁_e`. Therefore
  `|∂_{φ_a} E| ≤ Σ_e r^{|ν_e|} e₁_e` and
  `|∂_{u_l} E| ≤ Σ_e ν_{e,l} r^{|ν_e−e_l|} e₀_e`.
  Using `|D_a E| ≤ |∂_{u_a} E| + |∂_{u_2} E|` gives precisely `bracketErr` at lines 134–139.
  Whenever the prefactor `ν_{e,l}` is nonzero, `|ν_e−e_l| = |ν_e|−1`, so this is the brief's
  `(m_a+m_2) r^{|m|−1} e₀_m` formula. Terms with zero prefactor vanish, including the constant
  monomial. This formulation also works at `r=0`; it does not introduce `r⁻¹`.
* **TAIL:** the same bracket inequality applied to `R` gives
  `Σ_a [Fd_a Rp + Fp_a (Ru_{a.castSucc}+Ru_2)]`, exactly lines 142–143. The common `Rp` is a bound
  for both angle directions. No extra factor of two belongs in its first summand; the two action
  directions are explicitly added in the second.

For this application, instantiate the bracket cutoff `L=8`, while `Hl` contains the Taylor
monomials of degree **≤9** and `R` is N5a's remainder at Taylor order **9**. These are distinct
orders; the theorem leaves the Taylor order in `Hl` and `R`, rather than incorrectly identifying it
with the bracket cutoff. The hypothesis `hu` implies `0 ≤ r` by evaluating at action index 0.
Nonnegativity needed for multiplication follows from the absolute-value bounds, not an unstated
positivity assumption. Empty fibres are zero; they require a nonnegative `G p`, with `G p=0` allowed.

## Hypotheses and consumer discharge

| Premise | Discharge and applicability |
|---|---|
| `hg` | Finite literal angle polynomials are differentiable. `listObs` then has a joint derivative by `differentiable_listObs`; the identity does not use only slice differentiability. |
| `hcert` | N7's `Opd.Cert.close` has exactly the orientation `C1Close trueCoefficient literalEval e₀ e₁`. The N5a-2 `Ht_eq_hCoef` bridge identifies the true coefficient; rational error bounds coerce to reals. For `hIdx m=[]`, `Ht m=0` by its list definition; the literal must be checked to be the zero default and the certificate supplied separately. A certificate guarded by `hIdx m≠[]` alone does not discharge all of `hcert`. |
| `hdec` | N5a's `hTildeOf_taylor` is a global equality, including outside the positive tube. Replacing its finset sum by `listObs (truncSet (Fin 3) 9).toList id (hCoef …)` is algebraic. The scratch probe checks this exact conversion. Thus the global quantifier does not demand a stronger analytic Taylor identity than N5a provides. |
| `hG` | Exactly the brief's per-kept-monomial kernel output: the absolute value surrounds the sum of `coef · val`, before absolute values destroy cancellation. No `u`, original Hamiltonian, ERR, TAIL, or final η conclusion is assumed here. Triple indices must be transported to `Fin 3 → ℕ` using the same monomial convention. |
| `hV` | For kind false use `sup|g_i| sup|∂_a k_e|`; for kind true use `sup|∂_a g_i| sup|k_e|`. Finite sparse F bounds come from sums of absolute coefficients and frequency-weighted coefficients. N7's `Opd.abs_eval_le` and `abs_pderiv_eval_le` supply `|q|n` and `|q|C n` for H literals, under their layout/well-formedness checks. This supplies bounds on all terms as required, not only dropped terms. |
| `hFd`, `hFp` | N8's `sjsu_hFu` supplies `Fd a = Fu j a.castSucc + Fu j 2` by `abs_sub`; `sjsu_hFφ` supplies `Fp a`. Sharper direct difference bounds are permitted but not required. These are first-partial ceilings, not bracket-rate assumptions. |
| `hRu`, `hRp` | N5a's `hRem_tube`, using N4's `binomProd_tube`, has precisely these slice partials. Take `Ru_l = Σ_n τ_n remBoundU … l` and `Rp = Σ_n (τ'_n remBound₀ … + τ_n remBoundPhi …)`, at Taylor order 9. The derivative of `T_n` multiplying the remainder is included. Rational upper bounds for these expressions remain numerical checks for part (C), including lower/upper B bounds and half-power enclosures. |
| `hRd` | Must be joint. Derive `R = h − listObs Hl ν hc` from `hdec`; N5a's `differentiableAt_hTildeOf` applies when `B+u>0`, and the Taylor polynomial is jointly differentiable. Both the generic subtraction proof and a direct instantiation for N5a's actual `hRem`, using `differentiable_hCoef`, passed in the scratch probe. `hRem_tube`'s two slice-regularity statements alone are insufficient and are not used to infer joint regularity. |

N5b's already available positive tube margin (`r < bmin ≤ B`) implies `B+u>0`, including on the
closed box boundary. `C1Close` supplies global differentiability of both angle coefficients; hence
the models, error polynomial and original Hamiltonian are jointly differentiable where used. The
proof invokes `hRd` at both slice-to-joint rewrites (lines 272–273 and 329–330). No default zero
`fderiv` for a non-differentiable remainder is being substituted for an actual derivative.

The extra `_of_drop` variant has a distinct name and assumes the explicit dropped finite-model sum
bound `hDrop`, exactly the optional kernel DROP interface. This is a checkable component property,
not the final bracket bound. It cannot by itself supply a proof for the true Hamiltonian.

**Remaining attachment boundary:** at audit time the production `Ledger/H/Main` and `Ledger/Br/*`
results named in the brief were not present. The untracked `Ledger/Small/Main.lean` exports a
small-mode `sjsu_hcerts` with the nonempty-index guard; it is not a production certificate. The
untracked N5a-2 bridge and N7 continuation were inspected only for interface compatibility. Part (C)
must still attach actual kernel receipts, handle empty coefficients, identify its complete monomial
list with degree ≤9, and prove the literal rational budgets and `hTη`. This is a scope limit of the
present (A)+(B) audit, not evidence of production closure.

## Verification

All Lean/Lake invocations used `.drafts/g2/g2lake`, sequentially, one target per build. The wrapper's
serial lock, memory cap and configured thread count were left intact. No resource overrides.

| Exact command | Result |
|---|---|
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Check.BracketList` | Exit 0; `Build completed successfully (2944 jobs).` |
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Check.BracketBound` | Exit 0; `Build completed successfully (2948 jobs).` |
| `.drafts/g2/g2lake env lean .drafts/g2/scratch/audit/N9BracketAudit1.lean` | Final run exit 0, no warnings; exact (A) signature, global Taylor-to-list conversion, generic joint remainder regularity, and joint regularity of N5a's actual `hRem` all passed. |
| `.drafts/g2/lint_noabi.sh` | Exit 1: 24 width diagnostics outside the two audited files, plus stale generated roots. Module-format check, both guard test suites, and frozen-anchor guard passed; details below. |

Build warnings were dependency deprecations/unused simp arguments in `Algebra/Bounds`, `Trig/Tube`,
`Certificate/Arith/PiHigh`, and `Trig/Trunc`; neither audited file emitted a warning.

The probe's `#print axioms` output is `[propext, Classical.choice, Quot.sound]` for **all 17 exported
theorems**: `reducedBracket_listObs`, both `natCast_mul_umon*` lemmas, `sum_map_flatMap`,
`list_sum_mul_list_sum`, `list_sum_sub`, `list_sum_add`, `mem_truncSet_iff`, `list_sum_split_fiber`,
`list_sum_split_truncSet`, `reducedBracket_add`, `abs_reducedBracket_le`,
`abs_reducedBracket_listObs_le`, `abs_reducedBracket_listObs_le_of_drop`, `listObs_add_sub`,
`reducedBracket_bound`, and `reducedBracket_bound_of_drop`. No other axiom, including `sorryAx`.
Probe output: `.drafts/g2/scratch/audit/N9BracketAudit1.out`.

Direct comment-masked forbidden-token scan: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`,
`set_option`, `EuclideanSpace`, `native_decide`, or `sorryAx` in either audited file. Headers,
`module`, `public import`, module docstrings, public section and exposed definitions are present.
Both imports remain in core; no provider, draft anchor, application, or generated-root import.
Line counts: **135** and **334**; no line exceeds 100 characters, and both are below 1500 lines.

The single mandated lint run emitted `Lean lines over 100 characters:` at the following locations
(paths relative to `KAM/EffectiveStability/Tube/`; numbers are line numbers):

| File | Lines |
|---|---|
| `Check/TailMaj.lean` (new concurrent work, outside this package snapshot) | 56, 69 |
| `Engine/BTerm.lean` | 25 |
| `Engine/Block.lean` | 78, 95, 126 |
| `Engine/Deriv.lean` | 135, 172, 210 |
| `Engine/Exact.lean` | 227 |
| `Engine/Horner.lean` | 118, 134, 219, 220 |
| `Engine/Lit.lean` | 14, 40 |
| `Engine/Powers.lean` | 155 |
| `Engine/Sparse.lean` | 122 |
| `Engine/Spread.lean` | 13, 19 |
| `Engine/Step.lean` | 14, 25, 123 |
| `Engine/Types.lean` | 112 |

The other failure was exactly:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean, KAMSJSU/EffectiveStability.lean, KAMSJSU.lean)
```

Passing output was `check_lean_modules: PASS (18597 Lean files, 0 comparator configurations)`,
`Ran 29 tests in 4.174s` / `OK`, `Ran 8 tests in 0.008s` / `OK`, and
`FROZEN-ANCHOR GUARD OK`. Complete output, including diagnostic widths, is in
`.drafts/g2/scratch/audit/N9BracketAudit1-lint.out`. These shared-tree findings are recorded, not
waived as a globally green lint result. None names either audited file. Generated roots and other
workers' files were left untouched as required.

`abi_hashes` is skipped as explicitly directed by the worker rules' 15:25 lint amendment; the full
`scripts/lint_sources.sh` is not substituted for the mandated `.drafts/g2/lint_noabi.sh`.
No default-heartbeat elaboration failure or other design signal occurred.

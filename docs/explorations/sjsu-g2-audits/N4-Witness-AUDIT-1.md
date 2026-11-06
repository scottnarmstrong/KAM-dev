Audited commit (`git rev-parse HEAD`): `c7714004b949a09f07251820e64ee959c9320809`; package commit: `4fc1a8af8`; SHA256: `KAM/EffectiveStability/Tube/Witness/Binomial.lean` = `78a1af2a94d7a655006de4f1c7eba51271d8e6d882b5240d7c98beb37031b2e0`; `KAM/EffectiveStability/Tube/Witness/BinomialProd.lean` = `9cfb9d9058c4ae0983d2901ea7adabfb0d3ac4ee52b3584f10e82b72c18445d5`; `KAM/EffectiveStability/Tube/Witness/BinomialProdDeriv.lean` = `0d6014cc0402144470818a78ff0455015cd560135ca4ba59bf67036e5c868ccc`; `KAM/EffectiveStability/Tube/Witness/HalfPow.lean` = `665b8aa8c619b6d605768390fdb015592a348a8d5b97d9163ede7570198da84e`; `KAM/EffectiveStability/Tube/Witness/InvSqrt.lean` = `632cd310db848016d69099f2fa21e3f29d98820927a54ab5ed4aa52aa0aa2641`; `KAM/EffectiveStability/Tube/Witness/Sqrt.lean` = `4e2d025ec40221632bb32f72158b0e2c284de344b9c6e489558664d2a4ccf168`; `docs/explorations/sjsu-g2-handoffs/N4-Witness.md` = `39b10595045b4dfac1447989a530a8af34063626de30e8f917917affd237bca4`.

# N4-Witness independent package audit 1

**Verdict: PASS WITH NOTES.** Required targets (1)–(3) are supplied. No blocking mathematical,
statement, hypothesis, build, axiom, or package-rule defect was found. One low-severity handoff
claim confuses component degrees with total degree. The Lean definitions and bounds handle that
case correctly. Optional target (4) was explicitly optional and its omission is not a failure.
This verdict covers the generic analytic package; it does not certify the literal Hamiltonian,
the numerical SR-4 receipts, or confinement.

## Scope and integrity

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `.drafts/g2/WORKER-RULES.md`,
`.drafts/g2/AUDIT-PKG-brief.md`, `.drafts/g2/BRIEF-N4-Witness.md`, and the package handoff.
Also read the required rigor plan §§1.1, 2.2, 3.5, phase-1 gates including SR-4,
`hamiltonian_approxIntegrals_confinement`, and N5a's Taylor-model consumer requirements.

All six Witness modules are byte-identical to `git show 4fc1a8af8:<path>`.
Both `git diff 4fc1a8af8 -- KAM/EffectiveStability/Tube/Witness/` and the package working-tree
`git diff` are empty. `git diff --check -- KAM/EffectiveStability/Tube/Witness/` exits 0.
The directory has 1083 lines in six files: Sqrt 118, InvSqrt 143, Binomial 252,
BinomialProd 266, BinomialProdDeriv 240, HalfPow 64.

Read N3's uncommitted `KAM/EffectiveStability/Tube/Algebra/C1.lean` only to check the imported
interface; this is not an N3 audit. Its SHA256 is
`5b8b6d43d581c8a99e84e131012586188e683050a744872b8133a9cc936cc316`.
The shared `Tube/C1Close.lean` SHA256 is
`e0b2b5a5a0f392e49bcb10ad431c04e2cd63f4cb0c1e92e25820dc22f7219aa6`.
Build and axiom results are relative to these dependency bytes. The imported facts used by N4
are ordinary projections/constructors of the literal `C1Close` predicate and elementary calculus.

The initial working tree already contained modifications to `scripts/sjsu/rigor/gen_t2conf.py`
and untracked SJSU, Algebra, Ecc, Poly, Trig and N3-handoff files. These are concurrent work,
not changes by this auditor. This auditor writes only this report and the expressly required
scratch/diagnostic logs under `.drafts/g2/scratch/audit/n4-1/`. No production Lean file,
handoff, frozen file, manifest, generated root, wrapper, branch, or commit was edited.

## Statement and hypothesis review

| Target | Locations | Result |
|---|---|---|
| Square root | `Sqrt.lean:39`, `:42`, `:76` | Global `C1Close √B W`, with value error `ρ/(σ₀+w₀)` and derivative error `(ρ′+2e₀ω₁)/(2σ₀)`. The positive square lower bound and nonnegative witness lower bound protect every denominator. |
| Inverse square root | `InvSqrt.lean:33`, `:38`, `:69` | Uses precisely the upstream square-root model plus differentiable `Y`, residuals, and numerical derivative/value bounds; obtains both inverse errors with the correct quotient-rule signs. |
| One variable | `Binomial.lean:51`, `:76`, `:80`, `:108`, `:133`, `:200`, `:227` | Correct generalized falling-factorial coefficient; truncation uses `m < M`. Remainder and both derivative identities give the required explicit Lagrange bounds. |
| Three variables | `BinomialProd.lean:167`, `:171`, `:193`, `:226`, `:258` | Specialize the finite index type to `Fin 3`. The kept set is exactly total degree ≤ L, and the tail includes cross terms and every remainder slot. |
| First derivatives and tube | `BinomialProdDeriv.lean:91`, `:105`, `:149`, `:169`, `:213` | Actual partial derivatives, differentiability, and uniform box bounds in `u` and angles at fixed `u`; the angle bound includes every `B_i` chain-rule term. |
| Checker glue | `HalfPow.lean:32`, `:37`, `:56`; `BinomialProd.lean:216` | Correct integer powers of the positive square root, rational generalized binomials, and monotonic replacement by rational upper majorants. |

No main theorem assumes its own conclusion or a hidden source theorem. Hypotheses are regularity,
positivity, interval membership, residual inequalities, or explicit value/partial-derivative bounds.
`C1Close.invSqrt_witness` deliberately assumes target (1)'s output, exactly as the brief requests;
it is not circular. Errors and derivative majorants need not be separately assumed nonnegative:
the bounds on absolute values imply this on the inhabited angle domain. For `Fin 3`, the box
hypotheses also imply `0 ≤ r` and strictly positive `bmin`, `B`, and `B+u`.

The square-root target's replacement of `b₀` by `σ₀²` is a documented parametrization that permits
rational inputs. Taking `σ₀=√b₀` recovers the brief's exact value error; a smaller certified rational
`σ₀` gives a valid conservative bound. Dropping the `∂B` bound is a genuine weakening, justified
by the residual derivative identity. Allowing `w₀=0` weakens the brief's assumption safely.
Real exponents and finite index types generalize the requested rational/three-mode statements.

## Independent algebra and edge cases

Let `S=√B`, `D=B−W²`, `E=1−WY`, and `N=E−(S−W)Y=1−SY`. Direct differentiation gives

```text
S−W = D/(S+W),
∂S−∂W = [∂D−2(S−W)∂W]/(2S),
1/S−Y = N/S,
∂(1/S−Y) = [∂E−(∂S−∂W)Y−(S−W)∂Y]/S − N∂S/S².
```

These independently reproduce both signs and all terms of `sqrtErr₁` and `invSqrtErr₁`;
`|∂S| ≤ ω₁+e₁` supplies the latter's last numerator. No positivity of `Y` is needed.

For `c_m(s)=s(s−1)…(s−m+1)/m!`, direct multiplication yields
`(m+1)c_{m+1}(s)=s c_m(s−1)` and `(s−m)c_m(s)=s c_m(s−1)`.
They give respectively the `u`-derivative lowering the remainder order and the `B`-derivative
preserving the order. Induction integrates `|τ|^M` to `|u|^(M+1)/(M+1)` on both sides of zero;
the negative-`u` proof explicitly reverses the derivative sign. The endpoint maximum is valid
for either sign of `s−M` because the entire base interval is strictly positive.

For each mode, the expansion has Taylor slots `0,…,L` and one remainder slot `L+1`.
The full product is the finite sum over all slot tuples. Removing exactly the tuples of total
degree ≤ L leaves `tailSet`, including mixed Taylor terms of higher total degree.
Differentiating that fixed finite sum replaces one slot family at a time. For a `B_i` derivative,
that replacement is `s_i · binomSlot (s_i−1)`, as used in the angle chain rule.
A separate multivariable `B_i` bound can be obtained from the angle theorem by taking
`Bf j φ = B j + (if j=i then φ 0 else 0)` at `φ=0`, direction `0`, and `β_j=if j=i then 1 else 0`;
the separate angle theorem requires only pointwise box bounds. No uniform global bound on that
affine supplier is required. Thus the brief's base-derivative requirement is available as well.

- **Orders:** the brief's one-variable polynomial through degree M is `binomTaylor s (M+1)`.
  The product theorem already uses total degree ≤ L. N5a's degree-9 Taylor model uses `L=9`;
  a differentiated degree-8 remainder must retain the corresponding order shift.
- **Zero displacement:** `u=0` is covered. For a nonempty mode type and `r=0`, the value
  remainder is zero; with `L=0`, the first `u` derivative need not vanish and `slotMajDu`
  correctly retains the remainder derivative through its `r^0` term.
- **Zero/negative actions:** the analytic box results exclude them by `r<bmin` and `|u|≤r`.
  No derivative claim at a square-root singularity is exported by the main bounds.
- **Zero/negative exponents:** real exponents, including negative half-integers, are covered
  on the positive box; integer powers in `rpow_half_sub` use ℤ, so `n−2m` is not truncated.
- **Indices:** directions are `Pi.single i 1` and the angle carrier is literally `Fin 2 → ℝ`.
  General finite mode types specialize to `Fin 3`; the empty type gives empty products and a
  zero product remainder, so its vacuous radius assumptions introduce no false result.
- **Periodicity and branches:** there is no `Complex.arg` in this package. These are real
  calculus statements on the whole angle plane and require no periodicity assumption; they
  apply to the periodic trig inputs supplied by N3 without introducing a period normalization.

## Finding

**N4-A1-01 — low severity, handoff wording only.**
Location: `docs/explorations/sjsu-g2-handoffs/N4-Witness.md:164`.
Quoted text: “Both bounds are exactly 0 for nonnegative integer exponents ≤ L.”

Taken as a statement about the individual exponents of the product, this is false: each factor
can have degree ≤ L while their product has higher total degree. At `L=8`, take
`s=(4,4,1)`, `B=(1,1,1)`, `u=(1/2,1/2,1/2)`, `r=1/2`, and `bmin=bmax=(1,1,1)`.
Every component exponent is ≤ 8 and all box hypotheses hold. The total-degree truncation omits
`u₀^4 u₁^4 u₂`, giving the exact positive remainder `1/512`. Independent exact rational
arithmetic confirms this value. Thus a valid bound cannot be zero in this example.
`tailSet` and the proved Lean majorants correctly retain this term; no theorem fix is needed.

Suggested fix: restrict the wording to the actual sampled integer tuples, or say “for nonnegative
integer exponent tuples whose sum is ≤ L.” Distinguish the vanishing one-variable remainder
slots from the possibly nonzero cross-term tail. The producer's sample integer tuples
`(2,2,4)/2` and `(0,0,6)/2` have total degrees 4 and 3, so this correction preserves those samples.
No handoff edit was made.

## Verification receipts

All commands ran in `/mnt/HC_Volume_106379410/kam-sjsu-g2`.
Every Lean/Lake call went through the serial, capped `.drafts/g2/g2lake` wrapper;
no direct Lean/Lake call, resource override, clean, or application-library build was used.
Each of the six modules was requested exactly once, sequentially:

| Command | Exit | Exact completion output |
|---|---:|---|
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Witness.Sqrt` | 0 | `Build completed successfully (2087 jobs).` |
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Witness.InvSqrt` | 0 | `Build completed successfully (2091 jobs).` |
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Witness.Binomial` | 0 | `Build completed successfully (2318 jobs).` |
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Witness.BinomialProd` | 0 | `Build completed successfully (2319 jobs).` |
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Witness.BinomialProdDeriv` | 0 | `Build completed successfully (2320 jobs).` |
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Witness.HalfPow` | 0 | `Build completed successfully (2320 jobs).` |

`.drafts/g2/g2lake env lean .drafts/g2/scratch/audit/n4-1/Axioms.lean` exited 0.
The scratch imports all six package modules transitively and executes 38 `#print axioms`
commands. Every one reports exactly `[propext, Classical.choice, Quot.sound]`, including
`C1Close.sqrt_witness`, `C1Close.invSqrt_witness`, `abs_binomRem_le`,
`abs_binomRem_le_box`, both one-variable derivative identities,
`abs_binomProdRem_le_box`, both product derivative bounds, `binomProd_tube`,
`tailSum_eq`, `tailSum_mono`, `rpow_half_int`, `rpow_half_sub`, and `gbinom_ratCast`.
The full declaration list is in the scratch; exact outputs are retained in `axioms.log` beside it.
No `sorryAx` or other additional axiom occurs.

An independent comment-masked scan using the repository lexer found no forbidden token,
`set_option`, proof escape, or `EuclideanSpace` in Witness. All six files have the copyright
header, `module`, public imports, module docstring and `@[expose] public section`; all
are below 1500 lines and have no line exceeding 100 Unicode characters.

Per the worker rules' explicit **Lint (added 15:25 UTC)** instruction, ran
`.drafts/g2/lint_noabi.sh` once instead of the full lint; it exited **1**. The full log is
`.drafts/g2/scratch/audit/n4-1/lint.log`. Its only failure categories were over-100-character
lines outside Witness and the stale generated root. Exact summary output:

```text
Lean lines over 100 characters:
[findings in other packages; no KAM/EffectiveStability/Tube/Witness/ entry]
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (18376 Lean files, 0 comparator configurations)
Ran 29 tests in 4.733s
OK
Ran 8 tests in 0.008s
OK
FROZEN-ANCHOR GUARD OK
```

The bracketed line above summarizes the long unrelated width list, retained verbatim in the log.
`abi_hashes` was **skipped**, exactly as the worker lint addendum directs; no ABI result is
claimed by this audit. No generated root or other package was repaired. Repository-wide lint
is therefore not green, despite the package-specific checks passing.

## Consumer boundary, uncertainties, errata and deviations

N5 must certify the literal `B`, `W`, `Y` residuals, positivity, and numerical derivative bounds;
then propagate the supplied value/first-derivative estimates through products and the literal
trig coefficients. These are checkable input estimates, not assumed confinement conclusions.
The package gives an explicit finite majorant involving real endpoint powers; rationalizing
those endpoint bounds and applying `tailSum_mono` remains the checker's responsibility.
The float comparison with an assumed `bmax=1.3 bmin` and its ≤6% effect estimate are not a
verified literal N5 budget and are not part of this PASS. The Lagrange-vs-geometric choice is
permitted by the brief; N5 must use the bounds actually proved here.

No suspected pinned-source erratum was found. The only overstatement found is the handoff
wording above. The documented lower-bound parametrization, omission of the unnecessary `∂B`
premise, real exponents, slot-tail bookkeeping and optional-target omission are acceptable
within the stated package scope. This auditor introduced no mathematical deviation.

Final integrity check: HEAD is unchanged from the first line, all recorded Witness and handoff
SHA256 values still match, and the Witness directory remains byte-identical to `4fc1a8af8`.

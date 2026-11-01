# LP-W2A independent package audit 1

Audited revision: `ae960b07ed69c793f6bc5805e981076379ebaec6` (`inp-lp-w2a`).
Comparison refs at audit time: `inp = 96ef6d94df72007fd2031a93d873c620d03561c5`,
`inp-lp = 2b5e556db68e67afd3b3276869232277bc2d833c`.
Read AGENTS.md, PLAN, DECISIONS, the independent package-audit brief, SPEC, MAIN as amended,
and the combined and individual handoffs. Inspected `git diff inp...HEAD` and scoped the mathematical
review to `git diff inp-lp...HEAD -- KAM`: six new modules, 930 lines, plus six generated imports in
`KAM/Root/Planetary.lean`. Wave 1 and existing engine proofs are dependencies, not re-audited packages.
No frozen LP anchors exist; frozen/provider type and seal probes are inapplicable.

The named `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-W2A.md` does not exist (nor does its
worktree counterpart). Used the combined handoff's explicit constituent briefs `LP-DOM.md` and
`LP-NRS.md` at that package directory; both are byte-identical to this worktree's copies. This is a
provenance note, not an inferred additional contract.

## LP-DOM — PASS WITH NOTES

All bounded targets D0–D6 match the constituent brief and MAIN L8 (244–271), with N2/N3.
No mathematical blocking finding. The full source L8 contains more conclusions than this bounded
package exports; see the limitations below.

All declarations below are in `KAM.Planetary.StrongAMD`.

| Node | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| D0 | `isCompact_strongLSet` | PASS | Continuous image of the literal mass-weighted square-root map; arbitrary masses allowed for compactness. |
| D0 | `strongLSet_subset_chamber` | PASS | Positive masses and literal positive ordered axes give positive actions and exactly the original axes. |
| D1 | `isCompact_strongLevelSet` | PASS | Closed superlevel in compact chamber set; no nonemptiness assumption. |
| Helper | `strongLevelSet_subset` | PASS | Literal membership projection, no analytic premise. |
| Helper | `strongThresholdModulus_mono_set` | PASS | Set monotonicity of the literal supremum, justified using compact chamber sup bounds; handles empty sets. |
| D1 | `exists_isSharedTube` | PASS | Constructs positive radius using uniform continuity on a fixed larger compact chamber neighborhood, then restricts to the smaller tube. |
| Helper | `continuous_fast_snd` | PASS | Coordinate projection. |
| Helper | `continuous_chartAMD` | PASS | Polynomial sum of squares divided by two. |
| Helper | `norm_le_of_coord_le` | PASS | Literal product/Pi maximum norm, including dimension zero. |
| Helper | `abs_le_of_sq_le` | PASS | Elementary scalar bound; its premise forces the relevant nonnegative upper bound. |
| D2 | `isCompact_strongCore` | PASS | Projection of a closed bounded incidence set with the centre retained; not an arbitrary union-of-compacts argument. |
| D2 | `strongCore_margin` | PASS | Both actions belong to the same shared U; modulus loss is exactly δ/16, giving 3δ/16. |
| D2 | `strongCore_subset_dom` | PASS | Individual Γ is at most their sum, at most B(Λ)−3δ/16, strictly below B(Λ)≤Λᵢ. |
| D3 | `strongCore_barrierState` | PASS | Uses the established action/AMD dictionary on the proven chart domain. |
| D3 | `strongCore_subset_chartSafe` | PASS | Barrier compactness gives collision-free image; domain already proved. |
| D4 | `exists_strongTube` | PASS WITH NOTES | R, M, fc precede every centre and μ; holomorphic periodic scalar extension with safe real trace and uniform half-tube bound. Does not separately export all of source L8. |
| D5 | `strongCore_containment` | PASS | Literal complex action, imaginary fast-angle, and real slow-ball proximity conditions; N3 included. |
| D6 | `movingHamiltonian_poincareProd_split` | PASS | Exact physical Hamiltonian, all real μ, no expansion remainder. |

### Definitions and carriers

| Definition | Classification and edge behavior |
|---|---|
| `PositiveStrictlyOrdered` | Literal predicate on every member of A; empty A and missing index pairs are vacuous as intended. |
| `strongLSet` | Literal image a ↦ ν√a on the whole carrier. Lean's real sqrt is total, hence negative axes map using sqrt=0; positivity is required exactly for the chamber theorem. Compactness needs no positivity. |
| `strongLevelSet` | Literal intersection L ∩ {B≥δ}; empty levels permitted. No choice or fallback. |
| `IsSharedTube` | Bundle of radius-selection data: positivity, compactness, chamber inclusion, modulus bound for precisely the same closed 4r tube. D1 constructs it under source premises; it contains no core safety, analytic extension, or drift conclusion. |
| `sharedTube` | Abbreviation for precisely `cthickening (4*r) strongLevelSet`, not an independently chosen set. Outside the positive-radius setting it keeps Mathlib's thickening semantics; consumers use `hg.pos`. |
| `strongCore` | Literal existential union over I⁰∈Lδ with closed angle cell, action distance ≤4r and AMD ceiling B(I⁰)−δ/4. Empty Lδ gives empty core. Negative r gives empty core; at r=0 the action equals the centre. No fallback point. Safety uses δ>0 and chosen shared tube. |
| `secularBall` | Literal Euclidean sum-of-squares sublevel in real slow phase space, while tube distances use the Pi/product maximum norm. A negative ceiling gives the empty ball; for valid centres B≥δ>0 gives a positive ceiling. At n=0 the sum is zero and the sublevel has its literal meaning. |

`IsSharedTube` is a substantive proved geometric choice, used as data thereafter, not a smuggled
conclusion-shaped hypothesis. D5 is stronger than the standing-premise formulation: it needs neither
`hg` nor positive δ or masses because its conclusion is only geometric tube containment. Its input
conditions imply positive s,b; no separate positivity premises are needed. `hrs` and `hrg` give r>0. The proof chooses real parts of the actions,
reduces fast real angles by floor multiples of 2π, and keeps the supplied real slow point. Every
coordinate error is strictly below max(rs,4s,4b)<R/2. A single real slow point controls both blocks,
which is exactly distance to the ball in the product maximum norm. The sign change (x,y)=(ξ,−η)
preserves this ball and distance.

The compactness argument bounds both fast actions and all slow coordinates, retaining the centre
in a compact incidence set before projection. It remains valid for empty levels and does not require
`IsSharedTube` merely to prove compactness. D4 bounds fc on a compact closed half-radius neighborhood
of the fundamental-cell core inside the open full tube, then uses periodicity to cover every lattice
translate. Its arbitrary values outside the asserted tube are never consumed. Empty cores produce
vacuous trace/bound clauses, consistent with MAIN's empty-initial-set case. M is not asserted positive;
this matches D4's brief, and can be increased to a positive constant before engine assembly.

### Source and scope notes

MAIN L8 line 253 says “the chart, momenta, f, and all their first derivatives have bound M” and
“Every Newtonian denominator there has a single holomorphic branch”. These are not separate Lean
exports here. The bounded brief explicitly requests only the scalar fc extension/bound and real trace,
so this is not a failure of D0–D6. Checked `KAM.Weighted.wbound_of_sup_bound` (SupWeighted.lean:78):
it consumes holomorphic periodic class membership and a scalar sup bound, not first derivatives or
individual denominator branches. `ExtNFHyp.pert/bound` likewise consume that scalar class and norm.
Thus the omission is acceptable for the stated Lemma-13 assembly route, conditional on the later
coordinate/period conversion and domain fitting; this audit does not claim those later packages are
closed. Holomorphic chart/denominator and chart-derivative exports of the full source L8 remain outside
this package. No source erratum is inferred from this deliberate bounded target.

The five DOM module docstrings carry package/source/non-frozen tags but omit SPEC §4's exact phrase
“the statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md”. Documentation deviation only.
The abbreviation's comment “Lδ shorthand used by the core” actually labels U (`sharedTube`);
the body and exported types are correct.

## LP-NRS — PASS WITH NOTES

Items 1–3 match the brief, MAIN L13 (37)–(38) and the stated L12 scaling shape. N4 respected:
no appeal to the finite-tube divisor estimate (35). N6 respected: radius D₀√μ; this package supplies
numeric inputs and horizon, not the stopped drift theorem itself.

| Node | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| Arithmetic | `rpow_neg_scale_mul_sqrt` | PASS | Positive μ, τ ensure the exponent identity; no singular base cancellation. |
| Arithmetic | `cutoff_rpow_mul_sqrt_le` | PASS | Upper natural-floor bound and monotone positive real powers; cutoff zero is allowed in this helper. |
| Arithmetic | `scaledCutoff_lower` | PASS | Input 2≤κμ⁻ᵃ gives K≥1 and K≥κμ⁻ᵃ/2. |
| Arithmetic | `exists_scale_kappa` | PASS | Proves both smallness restrictions from positive data, including L=0; assumes neither desired restriction. |
| Item 1 | `lp_scale_choice` | PASS | κ, μ₀, c, T₀ chosen before μ. All seven conclusions have the brief's literals. |
| Item 2 | `diophantine_to_period_one` | PASS | Real dot product, division by positive 2π, decreasing K⁻ᵗ; ℓ¹ cutoff. Allows γ=0, τ=0 as a stronger result. |
| Item 3 | `scaleExponent_planar` | PASS | Exact exponent 1/(2n+1); algebraic identity also valid at n=0. |

### Definitions and carriers

| Definition | Classification and edge behavior |
|---|---|
| `scaleExponent` | Literal 1/(2(τ+1)); total real division gives zero at τ=−1. Scale consumers require τ>0. |
| `scaledCutoff` | Literal natural floor, cast to real, as explicitly requested. Negative arguments truncate to zero; small positive arguments may give K=0. The main theorem proves K≥1 before any negative-power/division use. |
| `stoppedRadius` | Literal D₀√μ; sqrt=0 for μ≤0. Main theorem requires D₀,μ>0. |
| `divisorGap` | Literal γ/(2π)K⁻ᵗ. Real powers are total at zero; no positive divisor claim is made there. Main theorem has γ>0,K≥1. |
| `perturbSize` | Literal M₂μ on all reals; positivity follows from the main theorem's premises. |

No branch, arbitrary optimizer, selected representative, or fallback definition replaces a requested
object. Standard total scalar operations outside the named positive-data carrier are not used to
obtain an analytic conclusion. All scalar helpers have arithmetic/source premises only; the
Diophantine hypothesis is precisely the source arithmetic assumption.

Engine check, directly against current source:

- `Partial/Setting.lean:123`: divisor_size is K*L*b.rB≤α/p, exactly item (b) at p=2.
- `Partial/Nonresonant.lean:344`: hsmall denominator is 2^7*conjExp p*K; conjExp 2=2,
  hence 256K, exactly item (c). The κ restriction uses 512π, correctly accounting for α=γ/(2π)K⁻ᵗ.
- `Partial/Setting.lean:85`: SL is 64π*k*s*b.rB≤b.w², exactly item (d).
- `Partial/Setting.lean:127`: cutoff is 6≤2π*K*s, exactly item (e).
- `Partial/Nonresonant.lean:351`: time bound is s*b.rB/(5ε)*exp((2π*K*s)/6), exactly item (g)'s RHS.
  The proof chooses c=π*s*κ/6 and T₀=s*D₀/(5M₂). K≥κμ⁻ᵃ/2 controls the exponential;
  μ≤1 controls the prefactor. Item (f) supplies r≤ρ; later assembly must choose a strict interior
  ρ when N6 requires r<r_*, rather than silently replacing that strict source condition by ≤.
- `Fourier/Derivative.lean:37`: modeSize is Σ|kᵢ|. `NormalForm/Setting.lean:34` defines zBall
  by precisely modeSize≤K. Dimension zero has no nonzero k, so item 2 is correctly vacuous there.

The NRS module also omits SPEC §4's exact freeze-proposal phrase. Documentation note only.

## Combined verdict — PASS WITH NOTES

No blocking mathematical or premise-fidelity finding in the scoped package. This is acceptance of
D0–D6 and NRS items 1–3 as ordinary, non-frozen declarations; it is not seal readiness for an LP
anchor, full source L8 closure, `ExtNFHyp` assembly, or a stopped-orbit/headline theorem.

## Validation and hygiene

No source files, generated files, frozen files or manifests were edited. The sole scratch probe was
removed after its successful run.

Commands were serialized. The owner D53 wrapper took precedence over the older nice-5 wording.
Builds used `/root/code/KAM-inp/.drafts/LP/lp_build.sh`, whose inspected implementation takes the
compile gate and executes each single target as:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake build <Module>
```

Lint command (only the authorized wrapper was used):

```sh
/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-thr
```

Exit 0; output:

```text
check_lean_modules: PASS (3681 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

Direct source checks: all six modules have copyright, module header, public imports, module docstring,
public section, exposed definitions; line counts are facade 28, Core 313, Safety 56, Extension 95,
Containment 137, NonresonantScale 301. No forbidden escape, sorry, resource override or EuclideanSpace
in the six files. A read-only KAM import walk reached 148 modules: no provider, DRAFT_SORRY module,
or `Exponential.Stopped`. No production module imports a generated root. Protected-path command
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` had empty output; only the six
expected additive generated root imports change under `KAM/Root/Planetary.lean`.
`git diff --check inp...HEAD` exited 0 with no output.

Kernel replay and short-name checks: not rerun, by the user's explicit economy instruction.
The user states both were already run by the launcher; their raw output and exit status were not
visible to this auditor. The handoff independently records the orchestrator's short-name result as OK.
This report does not invent a replay command or an independently observed replay exit code.

Targeted builds:

```sh
/root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-thr KAM.Planetary.StrongAMD.AnalyticDomain KAM.Planetary.StrongAMD.NonresonantScale
```

Exit 0. Output ended, respectively, with `Build completed successfully (9173 jobs).` and
`Build completed successfully (9080 jobs).` The first target includes all four DOM parts.
Only replayed upstream unused-variable warnings (Kepler.Energy, Poincare.Chart, Kepler.Mass,
Exponential.RealDomain) and the existing deprecated `dif_pos`
warning in Exponential.ComplexTube were observed; no new package failure or resource-limit signal.

Axiom probe: imported the DOM facade and NonresonantScale, then `#print axioms` for **every** one of
the 25 new public theorems listed in the tables above, including arithmetic and topology helpers.
Exact invocation:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/LPW2AAudit.lean
```

Exit 0. Every theorem reported exactly `[propext, Classical.choice, Quot.sound]`; none reported any
other axiom. Representative output (the same axiom list holds for all 25 table entries):

```text
'KAM.Planetary.StrongAMD.exists_isSharedTube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.exists_strongTube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.strongCore_containment' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lp_scale_choice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.diophantine_to_period_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.scaleExponent_planar' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No suspected new MAIN/AMENDMENTS defect. Package deviations/uncertainties are precisely the bounded
L8 exports, missing combined brief, and documentation notes above. No proof or hypothesis repair was
introduced by this audit. Final workspace status contains only this untracked report; no git mutation
or commit was made.

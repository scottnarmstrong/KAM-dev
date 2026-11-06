Audited commit (`git rev-parse HEAD`): `75c96013f5d28b0bc971a78e35a257022dbadbfc`; SHA256: `KAM/EffectiveStability/Tube/Chart/Bracket.lean` = `9d15c956e18d1a09cd50d609f217d499ad54fe996e85279d1e83745e6a2f4e5b`; `KAM/EffectiveStability/Tube/Chart/Composite.lean` = `6ce36fb917f9f011a693e3edd75a32270c2086d9ab1c64f0e7281f1c30a95f6e`; `KAM/EffectiveStability/Tube/Chart/LocalInverse.lean` = `75eeb50759891565228e8808b1836a30ea780caea756f03203269b28d41a1a28`; `KAM/EffectiveStability/Tube/Chart/Observable.lean` = `8a75ca8591baab9383b196bd1883391bbf250b8ce9fe8fb60731ae626d435f2e`; `KAM/EffectiveStability/Tube/Chart/Polar.lean` = `8902e60e9334c0020f12eb6e3f9e6c19ef135a2057e489be97031b752d7455d5`; `KAM/EffectiveStability/Tube/Chart/Rotation.lean` = `8c2735549121112f8ac3cb17c78183c52146f8cb2f4a275e1ecec2668fb78ca3`; `KAM/EffectiveStability/Tube/Chart/Shift.lean` = `139b14345b7a7cd4e5486148ddfee52dcab166492b5b616a752f7b915d5228d3`; `KAM/EffectiveStability/Tube/Chart/ShiftSymm.lean` = `ff6940b547f6da4e199c91786c5adaf36619f9650195a2f1ac2cbd2173ced806`; `docs/explorations/sjsu-g2-handoffs/N2-Chart.md` = `24a4b871fcbcd952887cf89b48fca00fb9784282d321ca55841851984b188420`.

# N2-Chart independent package audit 1

**Verdict: PASS WITH NOTES.** Targets (A)–(E) match the package brief. No blocking mathematical,
statement, hypothesis, build, axiom, or package-rule defect was found. Two documentation notes concern an overview regularity claim and the handoff
axiom-receipt coverage; all affected theorems pass this audit. Repository lint is recorded separately below.
This verdict covers the generic chart package, not the literal SJSU Hamiltonian or confinement theorem.

## Scope and integrity

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `.drafts/g2/WORKER-RULES.md`,
`.drafts/g2/AUDIT-PKG-brief.md`, `.drafts/g2/BRIEF-N2-Chart.md`, and
`docs/explorations/sjsu-g2-handoffs/N2-Chart.md`. Also checked the required SJS rigor plan §§1.1,
2.2, 3.5, phase-1 gates (especially SR-4), the `ApproxIntegral` consumer, and the N5a/N5b briefs.

All eight package files match `git show 75c96013f:<path>` byte for byte and retained their initial
SHA256 values throughout this audit. HEAD at the initial verification was the full commit in the first
line. The package commit adds exactly these eight modules and its explicitly requested handoff.
`git diff 75c96013f -- KAM/EffectiveStability/Tube/Chart/` and the package's `git diff --check` are empty.

The initial working tree already contained untracked `SJSU/`, `Tube/{Algebra,Ecc,Trig,Witness}/`, and
N3/N4 handoffs. Those belong to other workers and were not audited or changed. This auditor changes
only this report, plus the explicitly required audit scratch and its logs under
`.drafts/g2/scratch/audit/n2-1/`. No production source, frozen file, manifest, generated root, handoff,
wrapper, branch, or commit was changed.

## Statement and hypothesis review

| Target | Checked locations | Result |
|---|---|---|
| (A) Rotation | `Rotation.lean:36`, `:75`, `:79`, `:84`, `:98`, `:110`, `:131`, `:137`, `:143` | Exact `R = rotMap Vᵀ`, `Rinv = rotMap V`; both inverse identities, symplecticity, rate identity, and regularity at the correct preimages. Only square real orthogonality is needed. |
| (B) Polar transport | `Polar.lean:42`, `:57`, `:82`, `:118`, `:128`, `:135`, `:147` | Literal polar formula, full derivative, symplectic derivative, and bracket transport with the requested sign and positive-action hypotheses. |
| (C) Coverage and smoothness | `Polar.lean:46`, `:61`, `:74`, `:167`, `:170`, `:178`, `:191`, `:210` | Smooth on the open positive-action domain; all punctured modes covered. Right-inverse identity holds even at zero; the reverse identity retains angles only modulo `2π`, as necessary. |
| (D) Shift and reduction | `Shift.lean:37`, `:67`, `:96`, `:124`; `ShiftSymm.lean:28` | Correct two reduced angles and `D_a = ∂u_a − ∂u_2`; explicit derivative symmetry, with a separately proved gradient supplier. |
| (E) Composite | `Composite.lean:39`, `:51`, `:95`, `:111` | Exact all-positive-actions function identities from the brief; arbitrary positive lift and canonical `tubeChart` forms; derivative symmetry or gradient version. |
| Added consumer support | `LocalInverse.lean:47`, `:68`, `:82`, `:96`, `:112`; `Observable.lean:49`, `:72`, `:94`, `:113` | Local inverse derives ambient regularity; explicit periodicity gives the chart identity and removes the argument cut from the observable. |

Every principal hypothesis is typing data, local regularity, orthogonality, positivity, a literal chart
identity, periodicity, or the explicitly authorized shift symmetry. None assumes the bracket formula,
a rate bound, Hamiltonian confinement, or a hidden equivalent source conclusion. In particular:

- `hGf`/`hHh` in `Composite.lean:54-55` are the exact representation identities explicitly requested
  by target (E), not an assumed derivative identity. They quantify over all `actionPos 3`; they are
  deliberately not claimed to follow merely from charge balance or from local tube numerics.
- `hsym` in `Shift.lean:128-129` is the brief's checkable symmetry of `fderiv B`.
  `shift_symm_of_gradient` derives it from a local gradient identity and `C²` regularity of `S`.
- Orthogonality admits `V = 1`; constant shifts satisfy symmetry; periodic trigonometric data supply
  the intended periodicity. The hypotheses do not force vacuity.
- `LocalInverse` genuinely derives differentiability of `G`, `H` from their pullbacks. The composite
  result therefore needs fewer differentiability assumptions than the brief permits, without weakening
  the conclusion. Its generic transport invokes the existing
  `KAM.EffectiveStability.fderiv_chart_apply_hamiltonianVectorField`, whose body and frozen definitions
  were inspected.

## Independent computation of the signs and reduction

Write `r = √(2I) > 0`, `q = −r sin θ`, `p = r cos θ`. In `(I, θ)` column order,

```text
D polar = [ −sin θ/r    −r cos θ ]
          [  cos θ/r    −r sin θ ]
det(D polar) = sin² θ + cos² θ = 1.
```

The frozen field is `X_H = (H_p, −H_q)`, so
`dG(X_H) = Σ(G_q H_p − G_p H_q)`. Thus its polar-coordinate expression is
`Σ(G_I H_θ − G_θ H_I)`, with **actions first**. As an independent dynamical sign check,
`H = (q²+p²)/2` gives `(q̇,ṗ) = (p,−q)` and `θ̇ = −1`; its pullback is `I`, and
`{θ,I} = −1` in exactly the package convention. No sign is borrowed from a name such as “canonical.”

For the shift, let `A = [[1,0,−1],[0,1,−1]]`, `φ = Aθ`, and
`β_lj = ∂θ_j B_l`. The chain rule gives

```text
g_Ij = f_uj,
g_θj = Σ_a f_φa A_aj − Σ_l f_ul β_lj.
```

The corresponding bracket equals

```text
Σ_a [(f_ua − f_u2) h_φa − f_φa (h_ua − h_u2)]
  + Σ_{j,l} (f_ul h_uj − f_uj h_ul) β_lj.
```

The last sum vanishes by `β_lj = β_jl`. This independently verifies the minus signs in `D_a`
and the symmetry placement used in `Shift.lean:128-147`. The angle-reduction map has a five-dimensional
codomain; the exported result is the required reduced bracket identity, not an assertion that this
reduced map is an invertible six-dimensional symplectomorphism.

## Edge cases and N5 applicability

- **Zero actions:** derivative, symplecticity, inverse-function, and composite theorems all require
  strictly positive actions/nonzero rotated modes. `polar_polarInv` alone is valid at zero, because its
  radius is zero and Mathlib totalizes `arg 0 = 0`; it supplies no unwarranted differentiability there.
  Negative actions likewise receive no transport or coverage assertion. Generic dimension `n = 0`
  yields the empty-coordinate identities and introduces no denominator obligation.
- **Argument branch:** the inspected Mathlib `Complex.arg` takes values in `(-π,π]`.
  `polarInv_polar` asserts an integer multiple of `2π`, not literal inverse equality of angles.
  At the negative real axis `arg` changes representative, so `polarInv` and `tubeChart` are not
  asserted smooth. `Observable.lean:32-61` sends integer shifts to
  `(k₀−k₂,k₁−k₂)` and uses the separately assumed periodicities of **both** `B` and `f`.
  `LocalInverse` then proves observable regularity using a smooth local lift, including at the cut.
- **Indices:** `a.castSucc : Fin 3` retains the values `0,1` for `a : Fin 2`; it does not shift them
  to `1,2`. The reference mode in `reducedBracket` is index `2`. Directions
  `phiOf (Pi.single i 1)` are `(1,0)`, `(0,1)`, `(-1,-1)` for `i = 0,1,2`.
- **Period convention:** this package explicitly uses radian angles and `2π` periodicity, as its brief
  requires. It applies ordinary real calculus, not the period-one Fourier infrastructure; no missing
  Fourier `2π` factor is introduced.
- **Consumer boundary:** N5a still owes the literal `H ∘ Rinv ∘ polar` identity, its differentiability
  on the tube, and the literal shift data/symmetry. N5b still owes the literal observable identity
  (or the periodicity supplier), the open punctured domain, and the nonzero-mode proof on its compact
  tube. These are exactly the split briefs' assignments. N2 neither assumes their final estimates
  nor claims to prove them. The pointwise differentiability result can supply `DifferentiableOn`
  on the open punctured set by taking `differentiableWithinAt` at each point.

## Findings

**N2-A1-01 — low severity, documentation only.**
Location: `KAM/EffectiveStability/Tube/Chart/Observable.lean:15-16`.
Quoted text: “is as smooth as `f` on the punctured set”.

This omits the required regularity of the shift `B`. Periodicity alone is insufficient: take
`V = 1`, `B(φ) = (|sin φ₀|,0,0)`, and `f(u,φ) = u₀`. Both are `2π`-periodic in `φ`, and `f` is
smooth, but in a local positive-action lift the observable is
`I₀ − |sin(θ₀−θ₂)|`, which is not differentiable at `θ₀ = θ₂`. This occurs inside the punctured
set, not at a zero-action point. The actual theorem at `Observable.lean:72-81` correctly requires
`hB : ContDiffAt ℝ k B ...`, so no proof or theorem repair is needed.

Suggested fix: qualify the overview as “as smooth as `f` and `B` on the punctured set, under the
stated orthogonality and periodicity hypotheses”; qualify its rate claim by the Hamiltonian identity,
differentiability, and symmetry hypotheses stated in the rate theorem. No source edit was made.

**N2-A1-02 — low severity, handoff receipt wording.**
Location: `docs/explorations/sjsu-g2-handoffs/N2-Chart.md:209-210`.
Quoted text: “all 26 listed theorems (every theorem named above)”.

The referenced producer probe contains 26 commands, whereas the handoff displays 33 `theorem`
declarations. Its probe omits seven displayed names: `differentiableAt_comp_rotMap`,
`rotMap_preimage_eq_image`, `isOpen_actionPos`, `fderiv_polar_apply`, `polar_sq_add_sq`,
`polarInv_mem_actionPos`, and `exists_polar_localInverse`. Thus the parenthetical overstates the
coverage of that specific receipt. This audit's successful 62-theorem probe includes all seven,
so there is no remaining axiom-check gap for them.

Suggested fix: change the parenthetical to “the 26 main theorems in the referenced probe”, or
update the producer probe/receipt to cover all 33 displayed declarations. No handoff edit was made.

No other package finding. The handoff's completion claim for targets (A)–(E), 1,048-line total,
allowed axioms, extra local-inverse/observable/gradient modules, and remaining literal-consumer
obligations agree with the checked files.

## Checks and exact results

Every build below was invoked once, sequentially through `.drafts/g2/g2lake`, which supplies the
shared lock, `nice -n 5`, 6 GB memory cap, memory-availability gate, and `LEAN_NUM_THREADS=2`.
No direct Lake/Lean command or uncapped ABI call was used. The wrapper's live two-thread setting
was used as instructed by this campaign; older one-thread audit conventions were not substituted.

| Exact command | Output | Exit |
|---|---|---:|
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Chart.Bracket` | `Build completed successfully (2757 jobs).` | 0 |
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Chart.Rotation` | `Build completed successfully (2758 jobs).` | 0 |
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Chart.Polar` | `Build completed successfully (2774 jobs).` | 0 |
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Chart.Shift` | `Build completed successfully (2758 jobs).` | 0 |
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Chart.ShiftSymm` | `Build completed successfully (2762 jobs).` | 0 |
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Chart.LocalInverse` | `Build completed successfully (2779 jobs).` | 0 |
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Chart.Composite` | `Build completed successfully (2785 jobs).` | 0 |
| `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Chart.Observable` | `Build completed successfully (2786 jobs).` | 0 |

These are successful targeted build checks using the existing build cache. The output did not
announce fresh elaboration of package modules; no separate `leanchecker` kernel replay was requested
or performed, and this report does not claim one.

Exact axiom command:

```sh
.drafts/g2/g2lake env lean .drafts/g2/scratch/audit/n2-1/Axioms.lean
```

Exit 0. The scratch file contains 62 `#print axioms` commands, covering all 26 names in the handoff's
original probe plus other exported theorems (the two inline `@[simp]` projection lemmas are not in
this probe). All 62 printed exactly the allowed set `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx` or other axiom. All 26 handoff names were mechanically checked against the output.
In particular, every target (A)–(E), the local-inverse regularity results, the gradient supplier, and
the three observable results have this axiom set. Full output: scratch `axioms.log`; individual build
outputs: scratch `build-<Module>.log`.

Package rule checks: all eight files have copyright/module/import/docstring/public-section structure;
all definitions are under `@[expose] public noncomputable section`; imports are core/chart/Mathlib,
with no provider, application, root, or draft-sorry anchor import. No prohibited token or option
occurs anywhere in the package. Ambient vectors are `Fin n → ℝ`, reduced angles `Fin 2 → ℝ`.
Line counts: Bracket 89; Rotation 160; Polar 216; Shift 147; ShiftSymm 51; LocalInverse 128;
Composite 124; Observable 133; **total 1048, maximum 216 < 1500**.

LINT_RESULT_PENDING

## Uncertainties, errata, and deviations

No suspected pinned-source erratum was found in this package. The documentation issues above are
package overstatements, not a defect in the frozen Hamiltonian field or symplectic form. No frozen
statement looked defective; no protected-file edit or substitute premise was needed.

The producer's three extra support modules and stronger coverage result are justified additions
within its owned directory. The lack of an outer `Chart.lean` facade causes no missing import:
`Chart.Observable` re-exports the full package. The precise SJSU identities and numerical bounds
remain outside this audit's scope, as required by the brief.

READY g2-audit-n2-1

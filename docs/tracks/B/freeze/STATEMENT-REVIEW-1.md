# Independent statement review 1: B1-T and B1-E

**Verdict: PASS WITH NOTES.** No BLOCKING statement defect found. Both propositions are likely provable from their stated premises. Retain the mathematical Lean types. Correct the explanation of regularity in OD-B2; it asserts a consequence that is false, although that consequence is unnecessary for either theorem.

This is an independent, refute-first review of the proposed statements, not their implementations. Method: `/root/.claude/skills/lean-statement-audit/SKILL.md`, read in full; no subagents. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the user brief, the plan, decisions, conventions, source passages, and the three frozen definition bodies. Only this report is a repository edit. All line references below are to the reviewed snapshot; `P` abbreviates `/root/code/KAM/docs/explorations/program-b-plan.md`, `F` abbreviates `docs/tracks/B/FREEZE-PROPOSAL.md`, and `E` abbreviates `docs/tracks/B/freeze/elaboration-draft-1.lean.txt`.

## Identity and status

Repository HEAD at review: `0b61be41c4b916f735624d0116c6a3d9a53a0208`. Initial `git status --short` was empty.

| Object | Exact location / identity |
|---|---|
| B1-T | `F:24-52`; elaborated command `E:12-40`; export `KAM.EffectiveStability.torus_confinement` |
| B1-E | `F:54-91`; elaborated command `E:42-79`; export `KAM.EffectiveStability.oscillator_confinement` |
| Proposal SHA-256 | `a1d162988a5b03a0edbd87fc980b5ff3a9864a66e75e608f25fce9991e292d05` |
| Elaboration text SHA-256 | `719cd1402104b13d7e44bf98fd188c801f149a2abe18d8d3cc71f9c9197b74d1` |
| OWNER-DECISIONS SHA-256 | `e9026e3f6fefee9968bc01e65e3266ec8de34a5a0111a055eea06894c7e18a4e` |
| SPEC SHA-256 | `8ebd43045e739cfffbfa9ec57a4927e4fd4328391987930469836c9099ded0d7` |
| P SHA-256 | `b169200714847ff0c317c12c513770fa06887b93223ec1b1156542e8b53784f1` |

Mechanical comparison of the proposal's entire Lean fence with `E` from `open Set` onward, changing only each literal proof placeholder `  ...` to `  sorry`, returned **True**. Thus the scratch elaboration tests the reviewed command text, not another theorem with a similar name.

**NOTE N1 — proposal status.** Neither proposed export has a manifest entry, approved frozen path, versioned anchor ID, or registered provider. `F:3-6`, `OWNER-DECISIONS.md:3-5,10-14`, and `P:219-225` expressly defer freezing and exact-text approval. The overnight defaults are the review basis requested by the user; they are not represented here as final owner approval. Do not promote an ordinary implementation, this report, or the elaboration receipt to a frozen result.

```text
B1-T DECLARATION_FIDELITY: PASS under the recorded overnight defaults
B1-E DECLARATION_FIDELITY: PASS under the recorded overnight defaults
DRAFT_ALLOWLIST: N/A (unmanifested proposals; two temporary proof holes only)
PROOF_STATUS: PROPOSED_UNPROVED
AXIOM_CLOSURE: NOT ESTABLISHED (scratch declarations use sorryAx)
```

`FROZEN_UNPROVED` would become the appropriate status only after authorized installation as manifest-bound DRAFT_SORRY anchors. This audit does not certify a proof or downstream consumption.

## Sources and semantic definitions

Recomputed PDF hashes match `P:952,955` exactly:

| Source | SHA-256 | Reviewed evidence |
|---|---|---|
| CL20, arXiv 2102.05959v1 | `fe288ead9f2d02c3527875154bb1f21195eba0fac1f19bfaf55e6e0e596410e8` | `.drafts/B/papers/CL20.txt:789-885`, §4.1, (32)-(37), PDF pp. 15-16 |
| GLS17, arXiv 1702.04894v1 | `254d52fb9c545efe12cfcc4b138ac8b429c1e95aad0d63c12b4e6dfc182e1cae` | `.drafts/B/papers/GLS17.txt:1288-1323`, §4.3, (56)-(58), PDF pp. 24-25 |

Also freshly extracted precisely those page ranges with `pdftotext -layout`; the relevant formulas and the first-term disclaimer agree with the supplied text. CL20 (32) cancels the action-only normal part; (33)-(34) bound the whole action derivative; (35)-(37) use the **squared-radius** margin. GLS17 (56)-(57) gives the closed action box and derivative-times-time estimate. Its (58) explicitly truncates to the first remainder term (`GLS17.txt:1320-1321`); that numerical approximation cannot supply `hRη` without a tail bound. The reviewed `hRη` bounds the entire remainder instead. Neither paper literally states the full chart/existence/uniqueness interface: those are the elementary extensions explicitly adopted in `P:157-163,195-205` and the overnight defaults.

The complete meaning-carrying project definitions in the theorem types are:

| Frozen definition | Body and verdict | Manifest pin / recomputed whole-file SHA-256 |
|---|---|---|
| `KAM.hamiltonianVectorField` | `KAM/Frozen/Defs/HamiltonianVectorField.lean:24-26`: `(d_p H, -d_q H)`, using actual Fréchet derivatives. BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS for the used real formula. | `kam.hamiltonianVectorField.v1`, SEALED; `manifest/frozen-anchors.json:189-215`; `1592cf15aadef80f7e2017860494a1e067de8698ff8f6075c055a2d138877a79`, MATCH |
| `KAM.symplecticForm` | `KAM/Frozen/Defs/SymplecticForm.lean:23-24`: `Σ (v₂ w₁ - v₁ w₂)`. Same six definition verdicts as above. | `kam.symplecticForm.v1`, SEALED; manifest `565-591`; `cb406afe9c796cec050b1d0f340bf2327766481865dcaf001063c9b8d53df60a`, MATCH |
| `KAM.Planetary.oscillatorAction` | `KAM/Frozen/Planetary/Defs/OscillatorAction.lean:37-38`: `(p_j²+q_j²)/2` on all real Cartesian coordinates, including zero. Same six definition verdicts as above. | `planetary.oscillatorAction.v1`, SEALED; manifest `2633-2659`; `ad724cd5e19a4d4d420c5e30fbcd9f656107affaefa62e9e76c82fa66a4447c5`, MATCH |

No project-owned assumption aliases or structures hide further hypotheses. The domain set-builders, symplecticity, inverse condition, normal-form identity, and derivative bounds are inline. Standard predicates mean: `ContDiffOn` is regularity on the specified set; `DifferentiableOn` supplies within derivatives, upgraded to ordinary derivatives on these **open** domains; `Ioo` is an open interval; `OrdConnected` is the interval property; `HasDerivAt` is an ordinary two-sided derivative of the displayed total curve. `Fin`, function and product carriers are finite real coordinate spaces with the agreed Pi/product norms.

The Hamiltonian field's totalized `fderiv` is not silently trusted at nondifferentiable points: `hH`, `hΨ`, `hΨV` and openness supply actual derivatives of H, Ψ and K; `hR` does so for R on the enlarged chart domain. All points of the stopped region lie in that open domain by `hε`.

## Five-bin binder audit

SOURCE below includes the explicit **plan candidate** premises, whose relationship to the raw papers is reconstructed above. RULED means the precise weakening in the recorded overnight defaults, pending exact-text approval. No analytical proof step is classified SOURCE merely because an implementation might already prove it.

One row per outer binder, separating grouped Lean binders. Local quantifiers and domain restrictions are expanded in the table and following paragraph. No instance binders or ambient section variables are present. T/E columns give elaboration-text line numbers.

| Binder | T / E | Bin | Expanded content and source/ruling |
|---|---|---|---|
| `{n : ℕ}` | 13 / 45 | TYPING | Finite dimension; allowing 0 is OD-B6 (`OWNER-DECISIONS.md:14`), generalizing `P:105,175`. |
| `a` | 13 / 45 | TYPING | Real inner action widths/levels, `P:105-110,175-176`. |
| `b` | 13 / 45 | TYPING | Real outer action widths/levels, same source. E uses action levels, not radii (`P:203`). |
| `η` | 13 / 45 | TYPING | One real drift bound per index, same source. |
| `ε` | 13 / 45 | TYPING | Common real enlargement of each action level, same source. |
| `T` | 13 / 45 | TYPING | Requested finite real horizon, same source. |
| `hε` | 13 / 45 | SOURCE | `0 < ε`, `P:105,175`. |
| `hT` | 13 / 45 | SOURCE | `0 ≤ T`, same source. |
| `hη` | 14 / 46 | SOURCE | For every `j : Fin n`, `0 ≤ η j`, `P:110,176`. |
| `hmargin` | 14 / 46 | SOURCE | For every j, `a j + T * η j < b j`, same source; no time-dependent orbit premise. |
| `V` | 15 / 47 | TYPING | Set in the real physical phase carrier, `P:115,176-177`. |
| `hV` | 15 / 47 | SOURCE | `IsOpen V`, same source. |
| `H` | 16 / 48 | TYPING | Real scalar function on that phase space, same source. |
| `hH` | 16 / 48 | SOURCE | `ContDiffOn ℝ 2 H V`, `P:116,176`. |
| `Ψ` | 17 / 49 | TYPING | Map between equal finite-dimensional phase spaces, `P:117-119,177-178`. |
| `Ψinv` | 17 / 49 | TYPING | Explicit total extension of the inverse chart, OD-B3 (`OWNER-DECISIONS.md:11`). |
| `hΨ` | 18 / 50 | SOURCE | Ψ C² on D, where T: `∀j, |w.2 j| < b j+ε`; E: `∀j, I_j(w) < b j+ε`. `P:117,177`. |
| `hΨV` | 19 / 51-52 | SOURCE | Every w in D maps into V, `P:117-118,177-178`. |
| `hΨsymp` | 20-21 / 53-55 | SOURCE | For every w in D and **all phase vectors** u,v, `ω(DΨ u,DΨ v)=ω(u,v)`, `P:85-89,118,177`. No numerical defect substituted. |
| `hΨinv` | 22 / 56-57 | RULED | For every w in D, `Ψinv (Ψ w)=w`, OD-B2/B3, `OWNER-DECISIONS.md:10-11`; follows from the plan's inverse chart. |
| `N` | 23 / 58 | TYPING | Action-only scalar function; unrestricted off and on its declared total carrier except through `hHΨ`/`hR`. Dropped smoothness: OD-B2. |
| `R` | 23 / 58 | TYPING | Scalar function on phase space, `P:123,179`. |
| `hR` | 24 / 59 | RULED | `DifferentiableOn ℝ R D`, OD-B2; weakening of `P:123,179` C². No continuity of DR is asserted or needed. |
| `hRper` (T only) | 25-26 / — | SOURCE | Every `k : Fin n → ℤ` and w in D: `R(w+(k,0))=R(w)`. `P:72,123`; unit periods, whole enlarged domain. |
| `hHΨ` | 27-28 / 60-62 | SOURCE | Every w in D: `H(Ψ w)=N(w.2)+R w`, or `N(I(w))+R w`. `P:124,181-184`. This is a static identity, not assumed dynamics. |
| `hRη` | 29-30 / 63-66 | SOURCE | Every w in the closed stopped region and every j: absolute angle derivative ≤η_j (T), or the complete inline action bracket ≤η_j (E). `P:125-126,183`; GLS17 (57), CL20 (32)-(34). |
| `w₀` | 31 / 67 | TYPING | Arbitrary real phase point, `P:128,186`. |
| `hw₀` | 31 / 68 | SOURCE | Every j: `|w₀.2 j|≤a_j` or `I_j(w₀)≤a_j`, `P:128,186`. |

Counts (outer declaration parameters, not occurrences of bound indices):

| Theorem | SOURCE | STANDING | TYPING | RULED | EXCESS | Total |
|---|---:|---:|---:|---:|---:|---:|
| B1-T | 13 | 0 | 13 | 2 | **0** | 28 |
| B1-E | 12 | 0 | 13 | 2 | **0** | 27 |

All inner hypothesis binders are typing variables with the scopes just listed: set-builder `w` ranges over phase space, indices `i,j` over `Fin n`, `k` over the entire integer lattice, and `u,v` over the entire phase vector space. Domain guards restrict w only; the final j in `hRη` remains universal after that guard. The `i` in the torus shift lambda is a coordinate index, not a new premise. There are no hidden positive-action, nonzero-dimension, frequency, nonresonance, twist, steepness, or existence assumptions.

Conclusion binders, in order: existential `T₁ : ℝ` after **all** inputs including w₀; `T < T₁`; existential total `z`; initial value; universal t in `Ioo (-T₁) T₁` for the ODE; universal set I and total curve y with interval/initial-value/solution guards for uniqueness; universal t with `|t|≤T`; universal j for the two estimates. These are outputs and comparison-solution guards, not additional assumptions of the theorem.

## Refutation attempts and nonvacuity

**NOTE N2 — no blocking counterexample found.** Evidence is `E:13-39,45-78`; relevant edge cases follow.

| Attempt | Result |
|---|---|
| Noninjective Ψ or arbitrary inverse values | Impossible on D: apply Ψinv to `Ψ w=Ψ v` and use `hΨinv` to obtain w=v. No right inverse on all V is required. Arbitrary values of Ψinv outside Ψ(D) cannot change the proved orbit. |
| A discontinuous/non-C¹ R | R can have discontinuous first derivatives, but must be differentiable at every point of open D. The flow uses the C² function **K=H∘Ψ**, not a separately differentiated nonsmooth N. Stopped drift needs bounded existing derivatives, not continuous DR. |
| Exploit `fderiv`=0 for nondifferentiable R | Fails: `hR` and openness imply `DifferentiableAt ℝ R w` throughout D, including the closed stopped region. |
| Exploit nonsmooth N to make the action drift uncontrolled | Fails: F=K−R is differentiable on D and equals the action-only expression there. Constant-angle lines (T) and exact rotations (E) cancel F without applying a chain rule to N. See proof analysis below. |
| `T=0` | Initial point is in D with positive margin; local ODE existence supplies T₁>0. Uniqueness still has its stated meaning. Bounds at t=0 reduce to identity and `hw₀`. No division by T is needed. |
| `η_j=0`, including η identically zero | Gives zero drift for those coordinates. Strict `a_j<b_j` survives. No division by η is needed; arbitrary finite T is allowed when all η vanish. |
| Zero oscillator actions | Coordinates remain Cartesian; at `(q_j,p_j)=(0,0)` both terms in the bracket vanish. This is not a singular polar boundary. |
| `n=0` | Phase space is a singleton. Index conditions are vacuous, but `hΨV` still puts its image in V; the unique curve and zero vector field satisfy the conclusion for any T₁>T. No `Nonempty (Fin n)` is needed. |
| Negative a or empty chart/stopped/physical domain | Given `hw₀`, nonnegativity of absolute values or sums of squares gives `0≤a_j`; `hT,hη,hmargin` give `0≤a_j<b_j`, hence b_j>0. Thus w₀ lies in the stopped region and D, and `hΨV` gives an initial point in V. Empty domains are impossible for an actual allowed initial point. If `hw₀` is impossible for some parameters, that conditional instance is vacuous, as expected. |
| Escape via unbounded lifted angles | K and X_K are periodic on D; compactness in actions gives uniform field and local ODE bounds across lattice cells. Finite-time angle blow-up is excluded. The whole cylinder is not claimed compact. |
| Escape at t=±T or failure just beyond T | Strict margin prevents exit up to T; compact/periodic continuation excludes a finite maximal endpoint at or before T. Openness then supplies a symmetric T₁>T. |
| A second solution leaves the chart but stays in V | `hH` gives a C¹ physical field on open V. Physical ODE uniqueness applies throughout the interval intersection, independently of chart membership of that other solution. |

Joint satisfiability is explicit, with moving nonconstant solutions, not merely a zero vector field:

* **Torus:** n=1, a=1, b=2, ε=1, η=0, any finite T≥0, V=univ, Ψ=Ψinv=id, `N(J)=J₀²/2`, R=0, `H(φ,J)=N(J)`, w₀=(0,1/2). Every premise holds. `z(t)=(t/2,1/2)` solves the equation globally, the initial action is nonzero, and all drift bounds are equalities at zero drift.
* **Oscillator:** the same parameters and maps, `N(J)=J₀`, R=0, `H(q,p)=(q₀²+p₀²)/2`, w₀=(1,0). Every premise holds. `z(t)=(cos t,-sin t)` is a nonconstant harmonic oscillator, with action 1/2. w₀=(0,0) also satisfies the same premises and demonstrates that zero actions are admitted.

These are mathematical witness verifications, not claims that a Lean proof of their whole premise conjunction was compiled.

## Signs, directions, and chart transport

**NOTE N3 — conventions match.** `SPEC.md:9-16`, `P:77-86`, and the frozen formulas cited above give

```
X_H = (∂₂H, -∂₁H),      ω(X_H,v) = -DH(v).
```

For B1-T, `(Pi.single j 1,0)` is the **angle** direction, while `(0,Pi.single j 1)` is the action direction. Consequently `J'_j=-D K(e_j,0)=-D R(e_j,0)`; the absolute value in `E:29-30` is correct. Using the second slot here would not control J drift. No period conversion or extra 2π belongs in the theorem's real derivative bound; applications must first convert their Fourier convention.

For B1-E, q=w.1 and p=w.2; the frozen action takes arguments p then q. Direct differentiation gives

```
DI_j(X_R) = q_j ∂_{p_j}R - p_j ∂_{q_j}R = {I_j,R}.
```

This is precisely `E:65-66`, with the positive first term in the p direction and the negative second term in the q direction. There is no missing factor 2: differentiating `(p_j²+q_j²)/2` yields p_j and q_j. It matches CL20 (32) after passage to real Cartesian coordinates and the agreed bracket convention. The outer absolute value would tolerate an overall sign reversal, but the documented sign itself is correct.

For transport (`SPEC.md:35-38`), fix w in open D and write A=DΨ(w). Nondegeneracy of ω and `hΨsymp` imply A is injective: if Au=0, then ω(u,v)=0 for every v. Because the source and target are the **same finite-dimensional space**, A is surjective too. The actual chain rule, justified by `hH,hΨ,hΨV`, gives `dK=dH∘A`. For every u,

```
ω(A X_K, A u) = ω(X_K,u) = -dK(u)
              = -dH(A u) = ω(X_H(Ψ w), A u).
```

Surjectivity and nondegeneracy imply `A X_K = X_H(Ψ w)`. Thus derivative symplecticity **with the stated differentiability and composition hypotheses** is sufficient. Symplecticity is not a substitute for that chain rule; no inverse derivative, unproved transport premise, or new flow-conjugacy hypothesis needs adding.

## OD-B2 and the other weakenings

Every removed plan premise gives a pure logical generalization: plan data can supply each retained premise, with the inverse extended arbitrarily off its image if needed. The weaker surface remains faithful to the claimed **chart-coordinate confinement**. It does not assert that H, V or Ψ descend to a physical torus quotient.

| Removed/changed premise | Assessment |
|---|---|
| V lattice-invariant (T) | Safe. Local physical existence/uniqueness uses open V and H C² only. Continuation is performed in the chart. `P:115` → OD-B2. |
| H periodic on V (T) | Safe. `hHΨ` and `hRper` imply K periodic on D. Physical periodicity is not used for the lifted physical ODE. `P:116` → OD-B2. |
| Ψ lattice-equivariant (T) | Safe for these conclusions. The periodic chart flow is transported pointwise. This does not recover quotient equivariance; a later geometric claim/application requiring it must supply it separately. `P:119` → OD-B2. |
| Onto an open image | Redundant as an explicit assumption: Ψ has invertible derivative everywhere on D, hence is locally open by the inverse function theorem. Together with the left inverse it is injective and is a diffeomorphism onto its open image. No surjectivity onto all V is intended. `P:117-118,177-178` → OD-B2/B3. |
| C² inverse | Redundant on Ψ(D), by the local C² inverse function theorem and injectivity. The supplied Ψinv agrees there with that inverse. Its arbitrary extension off Ψ(D) need not be regular. |
| N C² | Safe, **not generally derivable**. Only differentiability of the composition represented by K−R, and its invariance, are used. E need not extend a smooth N across the zero-action boundary. `P:122,178-179` → OD-B2. |
| R C² weakened to differentiable | Safe, **not generally derivable** in reverse. K is C² independently; the remainder needs existing derivatives for cancellation and the drift estimate. `P:123,179` → OD-B2. |
| `0≤a_j` | Redundant after `hw₀`, as shown above. Also `a_j<b_j` follows from `hT,hη,hmargin`. `P:110,176` → OD-B2. |
| `n≥1` | Safe generalization by singleton-space case. OD-B6. |
| Abstract open lifetime interval replaced by symmetric interval | Equivalent for this existential local finite-horizon purpose: an open interval containing compact [-T,T] contains some `(-T₁,T₁)` with T₁>T. OD-B4; `P:91-98`. |

**CHANGE-RECOMMENDED C1 — correct OD-B2's false regularity explanation.** `OWNER-DECISIONS.md:10` says: “N's and R's regularity follow on the chart domain.” Read as recovery of the dropped C² assumptions, this is false. For n=1 on the torus domain, take Ψ=id, H=0, `N(J)=|J₀|^(3/2)` and `R(φ,J)=-|J₀|^(3/2)`. Then K=0 is C∞, R is differentiable, angle-periodic and has zero angle derivative, so all relevant premises hold with η=0; neither N nor R is C² at J₀=0. For an oscillator example with the same failure for R, take `N(J)=|J₀|^(3/4)` and `R=-N∘I`: the composition is a constant multiple of the radial function `r^(3/2)`, differentiable but not C² at the origin, while K=0. Even regularity of N off the accessible action set cannot follow from a composition identity.

Exact replacement explanatory text for the last sentence of OD-B2:

> Symplecticity gives an invertible derivative, and the stated C² chart regularity gives a C² inverse on the chart image. K = H ∘ Ψ is C². Since R is differentiable on the open chart domain, K − R is differentiable there and equals the action-only normal part. Its angle or rotation invariance supplies the cancellation needed for drift; neither C² regularity of R nor C² regularity of N is asserted or needed.

No mathematical Lean binder or conclusion replacement is recommended. For an exact Lean-text amendment accompanying this documentation correction, replace the two theorem docstrings (`F:24`, `F:54-56`; respectively `E:12`, `E:42-44`) with these complete docstrings, leaving both command types unchanged:

```lean
/-- **B1-T** (plan §2.2; GLS17 §4.3 (56)–(58)): finite confinement in a canonical cylinder.
The physical phase coordinates are lifted real coordinates. Only the pullback Hamiltonian
must be angle-periodic. The normal part is differentiated through `H ∘ Ψ - R`, which is
differentiable on the open chart domain; no differentiability hypothesis on `N` is needed. -/
```

```lean
/-- **B1-E** (plan §2.3; CL20 §4.1 (32)–(37)): Cartesian oscillator confinement,
including zero actions. Coordinates are `w = (q, p)`, with action
`KAM.Planetary.oscillatorAction w.2 w.1`, so `I_j = (p_j² + q_j²) / 2` and
`{I_j, R} = q_j ∂_{p_j} R - p_j ∂_{q_j} R`. Rotation invariance of the differentiable
function `H ∘ Ψ - R` gives the normal-part cancellation without differentiating `N`. -/
```

These are explanatory comment replacements only, not added hypotheses or changed propositions. The proof architecture in `SPEC.md:35-44` is otherwise sound if implemented as written.

## Lifetime, uniqueness, and complete conclusions

**NOTE N4 — quantifiers and endpoint scope pass.** `E:32-39,69-78` matches `P:91-98` and `SPEC.md:27-31`:

* All input data, including w₀, precede T₁ and z; no common uniform lifetime beyond the requested T is claimed.
* `hT` and `T<T₁` imply T₁>0 and `[-T,T] ⊆ Ioo (-T₁) T₁`. The ODE and V membership therefore hold at both endpoints, and slightly beyond them.
* The comparison clause ranges over **every** order-connected I containing 0 and **every** total y satisfying the ODE and V membership on I. It asserts equality at each point of `I ∩ Ioo (-T₁) T₁`. Closed, half-open, unbounded and singleton intervals are covered; no openness assumption on I or membership of y in the chart image is hidden.
* There is no `∃!` over total functions and no restriction on values outside the solution interval. Ordinary `HasDerivAt` at an included endpoint agrees with the plan's explicit convention. If a later API uses only `HasDerivWithinAt`, an endpoint-extension lemma may be needed; that does not invalidate this statement.

**NOTE N5 — all displayed confinement content is carried, some by immediate consequence.** The inverse-image clause is meaningful jointly with the bounds, not just a bare fixed-point equation. Write v=Ψinv(z t). In T the output bounds imply `|v.2 j|≤a_j+η_j*T<b_j`; in E they imply `I_j(v)≤a_j+η_j*T<b_j`. Hence v∈D and v is in the open stopped region. The output `Ψ v=z t` then identifies z t with a point of Ψ(D); the input left inverse makes v the unique chart point. At t=0 it yields v=w₀. Thus the drift measured from w₀ is precisely the drift from the initial inverse chart coordinates.

The final strict inequalities in (B1-T)/(B1-E) are consequences of `hmargin` after commuting `T*η_j` with `η_j*T`. The lower bound `0≤I_j(v)` follows from the frozen sum-of-squares formula. Neither needs another hypothesis or a frozen helper. The full chains in `P:132-135,189-192`, and membership in `C_b`/`E_b`, therefore follow from the returned conjunction. It is acceptable that these redundant consequences are not separately printed in the type. The observable-transfer formula is deliberately internal (`P:143-155,201,209-214`), not a missing anchor conclusion. There is no claimed confinement of arbitrary original actions or a user-specified physical box without the separate chart/observable transfer.

## Provability from precisely these premises

1. **Open domain and regular field.** Both D set-builders are finite intersections of strict sublevel sets of continuous functions. `hH,hΨ,hΨV` give K=H∘Ψ C² on D, hence X_K C¹. The physical X_H is C¹ on V. Existing API evidence: `KAM/ODE/Hamiltonian.lean:42-62` (`ham_smooth`, `ham_smooth_c1`), `KAM/ODE/Maximal.lean:331` (`gen_maximal`). No C¹/C² assumption on R enters local existence or uniqueness.
2. **Normal cancellation in T.** F=K−R is differentiable on D and locally equals `w ↦ N w.2`. The line `w+s(e_j,0)` remains in D and F is constant on it. Differentiate this constant curve at 0 to get `DF(e_j,0)=0`. Then `DK(e_j,0)=DR(e_j,0)` and the chart action derivative is its negative.
3. **Normal cancellation in E, including zero.** F=K−R is differentiable on D and equals N∘I. Rotate just the j-th coordinate plane by `q_j(s)=q_j cos s−p_j sin s`, `p_j(s)=q_j sin s+p_j cos s`; other coordinates are fixed. Every action, and hence D and F, is unchanged for every s. The tangent at 0 is `(-p_j e_j,q_j e_j)`. Differentiating F along this exact curve gives `-p_j ∂_{q_j}F+q_j ∂_{p_j}F=0`, which is exactly `{I_j,F}=0`. If q_j=p_j=0 the tangent and bracket are both zero. This argument never differentiates N and needs no smooth action-space extension at the boundary. A chain-rule proof through `fderiv N` without proving its applicability would be a provider error, not a defect of the stated theorem.
4. **Stopped drift and first exit.** On any stretch inside the closed stopped region, `hRη` bounds each observable derivative in absolute value. The real mean-value estimate gives drift ≤η_j|t| without requiring continuity of DR. The initial bounds and strict margin put any candidate exit point strictly inside the stopped region. Apply this to both time directions and to each finite segment of the maximal interval. Do not assume a trajectory at a maximal endpoint not yet known to exist.
5. **Continuation in E.** The closed product of oscillator disks is closed and bounded in the finite-dimensional phase space, hence compact. It lies inside D because ε>0. Under the contradictory assumption that a maximal endpoint is ≤T (or ≥−T), first-exit bounds apply all the way up to that endpoint. `KAM/ODE/Continuation.lean:132-140` then excludes it.
6. **Continuation in T.** `hHΨ,hRper` imply K periodic on D, since the domain and normal part are translation-invariant. Differentiating the local translation identity gives periodic X_K there, even if the total extensions outside D are not periodic. The closed action box is compact and lies in the enlarged open action box. Uniform C¹ ODE data on a fundamental cell transfer by lattice shifts, so bounded actions preclude a finite maximal endpoint. This is precisely the premise shape of `KAM/ODE/UniformPeriodic.lean:35-40` and `KAM/ODE/Continuation.lean:192-207`. **R periodic is sufficient in combination with the retained normal-form identity and K C²**; periodic R alone, without that identity and regularity, would not be sufficient. No periodicity of physical H, Ψ, or Ψinv is needed.
7. **Transport, inverse, and physical uniqueness.** Transport as derived above. On the required interval, `hΨinv` identifies the inverse chart of z with the constructed chart trajectory. C¹ regularity of X_H on open V supplies comparison with every physical solution; `KAM/ODE/Uniqueness.lean:80-85` has precisely the order-connected intersection shape needed.

This is a mathematical sufficiency check and API-shape inspection, not a review or approval of any B1 proof implementation. Term-level composition/consumer closure is not claimed.

## Checks, axioms, scope, and handoff

The exact scratch command was copied from E to `/tmp/maud-b-stmt-1.lean`, with only five `#print axioms` commands appended. From `/root/code/KAM-inp-b1`, executed one Lean process at a time:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean /tmp/maud-b-stmt-1.lean
```

Exit **0**, exact relevant output:

```text
/tmp/maud-b-stmt-1.lean:13:8: warning: declaration uses `sorry`
/tmp/maud-b-stmt-1.lean:45:8: warning: declaration uses `sorry`
'KAM.EffectiveStability.torus_confinement' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscillator_confinement' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.symplecticForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscillatorAction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No proof promotion follows from this output. No heartbeat, recursion, synthesis or other resource-budget override was used. No library build was necessary: no Lean module was edited, and the user requested an exact scratch elaboration against the existing snapshot, not rebuilding either implementation or a library. Targeted verification was the command above. Temporary Lean files are removed after checks.

Source lint was invoked as `PATH=/tmp/maud-b-stmt-1-bin:$PATH scripts/lint_sources.sh`. The temporary Python launcher preserves all lint checks and ABI comparisons, disables Python bytecode writes, and makes exactly two in-memory substitutions for the ABI script: move its scratch directory from `.lake/abi-scratch` to `/tmp/maud-b-stmt-1-abi`, and wrap its `lake env lean` subprocess in the exact required systemd/nice/thread command above. This permits the actual lint to run while respecting the report-only repository-write restriction and the D53 resource rule. No repository script was edited. Final receipt follows below.

Lint exit **0**, output:

```text
check_lean_modules: PASS (4483 Lean files, 0 comparator configurations)
.........................
----------------------------------------------------------------------
Ran 25 tests in 3.917s

OK
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (314 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The ABI run is scoped to the default core declarations; application exports were checked by file hash only, as its output says. No certificate application was built. The exact statement elaboration and the ABI Lean subprocess were sequential and both used the specified 4 GB / no-swap / nice-10 / single-thread wrapper.

**Suspected errata and deviations:** no new suspected defect in CL20 §4.1 (32)-(37) or GLS17 §4.3 (56)-(58) was found. GLS17's quoted “kept just the first term” is an acknowledged approximation, not an input to this theorem. The other plan §9 findings (`P:974-989`, carried in `F:145-154`) are outside these anchors and were not independently re-audited here. The local explanatory defect C1 is reported for the orchestrator, not silently repaired. Retained deviations from the paper estimates are those openly listed in `P:157-163,195-205,991-995` and `F:156-160`: finite C² chart/physical regularity, differentiable remainder, arbitrary action-only N, anisotropic closed initial levels, strict outer margins, explicit physical existence/uniqueness and endpoints, zero actions, and the recorded minimal-surface generalizations. No extra deviation or replacement mathematical premise was introduced by this review.

**Handoff:** file changed: `docs/tracks/B/freeze/STATEMENT-REVIEW-1.md` only. Approach: exact-byte pinning, raw-source reconstruction, expanded binder classification, counterexample attempts, explicit nontrivial models, derivative/sign/quantifier analysis, and capped exact-command elaboration plus source/manifest/ABI checks. Uncertainty: this audit supplies mathematical sufficiency arguments, not completed Lean proofs of the two anchors or of the entire architecture; those proofs and their consumer use need independent review after implementation. Exact-text owner approval and manifestation remain pending. Recommended action: correct C1's explanatory sentence and optionally use the supplied docstrings; retain both mathematical statement types.

**Overall verdict: PASS WITH NOTES.** No BLOCKING findings; one CHANGE-RECOMMENDED documentation finding (C1); N1-N5 record scope and semantic notes.

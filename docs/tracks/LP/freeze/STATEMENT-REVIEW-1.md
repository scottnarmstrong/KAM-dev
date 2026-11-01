# Independent LP statement review 1

Date: 2026-11-01. Reviewer: independent, refute-first; no authorship of the proposed declarations. Only this report was written in the repository. No subagents were used. Method: `/root/.claude/skills/lean-statement-audit/SKILL.md`, read in full, with the user's explicit pre-freeze target and no-delegation instruction taking precedence over the skill's manifest-only workflow.

## Verdict and scope

**RETURN FOR REVISION of the proposed freeze package.** The displayed LP0 and LP1 hypotheses, physical formulas, arithmetic, uniformity, and no-crossing/no-collision inequalities are sound statement translations on their guarded domains. Calling the osculating annuli **ellipses** additionally requires their validity, addressed in F2. There is no discovered false theorem statement and no EXCESS/conclusion-shaped premise. There are, however, source-scope omissions and definition-carrier issues that must not be concealed by a successful elaboration.

| Object | Declaration fidelity assessment | Proof/freeze status |
|---|---|---|
| LP0, the physical distance/annulus projection of L5 | PASS for that projection; **not the full L5** (F1) | PROPOSED_UNFROZEN; current proof text is `sorry` |
| LP1, T15's quantitative common conclusion §1 (6)–(9), under the overnight conventions | PASS for the inequalities actually displayed; no source hypothesis dropped; full osculating ellipse certification needs F2 | PROPOSED_UNFROZEN; current proof text is `sorry` |
| LP1 interpreted as exporting all of L16 | FAIL: first estimate of (43) is absent (F2); ellipse validity/tangency are not explicitly exported | No claim of L16 closure is justified by this proposed anchor alone |
| Proposed definition freeze inventory, proposal:21–29 | **BLOCKING** for a claim of source objects on their entire public carriers (F3–F4) | Carrier interfaces/semantic units must be fixed or explicitly scoped before manifestation |

For the requested source-complete L5 + T15 + L16 reading: `DECLARATION_FIDELITY: FAIL`. For the narrower projections above, fidelity is as specified in the table. `DRAFT_ALLOWLIST: N/A_UNFROZEN`; `PROOF_STATUS: PROPOSED_UNFROZEN`. These are not manifest-bound DRAFT_SORRY declarations, hence are not literally FROZEN_UNPROVED. If frozen with the approved statements and allowed proof holes, their status would be FROZEN_UNPROVED, never PROVED on this evidence.

## Exact objects and identity

All unqualified paths below are relative to `/root/code/KAM-inp-lp`. Implementation citations also hold in `/root/code/KAM-inp-lp-thr`: 91 StrongAMD/frozen-planetary-definition files present in the review checkout were compared byte-for-byte with the build checkout, with **zero differences**. Review HEAD: `c29da0781f87196ddacb71cf5de711da86f709be`; build-checkout HEAD at the check: `a290ce18af2f4ef6e37110c1875e04e201eb2472`. Conclusions attach to the bytes below, not to either branch's later state.

The exact LP0 command is `FREEZE-PROPOSAL.md:34–46`, identical to `freeze/elaboration-draft-1.lean.txt:24–36`; LP1 is proposal:57–96, identical to draft:39–78. Equality was checked including command text after stripping only surrounding whitespace. Fully qualified temporary exports are `KAM.Planetary.StrongAMD.Proposal.planar_strongAMD_barrier` and `.planar_strongAMD_exponentialSafety`; implicit `{n : ℕ}` comes from draft:17. The `ecc` abbreviation needed to interpret the Markdown text is draft:19–21, not a different eccentricity convention.

| Evidence | SHA-256 |
|---|---|
| `docs/tracks/LP/FREEZE-PROPOSAL.md` | `d5c7b674e61d8c8a0fbe8035fc55fd80c32fbbf8c7fe1227066d8b3b7fa06db5` |
| `docs/tracks/LP/freeze/elaboration-draft-1.lean.txt` | `bf06b234dcf8c543df79874f071e3a3c327dc73fcd3ec279892b6420e84d028c` |
| LP0 command, surrounding whitespace stripped | `36249d80bac8961c066a4dbc0426b2ed2a3a76b6027daca2633a22edc6ad8910` |
| LP1 command, surrounding whitespace stripped | `510e57c74d37475fdc7e238a13a1d7a6f72967a1db9f8e7a28c38960ecf987dc` |
| `docs/tracks/LP/source/MAIN.md` | `68e9167f04e4a04689ea163c74e02ffcaea657b252726080abdbe37bdba48c1b` |
| `docs/tracks/LP/source/AMENDMENTS.md` | `c887d1e27354a3db7fb8a20d8bf3e33a9ef95ff3173f925ba5ebfab192651881` |
| `docs/tracks/LP/OWNER-DECISIONS.md` | `49638e82262e0891d2d77c12199a4560d34f62c94466dcadcc95661f8c4f194b` |
| `docs/tracks/LP/SPEC.md` | `ffd8a2793b9b37ca35e4a626d38d9af3c2f79d5cefa7c36e5e2aa844978dad22` |

There are **zero** manifest entries naming `planar_strongAMD`; no versioned LP0/LP1 anchor ID, frozen path, approval, or registered provider export exists to certify. This agrees with proposal:3 and OD-7 (owner file:15). A Markdown proposal cannot be promoted to a frozen export. All 67 existing frozen planetary definition whole-file hashes were independently recomputed against their manifest records: no mismatch. Source revision here is the pinned local MAIN plus normative amendments, not an independently identified external manuscript revision.

## Independent reconstruction

MAIN:11–15 fixes `n ≥ 2`, positive normalized masses, compact ordered positive axes (empty allowed), positive δ and γ, and `τ > n−1`. MAIN:17–39 fixes G = stellar mass = 1, actual planet masses μν, canonical scaled p, physical time, and orientation-free C = ΣI − |L|. MAIN:41–55 defines B only on the action chamber, using attained pair minima and nonempty finite minima. MAIN:57–67 uses radian frequencies ν³/I³ and ℓ¹ integer mode size. MAIN:69–93 chooses eight positive constants before μ and every initial state, and exports the common T15 conclusion. L5:164 has an additional abstract eccentricity-list assertion, compact containment and invariable-frame angular momentum bounds. L16:510–529 defines the actual-velocity ellipse and contains both estimates of (43), nondegeneracy, incidence and tangency.

N1–N12 were read as normative (`source/AMENDMENTS.md:8–21`). N8 fixes the AMD convention issue, N10 fixes the small-μ ordering, N11 fixes the order in which the star-distance/momentum bounds are obtained. N2–N7 concern proof internals; they do not license any extra anchor premise. N9 and N12 do not change these planar statement types. OD-1–OD-9 are overnight defaults/open decisions, not fabricated final owner approvals (owner file:3–5,9–17).

## Five-bin input audit

One row below records each outer input or each independently meaningful component of a bundled input. Index binders internal to such a component are spelled out in the row; they are not additional analytical assumptions. SOURCE means a premise of this lemma; STANDING means the fixed physical data of §1; TYPING includes source-carrier membership used as a dependent proof argument. There are no instance/typeclass input binders. Existential outputs and conclusion-local universals are inventoried separately, to avoid counting a conclusion as a hypothesis.

### LP0 inputs (draft:17,24–30)

| Binder / expanded logical component | Bin | Evidence / assessment |
|---|---|---|
| implicit `n : ℕ` | TYPING | MAIN:11; number of planets |
| `hn : 2 ≤ n` | STANDING | MAIN:11; adjacent index family nonempty |
| `ν : Fin n → ℝ` | STANDING | MAIN:11; fixed masses |
| `hν`, with `∀ i : Fin n, 0 < ν i` | STANDING | MAIN:11 |
| `U : Set (Fin n → ℝ)` | SOURCE | L5:164 |
| `hU : IsCompact U` | SOURCE | L5:164; no nonemptiness assumption |
| `hUch`, positivity component `∀ I ∈ U, ∀ i, 0 < I i` | SOURCE | L5:164; chamber MAIN:43 |
| `hUch`, order component `∀ I ∈ U, ∀ i j, i < j → (I i/ν i)^2 < (I j/ν j)^2` | SOURCE | MAIN:43–45; Threshold/Defs:33–34 |
| `m : ℝ` | SOURCE | L5:164; fixed margin |
| `hm : 0 < m` | SOURCE | L5:164 |
| `z : Phase (n*2)` under `∀` | TYPING | arbitrary planar state; MAIN:15,26–37 |
| state premise, `∀ i, 0 < planeLength (bodyVector z.1 i)` | STANDING | nonsingular domain MAIN:24; §1 initial condition MAIN:70 |
| state premise, `∀ i, keplerEnergy ν z i < 0` | SOURCE | L5:164; positive ν converts total to specific energy |
| `hΛ : (fun i => keplerAction ν z i) ∈ U` | SOURCE | L5:164; chamber proof supplied by `hUch hΛ` |
| AMD inequality `strongAMD ν z ≤ orderedStrongThreshold hn ⟨_,hUch hΛ⟩ - m` | SOURCE | L5:164, MAIN:35,53 |

Counts of table components: SOURCE 9, STANDING 4, TYPING 2, RULED 0, EXCESS 0. No hidden dynamics, prograde restriction, pair-separation premise, eccentricity bound, threshold witness, supplier estimate, or compact-safe-set premise occurs. These are derived results, not inputs. Omitting `max ν = 1` in this static lemma is a homogeneous extension in fixed ν; there is no μ here to reinterpret.

### LP1 inputs (draft:17,39–54)

| Binder / expanded logical component | Bin | Evidence / assessment |
|---|---|---|
| implicit `n : ℕ` | TYPING | MAIN:11 |
| `hn : 2 ≤ n` | STANDING | MAIN:11 |
| `ν : Fin n → ℝ` | STANDING | MAIN:11 |
| `hν : ∀ i, 0 < ν i` | STANDING | MAIN:11 |
| `hνmax : ∃ i : Fin n, ν i = 1` | STANDING | MAIN:11; attained normalized maximum |
| `hνle : ∀ i, ν i ≤ 1` | STANDING | MAIN:11; together exactly max ν = 1 |
| `A : Set (Fin n → ℝ)` | STANDING | MAIN:12–14 |
| `hA : IsCompact A` | STANDING | MAIN:11–15; empty A allowed |
| `hAord`, `∀ a, a ∈ A → ∀ i, 0 < a i` | STANDING | MAIN:13 |
| `hAord`, `∀ a, a ∈ A → ∀ i j, i < j → a i < a j` | STANDING | MAIN:13 |
| `δ : ℝ` | STANDING | MAIN:15 |
| `γ : ℝ` | STANDING | MAIN:15 |
| `τ : ℝ` | STANDING | MAIN:15 |
| `hδ : 0 < δ` | STANDING | MAIN:15 |
| `hγ : 0 < γ` | STANDING | MAIN:15 |
| `hτ : (n : ℝ)-1 < τ` | STANDING | MAIN:15 |
| `μ : ℝ` | SOURCE | MAIN:70; varies after all constants |
| anonymous `0 < μ` | SOURCE | MAIN:70 |
| anonymous `μ ≤ μ₀` | SOURCE | MAIN:70 |
| `z₀ : Phase (n*2)` | TYPING | arbitrary planar initial data |
| state premise, `∀ i, 0 < planeLength (bodyVector z₀.1 i)` | SOURCE | MAIN:70 |
| state premise, `∀ i, keplerEnergy ν z₀ i < 0` | SOURCE | MAIN:70; equals ν_i E_i |
| axes membership `(fun i => keplerAxis ν z₀ i) ∈ A` | SOURCE | MAIN:72 (6) |
| Diophantine premise, `∀ k : Fin n → ℤ, k ≠ 0 → γ |k|₁^(-τ) ≤ |Σ k_i ν_i³/I_i³|` | SOURCE | MAIN:64–65 (5); k/hk are internal universal index/side condition |
| `hch`, positivity component `∀ i, 0 < keplerAction ν z₀ i` | TYPING | MAIN:31–34,43; follows from positive ν and negative energy |
| `hch`, axes-order component of chamber | TYPING | MAIN:43–45; follows from axes ∈ A, hAord, and `(I_i/ν_i)^2 = a_i` |
| AMD inequality `strongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_,hch⟩ - δ` | SOURCE | MAIN:72 (6) |

Counts: SOURCE 8, STANDING 15, TYPING 4, RULED 0, EXCESS 0. All mathematical logical inputs were expanded; `IsCompact` is Mathlib compactness, not a project-owned result bundle. No premise concerning the secular average, a normal form, a chart lift, a chosen torus, continuation, or stopped drift is present.

The dependent `∀ hch` does not restrict the family of initial data: its proposition follows from the preceding inputs. `Geometry.lean:66–75` proves `actionAxis_actionVector`, and `Orbital.lean:78–84`/`orbital_identities` supply positivity. A consumer still has to construct this proof argument; proposal:114–115 should not be read as saying Lean supplies it automatically. Proof irrelevance makes the B value independent of that proof. Likewise `∃ hcht` at time t is a conclusion asserting chamber membership, not a concealed premise.

### Outputs, binders and quantifier order

LP0 has `∃ dStar dPair`, their positivity, then `∀ z`; it chooses bounds using only `(n,ν,U,m)`. Its output universals are `i : Fin n` for perihelia/star distances, `a : AdjIdx n` (expanded `{i : Fin n // i.val+1<n}`) for adjacent annuli, and `i j : Fin n, i ≠ j` for all pairs. The internal subtype proof is typing data, not a separation assumption.

LP1 has `∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc`, eight positivity conclusions, then `∀ μ`, its range guards, then `∀ z₀` and the initial-data guards, then the let-bound T, then `∃ z`. The solution-output conjunction includes `z 0 = z₀`, solutionhood, local overlap uniqueness and Newtonian reconstruction. The time universal is `∀ t : ℝ, t ∈ Icc (-T) T`; the state conclusion has `∃ hcht` and the same `i`, `a`, and `i j/hij` output indexing as LP0. Thus **all constants precede μ, positions, momenta, phases, eccentricities, orientations and secular states**. They may depend on `(d=2,n,ν,A,δ,γ,τ)` only. Theorems do not promise uniformity over ν, γ or A. The norm of `Fin n → ℝ` is the Pi maximum norm (SPEC:33), not Euclidean length.

`MovingUniqueOn` expands to `∀ U w, IsOpen U → Convex ℝ U → 0 ∈ U → w 0 = z 0 → IsMovingSolutionOn ν μ U w → ∀ t ∈ U ∩ J, w t = z t` (`Frozen/Planetary/Defs/MovingUniqueOn.lean:37–40`). Its U, w, local-solution guards and t belong to the **conclusion**, not the anchor hypotheses. This states agreement on every interval overlap with 0. It expresses the finite-interval restriction of the unique maximal physical solution; no separately named maximal-domain object is exported. This is the repository convention explicitly chosen in proposal:126–127, not a new global-flow premise.

## Meaning-carrying definitions

### Literal formulas and physical conventions

| Definition / complete body checked | Evidence | Result |
|---|---|---|
| `Phase`, `bodyVector` | frozen Defs/Phase:37; BodyVector:37–38 | pairs of real Pi vectors; Cartesian two-coordinate blocks |
| `planeSq`, `planeLength`, `planeDot`, `planeCross` | frozen corresponding files:37,38,37,35 | Σv², √Σv², Σvw, oriented determinant; no Pi-norm substitution |
| `totalMomentum`, `strongAMD` | frozen TotalMomentum:36–37; Momentum:41–42 | Σ q×p, then ΣΛ **minus absolute value** of that sum, not Σ|L_i| and not signed `physicalAMD` |
| `keplerEnergy`, `keplerAxis`, `keplerAction` | frozen files:35–36,36–37,36–37 | total energy ν_i E_i, `-ν_i/(2 totalEnergy) = -1/(2E_i)`, then ν_i√a_i |
| `keplerEccVector`, proposal `ecc` | frozen KeplerEccVector:35–40; draft:19–21 | `(p²/ν²−1/r)q−(q·p/ν²)p`, Euclidean vector length; matches MAIN:28–35 |
| `keplerPeri`, `keplerApo` | Osculating/Basic:75–81 | a(1−e), a(1+e), with canonical parameter **one** |
| `oscVelocity`, `oscParam` | Osculating/Basic:41–46 | `p_i/ν_i + μ Σp_j`, **`1 + μ ν_i`**, not 1 and not 1+μΣν |
| `oscEnergy`, `oscAxis`, `oscEccVector`, `oscEcc` | Osculating/Basic:48–65 | all of (42), including division of the **whole** eccentricity vector by k_i |
| `oscPeri`, `oscApo` | Osculating/Basic:67–73 | a_osc(1−e_osc), a_osc(1+e_osc) |
| `modeSize` | Fourier/Derivative:37 | `Σ j, |(k j : ℝ)|`; real-valued ℓ¹ size already, not max norm |

Every displayed body is the literal formula, with no selected orbit, finite optimizer, `if`, `dite`, hand-chosen minimizer or invented correction term. `strongAMD_eq_physicalAMD` (Momentum:179–182) is guarded by nonnegative L; that bridge is not used to silently change the anchor premise. Reflection remains a proof tool, not an extra prograde input (MAIN:506, N8).

**Whole-carrier qualification:** literal formula equality everywhere is not physical-object identity everywhere. The already frozen canonical formulas are total Lean expressions with guarded physical interpretation (e.g. `KeplerAxis.lean:35` explicitly says this). These inherited total definitions were not changed. In the new proposed freeze list, `strongAMD`, `keplerPeri/Apo`, and the osc ellipse expressions also accept phases outside the source's domain; F4 records this explicitly. In particular `oscAxis` accepts E_osc = 0 and k = 0, which are not nondegenerate ellipses. The current anchor's canonical inputs are guarded, and its positive perihelion/half-gap conclusions do not assert that every arbitrary phase defines an ellipse. A whole-carrier **source-object** certification of these total new exports would nevertheless be incorrect.

Arithmetic and time are exact: LP1 uses `ν_i^3 / keplerAction_i^3` and `γ * modeSize k ^ (-τ)` with all nonzero integer k, no 2π factor, and `T₀ * exp (c * μ ^ (-(1/(2*(τ+1)))))`. Here μ>0, τ>n−1 and n≥2 remove sign/zero ambiguities for real powers. The interval is closed `[-T,T]` in physical time. The period-one normal-form conversion has not contaminated the source-facing Diophantine condition or time exponent (MAIN:64–76; draft:50–55).

### Threshold semantic unit

`Threshold/Defs.lean:30–50` gives a_i=(I_i/ν_i)^2, D(u)=1−√(1−u²), the entire [0,1]² feasible set with the correct crossing inequality, objective I_iD(u)+I_jD(v), and the objective-image sInf. `OrderedActions` is exactly the chamber subtype (:73–74), not a set of selected minimizers. `orderedPairThreshold` enforces i<j (:78–79). `orderedStrongThreshold` enforces n≥2 (:86–87). LP0 and LP1 feed actual chamber proofs to this interface, so neither anchor evaluates B off its source carrier.

The sInf is **not** an arbitrary minimizer: `Threshold/Pair.lean:68–84` proves compactness and nonemptiness of the entire feasible set; :87–101 proves `IsLeast` and attainment, even for the internal total helper. The scalar minimum value is unique; minimizers in (u,v) need not be unique and are not chosen. `Threshold/Strong.lean:51–87` proves ≤ each member and equality with a member for star/cross/strong finite minima under their nonempty index guards. :148–172 provides carrier positivity, continuity and the min-first specialization. These proofs are sorry-free in the checked axiom closure. An ordered `IsLeast`/unique-value export should accompany the source carrier interface at freeze time (F3 gives exact text).

For the chamber-restricted pair/strong threshold unit (fixed positive ν and hn for the strong threshold), the verdicts are:

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: OK
CHARACTERIZATION: OK
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

Well-definedness here is the attained unique scalar minimum, and characterization is the checked definitional application of `pairThreshold_isLeast`; no minimizer is chosen. For the proposed **unrestricted** raw cross/star exports and `orderedCrossThreshold` without hn:

```text
BODY_MATCH: OK_ON_SOURCE_INPUTS
PUBLIC_CARRIER: FAIL
WELL_DEFINEDNESS: FAIL_AS_SOURCE_NONEMPTY_MINIMUM_ON_FULL_CARRIER
CHARACTERIZATION: FAIL_AS_SOURCE_OBJECT_ON_FULL_CARRIER
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: FAIL
```

F3 must be resolved before calling the entire listed inventory source-faithful.

### Dynamics and reconstruction (expanded, no hidden gates)

`IsMovingSolutionOn` is differentiability-guarded Hamiltonian solutionhood plus `∀ t∈J, NoCollision (z t).1` (frozen file:35–38). `KAM.Iso.IsHamiltonianSolutionOn:37–41` expands to action membership (here `Set.univ`), differentiability of H and `HasDerivAt z (hamiltonianVectorField H ...)` at each t. The field is `(∂p H,−∂q H)` (`Frozen/Defs/HamiltonianVectorField:24–26`). `movingHamiltonian 1 1 ν μ` (frozen MovingHamiltonian:44–50) contains both μΣ|p_i|²/2 and μΣ_{i<j}p_i·p_j, together equal μ|Σp_i|²/2; the direct pair potential has the correct minus sign. It is (1), not the fixed-Sun Hamiltonian.

`NoCollision` expands to positive star lengths and every unequal pair length (frozen file:39–41). `actualMasses 1 ν μ = Fin.cons 1 (μν)` (ActualMasses:37–38). `barycentricPositions` uses `x₀=−μΣν_iq_i/(1+μΣν_i)` and Q_i=x₀+q_i (file:39–42); `barycentricVelocities` uses V₀=−μΣp_i and V_i=p_i/ν_i (file:38–41). Thus relative velocity is exactly oscVelocity. `IsNewtonSolutionOn:36–42` asserts all actual unequal-body distances are positive, Q'=V, and V'_i=Σ_{j≠i}m_j(Q_j−Q_i)/|Q_j−Q_i|³. None of these aliases assumes the desired result in the input telescope. The differentiated barycentric positions/velocities are the conclusion to prove.

## Findings and exact replacements

### F1 — BLOCKING for full-L5 fidelity: LP0 is a projection, not the whole L5

Evidence: MAIN:164 says "The same holds for every list e∈[0,1]^n" and "All these states belong to a compact subset ... and satisfy H_i ≥ m in their invariable frame." Draft:24–36 only exports four geometric inequalities. Its source premises are correct and its conclusion is valid, but calling it the full L5 or a direct restatement of `strongBarrier_physical` omits that theorem's `DeficitBarrier`, R/P/energy and angular-momentum outputs (`Geometry.lean:253–267`) and compact-containment result (:426–429). Bounds on momenta and negative energy are consequences available from U and the perihelion floor, but are not exported by LP0 as written.

Recommended source-complete replacement below retains the original bounds and adds the abstract e-list statement, compact physical containment with energies bounded away from zero by compactness, and the orientation-free expression of H_i≥m. The sign-product clause ensures every individual angular momentum has total L's sign; together with |L_i|≥m this is precisely the planar invariable-frame conclusion. It adds **outputs**, no new premises. This is a recommendation to the owner, not an edit to the audited text.

```lean
theorem planar_strongAMD_barrier (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (U : Set (Fin n → ℝ)) (hU : IsCompact U) (hUch : U ⊆ chamber ν) (m : ℝ) (hm : 0 < m) :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
      (∀ I : Fin n → ℝ, ∀ hI : I ∈ U, ∀ e : Fin n → ℝ,
        (∀ i, e i ∈ Set.Icc (0 : ℝ) 1) →
        (∑ i, I i * eccDeficit (e i)) ≤ orderedStrongThreshold hn ⟨I, hUch hI⟩ - m →
        (∀ i, dStar ≤ actionAxis ν I i * (1 - e i)) ∧
        (∀ a : AdjIdx n, dPair ≤ actionAxis ν I a.upperIdx * (1 - e a.upperIdx) -
          actionAxis ν I a.1 * (1 + e a.1))) ∧
      ∃ K : Set (Phase (n * 2)), IsCompact K ∧
        (∀ w ∈ K, NoCollision w.1 ∧ ∀ i, keplerEnergy ν w i < 0) ∧
      ∀ z : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0) →
        ∀ hΛ : (fun i => keplerAction ν z i) ∈ U,
        strongAMD ν z ≤ orderedStrongThreshold hn ⟨_, hUch hΛ⟩ - m →
        (∀ i, dStar ≤ keplerAxis ν z i * (1 - ecc ν z i)) ∧
        (∀ a : AdjIdx n, dPair ≤ keplerAxis ν z a.upperIdx * (1 - ecc ν z a.upperIdx) -
            keplerAxis ν z a.1 * (1 + ecc ν z a.1)) ∧
        (∀ i, dStar ≤ planeLength (bodyVector z.1 i)) ∧
        (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j)) ∧
        z ∈ K ∧
        (∀ i, m ≤ |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| ∧
          0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i) * totalMomentum z) := by
  sorry
```

### F2 — BLOCKING for full-L16 fidelity: missing estimate and explicit ellipse validity

LP1 includes every quantitative conclusion of (8)–(9) and the endpoint-error/half-gap part of MAIN:91. It omits L16:522's **sum of axis error and Euclidean eccentricity-vector error**. Scalar peri/apo errors do not, as scalar errors alone, bound the direction of the eccentricity vector. A proof of that additional estimate exists as an ingredient (`Osculating.lean:48–55,268–276`), but an ingredient is not an exported anchor conclusion. Add a positive `Aelem` **before μ and z₀**, and export that sum bound.

Nondegenerate canonical ellipticity is not a genuine logical omission: negative energy gives a>0, and `a(1−e)≥dStar>0` gives e<1. For the actual elements, positive oscPeri alone does **not** imply ellipticity: hyperbolic elements have a<0 and e>1 and hence a(1−e)>0 too. An explicit oscEnergy<0/oscEcc<1 conclusion, or an actual derivation using a certified smallness bound, is required before calling these expressions osculating **ellipses**. Incidence/tangency and q'=oscVelocity follow on the valid locus from the definitions, the actual ODE and the orbital identities; radial incidence inequalities alone are not a separate proof of geometric tangency. F2 makes validity explicit. No separate ellipse parametrization or two-body flow is exported by the original proposal.

The following exact replacement keeps the current normalized-mass version and strengthens the outputs to include L16's first estimate, explicit ellipse validity and radial incidence. It also displays N10's small-μ inequalities. OD-9 (`OWNER-DECISIONS.md:17`) allows those inequalities to stay internal when the half-gaps are stated, so **their absence alone is not a blocker** under the supplied overnight default. The visible inequalities below also satisfy the stricter literal N10 wording (`AMENDMENTS.md:19`). The new constant `Aelem` is needed for the first estimate, not as a hidden premise.

```lean
theorem planar_strongAMD_exponentialSafety (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧ 0 < Aelem ∧
      Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0) →
        (fun i => keplerAxis ν z₀ i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / keplerAction ν z₀ i ^ 3)|) →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        strongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))
        ∃ z : ℝ → Phase (n * 2), z 0 = z₀ ∧
          IsMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          MovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsNewtonSolutionOn (actualMasses 1 ν μ) (Set.Icc (-T) T)
            (fun t => barycentricPositions 1 ν μ (z t).1)
            (fun t => barycentricVelocities 1 ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            (∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0) ∧
            (∃ hcht : (fun i => keplerAction ν (z t) i) ∈ chamber ν,
              strongAMD ν (z t) ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤ AΛ * Real.sqrt μ ∧
            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤ Aa * Real.sqrt μ ∧
            |strongAMD ν (z t) - strongAMD ν z₀| ≤ n * AΛ * Real.sqrt μ ∧
            (∀ i, dStar ≤ keplerAxis ν (z t) i * (1 - ecc ν (z t) i)) ∧
            (∀ a : AdjIdx n, dPair ≤ keplerAxis ν (z t) a.upperIdx * (1 - ecc ν (z t) a.upperIdx) -
                keplerAxis ν (z t) a.1 * (1 + ecc ν (z t) a.1)) ∧
            (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
            (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) ∧
            (∀ i, oscEnergy ν μ (z t) i < 0 ∧
                  0 < oscAxis ν μ (z t) i ∧ oscEcc ν μ (z t) i < 1 ∧
                  oscPeri ν μ (z t) i ≤ planeLength (bodyVector (z t).1 i) ∧
                  planeLength (bodyVector (z t).1 i) ≤ oscApo ν μ (z t) i ∧
                  |oscAxis ν μ (z t) i - keplerAxis ν (z t) i| +
                    planeLength (oscEccVector ν μ (z t) i - keplerEccVector ν (z t) i)
                      ≤ Aelem * μ) ∧
            (∀ i, |oscPeri ν μ (z t) i - keplerPeri ν (z t) i| ≤ Aosc * μ ∧
                  |oscApo ν μ (z t) i - keplerApo ν (z t) i| ≤ Aosc * μ) ∧
            (∀ i, dStar / 2 ≤ oscPeri ν μ (z t) i) ∧
            (∀ a : AdjIdx n, dPair / 2 ≤ oscPeri ν μ (z t) a.upperIdx - oscApo ν μ (z t) a.1) := by
  sorry
```

### F3 — BLOCKING for the stated freeze inventory: source threshold carriers are not enforced on every listed export

The anchor calls themselves use the good interface `orderedStrongThreshold hn ⟨I,hch⟩`. However, proposal:21–24 proposes freezing **all** of `pairThreshold`, `crossThreshold`, `starThreshold`, `strongThreshold`, and the ordered variants. The raw helpers have all-real action carriers (`Threshold/Defs.lean:49–67`), while MAIN:55 explicitly disclaims values outside Q. Further, `orderedCrossThreshold` (:82–83) lacks `hn : 2 ≤ n`; even with an ordered action, n=1 gives an **empty** adjacent family and Lean's real indexed infimum returns 0, not the source minimum over a nonempty family. This is a complete-carrier defect of the proposed definition export, not a counterexample to LP0 or LP1 (both have hn).

Exact replacement for the ordered cross/strong definitions (same namespace and implicit n as existing Defs):

```lean
noncomputable def orderedCrossThreshold {ν : Fin n → ℝ} (_hn : 2 ≤ n)
    (I : OrderedActions ν) : ℝ :=
  ⨅ a : AdjIdx n, orderedPairThreshold I a.1 a.upperIdx a.lt_upperIdx

noncomputable def orderedStrongThreshold {ν : Fin n → ℝ} (hn : 2 ≤ n)
    (I : OrderedActions ν) : ℝ :=
  min (orderedCrossThreshold hn I) (⨅ i : Fin n, I.1 i)
```

The added guard is typing data already implied at every anchor use. Internal helper equalities remain definitionally true; downstream references to orderedCrossThreshold need the extra argument. Do not silently change the frozen surface later to repair it.

Exact carrier-level characterization and unique-value exports to accompany the ordered pair definition (these bodies were checked, unlike a deferred characterization promise):

```lean
theorem orderedPairThreshold_isLeast {ν : Fin n → ℝ}
    (I : OrderedActions ν) (i j : Fin n) (hij : i < j) :
    IsLeast (pairObjective I.1 i j '' pairFeasible ν I.1 i j)
      (orderedPairThreshold I i j hij) :=
  pairThreshold_isLeast ν I.1 i j

theorem orderedPairThreshold_existsUnique_value {ν : Fin n → ℝ}
    (I : OrderedActions ν) (i j : Fin n) (hij : i < j) :
    ∃! b : ℝ, IsLeast (pairObjective I.1 i j '' pairFeasible ν I.1 i j) b := by
  refine ⟨orderedPairThreshold I i j hij, pairThreshold_isLeast ν I.1 i j, ?_⟩
  intro b hb
  exact hb.unique (pairThreshold_isLeast ν I.1 i j)
```

Recommended freeze inventory text: **Freeze the source-facing `OrderedActions`, orderedPairThreshold with i<j and its complete attained-minimum/unique-value characterization, orderedCrossThreshold with hn, and orderedStrongThreshold with hn. Keep the raw total threshold formulas as internal implementation helpers covered by the frozen definition closure, rather than separately certifying them as MAIN's source objects off Q.** The chamber, axes, deficit and objective remain literal formula/predicate helpers; no source minimizer is selected. `starThreshold` is implemented directly by the nonempty finite infimum inside the guarded strong definition; a separate source-facing star export, if desired, needs `1 ≤ n` and `OrderedActions ν` in its signature.

This distinguishes a formula whose body computes a helper everywhere from the source threshold's public carrier. No change to the two anchor threshold applications is needed after this guard repair.

### F4 — BLOCKING to an unqualified whole-carrier source-object freeze: total new ellipse/AMD expressions

Source locations: canonical elements are introduced **when E_i<0**, MAIN:31–37; actual osculating **ellipses** are introduced on safe physical sets for sufficiently small positive μ, MAIN:510–525. New public `strongAMD`, `keplerPeri/Apo`, `oscAxis`, `oscEccVector`, `oscPeri/Apo` accept every phase (Momentum:41; Osculating/Basic:53–81). At q=p=0, for example, the Lean energy/axis expressions use totalized division at zero; that phase is not a source Kepler ellipse. `oscParam` also has nonpositive values on its unrestricted real-parameter carrier. There is no branch disguising these facts, but literal algebra alone does not certify the physical object on the entire type.

This is **not** a demand to edit existing frozen planetary definitions, and **not** a new hypothesis on the allowed initial data. Existing frozen total canonical definitions are inherited conventions, consumed only under their source guards. The new objects should either be explicitly registered as **total algebraic expressions with guarded physical interpretation**, with a precise owner ruling on that convention, or expose source objects on source subtypes. The supplied overnight defaults choose the formulas but do not independently approve all off-domain values as physical source objects. Merely freezing the bytes of total internal helpers in a definition closure is permissible; the blocker concerns representing those helpers themselves as complete-carrier source objects. Proposal:116–117 already describes total strongThreshold as internal; the final inventory should preserve that distinction consistently. The skill does not allow a universal physical-object PASS based solely on a future valid-locus lemma.

The following exact adapter definitions implement the subtype option while preserving the total helpers internally. Distinct names ensure no repair of an already frozen definition. Positive masses are part of each carrier, not assumed later to justify off-source values. These definitions are literal restrictions; they do not choose an ellipse or defer its formula. `SourceCanonicalPhase` includes the source negative-energy states (possibly degenerate until the barrier is applied); `SourceOsculatingPhase` includes precisely nondegenerate actual-velocity elliptic states.

```lean
abbrev SourceCanonicalPhase (n : ℕ) (ν : Fin n → ℝ) :=
  {z : Phase (n * 2) // (∀ i, 0 < ν i) ∧
    ∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0}

abbrev SourceOsculatingPhase (n : ℕ) (ν : Fin n → ℝ) (μ : ℝ) :=
  {z : Phase (n * 2) // (∀ i, 0 < ν i) ∧ 0 < μ ∧
    ∀ i, 0 < planeLength (bodyVector z.1 i) ∧
      oscEnergy ν μ z i < 0 ∧ oscEcc ν μ z i < 1}

noncomputable def sourceStrongAMD {ν : Fin n → ℝ}
    (z : SourceCanonicalPhase n ν) : ℝ := strongAMD ν z.1
noncomputable def sourceKeplerPeri {ν : Fin n → ℝ}
    (z : SourceCanonicalPhase n ν) (i : Fin n) : ℝ := keplerPeri ν z.1 i
noncomputable def sourceKeplerApo {ν : Fin n → ℝ}
    (z : SourceCanonicalPhase n ν) (i : Fin n) : ℝ := keplerApo ν z.1 i
noncomputable def sourceOscVelocity {ν : Fin n → ℝ} {μ : ℝ}
    (z : SourceOsculatingPhase n ν μ) (i : Fin n) : Fin 2 → ℝ := oscVelocity ν μ z.1 i
noncomputable def sourceOscParam {ν : Fin n → ℝ} {μ : ℝ}
    (_z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ := oscParam ν μ i
noncomputable def sourceOscEnergy {ν : Fin n → ℝ} {μ : ℝ}
    (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ := oscEnergy ν μ z.1 i
noncomputable def sourceOscAxis {ν : Fin n → ℝ} {μ : ℝ}
    (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ := oscAxis ν μ z.1 i
noncomputable def sourceOscEccVector {ν : Fin n → ℝ} {μ : ℝ}
    (z : SourceOsculatingPhase n ν μ) (i : Fin n) : Fin 2 → ℝ := oscEccVector ν μ z.1 i
noncomputable def sourceOscEcc {ν : Fin n → ℝ} {μ : ℝ}
    (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ := oscEcc ν μ z.1 i
noncomputable def sourceOscPeri {ν : Fin n → ℝ} {μ : ℝ}
    (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ := oscPeri ν μ z.1 i
noncomputable def sourceOscApo {ν : Fin n → ℝ} {μ : ℝ}
    (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ := oscApo ν μ z.1 i
```

Recommended inventory replacement: freeze these source-facing restrictions and their exact defining equations, retaining the existing total functions as algebraic implementation helpers in the definition closure. F2's explicit **output** oscEnergy<0/oscEcc<1 constructs the oscillating carrier proof along the solution; never assume those outputs as initial hypotheses. The raw formulas in the present anchor remain interpretable under their stated/proved guards. If choosing the alternative owner-approved total-expression convention, that decision must explicitly distinguish formula totality from physical ellipse existence; this audit has not invented such an approval.

For these new functions regarded merely as literal total formulas: `BODY_MATCH: OK; WELL_DEFINEDNESS: N/A_LITERAL; CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A`. For an unqualified claim of source physical objects at every phase: `PUBLIC_CARRIER: FAIL; DEFINITION_VERDICT: FAIL`. For the typed restrictions above: all their values are the source formulas on the indicated carriers. No arbitrary fallback or nonunique witness is used.

### F5 — CHANGE-RECOMMENDED: OD-3's generalization requires a precise μ/constant convention

The **current LP1** draft retains both normalization binders; it exactly matches MAIN:11 and SPEC:15. LP0 does not carry those two standing normalization assumptions: its static barrier is valid for arbitrary fixed positive ν, a homogeneous extension of the globally normalized setting of MAIN:11. Thus LP0 is already generalized in this respect, rather than literally repeating every §1 standing assumption. This does not change a μ convention in LP0 because that lemma has no μ. If literal normalized-source scope is required for LP0 too, insert the same two binders immediately after hν; otherwise record this explicit static generalization with the approval. Removing them leaves literal meanings of `actualMasses`, `movingHamiltonian`, `oscParam`, I and C unchanged at each fixed `(ν,μ,z)`: μ is still the coefficient in masses μν_i. It is therefore a legitimate generalization of the **parameterized equation**, with constants still allowed to depend on the fixed ν. It does **not** preserve the interpretation **μ = largest planet-to-star mass ratio**, unless max ν=1; for general ν that ratio is μM, where M=max ν_i>0. The nominal physical smallness threshold and numerical exponential constant cannot be held fixed under renormalization. "No proof step uses it" (proposal:119–121) is not by itself the semantic justification.

Explicit scaling check: put ν'=ν/M, μ'=Mμ and p'=p/M, with q unchanged. Then H_{ν,μ}(q,p)=M H_{ν',μ'}(q,p') and physical time is unchanged. I'=I/M, C'=C/M, B'=B/M, δ'=δ/M; a and ω=ν³/I³ are unchanged, as are γ and τ. The same actual V and k=1+μν result. If the normalized source theorem gives constants with exponent α=1/(2(τ+1)), then one admissible transported choice is

- μ₀ = μ₀'/M, c = c' M^(−α), T₀=T₀';
- AΛ = AΛ' M^(3/2), Aa = Aa' √M, Aosc = Aosc' M;
- dStar=dStar', dPair=dPair'.

The normalized theorem is applied at margin δ/M and masses ν/M. Thus the original constants' **allowed dependence set** is preserved (M is a function of ν), but their values/normalization are changed. No uniformity over ν is obtained. This also explains why replacing k by 1 to remove the apparent mass dependence would be wrong.

Recommendation: **retain** the current exact normalized binders in the source-facing freeze:

```lean
(hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
```

A separately approved generalized successor can delete precisely those two binders, keeping `(ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)` and the entire rest of the type. Its documentation must call μ the mass **scale** and state max physical ratio = μ max ν, with ν-dependent constants. No other replacement Lean term is needed for that optional generalization; the recommendation here is to keep the exact current Lean line. OD-3 remains open; this review does not resolve it for the owner.

### F6 — NOTE: no missing crossing/collision clauses of (8)–(9)

Draft:63–77 explicitly contains elliptic-energy guards, chamber membership, strong-AMD margin δ/2, max-norm action and axis drift, n AΛ√μ AMD drift, canonical pericentres, adjacent whole-annulus gaps, all star distances, **every unequal planet pair** distance, both osculating endpoint errors and both half-gap inequalities. AdjIdx.upperIdx is the literal adjacent index i+1 (`Threshold/Defs:53–56`), with no periodic wrap-around. Positive dPair orders whole instantaneous annuli, not merely current positions. Chaining adjacent intervals separates all pairs. `IsNewtonSolutionOn` additionally includes star/planet and planet/planet noncollision in barycentric coordinates. The endpoint statements are uniform in all phases and allowed secular states, including retrograde planar orientations and circular states. No extra eccentricity, secular stability, prograde or chart-domain premise should be added to make a proof convenient.

No textual replacement is required for these clauses. The separate τ=n−1/2 corollary is not part of the LP0/LP1 targets (OD-4); its absence here is not a defect.

### F7 — NOTE: N10 and “maximal solution” scope

The literal N10 headline-constant wording and OD-9's internal-ordering default differ in presentation, but both require the actual half-gaps in the conclusion. The draft has those half-gaps. F2 displays the inequalities for the strict literal reading without claiming they were absent physics. The draft's local-overlap uniqueness is the repository's explicit replacement for naming a maximal flow; it does not assert a maximal solution whose time domain is exactly [-T,T]. No source conclusion is lost by restricting the unique maximal physical trajectory to the certified interval. A standalone theorem constructing a maximal flow domain has not been certified here.

## Checks, exact commands, outputs and limitations

All deliberate direct Lean/Lake checks below were executed from `/root/code/KAM-inp-lp-thr`, one reviewer invocation at a time, with this exact wrapper. **Process deviation:** the first lint invocation was plain `scripts/lint_sources.sh` from the review checkout; it unexpectedly launched the ABI script's Lean subprocess without this wrapper and failed for missing KAM build artifacts. This violated the user's all-invocations/cwd requirement. Because that lint process remained in flight during direct checks, its brief failing ABI subprocess also cannot be certified as serialized against those checks. It is recorded, not counted as a compliant Lean check. The corrected lint run started only after all reviewer probes had exited. The subsequent build/probe and build-checkout lint invocations use the required wrapper:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

Other agents' machine processes were not controlled or terminated. The commands did not override heartbeat, recursion, or synthesis budgets. The targeted build reused the existing build snapshot; no clean/root/library build was requested.

1. `lake build KAM.Planetary.StrongAMD.Osculating` under the wrapper: exit 0, **`Build completed successfully (9129 jobs).`** Existing unused-variable warnings were replayed for `KAM/Kepler/Energy.lean:106` (`hm`, `hκ`); no audit-owned Lean source was changed. The job count is Lake's dependency graph, not 9129 newly launched compiler processes.
2. Exact draft copied outside both repositories to `/tmp/maud-lp-stmt-1.lean`; `lake env lean /tmp/maud-lp-stmt-1.lean` under the wrapper: exit 0, only the two expected declaration-uses-sorry warnings, with axiom output below. An added **sorry-free** example consumed `strongBarrier_physical hν hn hU hUch hm`, constructed `BarrierState` from the literal anchor premises, and returned the four exact LP0 conclusions (using definitionally equal peri/apo expressions). This demonstrates actual producer-to-current-LP0 consumption rather than name reachability.
3. The same probe was extended with ordered-pair IsLeast and unique-value proofs, plus a negative carrier regression: at n=1, ν=1 and I=1, `orderedCrossThreshold I = 0` by empty-family simplification. **Exit 0**; both characterization examples and the negative regression elaborated. The only additional warning was a proof-style suggestion to use `have` instead of `haveI` in the test. This is why accepting the full public carrier of that definition would be unsound as a translation of the source's nonempty minimum.
4. Source-complete replacement signatures F1/F2 and the exact carrier/characterization adapters F3/F4 were assembled in `/tmp/maud-lp-replacements.lean` using the same imports, with new threshold names isolated in a scratch namespace. Only the two proposed anchor proofs were placeholders; adapter/characterization bodies were complete. The first run exposed missing `noncomputable` modifiers in that scratch context for the two guarded threshold definitions (the original Defs file has a noncomputable section); the report now spells out those modifiers. Final result: **exit 0**, only the two expected declaration-uses-sorry warnings at lines 23 and 48. All typed adapters, guarded threshold definitions and characterization proofs elaborated. These checks concern syntax/type elaboration, not proofs of the stronger anchors.
5. Initial `scripts/lint_sources.sh` from the review checkout: **exit 1**, after `check_lean_modules: PASS (3685 Lean files, 0 comparator configurations)` and `FROZEN-ANCHOR GUARD OK`; ABI subprocess failed with **`error: unknown module prefix 'KAM'`** because that checkout has no compiled KAM search-path entry. This is an incomplete lint gate, not a source-fidelity finding. Corrected command, executed from `/root/code/KAM-inp-lp-thr`, was the exact wrapper above followed by `sh scripts/lint_sources.sh`: **exit 0**, with this output:

   ```text
   check_lean_modules: PASS (3702 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
   ```

   This is a passing lint/ABI gate for the **build checkout**, not a retroactive pass of the failed review-checkout invocation. The two opt-in lunar declarations were checked by file hash only, as stated by the checker; no application was built. No generated root, README, frozen file or manifest was repaired to make the check pass.
6. Independent byte comparisons, proposal/draft command matching, manifest absence for LP anchors and all 67 frozen planetary whole-file hash checks passed as described above.

The original exact draft axiom outputs are:

```text
planar_strongAMD_barrier:
  [propext, sorryAx, Classical.choice, Quot.sound]
planar_strongAMD_exponentialSafety:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

`#print axioms` for each of `strongAMD`, `oscVelocity`, `oscParam`, `oscEnergy`, `oscAxis`, `oscEccVector`, `oscPeri`, `keplerPeri`, `pairThreshold_isLeast`, `orderedStrongThreshold`, `strongBarrier_physical` and `osculating_barrier` reported **only `[propext, Classical.choice, Quot.sound]`**, no `sorryAx` or project axiom. This is semantic-unit support, not a new sealed LP0/LP1 result. No assembled LP1 proof, independent kernel replay, or complete future freeze-manifest/ABI approval is claimed.

### Exact sorry-free LP0 consumption check

After the draft imports, `open KAM.Planetary` and `open KAM.Planetary.StrongAMD`, the following complete check elaborated. It uses the current four-conclusion LP0 projection, not the stronger replacement proof placeholder.

```lean
example {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (U : Set (Fin n → ℝ)) (hU : IsCompact U) (hUch : U ⊆ chamber ν) (m : ℝ) (hm : 0 < m) :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
      ∀ z : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0) →
        ∀ hΛ : (fun i => keplerAction ν z i) ∈ U,
        strongAMD ν z ≤ orderedStrongThreshold hn ⟨_, hUch hΛ⟩ - m →
        (∀ i, dStar ≤ keplerPeri ν z i) ∧
        (∀ a : AdjIdx n, dPair ≤ keplerPeri ν z a.upperIdx - keplerApo ν z a.1) ∧
        (∀ i, dStar ≤ planeLength (bodyVector z.1 i)) ∧
        (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j)) := by
  obtain ⟨dS, dP, R, P, c, hdS, hdP, hR, hP, hc, hdef, h⟩ :=
    strongBarrier_physical hν hn hU hUch hm
  refine ⟨dS, dP, hdS, hdP, ?_⟩
  intro z hz hΛ hC
  obtain ⟨h1, h2, h3, h4, rest⟩ := h z ⟨hz, hΛ, hC⟩
  exact ⟨h1, h2, h3, h4⟩
```

## Handoff: uncertainty, errata and deviations

Files written in the repository: this report only. The three reviewer-owned `/tmp/maud-lp-*` probe/text files were deleted after recording the checks; no probe remains in either repository. Approach: reconstruct MAIN + amendments first, expand all logical inputs and physical definitions, inspect full source carriers, compare exact target bytes, then run bounded elaboration/consumption/axiom checks. The source-complete replacements are recommendations only. The scope blockers F1/F2 can instead be resolved by an explicit approved split naming these as projections and providing the omitted source exports separately; no such split was silently assumed in the full-source verdict. Owner choices OD-1–OD-7/OD-9 still require exact-text approval; report readiness is not freeze permission.

No new suspected arithmetic or mathematical defect in the pinned MAIN under N1–N12 was found in this scoped statement review. Reported discrepancies are proposal/export-scope defects, especially the omitted L5/L16 exports and the too-broad definition freeze inventory. MAIN:527's `|k_i−1|≤μ` uses max ν=1 correctly; if OD-3 is generalized it must become `|k_i−1|≤Mμ`, an introduced deviation to record, not an erratum in the current source. N7's alternative supplier correction is respected; no L12-and-L13 joint hypothesis was introduced. No repository correction, ledger edit, frozen edit or provider change was made.

## Hard rules (verbatim from the supplied Lean brief)

1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
   proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
3. **Every `.lean` file is a Lean module**: copyright comment, `module`, imports (`public import` for the
   interface), module docstring, `public section`. Expose (`@[expose]`) definitions whose bodies must unfold.
4. **No `axiom`, `admit`, `unsafe`, `opaque`; `sorry` only** as the manifest-bound body of a frozen statement in
   `KAM/Frozen/`. No recursion-depth or synthesis-heartbeat overrides either.
5. **Frozen files are read-only.** Never edit anything under `KAM/Frozen/` or `manifest/`. If a frozen
   declaration looks wrong, stop and report; never add a premise or substitute a helper.
6. **No conclusion-shaped hypotheses.** A theorem may assume only source premises, standing assumptions, typing
   data and explicit owner rulings. Conditional helpers get distinct names and never stand in for a source result.
7. **Ambient types:** `Fin n → ℝ`, `Fin n → ℂ`, Fourier indices `Fin n → ℤ`. Never `EuclideanSpace`.
8. **Builds:** one targeted `nice -n 5 lake build <Module>` at a time; never `lake clean`; never rebuild the
   library from scratch in a worktree (worktrees use a copy-on-write overlay on `main`'s build snapshot). A wait
   on the compile gate is expected, not a hang. A plain `lake build` builds the core library `KAM`, i.e. every
   core theorem. Certificate applications (`KAMLunarBand`, `KAMLunarLock`, …; modules assigned in
   `scripts/build_roots.json`) are opt-in: build one only deliberately, with `lake build <Lib>` through the serial
   capped driver `scripts/prebuild_heavy.py --lib <Lib>`, never in parallel and never as a side effect (D51).
   No core module imports an application module. See `docs/campaign/design/APPLICATIONS.md`.
9. **Providers are quarantined.** `KAM/Provider/<Name>.lean` proves its frozen theorem as `KAM.Provider.<name>`;
   no module except the frozen anchor may import a provider or a `DRAFT_SORRY` anchor (the root file skips them).
10. **Never edit `README.md`** (generated) or `KAM.lean` and its parts `KAM/Root/*.lean`, the application roots
    `<Lib>.lean` and their parts `<Lib>/`, or the generated block of `lakefile.lean` (all generated by
    `scripts/gen_root_imports.py`; no module imports a root or part).
11. **Errata:** report every suspected defect in a pinned source (location, quoted text, why it is wrong) in your
    handoff; the orchestrator records it in `docs/errata/ledger.json`. Deviations you introduce are reported too.

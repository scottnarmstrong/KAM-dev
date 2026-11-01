# Independent LP statement review 4: LP2 (§3c) and LP2 under OD-11 (b) (§3d)

2026-11-01. Independent, refute-first reviewer. I did not write any of the reviewed declarations and used no
subagents. Method: `/root/.claude/skills/lean-statement-audit/SKILL.md`, read in full. The pre-freeze review request
takes precedence over the skill's manifest-only workflow. Following the brief, **Lean and Lake were not run**, so no
elaboration, consumption or `#print axioms` result below is my own (see "Checks"). This report is the only file I
wrote in the repository.

## Verdict

**§3c (LP2): PASS for declaration fidelity**, with one documentation/naming CHANGE-RECOMMENDED (R4.2). LP2 is the
exact spatial twin of the reviewed LP1:

- Every binder is SOURCE, STANDING or TYPING; there is no EXCESS and no conclusion-shaped premise.
- None of the roadmap-forbidden premises appears: prograde, small inclination, `L ≠ 0`, secular-domain confinement,
  normal-form existence, or stopped action.
- All constants are chosen before `μ` and before the initial data.
- The conclusion covers every item of MAIN (7)–(9) and the L16 conclusions that LP1 exports.

**§3d (LP2 under OD-11 (b)): faithful to §3c, but OD-11 (b) is NOT fully resolved: one BLOCKING freeze-gate
finding (R4.1).**

- §3d is the exact twin of §3b. Each subtype proof is a typing input or an existential output, never an assumption.
- The new spatial source carriers and source definitions pass the definition audit on their whole carriers.
- However, §3d still uses the **unrestricted total helpers** `spatialKeplerAxis`, `spatialKeplerAction` and
  `spatialKeplerEccVector` as meaning-carrying objects. They occur in the axes-in-`A` premise, the Diophantine
  premise, the chamber binder, the drift clauses, the canonical (9) clauses and the `A_elem` clause.
- In the planar §3b the corresponding `keplerAxis`, `keplerAction` and `keplerEccVector` were acceptable only because
  they are **already-frozen repository definitions** (inherited conventions; review 1 F4). The spatial ones are new
  and unfrozen.
- So freezing §3d as written would freeze these total helpers as physical quantities. W4A N1 explicitly forbids this,
  OD-11 (b) excludes it, and the package's own module docstring disclaims it (`odb-Spatial-SourceCarrier`:20–22).
- The source restrictions `spatialSourceKeplerAxis/Action/EccVector` already exist in that same file (:71–84) but are
  not used.
- Two fixes: exact replacement text is given in R4.1, or an explicit owner ruling can extend the planar inherited
  convention to these helpers.

```text
LP2 (§3c)  DECLARATION_FIDELITY: PASS     DRAFT_ALLOWLIST: N/A_UNFROZEN   PROOF_STATUS: PROPOSED_UNFROZEN
LP2 (§3d)  DECLARATION_FIDELITY: PASS     (faithful restatement of §3c; twin of §3b)
OD-11 (b) spatial definition/freeze gate: NOT RESOLVED (R4.1 BLOCKING); FREEZE_PACKAGE: NOT_READY for LP2 under (b)
```

| Id | Class | One line |
|---|---|---|
| R4.1 | **BLOCKING** (freeze gate under OD-11 (b)) | §3d still uses the unfrozen total `spatialKeplerAxis/Action/EccVector` as physical quantities; restate through `spatialSource*` (exact text below) or obtain an explicit owner ruling |
| R4.2 | CHANGE-RECOMMENDED | §3c displays the implementation name `lp2_spatial_strongAMD_safety_normalized` with `_hνmax/_hνle`, not the anchor name `spatial_strongAMD_exponentialSafety` from proposal §1 |
| R4.3 | CHANGE-RECOMMENDED | §4b (definition freeze inventory) has no spatial bullet; add one (exact text below) |
| R4.4–R4.9 | NOTE | twin-shape difference of `h₀/hs`; geometric-L16 scope; documentation misnomers; `SpatialElliptic` is a `def`; totalized `spatialHamiltonian`; no spatial LP0 |

No new suspected erratum in MAIN as amended.

## Identity

All relative paths are under `/root/code/KAM-inp-lp/`. Review HEAD (`inp-lp`) is
`5cc79af0852b13822379da07fc6d76e2d2639469`. The spatial definitions were read from `inp-lp-spsrcb` at
`6e84c27a257d6fdc58abd03091363a1be1998665`; LP-SP-SAFE is `inp-lp-spsafe` `c9553935`.

| Object | SHA-256 |
|---|---|
| `docs/tracks/LP/FREEZE-PROPOSAL.md` (draft 5) | `e6ee7b81f474f9a34a4219da0427499f8abcf4dbaf9777ee91672b61aac1867a` |
| `freeze/lp2-SpatialSafety-Main.lean.txt` | `fdd83783db8dd60fa3e04f90a17cf97d410423ac267d6321675e8cbeac337c47` |
| `freeze/odb-Spatial-SourceCarrier.lean.txt` | `efe897ea57837613d406fd3176ff0fd35fc32b403027440830d454dcf34b3fe6` |
| `freeze/odb-Spatial-SpatialSafety-Source.lean.txt` | `19522c834648daea38edf9b9c9405fb51fabfa898000402b88872179194cbf6c` |
| `source/MAIN.md` | `68e9167f04e4a04689ea163c74e02ffcaea657b252726080abdbe37bdba48c1b` |
| `source/AMENDMENTS.md` | `c887d1e27354a3db7fb8a20d8bf3e33a9ef95ff3173f925ba5ebfab192651881` |
| `OWNER-DECISIONS.md` | `ab7692eb2f61d35e516a50d3941e6a6465e0db91423790d6ca5e9618f9d38ef3` |

**Attachments vs. branch.** The three attachments are byte-identical to `inp-lp-spsrcb:KAM/Planetary/Spatial/`
`SpatialSafety/Main.lean`, `SourceCarrier.lean` and `SpatialSafety/Source.lean` (identical hashes). `Main.lean` is
also identical on `inp-lp-spsafe`.

**Proposal text vs. attachments** (whitespace-normalized token comparison):

- proposal:309–362 equals the type of `lp2_spatial_strongAMD_safety_normalized` (`lp2-…Main`:153–206).
- proposal:375–455 equals the type of `lp2_spatial_strongAMD_safety_source` (`odb-…Source`:142–222).
- The `_general` variant (`odb-…Source`:40–120) is exactly the same type without `hνmax`, `hνle`.

**Mechanical twin diffs.** I applied a planar→spatial renaming map (`Phase (n*2)→(n*3)`, `planeLength→spaceLength`,
`bodyVector→bodyVector3`, `kepler*→spatialKepler*`, `osc*→spatialOsc*`, `source*→spatialSource*`, the solution and
Newton predicates, `actualMasses 1→spatialMasses`, barycentric maps) and diffed the token streams:

- **§3 → §3c.** The only differences are the theorem name, `hνmax/hνle → _hνmax/_hνle`, and three expansions of the
  abbreviation `ecc ν z i` into `spaceLength (spatialKeplerEccVector ν z i)` (the same expansion as §3b).
- **§3b → §3d.** The only differences are the name, `_hνmax/_hνle → hνmax/hνle`, and the bracketing of `h₀` and the
  three `hs`: §3d writes `∀ i, 0 < ν i ∧ …`, §3b writes `(∀ i, 0 < ν i) ∧ ∀ i, …` (R4.4).

No manifest entry or frozen path exists for LP2; nothing is frozen (proposal:3). The planar threshold unit
(`chamber`, `OrderedActions`, `orderedStrongThreshold hn`) is the THR2-repaired one on this branch
(`StrongAMD/Threshold/Defs.lean`:33,74,84,88). Reviews 2–3 already audited it; I did not re-audit it.

## Independent reconstruction (MAIN §1 with d = 3, T19, L16–L18)

**Standing data (MAIN:11–15):**

- `n ≥ 2`; `ν_i > 0` with `max ν = 1`.
- `𝒜` is compact and contained in `{0 < a_1 < … < a_n}`; the empty set is allowed.
- `δ, γ > 0` and `τ > n − 1`.
- `d = 3` is fixed by T19 (MAIN:601).

**Model and canonical elements (MAIN:17–37):**

- Physical time; masses `μν_i`; scaled canonical `p`.
- Hamiltonian (1): `Σ(|p_i|²/(2ν_i) − ν_i/|q_i|) + μ(½|Σp_i|² − Σ_{i<j} ν_iν_j/|q_i−q_j|)`.
- `v = p/ν`, `E = |v|²/2 − 1/|q|`, `𝐞 = (|v|² − 1/|q|)q − (q·v)v`.
- For `E < 0`: `a = −1/(2E)`, `Λ = ν√a`, `e = |𝐞|`, `L_i = q_i × p_i`, `C = ΣΛ − |L|` with Euclidean `|L|` in 3D.

**Thresholds and frequencies (MAIN:41–65):** `B` on the chamber `𝒬`; radian `ω = ν³/I³`; condition (5) with `|k|₁`.

**Conclusion (MAIN:69–93).** Eight positive constants are chosen depending only on `(d,n,ν,𝒜,δ,γ,τ)`, and N10 adds
a ninth, `A_elem`, together with the ordering of `μ₀`. Then for every `0 < μ ≤ μ₀` and every initial state with
`q_i ≠ 0`, `E_i < 0` and (6), the following hold on `[−T_μ, T_μ]`:

- existence, uniqueness and Newtonian reconstruction (L1);
- ellipticity, `I(t) ∈ 𝒬`, and (8)–(9);
- lower bounds on all star distances and all planet-pair distances;
- osculating endpoint errors `≤ A_osc μ` and half-gaps (L16, N10).

**T19 (MAIN:601)** asserts this "for precisely hypotheses (6), including circular or coplanar initial orbits". The
alignment of `L` with `e₃` and `L ≠ 0` are **proof steps** (L3, L18:597; T19:603), not premises.

**L16 (MAIN:510–529)** in d = 3:

- `V = p/ν + μΣp` and `k = 1 + μν`.
- The elements (42), with the whole eccentricity vector divided by `k`.
- Nondegeneracy, both estimates of (43), and passage through `q` with tangency to `V`.

AMENDMENTS N8/N10/N11 apply as in the planar reviews. N12 is engineering-only. **LEAN-ROADMAP §2** forbids prograde,
small-inclination, `L ≠ 0`, secular-confinement, normal-form-existence and stopped-action hypotheses.

## Five-bin binder test, LP2 (§3c = `lp2-…Main`:153–169)

Each bundle is expanded pointwise. No instance binders.

| Input | Bin | Source / evidence |
|---|---|---|
| implicit `n : ℕ` (`Main`:38) | TYPING | MAIN:11 |
| `hn : 2 ≤ n` | STANDING | MAIN:11 |
| `ν : Fin n → ℝ` | STANDING | MAIN:11 |
| `hν : ∀ i, 0 < ν i` | STANDING | MAIN:11 |
| `_hνmax : ∃ i, ν i = 1` | STANDING | MAIN:11; OD-3 (unused-name prefix does not remove the premise) |
| `_hνle : ∀ i, ν i ≤ 1` | STANDING | MAIN:11; OD-3 |
| `A : Set (Fin n → ℝ)` | STANDING | MAIN:12–14 |
| `hA : IsCompact A` | STANDING | MAIN:11,15; empty allowed |
| `hAord.1 : ∀ a ∈ A, ∀ i, 0 < a i` | STANDING | MAIN:13 |
| `hAord.2 : ∀ a ∈ A, ∀ i j, i < j → a i < a j` | STANDING | MAIN:13 |
| `δ`, `γ`, `τ` (three rows) | STANDING | MAIN:15 |
| `hδ : 0 < δ`, `hγ : 0 < γ` (two rows) | STANDING | MAIN:15 |
| `hτ : (n:ℝ) − 1 < τ` | STANDING | MAIN:15 |
| `μ : ℝ` | SOURCE | MAIN:70 |
| `0 < μ` | SOURCE | MAIN:70 |
| `μ ≤ μ₀` | SOURCE | MAIN:70 |
| `z₀ : Phase (n * 3)` | TYPING | arbitrary 3D state, MAIN:17–37 |
| `∀ i, 0 < spaceLength (bodyVector3 z₀.1 i)` | SOURCE | MAIN:70 (`q_i ≠ 0`) |
| `∀ i, spatialKeplerEnergy ν z₀ i < 0` | SOURCE | MAIN:70; total energy `ν_iE_i`, same sign |
| `(fun i => spatialKeplerAxis ν z₀ i) ∈ A` | SOURCE | MAIN:72 (6) |
| `∀ k ≠ 0, γ·(modeSize k)^(−τ) ≤ |Σ k_i ν_i³/Λ_i³|` | SOURCE | MAIN:64–65 (5); `k`, `k ≠ 0` internal |
| `hch.1 : ∀ i, 0 < spatialKeplerAction ν z₀ i` | TYPING | follows from `hν`, negative energy (`SourceCarrier`:157–159) |
| `hch.2` : ordered `(Λ_i/ν_i)²` | TYPING | follows from axes ∈ A, `hAord`, `Λ² = ν²a` (`SourceCarrier`:162–164) |
| `spatialStrongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_,hch⟩ − δ` | SOURCE | MAIN:35,72 (6), Euclidean `|L|` |

**Counts:** SOURCE 8, STANDING 15, TYPING 4, RULED 0, **EXCESS 0**. These are identical to LP1 (review 2:108).

**Forbidden-premise check.** There is no premise on `angularMomentum3 z₀` (neither nonzero nor aligned), no
inclination or prograde bound (`(q×p)·e₃ > 0`), no pair separation, no eccentricity bound, no secular, normal-form,
chart or stopped-drift premise. Circular states (`𝐞 = 0`), coplanar states and radial states (`e = 1`, excluded only
later by the proved barrier) are all admitted.

**Proof route, for evidence only:**

- The alignment premise lives solely in the distinctly named internal helper `spatial_safety_of_aligned`
  (`SpatialSafety/Aligned.lean`:60).
- `lp2_spatial_strongAMD_safety` discharges it by constructing a rotation (`Main`:122–135).
- It first **derives** `L ≠ 0` from the AMD premise through MAIN L3 (`Main`:106–109).

**Quantifier order.** `∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem`, nine positivity facts and the two N10 inequalities
(`Main`:158–160) come first. Then `∀ μ`, its two guards, `∀ z₀` and its premises, the `let T`, `∃ z`, and finally
`∀ t ∈ Icc (−T) T`.

- The constants may depend only on `(n, ν, A, δ, γ, τ)` (d = 3 is fixed).
- They are therefore uniform over all phases, orientations (including the direction of `L`), eccentricities,
  inclinations and secular states.
- The output universals `i`, `a : AdjIdx n` and `i j, i ≠ j` have full carriers.
- The time horizon is `T₀ exp(c μ^(−1/(2(τ+1))))`, as in MAIN (7).

## Meaning-carrying definitions (branch `inp-lp-spsrcb`)

| Definition | Body checked | Verdict |
|---|---|---|
| `spaceDot/spaceSq/spaceLength` (`Vector`:31–37) | `Σ v_k w_k`, `Σ v_k²`, `√Σ v_k²`: Euclidean, not the Pi sup norm | literal |
| `spaceCross` (`Vector`:40–41) | `(v₁w₂−v₂w₁, v₂w₀−v₀w₂, v₀w₁−v₁w₀)`, the standard cross product | literal |
| `bodyVector3` (`Vector`:44–45) | coordinates `finProdFinEquiv (i,k)` | literal block extraction |
| `spatialHamiltonian` (`Model`:41–45) | `Σ(|p|²/(2ν) − ν/|q|) + μ(|Σp|²/2 − Σ_{i<j} ν_iν_j/|q_i−q_j|)` = MAIN (1), d = 3; recoil as `|Σp|²/2`, attractive pair term | literal (totalized at collisions, R4.8) |
| `SpatialNoCollision`, `IsSpatialMovingSolutionOn`, `SpatialMovingUniqueOn` (`Model`:48–64) | the frozen planar patterns (`IsHamiltonianSolutionOn H Set.univ J z ∧ ∀ t ∈ J, NoCollision`; overlap uniqueness over open convex `U ∋ 0`) in `Fin 3`; frozen `hamiltonianVectorField = (∂_p H, −∂_q H)` | faithful (guards inside the conclusion) |
| `spatialKeplerEnergy` (`Elements`:32–33) | `|p|²/(2ν) − ν/|q| = ν_i E_i` | literal (ν E convention) |
| `spatialKeplerAxis` (:36–37) | `−ν/(2·νE) = −1/(2E)` | literal |
| `spatialKeplerAction` (:40–41) | `ν√a` | literal |
| `spatialKeplerEccVector` (:44–47) | `(|p|²/ν² − 1/|q|)q − (q·p/ν²)p = (|v|²−1/|q|)q − (q·v)v` | literal |
| `planetAngularMomentum3`, `angularMomentum3` (:50–55) | `q_i×p_i`, `Σ q_i×p_i` (scaled `p`, as MAIN `L_i`) | literal |
| `spatialStrongAMD` (:58–59) | `ΣΛ − spaceLength(Σ q×p)`: Euclidean `|L|`, not `Σ|L_i|` and not a signed projection | literal (MAIN (2), d = 3) |
| `spatialOscVelocity`, `spatialOscParam` (`Osculating/Basic`:45–49) | `(1/ν)p_i + μΣp_j`, **`1 + μν_i`** | literal L16 |
| `spatialOscEnergy/Axis/EccVector/Ecc/Peri/Apo` (:52–77) | `|V|²/2 − k/|q|`; `−k/(2E^osc)`; `(1/k)·((|V|² − k/|q|)q − (q·V)V)` (whole vector divided by `k`); Euclidean length; `a(1∓e)` | literal (42) |
| `spatialKeplerPeri/Apo` (:80–85) | `a(1 ∓ |𝐞|)`, parameter one | literal |
| `spatialMasses`, `spatialBarycentricPositions/Velocities` (`Newton`:33–45) | `(1, μν)`; `x₀ = −μΣνq/(1+μΣν)`, `x_i = x₀+q_i`; `ẋ₀ = −μΣp`, `ẋ_i = p_i/ν_i` | literal MAIN L1:104 |
| `IsSpatialNewtonSolutionOn` (`Newton`:48–54) | all unequal-body distances positive, `Q' = V`, `V'_i = Σ_{j≠i} m_j(Q_j−Q_i)/|Q_j−Q_i|³` (G = 1) | literal |
| `KAM.Fourier.modeSize`, threshold unit | as reviews 1–3 (ℓ¹; THR2 carrier) | unchanged |

`spatialOscVelocity_eq_hamiltonianVectorField` (`Basic`:91–95) identifies `V` with the `q`-block of the moving field
(MAIN (10)), and Newton reconstruction makes `V` the actual relative velocity. The literal formulas therefore match
the source. Under OD-11 (b), the off-carrier semantics of the total ones is the subject of R4.1 and R4.3.

## Conclusion vs. MAIN (7)–(9) + L16 (`Main`:171–206)

Every conjunct of LP1 (review 2:128; review 3 R3.2) is present in its spatial form:

- existence on the closed interval `[−T, T]`; overlap uniqueness; Newtonian `(1, μν)` reconstruction;
- negative energy and `|q_i| > 0`; `∃ hcht` chamber membership with `C ≤ B − δ/2`;
- sup-norm `Λ` and `a` drift `≤ A·√μ`; `|C(t) − C(0)| ≤ n A_Λ √μ`;
- canonical perihelia `≥ d⋆` and **whole adjacent annuli** separated by `≥ d_pair` (no orbit crossing, MAIN:93);
- every star distance `≥ d⋆` and **every unequal pair** distance `≥ d_pair`; star and pair noncollision are also inside
  the solution and Newton predicates;
- the osculating block: `E^osc < 0`, `a^osc > 0`, `e^osc < 1`, radial incidence, and
  `|a^osc − a| + |𝐞^osc − 𝐞| ≤ A_elem μ` (Euclidean in `Fin 3`);
- both endpoint errors `≤ A_osc μ`; the half star and adjacent gaps; both N10 inequalities before `μ`.

Nondegeneracy of the osculating ellipses is **produced**, never assumed. The geometric caveat (R4.5) is unchanged
from the planar reviews.

## §3d: five-bin delta, twin check, carriers

**Binders.** These are the §3c rows, plus `h₀ : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z₀.1 i) ∧
spatialKeplerEnergy ν z₀ i < 0` (`Source`:158–159). Its three pointwise components duplicate `hν` and the physical
premise, so all three are TYPING. The AMD premise becomes `spatialSourceStrongAMD ⟨z₀,h₀⟩ ≤ …` (SOURCE; `rfl`-equal
to `spatialStrongAMD ν z₀`, `SourceCarrier`:95–96,127–133). **Counts: SOURCE 8, STANDING 15, TYPING 7, RULED 0,
EXCESS 0**, identical to §3b (review 3).

**Outputs.** `hs` and `ho` occur only under `∃` in the conclusion. `ho` contains `0 < μ`, `E^osc < 0` and
`e^osc < 1`; these are proved outputs (`Source`:236–239), not inputs.

**Faithfulness to §3c.**

- The proof (`Source`:223–241) obtains §3d from the §3c producer by unpacking and repacking only, with source
  restrictions that are `rfl`-equal.
- The reverse direction is equally definitional: drop the `hs` and `ho` witnesses, and since `h₀` is constructible
  from `hν` and the physical premise, it adds no restriction.
- No conclusion is weakened, and the constants and their order are unchanged.

**Carriers.**

- `SpatialSourceCanonicalPhase n ν := SpatialElliptic ν = {z // ∀ i, 0 < ν i ∧ 0 < |q_i| ∧ E_i < 0}`
  (`SourceCarrier`:50; `Elements`:63–67). This is the planar `SourceCanonicalPhase` predicate, regrouped (R4.4). It
  admits radial `e = 1` (MAIN:122) and imposes no pair separation.
- `SpatialSourceOsculatingPhase n ν μ := SpatialOscPhase n ν μ = {z // (∀ i, 0<ν i) ∧ 0<μ ∧ ∀ i, 0<|q_i| ∧
  E^osc_i<0 ∧ e^osc_i<1}` (`SourceCarrier`:53–54; `Basic`:163–166). This is exactly the planar osculating carrier.

**Source definitions and characterizations.**

- **Twin set.** `spatialSourceStrongAMD`, `spatialSourceKeplerPeri/Apo` and `spatialSourceOsc{Velocity,Param,Energy,
  Axis,EccVector,Ecc,Peri,Apo}` are literal restrictions with `rfl` equations (`Basic`:169–252; `SourceCarrier`:95,
  127–147).
- **Additional canonical restrictions.** `spatialSourceKeplerAxis/Action/EccVector/Ecc` and
  `spatialSourcePlanetAngularMomentum/AngularMomentum` are also literal restrictions with `rfl` equations
  (`SourceCarrier`:71–129).
- **Characterizations on the whole carriers** (`SourceCarrier`:151–263): `a > 0`, `Λ > 0`, `Λ² = ν²a`,
  `e² = 1 − |L_i|²/Λ²`, `0 ≤ e ≤ 1`, `|L_i| = Λ√(1−e²)`, `|L_i| ≤ Λ`, `a(1−e) ≤ |q| ≤ a(1+e)`, `C ≥ 0`,
  `Σ Λ D(e) ≤ C` (MAIN L2, L3), and `k > 0`, `E^osc < 0`, `0 ≤ e^osc < 1`, `a^osc > 0`, `a^osc(1−e^osc) > 0`, and
  radial incidence for the osculating carrier.
- **Adequacy.** These cover the planar characterization set of review 3 and add the spatial L2 identities. They are
  adequate for literal formulas. No choice is involved, so no `∃!` is needed.

For each spatial source definition named above:

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: OK (rfl defining equations + carrier consequences above)
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

For the total helpers `spatialKeplerAxis`, `spatialKeplerAction`, `spatialKeplerEccVector`, `spatialStrongAMD`,
`spatialKeplerPeri/Apo` and `spatialOsc*`, regarded as source physical objects on all of `Phase (n*3)`:
`PUBLIC_CARRIER: FAIL; DEFINITION_VERDICT: FAIL_AS_WHOLE_CARRIER_SOURCE_OBJECTS`. These are the same verdicts as
review 2's F4. This is acceptable only if they are not frozen as physical quantities, which R4.1 shows §3d does not
achieve.

## Findings

### R4.1 — BLOCKING (OD-11 (b) freeze gate): canonical spatial elements still appear as unrestricted total helpers in §3d

**Evidence.** In the §3d text, `spatialKeplerAxis`, `spatialKeplerAction` and `spatialKeplerEccVector` are applied
directly to `z₀` and `z t`:

- proposal:386 (axes ∈ A), :389 (Diophantine), :390 (`hch`);
- :409–412 (Λ and a drift), :418–423 (canonical (9));
- :440 and :443 (the `A_elem` clause, against the canonical `a` and `𝐞`).

They are the same at `odb-…Source`:153–157,176–190,207–210.

**Why it is blocking.**

- These definitions are new and unfrozen (`Elements`:31–47). Unlike planar `keplerAxis/keplerAction/keplerEccVector`,
  they are not inherited frozen conventions.
- If §3d were frozen, they would enter the frozen closure as meaning-carrying public total functions on
  `Phase (n*3)`. Their values at `|q_i| = 0` or `E_i ≥ 0` are junk (for example, Lean's `x/0 = 0` in
  `spatialKeplerAxis`).
- That is precisely F4's whole-carrier failure (review 1:305–349; review 2:161–176).
- W4A N1 says: "do not freeze the unrestricted helpers as physical quantities" (`inp-lp-w4a:…/LP-W4A-audit-1.md`:55–56).
- OD-11 (b) asks for "source subtypes for every frozen meaning-carrying definition" (`OWNER-DECISIONS.md`:19).
- `odb-Spatial-SourceCarrier`:20–22 itself claims that these helpers "stay internal and are not frozen as physical
  quantities. Every physical quantity is exposed through a source subtype".

The anchor contradicts that claim, although the needed restrictions already exist (`SourceCarrier`:71–84).

**Not affected.** This is not a fidelity defect of the theorem: every use is under the guard
`0 < |q_i| ∧ E_i < 0`, and the formulas are literal. `spatialKeplerEnergy` is not part of the finding. It occurs only
inside the guard conjunction `0 < ν ∧ 0 < |q_i| ∧ E_i < 0`, the literal carrier predicate `SpatialNegativeEnergy`.
That predicate is false whenever `|q_i| = 0`, so as a predicate it is whole-carrier faithful.

**Resolution (either one):**

- **(A, recommended).** Replace the §3d theorem by the following exact text. The changes:
  - `h₀` moves immediately after the physical premise (still TYPING);
  - every canonical element at `z₀` and `z t` is the `spatialSource*` restriction;
  - the canonical (9) clauses use `spatialSourceKeplerPeri/Apo`, which are definitionally `a(1 ∓ |𝐞|)`;
  - the per-time block is scoped under one `∃ hs`, which literally contains the former ellipticity clause plus
    `0 < ν_i`.

  No premise is added, and every conclusion of the current §3d is recovered definitionally. The proof is expected to
  be the current one with `rfl`-unfolding. I did not elaborate it (Lean not run per brief), so the orchestrator must
  elaborate it transiently and close it from `lp2_spatial_strongAMD_safety_normalized` before re-review.

```lean
theorem lp2_spatial_strongAMD_safety_source (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        ∀ h₀ : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z₀.1 i) ∧
          spatialKeplerEnergy ν z₀ i < 0,
        (fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 /
              spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i ^ 3)|) →
        ∀ hch : (fun i => spatialSourceKeplerAction
            (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
        spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))
        ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧
          IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
            (fun t => spatialBarycentricPositions ν μ (z t).1)
            (fun t => spatialBarycentricVelocities ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            ∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                spatialKeplerEnergy ν (z t) i < 0,
            ∃ hcht : (fun i => spatialSourceKeplerAction
                (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
            spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) ≤
                orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2 ∧
            ‖(fun i => spatialSourceKeplerAction (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              AΛ * Real.sqrt μ ∧
            ‖(fun i => spatialSourceKeplerAxis (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              Aa * Real.sqrt μ ∧
            |spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) -
                spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν)| ≤
              n * AΛ * Real.sqrt μ ∧
            (∀ i, dStar ≤
                spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ∧
            (∀ a : AdjIdx n, dPair ≤
                spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) a.upperIdx -
                  spatialSourceKeplerApo (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) a.1) ∧
            (∀ i, dStar ≤ spaceLength (bodyVector3 (z t).1 i)) ∧
            (∀ i j, i ≠ j →
              dPair ≤ spaceLength (bodyVector3 (z t).1 i - bodyVector3 (z t).1 j)) ∧
            ∃ ho : (∀ i, 0 < ν i) ∧ 0 < μ ∧
                ∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                  spatialOscEnergy ν μ (z t) i < 0 ∧ spatialOscEcc ν μ (z t) i < 1,
              (∀ i, spatialSourceOscEnergy (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i < 0 ∧
                  0 < spatialSourceOscAxis (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ∧
                  spatialSourceOscEcc (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i < 1 ∧
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ≤
                    spaceLength (bodyVector3 (z t).1 i) ∧
                  spaceLength (bodyVector3 (z t).1 i) ≤
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ∧
                  |spatialSourceOscAxis (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerAxis (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| +
                    spaceLength (spatialSourceOscEccVector
                        (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerEccVector
                        (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ≤ Aelem * μ) ∧
              (∀ i, |spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| ≤
                    Aosc * μ ∧
                  |spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerApo (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| ≤
                    Aosc * μ) ∧
              (∀ i, dStar / 2 ≤
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i) ∧
              (∀ a : AdjIdx n, dPair / 2 ≤
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ)
                      a.upperIdx -
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) a.1)
```

  Bins for (A) are unchanged: SOURCE 8, STANDING 15, TYPING 7, EXCESS 0. The premises use source objects
  throughout. The only remaining raw formula is `spatialKeplerEnergy`, inside the literal carrier predicate.

  - **Twin consistency.** If (A) is adopted, the planar §3b may optionally be restated the same way for symmetry. It
    does not need to be, because its raw canonical helpers are frozen.
  - **Scope of the change.** The `_general` sibling (`odb-…Source`:40–120) needs the same change, minus `hνmax`,
    `hνle`.
  - **Dependent existentials.** `orderedStrongThreshold hn ⟨_, hcht⟩` and `hch` now have types that depend on `hs`
    and `h₀`. Proof irrelevance makes the values independent of these proofs, as with `hcht` in LP1.

- **(B).** Obtain an explicit owner ruling recorded under OD-11, then register it as RULED. Suggested ruling text:
  "OD-11 (b), spatial carve-out: `spatialKeplerAxis`, `spatialKeplerAction` and `spatialKeplerEccVector` are frozen as
  total algebraic formulas under the inherited convention of the frozen planar
  `keplerAxis/keplerAction/keplerEccVector` (D20/D25). They are consumed only under the guard
  `0 < |q_i| ∧ E_i < 0` that the anchor states or proves." The §3d text could then stay as it is, but the proposal
  must stop describing §3d as resolving N1 by source subtypes for every physical quantity. The SourceCarrier docstring
  (:20–22) must also be corrected.

### R4.2 — CHANGE-RECOMMENDED: §3c shows the implementation name and unused-binder names, not the anchor surface

Proposal §1 (:31) names LP2 `spatial_strongAMD_exponentialSafety`, by analogy with LP1's
`planar_strongAMD_exponentialSafety`, which §3 displays (:84–85). §3c (:309–310) instead displays the provider name
`lp2_spatial_strongAMD_safety_normalized`, with `_hνmax`/`_hνle`. Replace proposal:309–310 by:

```lean
theorem spatial_strongAMD_exponentialSafety (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
```

Leave the remainder of the §3c type unchanged; the producer `lp2_spatial_strongAMD_safety_normalized` closes it by
`exact`. If OD-11 (b) is adopted, the anchor surface is the §3d (or R4.1 (A)) text, and §1 should then name the
anchor exported under that text, as for §3b.

### R4.3 — CHANGE-RECOMMENDED: no spatial definition-freeze inventory in §4b

§4b (:483–503) lists only the planar objects, so the LP2 definition closure has no stated freeze policy. Append to
§4b:

> - **Spatial (LP2; OD-11 (b)).** The following are frozen **as literal formulas and predicates**, faithful on
>   their whole carriers:
>   - `spaceDot`, `spaceSq`, `spaceLength`, `spaceCross`, `bodyVector3`, `planetAngularMomentum3`,
>     `angularMomentum3`;
>   - `SpatialNoCollision`, `IsSpatialMovingSolutionOn`, `SpatialMovingUniqueOn`;
>   - `spatialMasses`, `spatialBarycentricPositions`, `spatialBarycentricVelocities`, `IsSpatialNewtonSolutionOn`;
>   - the carrier predicates `SpatialNegativeEnergy` and the subtypes `SpatialElliptic` (=
>     `SpatialSourceCanonicalPhase`) and `SpatialOscPhase` (= `SpatialSourceOsculatingPhase`).
>
>   The following are frozen **as one semantic unit with their `rfl` equations and the SourceCarrier
>   characterizations**:
>   - `spatialSourceKeplerAxis`, `spatialSourceKeplerAction`, `spatialSourceKeplerEccVector`,
>     `spatialSourceKeplerEcc`;
>   - `spatialSourcePlanetAngularMomentum`, `spatialSourceAngularMomentum`, `spatialSourceStrongAMD`;
>   - `spatialSourceKeplerPeri/Apo`;
>   - `spatialSourceOsc{Velocity,Param,Energy,Axis,EccVector,Ecc,Peri,Apo}`.
>
>   The total formulas stay **internal implementation helpers in the definition closure** and are not certified as
>   MAIN's objects off their carriers. These are `spatialKeplerEnergy` (used only inside the carrier predicate),
>   `spatialKeplerAxis/Action/EccVector`, `spatialStrongAMD`, `spatialStrongAMDOn`, `spatialKeplerPeri/Apo` and
>   `spatialOsc*`. The same holds for `spatialHamiltonian`, which is totalized at collisions and consumed only
>   through `IsSpatialMovingSolutionOn`, whose collision guard and `DifferentiableAt` on an open domain make the
>   predicate faithful (R4.8).
>
>   This bullet presupposes R4.1 (A); under R4.1 (B), move `spatialKeplerAxis/Action/EccVector` to the frozen list
>   with the recorded ruling.

### Notes

- **R4.4 — h₀/hs bracketing.** The spatial canonical carrier predicate is `∀ i, 0 < ν i ∧ 0 < |q_i| ∧ E_i < 0`
  (`Elements`:63–64). The planar one is `(∀ i, 0 < ν i) ∧ ∀ i, …`. They are logically equivalent, so the only §3b
  versus §3d difference is this regrouping in `h₀` and the three `hs`. The `ho` shape is identical to the planar one.
  Acceptable; no change needed.

- **R4.5 — Geometric L16 scope (unchanged from reviews 2–3).**
  - L16:525 says the ellipses pass through `q` and are tangent to `V`. LP2 exports only radial incidence
    `a^osc(1−e^osc) ≤ |q| ≤ a^osc(1+e^osc)` and the quantitative estimates.
  - The names `spatialOsc_tangency` (`Basic`:149–156) and "Tangency on the … carrier" (`SourceCarrier`:197–205,
    253–263) label radial inequalities; they do not prove geometric tangency.
  - LP2 is the T19 orbit application. It is not standalone L16 over arbitrary safe compact sets.
  - No Lean change is required for this anchor, but do not claim geometric-L16 closure.

- **R4.6 — Documentation misnomers, to fix before freeze.**
  - `Elements`:35 documents `spatialKeplerAxis` as "Osculating semimajor axis". It is the **canonical** axis
    `−1/(2E_i)`.
  - `Model`:21 says "(MAIN (1), literally; no totalization)". Lean division totalizes at `|q_i| = 0` or
    `q_i = q_j` (R4.8).
  - `SourceCarrier`:20–22 is false for §3d as written (R4.1).

- **R4.7 — `SpatialElliptic` is a `def … : Type`.** It is not an `abbrev` like planar `SourceCanonicalPhase`
  (`Elements`:67), though `SpatialSourceCanonicalPhase` is an `abbrev` of it. Anonymous construction elaborated on the
  branch (per the package), so this is harmless for statements. For a frozen carrier, an `abbrev` would be more
  transparent; optional.

- **R4.8 — `spatialHamiltonian` is totalized at collisions.** This mirrors the frozen planar `movingHamiltonian`. Its
  junk values never affect `IsSpatialMovingSolutionOn`:
  - the predicate requires `SpatialNoCollision` at every `t ∈ J`;
  - it requires `DifferentiableAt`/`HasDerivAt` at those points;
  - the collision-free set is open (`Model`:167–183), so the derivative there depends only on collision-free values.

  Classify it as an internal helper (R4.3), not a whole-carrier source object.

- **R4.9 — No spatial LP0 twin.** MAIN L5 is dimension-agnostic, but the proposal freezes no spatial barrier anchor.
  T19's conclusion does not require one, so this is not a defect of LP2. Record it if a source-complete d = 3 L5
  export is ever claimed.

## Checks performed

- Text identity and hashes: proposal ↔ attachments ↔ branch blobs, as recorded above (`sha256sum`,
  `git show inp-lp-spsrcb:…`, and a whitespace-normalized Python comparison).
- Mechanical twin token diffs §3→§3c and §3b→§3d (Python `difflib`), with exactly the differences listed.
- Full reading of `Vector.lean` definitions, `Model.lean`, `Elements.lean`, `Newton.lean` (definitions),
  `Osculating/Basic.lean`, `SourceCarrier.lean`, `SpatialSafety/Main.lean`, `SpatialSafety/Source.lean`, the
  signature of `SpatialSafety/Aligned.lean:46–65`, the frozen
  `Phase/IsHamiltonianSolutionOn/hamiltonianVectorField/IsMovingSolutionOn/MovingUniqueOn/IsNewtonSolutionOn`, and
  the THR2 threshold signatures on the branch.
- Sources: MAIN:1–140, 160–164, 500–603; AMENDMENTS; OWNER-DECISIONS (OD-1–OD-12); W4A audit 1 (N1); reviews 1–3.

**Not performed: any Lean, Lake or lint run** (the brief forbids Lean/Lake, and `scripts/lint_sources.sh` launches a
Lean ABI subprocess; review 1:383–395). This is a deviation from AGENTS "Before handing off". Consequently:

- The proposal's claims that `lp2_spatial_strongAMD_safety_normalized` and `lp2_spatial_strongAMD_safety_source` are
  proved with axioms `[propext, Classical.choice, Quot.sound]` (proposal:31,369) are **unverified by me**.
- The R4.1 (A) replacement text is **unelaborated**.
- The statement fidelity conclusions above rest on the exact text, not on compilation.

## Handoff

- **Files:** `docs/tracks/LP/freeze/STATEMENT-REVIEW-4.md` only (not staged, not committed).
- **Approach:** independent reconstruction of MAIN §1 (d = 3), T19 and L16; five-bin expansion; quantifier and
  forbidden-premise check; literal-body comparison of every meaning-carrying spatial definition; mechanical twin
  diffs; carrier/characterization audit; OD-11 (b) closure check.
- **Uncertainties:** R4.1 (A) needs transient elaboration and a proof before re-review. Final anchor naming (R4.2) and
  owner choices OD-1–OD-11 remain open. There is no independent proof-package audit of LP-SP-SAFE or LP-SP-SRC/SRCB.
- **Suspected errata in MAIN:** none new.
- **Deviations:** no lint run (above); LP2's normalization binders retained (no deviation); the static homogeneous
  extension does not apply to LP2.

## Hard rules (verbatim from AGENTS.md)

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

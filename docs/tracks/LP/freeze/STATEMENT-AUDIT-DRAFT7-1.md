# Independent statement audit: LP draft 7, round 1

**RETURN FOR REVISION**

Audited HEAD: `809aa0dd84ff6a7ba3ec4f33bc31af4768d60d01`, branch `inp-lp-freeze7`, worktree
`/root/code/KAM-inp-lp-freeze7`, 2026-11-01. Independent, refute-first; no subagents. Method:
`/root/.claude/skills/lean-statement-audit/SKILL.md`, read in full. Read AGENTS, PLAN, DECISIONS,
the entire audit brief, MAIN and N1–N12, SPEC, OWNER-DECISIONS, the previous reviews and the author's handoff.
D59 was read from `git show main:docs/DECISIONS.md`, rather than inferred from the worktree's older decisions.
Only this report is edited; nothing is committed. No frozen or manifest file is changed.

The five anchor types pass the mathematical input/output comparison, including the new LP0 source-AMD
restatement. The 34 characterization types have sorry-free implementations and the threshold minima are genuine.
The package nevertheless fails its advertised **whole-carrier** definition certification: four new total
formulas are labelled `literal`, faithful on their whole carriers, although their declared domains include
zero-denominator or negative-square-root cases outside the source. Two are used directly as physical
reconstruction maps in LP2/LP2-H. Existing planar total definitions are inherited D20/D25 conventions;
that precedent does not by itself approve new spatial whole-carrier source objects under D59(b).
This is a definition/freeze-surface return, not a counterexample to the guarded safety theorems.


| Pinned input | SHA-256 |
|---|---|
| `source/MAIN.md` | `68e9167f04e4a04689ea163c74e02ffcaea657b252726080abdbe37bdba48c1b` |
| `source/AMENDMENTS.md` | `c887d1e27354a3db7fb8a20d8bf3e33a9ef95ff3173f925ba5ebfab192651881` |
| `FREEZE-PROPOSAL.md` | `429830d26f76541d63e114ddba1a15937bcfec2102babf9d96d0ebe62dc3a6d5` |
| `freeze/draft7/manifest-entries.json` | `e377d75815a225b3102c2314594ae7e446d63802b16c3730e3e1c0c2fce97730` |

The 127 per-file SHA-256 identities are those in verification-draft-7.txt:7–133, all recomputed
and matched during this audit. The manifest entries supply each versioned ID, kind, path, export,
source range, state, provider identity and proposed closure; these remain approval drafts.

## Findings and exact changes

`P` means `docs/tracks/LP/FREEZE-PROPOSAL.md`. `D` means
`docs/tracks/LP/freeze/draft7/KAM/Frozen/`. Line citations into D refer to the `.lean.txt` draft,
not to an existing frozen Lean file.

| ID | Class | Finding and exact replacement |
|---|---|---|
| F1 | **BLOCKING** | New `spatialBarycentricPositions` and `spatialBarycentricVelocities` are unrestricted total maps, but their module role paragraphs certify physical meaning on the whole carrier. See D`Planetary/Spatial/Defs/SpatialBarycentricPositions.lean.txt:22` and `:31–35`, D`Planetary/Spatial/Defs/SpatialBarycentricVelocities.lean.txt:22` and `:31–33`, P:603–604. Adopt the guarded source exports and exact role replacement below; use those exports in both spatial anchors. A role-only rename to internal does not repair direct physical use in those anchors. |
| F2 | **BLOCKING** for the stated literal/whole-carrier certification | `actionAxis` and `eccDeficit` have the same unqualified literal-role paragraph, despite accepting zero masses and `u` outside the real square-root domain. D`Planetary/StrongAMD/Defs/ActionAxis.lean.txt:19–28`, D`Planetary/StrongAMD/Defs/EccDeficit.lean.txt:19–28`, P:556,558. Classify these two expressions as internal algebraic helpers, with the exact role paragraph below. Their abstract guarded uses in LP0 and in the threshold objective are valid. This does not ask to alter their formulas or LP0. |
| N1 | NOTE | File-form check 4 says frozen/Mathlib imports only, but all 39 theorem drafts also import their designated stub provider (e.g. D`Planetary/StrongAMD/Theorems/OrderedPairThresholdIsLeast.lean.txt:13`). This follows the existing frozen-anchor/provider convention and AGENTS rule 9. The simulated check (a) deliberately removes those provider imports; it is not a real-module check of the eventual provider/import graph. Carry that explicit limitation into freeze/seal verification. No declaration replacement. |
| N2 | CHANGE-RECOMMENDED | P:16–18 says only date/decision placeholders and hash fields change at freeze, although P:1358–1365 also requires filling `author_approval` and extending `ruling_ref`. Replace that sentence with the exact sentence below. |
| N3 | NOTE | Geometric conic incidence/tangency and standalone L16 on arbitrary safe compact sets remain outside the exported anchors. Radial incidence, element errors and half gaps are present. P:1443 and review 4:491–496 carry this correctly. No replacement. |
| N4 | NOTE | Literal/source bodies have been checked and the ordinary characterizations are proved, but the proposed frozen characterizations still contain `by sorry`. Freeze and seal must finish before any semantic unit is admitted or consumed as sealed. P:1409–1411 already records this. No source-node promotion follows from this audit. |

F1 is witnessed without any dynamical argument. Set `n=2`, `μ=1`, `ν=(-2,1)` and
`q_0=(1,0,0)`, `q_1=(3,0,0)`. The total mass `1+μΣν` is zero and the numerator `Σν_iq_i`
is `(1,0,0)`. Lean division by zero makes the proposed stellar position zero. The mass-weighted
sum of the returned positions is then `(1,0,0)`, not zero: the output is not a barycentric
reconstruction. For velocities take `ν_0=0` and `p_0=(1,0,0)`; the returned planet velocity is
zero by totalized division and cannot satisfy `p_0=ν_0 V_0`. These inputs belong to the
*declared* carriers. MAIN:100 and :106 require positive masses. The actual anchors supply positive
masses and positive μ, so these examples do not refute their conclusions.

For F2, `actionAxis (ν_i=0) (I_i=1) i=0`; MAIN:43–45 works with the standing positive masses.
`eccDeficit 2=1` because `Real.sqrt (-3)=0`; the real source expression `1−√(1−u²)` has no
such value there. MAIN:47–51 uses `u,v∈[0,1]`, and LP0 explicitly quantifies `e∈[0,1]^n`.
The frozen-role paragraph must distinguish a literal Lean expression from a physical/source object
on its entire Lean carrier, just as the proposal already does for `pairThreshold` and `spatialHamiltonian`.

Exact role replacement for the four raw helpers in F1/F2, in their module docstrings:

> Freeze role (D59, OD-11 (b)): an internal total algebraic helper in the definition closure.
> No source-object meaning is asserted off the source domain. Source-facing uses must supply
> positive masses; barycentric reconstruction also supplies positive μ. The eccentricity-deficit
> expression is interpreted only on [0,1]. Source-facing restrictions and guarded predicates,
> rather than this total helper alone, carry the physical meaning.

Change the corresponding four role cells in P §4.2 from `literal` to `internal`, and add the four names
to the internal-helper inventory in §4.4. For F1 also add these **new**, source-facing declarations,
each in its own frozen definition file (plus manifest/closure entries); the old raw helpers retain their bodies:

```lean
namespace KAM.Planetary.Spatial

def spatialSourceBarycentricPositions {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ)
    (_hν : ∀ i, 0 < ν i) (_hμ : 0 < μ) (q : Fin (n * 3) → ℝ) :
    Fin (n + 1) → (Fin 3 → ℝ) := spatialBarycentricPositions ν μ q

def spatialSourceBarycentricVelocities {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ)
    (_hν : ∀ i, 0 < ν i) (_hμ : 0 < μ) (p : Fin (n * 3) → ℝ) :
    Fin (n + 1) → (Fin 3 → ℝ) := spatialBarycentricVelocities ν μ p

end KAM.Planetary.Spatial
```

In each spatial anchor replace `∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →` by
`∀ μ : ℝ, ∀ hμ : 0 < μ, μ ≤ μ₀ →`, and replace the two reconstruction expressions by
`spatialSourceBarycentricPositions ν μ hν hμ (z t).1` and
`spatialSourceBarycentricVelocities ν μ hν hμ (z t).2`. These source-premise proof arguments
remove the zero-denominator cases; they add no new mathematical premise. Their applications reduce
by definition to the existing expressions, so the ordinary LP producer theorem types need not change.
The proposed fix is exact review text, not a claim that those additional files were created or checked here.
Regenerate the approval object and counts and repeat the identity/consumption checks after the change.

Exact replacement for P:16–18 (N2):

> At freeze, fill `<APPROVAL-DATE>` and `<DECISION>` in each module docstring, fill the manifest's
> `author_approval`, extend each `split_policy.ruling_ref` with the exact-text approval decision,
> and compute every `TBD at freeze` hash; all other approved declaration bytes remain unchanged.

### Exact anchor identities

All five have kind theorem and draft state DRAFT_SORRY, approval PENDING; their proposed
provider exports are listed below, not assumed to be installed.

| Versioned ID | Frozen export | Frozen path | Provider export |
|---|---|---|---|
| `planetary.d59.planar_strongAMD_barrier.v1` | `KAM.Planetary.StrongAMD.planar_strongAMD_barrier` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDBarrier.lean` | `KAM.Provider.Planetary.StrongAMD.planar_strongAMD_barrier` |
| `planetary.d59.planar_strongAMD_exponentialSafety.v1` | `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean` | `KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety` |
| `planetary.d59.planar_strongAMD_exponentialSafety_halfInteger.v1` | `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyHalfInteger.lean` | `KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger` |
| `planetary.d59.spatial_strongAMD_exponentialSafety.v1` | `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafety.lean` | `KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety` |
| `planetary.d59.spatial_strongAMD_exponentialSafety_halfInteger.v1` | `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyHalfInteger.lean` | `KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger` |

## Source reconstruction and five-bin audit

MAIN:11–15 fixes `n≥2`, positive normalized ν, compact ordered positive axes (possibly empty),
δ,γ>0 and τ>n−1. MAIN:17–39 fixes the exact Hamiltonian, physical time, scaled canonical momenta,
and orientation-free normalized AMD. MAIN:43–55 defines all threshold minima on the chamber.
MAIN:64–65 uses radian frequencies and integer ℓ¹ modes. MAIN:69–93 chooses constants before μ
and every allowed state, and gives the full drift/moving-threshold/annulus/distance conclusions.
L5:164 adds the abstract deficit-list branch, compact physical containment and invariable-frame bounds.
L16:510–529 supplies actual velocity, parameter `1+μν_i`, element/endpoint errors, validity and the
N10 half-gap inequalities. L17–L19 introduce no prograde, inclination or reference-frame input into T19.
N1–N7, N9, N11–N12 are proof/engineering provisions; N8 and N10 affect this surface explicitly.

No anchor has an instance/typeclass input, source-normal-form supplier, stopped-drift assumption,
secular condition, prescribed inclination, positive signed L, nonzero total L, or an osculating-validity
input. Guards on the competing solutions in the uniqueness predicate are conclusion-local.

### LP1 and LP2, and their half-integer corollaries

The following is one row per binder or expanded logical component. It applies separately to each of
LP1, LP2, LP1-H, LP2-H; rows marked “general only” are absent in the two corollaries. The spatial
`h₀` is earlier in the telescope, immediately after the physical premise; this does not change its bin.
Exact declaration evidence is P:134–210 (LP1), P:230–306 (LP1-H), P:321–405 (LP2), P:423–507 (LP2-H).
The file-inventory appendix gives the exact declaration starting lines independently of these section ranges.

| Expanded input | Bin | Source or justification |
|---|---|---|
| implicit `n : ℕ` | TYPING | MAIN:11 |
| `hn : 2≤n` | STANDING | MAIN:11 |
| `ν : Fin n→ℝ` | STANDING | MAIN:11 |
| `hν : ∀i,0<ν_i` | STANDING | MAIN:11 |
| `hνmax : ∃i,ν_i=1` | STANDING | MAIN:11; D59 OD-3 |
| `hνle : ∀i,ν_i≤1` | STANDING | MAIN:11; D59 OD-3 |
| `A` | STANDING | MAIN:11–14 |
| `hA : IsCompact A` | STANDING | MAIN:11–15; empty allowed |
| `hAord`, positive axes | STANDING | MAIN:13 |
| `hAord`, all ordered pairs of axes | STANDING | MAIN:13 |
| `δ` | STANDING | MAIN:15 |
| `γ` | STANDING | MAIN:15 |
| `τ` (general only) | STANDING | MAIN:15 |
| `hδ` | STANDING | MAIN:15 |
| `hγ` | STANDING | MAIN:15 |
| `hτ` (general only) | STANDING | MAIN:15; D59 OD-4 |
| `μ` | SOURCE | MAIN:70 |
| anonymous `0<μ` | SOURCE | MAIN:70 |
| anonymous `μ≤μ₀` | SOURCE | MAIN:70 |
| `z₀ : Phase (n*d)` | TYPING | MAIN:26–37,70 |
| physical premise: all star distances positive | SOURCE | MAIN:70 |
| physical premise: all Kepler energies negative | SOURCE | MAIN:70; Lean energy is ν_i times specific E_i |
| initial axes belong to A | SOURCE | MAIN:72 |
| every nonzero integer mode satisfies (5) | SOURCE | MAIN:64–65 |
| `hch`: positive actions | TYPING | positive masses and negative energies |
| `hch`: ordered action axes | TYPING | axes in A; Λ_i²=ν_i²a_i |
| `h₀`: positive masses | TYPING | duplicate of hν |
| `h₀`: nonzero positions | TYPING | duplicate physical premise |
| `h₀`: negative energies | TYPING | duplicate physical premise |
| source AMD ≤ ordered B − δ | SOURCE | MAIN:35,72; D59 OD-1/2/11 |

Counts per general anchor: SOURCE 8, STANDING 15, TYPING 7, EXCESS 0,
CONCLUSION-SHAPED 0. Counts per half-integer anchor: SOURCE 8, STANDING 13,
TYPING 7, EXCESS 0, CONCLUSION-SHAPED 0. RULED corrections add no extra hypothesis;
D59 fixes conventions rather than authorizing excess premises.

The internal Diophantine quantifiers `k : Fin n→ℤ`, `k≠0`, and finite summation index `i` are
SOURCE/TYPING indexing of (5), not an additional arithmetic gate. `modeSize` is precisely
`Σ |(k_i:ℝ)|`, with no 2π factor. Both corollary signatures are byte-identical to the general
signature after the declared theorem-name change, deletion of τ/hτ, substitution of `n−1/2` in (5),
and explicit replacement of the time denominator by `2n+1`. No other premise or conclusion changes.

### LP0 (new sourceStrongAMD text)

Evidence: P:83–114; D`Planetary/StrongAMD/Theorems/PlanarStrongAMDBarrier.lean.txt`.

| Expanded input | Bin | Source or justification |
|---|---|---|
| implicit n | TYPING | MAIN:11 |
| hn | STANDING | MAIN:11 |
| ν | STANDING | MAIN:11; L4/L5 arbitrary positive masses |
| hν | STANDING | MAIN:11; L4/L5 |
| U | SOURCE | MAIN:164 |
| compact hU | SOURCE | MAIN:164 |
| hUch: positive actions | SOURCE | MAIN:43,164 |
| hUch: ordered axes | SOURCE | MAIN:43,164 |
| m | SOURCE | MAIN:164 |
| hm | SOURCE | MAIN:164 |
| physical z | TYPING | MAIN:26–37 |
| nonzero positions | STANDING | MAIN:24,28 |
| negative energies | SOURCE | MAIN:164 |
| hΛ: actions in U | SOURCE | MAIN:164 |
| h: positive masses | TYPING | hν |
| h: nonzero positions | TYPING | preceding physical premise |
| h: negative energies | TYPING | preceding physical premise |
| source AMD ≤ B−m | SOURCE | MAIN:164 |

Physical-branch counts: SOURCE 9, STANDING 4, TYPING 5, EXCESS 0,
CONCLUSION-SHAPED 0. The extra typing proof is supplied by `⟨hν,hphys⟩`, after hΛ;
it asserts no separation, nonradiality or dynamical conclusion.

| Abstract-list branch input (after dStar,dPair are chosen) | Bin | Source |
|---|---|---|
| I | TYPING | MAIN:164 |
| hI:I∈U | SOURCE | MAIN:164 |
| e | TYPING | MAIN:164 |
| all e_i≥0 | SOURCE | MAIN:164 |
| all e_i≤1 | SOURCE | MAIN:164 |
| Σ I_i D(e_i)≤B−m | SOURCE | MAIN:164 |

Here SOURCE 4, TYPING 2, all other bins zero. The compact K is chosen before every physical
state and is contained in the collision-free negative-energy region. The final `|L_i|≥m`
and `L_i L>0` encode precisely the planar invariable-frame lower bound. No `max ν=1` input is
needed in the static L5 statement; the proposal discloses this extension, already reviewed in rounds 1–3.

### Quantifiers and conclusions

All nine positive dynamical constants precede μ and z₀; they may depend only on standing data,
not on phases, orientation, eccentricities or a chosen subset of the AMD sublevel. LP0 similarly
chooses its floors before both branches and chooses K before z. Empty A or U is allowed.

For each of LP1/LP2/LP1-H/LP2-H, the conclusion has the closed physical-time interval,
Hamilton solutionhood, overlap uniqueness, Newtonian reconstruction, negative energy and chamber,
`O(√μ)` action and axis drift in the Pi sup norm, AMD drift `n AΛ√μ`, moving margin δ/2,
canonical perihelia and adjacent radial gaps, every star distance and every unequal pair distance,
valid actual-velocity elements, the SUM of axis and Euclidean eccentricity-vector errors,
both radial endpoint errors, and the star/adjacent osculating half gaps. Both N10 inequalities
are chosen before μ. Canonical e<1 follows from a>0 and the positive perihelion floor.

This checks MAIN (7)–(9) and the quantitative orbit application of L16. It does not turn the
radial inequalities into a separately exported conic/tangency theorem (N3).

Expansion evidence: frozen `IsMovingSolutionOn.lean:35`, `IsHamiltonianSolutionOn.lean:37`,
`HamiltonianVectorField.lean:24`, `MovingUniqueOn.lean:37`, `IsNewtonSolutionOn.lean:36`;
spatial draft `IsSpatialMovingSolutionOn.lean.txt:31`, `SpatialMovingUniqueOn.lean.txt:30`,
`IsSpatialNewtonSolutionOn.lean.txt:28`. The Hamilton field is `(∂pH,−∂qH)`; moving solutionhood
adds collision freedom at each time and differentiability. Newton solutionhood expands to all-body
separation, Q′=V, V′ equal to the full Newton sum with Euclidean distance cubed. The recoil term
is μ|Σp|²/2; no fixed-Sun or time-rescaled system has been substituted.

## Definitions and characterization units

All 88 new bodies were read, including all wrappers, predicates and raw helpers, not just their
signatures. Their types, values and reducibility were compared to the implementation by replay (b).
There is no classical choice of an optimizer or orbit, no if/default branch, and no selected
family in a source wrapper. Real division and square root totalization still matter (F1/F2).

`SourceCanonicalPhase` includes positive ν, nonzero positions and negative energy, including
radial e=1. The osculating carriers include positive ν,μ, nonzero positions, negative osculating
energy and eosc<1; hence k>0 and their reciprocal denominators are nonzero. Their validity is an
existential OUTPUT along an orbit, not an input restriction on the initial data. The spatial
aliases `SpatialSourceCanonicalPhase` and `SpatialSourceOsculatingPhase` unfold to the intended
carriers despite `SpatialElliptic` being a def rather than abbrev.

At fixed positive source ν, `OrderedActions ν` is precisely Q. Pair feasibility is compact and
nonempty, including its boundary: `(u,v)=(1,1)` is feasible, and the objective is continuous on
[0,1]². The image is nonempty, bounded below and attains its minimum; `IsLeast` identifies its
unique scalar value, without claiming a unique eccentricity minimizer. `hn:2≤n` excludes empty
adjacent and star index families. There is no empty real infimum on the guarded source carrier.
The raw parameter ν is not itself a positive-mass subtype; source interpretation throughout this
threshold unit is under the standing positive ν, as in the anchors and MAIN. No physical
interpretation at ν_i=0 is certified here.

For cross/strong characterizations, a:AdjIdx n maps to `(i,j)=(a.1,a.upperIdx)` with
`j.val=i.val+1`. Conversely `(j:ℕ)=i+1`, with j:Fin n, gives `i.val+1<n` and exactly that
adjacent index. Coercion to ℕ prevents wraparound at the last index. `IsLeast` includes membership,
so it proves attainment, not just a lower bound. Union with `Set.range I.1` takes the least of
all adjacent pair values and all actions, exactly `min(Bcross,Bstar)`, not a sum, intersection
or first-coordinate shortcut. The inlined `Nat.lt_succ_self a.1.val` supplies the same proposition
as `AdjIdx.lt_upperIdx`; proof irrelevance explains its definitional equality in replay (b).

All 34 characterization statements were compared individually with L2–L4/L16 and replayed in
(c). Positivity, angular momentum magnitude, squared eccentricity, radial incidence and AMD
inequalities concern the declared definitions and the entire guarded carrier. The three spatial
osculating validity facts read from carrier membership are legitimate subtype properties, not
proofs of global dynamical validity. Literal restriction bodies without a separate listed theorem
have `CHARACTERIZATION: N/A_LITERAL`; none uses deferred reconstruction.

Definition status keys used in the appendix:

- `L`: BODY_MATCH OK; PUBLIC_CARRIER OK for the total algebraic/predicate object;
  WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; PASS.
- `C`: BODY_MATCH OK; PUBLIC_CARRIER OK on the stated source carrier; WELL_DEFINEDNESS
  N/A_LITERAL; CHARACTERIZATION OK where listed, otherwise N/A_LITERAL; CHOICE_INDEPENDENCE N/A; PASS.
- `T`: BODY_MATCH OK on fixed positive source masses; PUBLIC_CARRIER OK on Q and the stated
  n/i/j guards; WELL_DEFINEDNESS OK; CHARACTERIZATION OK by the proved minimum-value results;
  CHOICE_INDEPENDENCE N/A (no optimizer choice); PASS for the guarded threshold unit.
- `H`: exact internal algebraic body and dependency inventory OK; no independent off-carrier
  physical-object verdict is issued. The source restriction is audited separately as C/T.
- `F`: BODY_MATCH OK_ON_SOURCE_INPUTS; PUBLIC_CARRIER FAIL_AS_WHOLE_CARRIER_SOURCE_OBJECT;
  WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A;
  DEFINITION_VERDICT FAIL_AS_ADVERTISED (F1/F2).

## File form, identity, closure and rebase

There are exactly 127 unique draft paths/exports/manifest entries: 88 definitions and 39 theorems.
Every file has copyright, module, module docstring, the expose/public section form, exactly one
public declaration and closing namespace/section commands. Maximum draft length is 153 lines.
All definitions are sorry-free; each theorem has exactly one `by sorry` in its proof markers.
No resource override or forbidden proof escape was introduced. Definitions import frozen/Mathlib
modules only; the 39 theorem-provider imports are the N1 convention exception to the brief's wording.
Provider modules/exports agree with the manifest and stated sealed bodies. No actual provider files
or approval are pretended to exist.

Independently checked: every one of the 127 declaration regions is exactly the text used in the
existing (b)/(c) scratch check after the documented namespace/proof replacement; every one of the
127 proposal Lean excerpt segments is an exact draft-file excerpt. All 127 whole-file hashes and
the manifest draft hash match verification-draft-7.txt. This establishes identity of the text checked,
not physical meaning. Check (c) imports implementation definitions; replay (b) supplies the definitional
body-equality bridge. Check (a) inlines dependencies rather than exercising real frozen module boundaries.

The recomputed type/definition-value closure is 85 new definitions plus 21 already-frozen definitions;
the three additional source wrappers are exactly sourceOscVelocity, sourceOscParam and
spatialSourceOscVelocity. Raw crossThreshold/starThreshold/strongThreshold and spatialStrongAMD/On
are absent for the reasons in P:645–654. The unfrozen `AdjIdx.lt_upperIdx` occurs only in the
implementation proof-argument closure and is eliminated from the draft definition by its inlined
proof. Generated `_proof_*` constants belong to their owning files, not to independent unfrozen
source exports. No additional meaning-carrying definition is missing from the inventory.

Independently traversed all actual frozen imports and compared the full transitive definition-file
sets with all 127 manifest `definition_closure` lists: no missing or extra member. This larger
import closure also includes the already-frozen core/P definitions imported indirectly by old
broad interfaces; it is not confused with the 21 semantic constants or the 19 directly reused ones.
TBD hashes and PENDING approval are proper draft fields, not valid current seals. IDs, version 1,
paths and provider exports agree; all existing frozen/manifest bytes are untouched.

The original rebase strategy is mechanically sound **for the original declarations**: same names,
definitional bodies and reducibility let implementation theorem statements remain unchanged; delete
definitions, public-import their new definition modules; keep raw implementation helper theorems.
The shared modeSize edit needs the orchestrator, not an LP prover. Cross's proof-term replacement
is defeq. Moving characterizations into providers requires the two sibling-proof inlinings already
identified at P:1396–1403. A provider must never import another provider or its own frozen theorem;
ordinary implementation imports can supply all remaining lemmas. After seal D58 permits frozen
characterization imports. A future real-module build and post-rebase print-axioms pass remain mandatory.
F1's additional source wrappers require updating this plan and the draft inventory; they do not
require changing an ordinary LP theorem type, since the applied wrappers unfold to the old maps.

### Author choices and uncertainties

| Handoff choice | Audit disposition |
|---|---|
| 1 paths/namespaces | consistent; manifest and namespaces agree |
| 2 same implementation names | exact type/body checks support unchanged ordinary theorem statements |
| 3 characterization anchors; rfl equations in bodies | adequate for literal restrictions; actual semantic admission waits for seal |
| 4 closure + extra source set | independently recomputed; 85+3 new definitions, all accounted for |
| 5 modeSize freeze | ℓ¹ real formula exact; shared-module edit correctly escalated to orchestrator |
| 6 inlined index proof | type-correct, rfl equal by proof irrelevance; no hidden analytical premise |
| 7 imports | five fresh (a) samples pass; provider imports omitted by simulation, N1 |
| 8 definition_closure | all 127 lists independently traversed and equal; complete imported-definition convention |
| 9 module docstrings | overall form good; four whole-carrier role claims fail, F1/F2 |
| 10 terminology/reflow | canonical axis and radial-incidence corrections present; no type change |
| 11 LP1 whitespace | confirmed no semantic effect; half-integer signatures compared independently |
| 12 split policy/ruling | draft IDs/version/schema consistent; final exact-text ruling still required, N2 |
| uncertainty: provider files/commits not drafted | not yet a post-rebase provider/seal audit; plan reviewed, actual imports/seals remain future gates |
| uncertainty: concatenated module simulation | retained; cannot claim module visibility was tested across real new frozen paths |

Prior notes: review 1 F1/F2 full quantitative outputs are present; F3 repaired threshold guards and
characterizations are integrated; F4 source-AMD/Kepler/osculating restrictions are present;
F5 normalization retained. Review 4 R4.1(A), names and spatial inventory corrections are present.
R4.4/R5.4–5 binder-shape/adjacency differences remain harmless. R4.5/R4.9 scope limitations remain
explicit. R4.6's frozen axis docstring is fixed; its implementation Model docstring remains an
owner follow-up, outside this report. R4.7 def/abbrev is unchanged and elaborates; R4.8 total
Hamiltonian remains internal with the collision/differentiability guard. R5.1 wording is repaired
in §4.4, R5.2 optional implementation prose remains optional, R5.3 stale proposal prose is removed,
and R5.6–7 historical handoff details are not new closure claims. The new F1/F2 findings concern
remaining whole-carrier claims in the expanded exact freeze inventory, beyond those earlier deltas.

## Commands and fresh outputs

All commands ran from `/root/code/KAM-inp-lp-freeze7`. Define the following notation solely to
shorten the transcript (the actual invocations used these arguments):

```sh
W='systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1'
```

No Lean/Lake invocations ran concurrently. The whole lint driver, including its ABI Lean child,
ran within the same capped scope. No whole-library build, clean, source regeneration or heartbeat
change was run. Required build artifacts are not source edits.

| Command | Fresh result |
|---|---|
| `git status --short`; `git rev-parse HEAD` | initially clean; HEAD recorded above |
| `git show main:docs/DECISIONS.md` | D53, D56–D59 read; D59 exact-text approval still pending |
| `$W lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .drafts/freeze7/c_verification.lean` | exit 0; all 39 `TYPE_EQV THEOREM REDUCIBILITY_SAME`; all 39 axiom lists `[propext, Classical.choice, Quot.sound]` |
| same Lean command on `.drafts/freeze7/b_bodies_equal.lean` | exit 0; 88 rfl equations, 88 TYPE_EQV/REDUCIBILITY_SAME; 77 VALUE_EQV, 11 VALUE_NOT_EQV (auxiliary proof terms; inspected b2_value_diff.out) |
| same Lean command on `.drafts/freeze7/closure.lean` | exit 0; closure listed; 85 new + 21 old definition constants, plus proof auxiliaries |
| same Lean command on `.drafts/freeze7/a/KAM_Frozen_Fourier_Defs_ModeSize.lean` | exit 0, empty output |
| same on `a/KAM_Frozen_Planetary_StrongAMD_Defs_OrderedCrossThreshold.lean` | exit 0, empty output |
| same on `a/KAM_Frozen_Planetary_Spatial_Defs_SpatialBarycentricPositions.lean` | exit 0, empty output |
| same on `a/KAM_Frozen_Planetary_StrongAMD_Theorems_PlanarStrongAMDBarrier.lean` | exit 0; line 234:8, one expected declaration-uses-sorry warning |
| same on `a/KAM_Frozen_Planetary_Spatial_Theorems_SpatialStrongAMDExponentialSafety.lean` | exit 0; line 841:8, one expected declaration-uses-sorry warning |
| `$W lake build KAM.Planetary.StrongAMD.PlanarSafety.SourceThreshold` | exit 0, `Build completed successfully (9051 jobs).` |
| `$W lake build KAM.Planetary.StrongAMD.PlanarSafety.SourceCorollary` | exit 0, `Build completed successfully (9316 jobs).`; cached dependency lint warnings |
| `$W lake build KAM.Planetary.Spatial.SpatialSafety.SourceCorollary` | exit 0, `Build completed successfully (9366 jobs).`; cached dependency lint/deprecation warnings |
| `$W lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false --stdin` with the five direct `#print axioms` commands below | exit 0; all five `[propext, Classical.choice, Quot.sound]` |
| `$W scripts/lint_sources.sh` | exit 0; `check_lean_modules: PASS (3780 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))` |
| Python read-only identity/closure scans | 127 file hashes and manifest hash agree; 127 declaration matches; 127 excerpt matches; 127 import-definition closures agree |
| Python exact general/corollary declaration comparison | `planar exact signature specialization: True`; `spatial exact signature specialization: True` |
| `git diff 701c239b --stat -- KAM/Frozen manifest README.md KAM.lean` | empty |

The build dependency warnings include existing unused variables in Nekhoroshev/Partial/Transfer,
unused simp arguments in StrongAMD/NonresonantReuse/Pert and Spatial/Alignment, and deprecated
dif_pos in Planetary/Exponential/ComplexTube. They are not default-heartbeat failures or new audit edits.
No claimed clean-warning build is inferred from exit 0.

Direct axiom input (supplied on stdin; no new scratch file):

```lean
import KAM.Planetary.StrongAMD.PlanarSafety.SourceCorollary
import KAM.Planetary.Spatial.SpatialSafety.SourceCorollary
#print axioms KAM.Planetary.StrongAMD.lp0_planar_barrier_source
#print axioms KAM.Planetary.StrongAMD.lp1_planar_strongAMD_safety_source
#print axioms KAM.Planetary.StrongAMD.lp1_planar_strongAMD_safety_source_halfInteger
#print axioms KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_source
#print axioms KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_source_halfInteger
```

For each **proposed** anchor:

```text
DECLARATION_FIDELITY: PASS for the guarded mathematical theorem
DRAFT_ALLOWLIST: PASS_AS_DRAFT_TEXT (one by sorry, declared DRAFT_SORRY; not a current manifest permission)
PROOF_STATUS: PROPOSED_UNFROZEN; would be FROZEN_UNPROVED until its exact frozen export is sealed
```

The ordinary producers and check-(c) aliases have clean axiom closure. The `by sorry` draft exports
themselves do not: no claim of frozen theorem/axiom closure is made.

## Per-definition inventory and per-characterization evidence

The following rows cover all 88 bodies. Evidence paths start after D; line is the actual declaration
line. T covers the minimum-value semantic unit; C includes source-carrier aliases. H is a deliberately
internal expression, not a whole-carrier physical object. F records the precise failed role claim.

| # | Definition | Draft evidence | Role/status |
|---|---|---|---|
| 1 | `KAM.Fourier.modeSize` | `Fourier/Defs/ModeSize.lean.txt:28` | literal; L |
| 2 | `KAM.Planetary.StrongAMD.actionAxis` | `Planetary/StrongAMD/Defs/ActionAxis.lean.txt:27` | literal; F |
| 3 | `KAM.Planetary.StrongAMD.chamber` | `Planetary/StrongAMD/Defs/Chamber.lean.txt:27` | literal; L |
| 4 | `KAM.Planetary.StrongAMD.eccDeficit` | `Planetary/StrongAMD/Defs/EccDeficit.lean.txt:27` | literal; F |
| 5 | `KAM.Planetary.StrongAMD.pairFeasible` | `Planetary/StrongAMD/Defs/PairFeasible.lean.txt:28` | literal; L |
| 6 | `KAM.Planetary.StrongAMD.pairObjective` | `Planetary/StrongAMD/Defs/PairObjective.lean.txt:27` | literal; L |
| 7 | `KAM.Planetary.StrongAMD.pairThreshold` | `Planetary/StrongAMD/Defs/PairThreshold.lean.txt:32` | internal; H |
| 8 | `KAM.Planetary.StrongAMD.AdjIdx` | `Planetary/StrongAMD/Defs/AdjIdx.lean.txt:27` | literal; L |
| 9 | `KAM.Planetary.StrongAMD.AdjIdx.upperIdx` | `Planetary/StrongAMD/Defs/AdjIdxUpperIdx.lean.txt:27` | literal; L |
| 10 | `KAM.Planetary.StrongAMD.OrderedActions` | `Planetary/StrongAMD/Defs/OrderedActions.lean.txt:26` | carrier; C |
| 11 | `KAM.Planetary.StrongAMD.orderedPairThreshold` | `Planetary/StrongAMD/Defs/OrderedPairThreshold.lean.txt:29` | source; T |
| 12 | `KAM.Planetary.StrongAMD.orderedCrossThreshold` | `Planetary/StrongAMD/Defs/OrderedCrossThreshold.lean.txt:32` | source; T |
| 13 | `KAM.Planetary.StrongAMD.orderedStrongThreshold` | `Planetary/StrongAMD/Defs/OrderedStrongThreshold.lean.txt:28` | source; T |
| 14 | `KAM.Planetary.StrongAMD.strongAMD` | `Planetary/StrongAMD/Defs/StrongAMD.lean.txt:31` | internal; H |
| 15 | `KAM.Planetary.StrongAMD.keplerPeri` | `Planetary/StrongAMD/Defs/KeplerPeri.lean.txt:31` | internal; H |
| 16 | `KAM.Planetary.StrongAMD.keplerApo` | `Planetary/StrongAMD/Defs/KeplerApo.lean.txt:31` | internal; H |
| 17 | `KAM.Planetary.StrongAMD.oscVelocity` | `Planetary/StrongAMD/Defs/OscVelocity.lean.txt:29` | internal; H |
| 18 | `KAM.Planetary.StrongAMD.oscParam` | `Planetary/StrongAMD/Defs/OscParam.lean.txt:28` | internal; H |
| 19 | `KAM.Planetary.StrongAMD.oscEnergy` | `Planetary/StrongAMD/Defs/OscEnergy.lean.txt:35` | internal; H |
| 20 | `KAM.Planetary.StrongAMD.oscAxis` | `Planetary/StrongAMD/Defs/OscAxis.lean.txt:30` | internal; H |
| 21 | `KAM.Planetary.StrongAMD.oscEccVector` | `Planetary/StrongAMD/Defs/OscEccVector.lean.txt:34` | internal; H |
| 22 | `KAM.Planetary.StrongAMD.oscEcc` | `Planetary/StrongAMD/Defs/OscEcc.lean.txt:32` | internal; H |
| 23 | `KAM.Planetary.StrongAMD.oscPeri` | `Planetary/StrongAMD/Defs/OscPeri.lean.txt:30` | internal; H |
| 24 | `KAM.Planetary.StrongAMD.oscApo` | `Planetary/StrongAMD/Defs/OscApo.lean.txt:30` | internal; H |
| 25 | `KAM.Planetary.StrongAMD.SourceCanonicalPhase` | `Planetary/StrongAMD/Defs/SourceCanonicalPhase.lean.txt:30` | carrier; C |
| 26 | `KAM.Planetary.StrongAMD.SourceOsculatingPhase` | `Planetary/StrongAMD/Defs/SourceOsculatingPhase.lean.txt:31` | carrier; C |
| 27 | `KAM.Planetary.StrongAMD.sourceStrongAMD` | `Planetary/StrongAMD/Defs/SourceStrongAMD.lean.txt:28` | source; C |
| 28 | `KAM.Planetary.StrongAMD.sourceKeplerPeri` | `Planetary/StrongAMD/Defs/SourceKeplerPeri.lean.txt:28` | source; C |
| 29 | `KAM.Planetary.StrongAMD.sourceKeplerApo` | `Planetary/StrongAMD/Defs/SourceKeplerApo.lean.txt:28` | source; C |
| 30 | `KAM.Planetary.StrongAMD.sourceOscVelocity` | `Planetary/StrongAMD/Defs/SourceOscVelocity.lean.txt:28` | source; C |
| 31 | `KAM.Planetary.StrongAMD.sourceOscParam` | `Planetary/StrongAMD/Defs/SourceOscParam.lean.txt:28` | source; C |
| 32 | `KAM.Planetary.StrongAMD.sourceOscEnergy` | `Planetary/StrongAMD/Defs/SourceOscEnergy.lean.txt:28` | source; C |
| 33 | `KAM.Planetary.StrongAMD.sourceOscAxis` | `Planetary/StrongAMD/Defs/SourceOscAxis.lean.txt:28` | source; C |
| 34 | `KAM.Planetary.StrongAMD.sourceOscEccVector` | `Planetary/StrongAMD/Defs/SourceOscEccVector.lean.txt:28` | source; C |
| 35 | `KAM.Planetary.StrongAMD.sourceOscEcc` | `Planetary/StrongAMD/Defs/SourceOscEcc.lean.txt:28` | source; C |
| 36 | `KAM.Planetary.StrongAMD.sourceOscPeri` | `Planetary/StrongAMD/Defs/SourceOscPeri.lean.txt:28` | source; C |
| 37 | `KAM.Planetary.StrongAMD.sourceOscApo` | `Planetary/StrongAMD/Defs/SourceOscApo.lean.txt:28` | source; C |
| 38 | `KAM.Planetary.Spatial.spaceDot` | `Planetary/Spatial/Defs/SpaceDot.lean.txt:28` | literal; L |
| 39 | `KAM.Planetary.Spatial.spaceSq` | `Planetary/Spatial/Defs/SpaceSq.lean.txt:28` | literal; L |
| 40 | `KAM.Planetary.Spatial.spaceLength` | `Planetary/Spatial/Defs/SpaceLength.lean.txt:28` | literal; L |
| 41 | `KAM.Planetary.Spatial.spaceCross` | `Planetary/Spatial/Defs/SpaceCross.lean.txt:28` | literal; L |
| 42 | `KAM.Planetary.Spatial.bodyVector3` | `Planetary/Spatial/Defs/BodyVector3.lean.txt:28` | literal; L |
| 43 | `KAM.Planetary.Spatial.planetAngularMomentum3` | `Planetary/Spatial/Defs/PlanetAngularMomentum3.lean.txt:29` | literal; L |
| 44 | `KAM.Planetary.Spatial.angularMomentum3` | `Planetary/Spatial/Defs/AngularMomentum3.lean.txt:29` | literal; L |
| 45 | `KAM.Planetary.Spatial.spatialHamiltonian` | `Planetary/Spatial/Defs/SpatialHamiltonian.lean.txt:34` | internal; H |
| 46 | `KAM.Planetary.Spatial.SpatialNoCollision` | `Planetary/Spatial/Defs/SpatialNoCollision.lean.txt:28` | literal; L |
| 47 | `KAM.Planetary.Spatial.IsSpatialMovingSolutionOn` | `Planetary/Spatial/Defs/IsSpatialMovingSolutionOn.lean.txt:31` | literal; L |
| 48 | `KAM.Planetary.Spatial.SpatialMovingUniqueOn` | `Planetary/Spatial/Defs/SpatialMovingUniqueOn.lean.txt:30` | literal; L |
| 49 | `KAM.Planetary.Spatial.spatialBarycentricPositions` | `Planetary/Spatial/Defs/SpatialBarycentricPositions.lean.txt:31` | literal; F |
| 50 | `KAM.Planetary.Spatial.spatialBarycentricVelocities` | `Planetary/Spatial/Defs/SpatialBarycentricVelocities.lean.txt:31` | literal; F |
| 51 | `KAM.Planetary.Spatial.spatialMasses` | `Planetary/Spatial/Defs/SpatialMasses.lean.txt:28` | literal; L |
| 52 | `KAM.Planetary.Spatial.IsSpatialNewtonSolutionOn` | `Planetary/Spatial/Defs/IsSpatialNewtonSolutionOn.lean.txt:28` | literal; L |
| 53 | `KAM.Planetary.Spatial.spatialKeplerEnergy` | `Planetary/Spatial/Defs/SpatialKeplerEnergy.lean.txt:33` | internal; H |
| 54 | `KAM.Planetary.Spatial.spatialKeplerAxis` | `Planetary/Spatial/Defs/SpatialKeplerAxis.lean.txt:29` | internal; H |
| 55 | `KAM.Planetary.Spatial.spatialKeplerAction` | `Planetary/Spatial/Defs/SpatialKeplerAction.lean.txt:29` | internal; H |
| 56 | `KAM.Planetary.Spatial.spatialKeplerEccVector` | `Planetary/Spatial/Defs/SpatialKeplerEccVector.lean.txt:32` | internal; H |
| 57 | `KAM.Planetary.Spatial.SpatialNegativeEnergy` | `Planetary/Spatial/Defs/SpatialNegativeEnergy.lean.txt:30` | carrier; C |
| 58 | `KAM.Planetary.Spatial.SpatialElliptic` | `Planetary/Spatial/Defs/SpatialElliptic.lean.txt:27` | carrier; C |
| 59 | `KAM.Planetary.Spatial.spatialKeplerPeri` | `Planetary/Spatial/Defs/SpatialKeplerPeri.lean.txt:31` | internal; H |
| 60 | `KAM.Planetary.Spatial.spatialKeplerApo` | `Planetary/Spatial/Defs/SpatialKeplerApo.lean.txt:31` | internal; H |
| 61 | `KAM.Planetary.Spatial.spatialOscVelocity` | `Planetary/Spatial/Defs/SpatialOscVelocity.lean.txt:30` | internal; H |
| 62 | `KAM.Planetary.Spatial.spatialOscParam` | `Planetary/Spatial/Defs/SpatialOscParam.lean.txt:28` | internal; H |
| 63 | `KAM.Planetary.Spatial.spatialOscEnergy` | `Planetary/Spatial/Defs/SpatialOscEnergy.lean.txt:35` | internal; H |
| 64 | `KAM.Planetary.Spatial.spatialOscAxis` | `Planetary/Spatial/Defs/SpatialOscAxis.lean.txt:30` | internal; H |
| 65 | `KAM.Planetary.Spatial.spatialOscEccVector` | `Planetary/Spatial/Defs/SpatialOscEccVector.lean.txt:34` | internal; H |
| 66 | `KAM.Planetary.Spatial.spatialOscEcc` | `Planetary/Spatial/Defs/SpatialOscEcc.lean.txt:32` | internal; H |
| 67 | `KAM.Planetary.Spatial.spatialOscPeri` | `Planetary/Spatial/Defs/SpatialOscPeri.lean.txt:30` | internal; H |
| 68 | `KAM.Planetary.Spatial.spatialOscApo` | `Planetary/Spatial/Defs/SpatialOscApo.lean.txt:30` | internal; H |
| 69 | `KAM.Planetary.Spatial.SpatialOscPhase` | `Planetary/Spatial/Defs/SpatialOscPhase.lean.txt:32` | carrier; C |
| 70 | `KAM.Planetary.Spatial.SpatialSourceCanonicalPhase` | `Planetary/Spatial/Defs/SpatialSourceCanonicalPhase.lean.txt:27` | carrier; C |
| 71 | `KAM.Planetary.Spatial.SpatialSourceOsculatingPhase` | `Planetary/Spatial/Defs/SpatialSourceOsculatingPhase.lean.txt:26` | carrier; C |
| 72 | `KAM.Planetary.Spatial.spatialSourceKeplerAxis` | `Planetary/Spatial/Defs/SpatialSourceKeplerAxis.lean.txt:28` | source; C |
| 73 | `KAM.Planetary.Spatial.spatialSourceKeplerAction` | `Planetary/Spatial/Defs/SpatialSourceKeplerAction.lean.txt:28` | source; C |
| 74 | `KAM.Planetary.Spatial.spatialSourceKeplerEccVector` | `Planetary/Spatial/Defs/SpatialSourceKeplerEccVector.lean.txt:28` | source; C |
| 75 | `KAM.Planetary.Spatial.spatialSourceKeplerEcc` | `Planetary/Spatial/Defs/SpatialSourceKeplerEcc.lean.txt:29` | source; C |
| 76 | `KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum` | `Planetary/Spatial/Defs/SpatialSourcePlanetAngularMomentum.lean.txt:28` | source; C |
| 77 | `KAM.Planetary.Spatial.spatialSourceAngularMomentum` | `Planetary/Spatial/Defs/SpatialSourceAngularMomentum.lean.txt:28` | source; C |
| 78 | `KAM.Planetary.Spatial.spatialSourceStrongAMD` | `Planetary/Spatial/Defs/SpatialSourceStrongAMD.lean.txt:30` | source; C |
| 79 | `KAM.Planetary.Spatial.spatialSourceKeplerPeri` | `Planetary/Spatial/Defs/SpatialSourceKeplerPeri.lean.txt:28` | source; C |
| 80 | `KAM.Planetary.Spatial.spatialSourceKeplerApo` | `Planetary/Spatial/Defs/SpatialSourceKeplerApo.lean.txt:28` | source; C |
| 81 | `KAM.Planetary.Spatial.spatialSourceOscVelocity` | `Planetary/Spatial/Defs/SpatialSourceOscVelocity.lean.txt:28` | source; C |
| 82 | `KAM.Planetary.Spatial.spatialSourceOscParam` | `Planetary/Spatial/Defs/SpatialSourceOscParam.lean.txt:28` | source; C |
| 83 | `KAM.Planetary.Spatial.spatialSourceOscEnergy` | `Planetary/Spatial/Defs/SpatialSourceOscEnergy.lean.txt:28` | source; C |
| 84 | `KAM.Planetary.Spatial.spatialSourceOscAxis` | `Planetary/Spatial/Defs/SpatialSourceOscAxis.lean.txt:28` | source; C |
| 85 | `KAM.Planetary.Spatial.spatialSourceOscEccVector` | `Planetary/Spatial/Defs/SpatialSourceOscEccVector.lean.txt:28` | source; C |
| 86 | `KAM.Planetary.Spatial.spatialSourceOscEcc` | `Planetary/Spatial/Defs/SpatialSourceOscEcc.lean.txt:28` | source; C |
| 87 | `KAM.Planetary.Spatial.spatialSourceOscPeri` | `Planetary/Spatial/Defs/SpatialSourceOscPeri.lean.txt:28` | source; C |
| 88 | `KAM.Planetary.Spatial.spatialSourceOscApo` | `Planetary/Spatial/Defs/SpatialSourceOscApo.lean.txt:28` | source; C |

All 19 directly reused definitions were also expanded as consumed: Phase is a product of Pi spaces;
bodyVector uses the product-coordinate equivalence; planeDot/Sq/Length/Cross give Euclidean plane
operations; totalMomentum sums the determinant; KeplerEnergy is ν_i E_i; Axis is −ν/(2νE);
Action is ν√a; EccVector is the literal LRL formula; solution/uniqueness/collision/Newton predicates
and masses/barycentric maps have the meanings expanded above. Their broad total carriers and old
imports are inherited frozen conventions, not reapproved new definitions by this audit. The two
extra semantic dependencies are movingHamiltonian and hamiltonianVectorField.

| Characterization | Draft declaration evidence | Expanded inputs and result |
|---|---|---|
| `orderedPairThreshold_isLeast` | `Planetary/StrongAMD/Theorems/OrderedPairThresholdIsLeast.lean.txt:34` | n TYPING; ν STANDING; I TYPING (chamber positivity/order SOURCE); i,j TYPING; hij TYPING (source i<j). IsLeast/unique scalar value OK; no EXCESS. |
| `orderedPairThreshold_existsUnique_value` | `Planetary/StrongAMD/Theorems/OrderedPairThresholdExistsUniqueValue.lean.txt:33` | n TYPING; ν STANDING; I TYPING (chamber positivity/order SOURCE); i,j TYPING; hij TYPING (source i<j). IsLeast/unique scalar value OK; no EXCESS. |
| `orderedCrossThreshold_isLeast` | `Planetary/StrongAMD/Theorems/OrderedCrossThresholdIsLeast.lean.txt:33` | n TYPING; ν STANDING; hn STANDING; I TYPING (chamber positivity/order SOURCE). Adjacent minimum/union minimum OK; no EXCESS. |
| `orderedStrongThreshold_isLeast` | `Planetary/StrongAMD/Theorems/OrderedStrongThresholdIsLeast.lean.txt:33` | n TYPING; ν STANDING; hn STANDING; I TYPING (chamber positivity/order SOURCE). Adjacent minimum/union minimum OK; no EXCESS. |
| `sourceStrongAMD_nonneg` | `Planetary/StrongAMD/Theorems/SourceStrongAMDNonneg.lean.txt:30` | n TYPING; ν STANDING; z TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `sum_action_mul_eccDeficit_le_sourceStrongAMD` | `Planetary/StrongAMD/Theorems/SumActionMulEccDeficitLeSourceStrongAMD.lean.txt:35` | n TYPING; ν STANDING; z TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `sourceKepler_axis_pos` | `Planetary/StrongAMD/Theorems/SourceKeplerAxisPos.lean.txt:30` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `sourceKepler_ecc_le_one` | `Planetary/StrongAMD/Theorems/SourceKeplerEccLeOne.lean.txt:31` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `sourceKeplerPeri_le_planeLength` | `Planetary/StrongAMD/Theorems/SourceKeplerPeriLePlaneLength.lean.txt:32` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `planeLength_le_sourceKeplerApo` | `Planetary/StrongAMD/Theorems/PlaneLengthLeSourceKeplerApo.lean.txt:32` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `sourceOscAxis_pos` | `Planetary/StrongAMD/Theorems/SourceOscAxisPos.lean.txt:30` | n TYPING; ν STANDING; μ STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, μ>0 SOURCE, q≠0 SOURCE, Eosc<0 SOURCE, eosc<1 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `sourceOscPeri_pos` | `Planetary/StrongAMD/Theorems/SourceOscPeriPos.lean.txt:30` | n TYPING; ν STANDING; μ STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, μ>0 SOURCE, q≠0 SOURCE, Eosc<0 SOURCE, eosc<1 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `sourceOscPeri_le_planeLength` | `Planetary/StrongAMD/Theorems/SourceOscPeriLePlaneLength.lean.txt:32` | n TYPING; ν STANDING; μ STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, μ>0 SOURCE, q≠0 SOURCE, Eosc<0 SOURCE, eosc<1 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `planeLength_le_sourceOscApo` | `Planetary/StrongAMD/Theorems/PlaneLengthLeSourceOscApo.lean.txt:32` | n TYPING; ν STANDING; μ STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, μ>0 SOURCE, q≠0 SOURCE, Eosc<0 SOURCE, eosc<1 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceKeplerAxis_pos` | `Planetary/Spatial/Theorems/SpatialSourceKeplerAxisPos.lean.txt:30` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceKeplerAction_pos` | `Planetary/Spatial/Theorems/SpatialSourceKeplerActionPos.lean.txt:30` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceKeplerAction_sq` | `Planetary/Spatial/Theorems/SpatialSourceKeplerActionSq.lean.txt:31` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceKeplerEcc_sq` | `Planetary/Spatial/Theorems/SpatialSourceKeplerEccSq.lean.txt:33` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceKeplerEcc_nonneg` | `Planetary/Spatial/Theorems/SpatialSourceKeplerEccNonneg.lean.txt:30` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceKeplerEcc_le_one` | `Planetary/Spatial/Theorems/SpatialSourceKeplerEccLeOne.lean.txt:30` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourcePlanetAngularMomentum_length` | `Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLength.lean.txt:33` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourcePlanetAngularMomentum_length_le` | `Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLengthLe.lean.txt:32` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceKeplerPeri_le_length` | `Planetary/Spatial/Theorems/SpatialSourceKeplerPeriLeLength.lean.txt:32` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceKeplerApo_ge_length` | `Planetary/Spatial/Theorems/SpatialSourceKeplerApoGeLength.lean.txt:32` | n TYPING; ν STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceStrongAMD_nonneg` | `Planetary/Spatial/Theorems/SpatialSourceStrongAMDNonneg.lean.txt:30` | n TYPING; ν STANDING; z TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceAction_mul_eccDeficit_le` | `Planetary/Spatial/Theorems/SpatialSourceActionMulEccDeficitLe.lean.txt:32` | n TYPING; ν STANDING; z TYPING; carrier expands to ν>0 STANDING, q≠0 SOURCE, E<0 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceOscParam_pos` | `Planetary/Spatial/Theorems/SpatialSourceOscParamPos.lean.txt:30` | n TYPING; ν STANDING; μ STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, μ>0 SOURCE, q≠0 SOURCE, Eosc<0 SOURCE, eosc<1 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceOscEnergy_neg` | `Planetary/Spatial/Theorems/SpatialSourceOscEnergyNeg.lean.txt:30` | n TYPING; ν STANDING; μ STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, μ>0 SOURCE, q≠0 SOURCE, Eosc<0 SOURCE, eosc<1 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceOscEcc_lt_one` | `Planetary/Spatial/Theorems/SpatialSourceOscEccLtOne.lean.txt:30` | n TYPING; ν STANDING; μ STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, μ>0 SOURCE, q≠0 SOURCE, Eosc<0 SOURCE, eosc<1 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceOscEcc_nonneg` | `Planetary/Spatial/Theorems/SpatialSourceOscEccNonneg.lean.txt:30` | n TYPING; ν STANDING; μ STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, μ>0 SOURCE, q≠0 SOURCE, Eosc<0 SOURCE, eosc<1 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceOscAxis_pos` | `Planetary/Spatial/Theorems/SpatialSourceOscAxisPos.lean.txt:30` | n TYPING; ν STANDING; μ STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, μ>0 SOURCE, q≠0 SOURCE, Eosc<0 SOURCE, eosc<1 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceOscPeri_pos` | `Planetary/Spatial/Theorems/SpatialSourceOscPeriPos.lean.txt:30` | n TYPING; ν STANDING; μ STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, μ>0 SOURCE, q≠0 SOURCE, Eosc<0 SOURCE, eosc<1 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceOscPeri_le_length` | `Planetary/Spatial/Theorems/SpatialSourceOscPeriLeLength.lean.txt:32` | n TYPING; ν STANDING; μ STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, μ>0 SOURCE, q≠0 SOURCE, Eosc<0 SOURCE, eosc<1 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |
| `spatialSourceOscApo_ge_length` | `Planetary/Spatial/Theorems/SpatialSourceOscApoGeLength.lean.txt:32` | n TYPING; ν STANDING; μ STANDING; z TYPING; i TYPING; carrier expands to ν>0 STANDING, μ>0 SOURCE, q≠0 SOURCE, Eosc<0 SOURCE, eosc<1 SOURCE. Exact stated property OK; no EXCESS or conclusion-shaped premise. |

Subtype membership in these characterization rows defines the object being characterized. It is not
used as an assumed theorem of dynamical persistence. The binder bins of carrier properties are
therefore source-domain conditions, not conclusion-shaped analytical premises. No hidden
project typeclass or bundled source obligation remains unexpanded.

### Expanded characterization binder ledger

Each table enumerates the declared binders and the source conditions inside its subtype.
Finite index quantifiers inside the result merely express the displayed source property; no
input instance binder is omitted. Counts use these rows, including expanded subtype conditions.

`KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| I : OrderedActions ν | TYPING | MAIN:43 |
| I.2: all actions positive | SOURCE | MAIN:43 |
| I.2: all axes ordered | SOURCE | MAIN:43 |
| i | TYPING | MAIN:47–51 |
| j | TYPING | MAIN:47–51 |
| hij : i<j | TYPING | MAIN:47–51 |

Counts: SOURCE 2, STANDING 1, TYPING 5, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| I : OrderedActions ν | TYPING | MAIN:43 |
| I.2: all actions positive | SOURCE | MAIN:43 |
| I.2: all axes ordered | SOURCE | MAIN:43 |
| i | TYPING | MAIN:47–51 |
| j | TYPING | MAIN:47–51 |
| hij : i<j | TYPING | MAIN:47–51 |

Counts: SOURCE 2, STANDING 1, TYPING 5, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.StrongAMD.orderedCrossThreshold_isLeast`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| hn : 2≤n | STANDING | MAIN:11; nonempty finite minimum |
| I : OrderedActions ν | TYPING | MAIN:43 |
| I.2: all actions positive | SOURCE | MAIN:43 |
| I.2: all axes ordered | SOURCE | MAIN:43 |

Counts: SOURCE 2, STANDING 2, TYPING 2, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.StrongAMD.orderedStrongThreshold_isLeast`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| hn : 2≤n | STANDING | MAIN:11; nonempty finite minimum |
| I : OrderedActions ν | TYPING | MAIN:43 |
| I.2: all actions positive | SOURCE | MAIN:43 |
| I.2: all axes ordered | SOURCE | MAIN:43 |

Counts: SOURCE 2, STANDING 2, TYPING 2, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.StrongAMD.sourceStrongAMD_nonneg`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |

Counts: SOURCE 2, STANDING 2, TYPING 2, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |

Counts: SOURCE 2, STANDING 2, TYPING 2, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.StrongAMD.sourceKepler_axis_pos`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.StrongAMD.sourceKepler_ecc_le_one`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.StrongAMD.planeLength_le_sourceKeplerApo`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.StrongAMD.sourceOscAxis_pos`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| μ | STANDING | MAIN:510–518 |
| z : source subtype | TYPING | MAIN:510–525 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: μ>0 | SOURCE | MAIN:520 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: Eosc<0 | SOURCE | MAIN:520 |
| z.property: eosc<1 | SOURCE | MAIN:520 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 4, STANDING 3, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.StrongAMD.sourceOscPeri_pos`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| μ | STANDING | MAIN:510–518 |
| z : source subtype | TYPING | MAIN:510–525 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: μ>0 | SOURCE | MAIN:520 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: Eosc<0 | SOURCE | MAIN:520 |
| z.property: eosc<1 | SOURCE | MAIN:520 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 4, STANDING 3, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| μ | STANDING | MAIN:510–518 |
| z : source subtype | TYPING | MAIN:510–525 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: μ>0 | SOURCE | MAIN:520 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: Eosc<0 | SOURCE | MAIN:520 |
| z.property: eosc<1 | SOURCE | MAIN:520 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 4, STANDING 3, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| μ | STANDING | MAIN:510–518 |
| z : source subtype | TYPING | MAIN:510–525 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: μ>0 | SOURCE | MAIN:520 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: Eosc<0 | SOURCE | MAIN:520 |
| z.property: eosc<1 | SOURCE | MAIN:520 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 4, STANDING 3, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceKeplerAction_pos`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceKeplerAction_sq`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceKeplerEcc_sq`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceKeplerEcc_nonneg`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceKeplerEcc_le_one`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceKeplerApo_ge_length`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 2, STANDING 2, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |

Counts: SOURCE 2, STANDING 2, TYPING 2, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| z : source subtype | TYPING | MAIN:31–37 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: E<0 | SOURCE | MAIN:31–37 |

Counts: SOURCE 2, STANDING 2, TYPING 2, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceOscParam_pos`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| μ | STANDING | MAIN:510–518 |
| z : source subtype | TYPING | MAIN:510–525 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: μ>0 | SOURCE | MAIN:520 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: Eosc<0 | SOURCE | MAIN:520 |
| z.property: eosc<1 | SOURCE | MAIN:520 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 4, STANDING 3, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceOscEnergy_neg`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| μ | STANDING | MAIN:510–518 |
| z : source subtype | TYPING | MAIN:510–525 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: μ>0 | SOURCE | MAIN:520 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: Eosc<0 | SOURCE | MAIN:520 |
| z.property: eosc<1 | SOURCE | MAIN:520 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 4, STANDING 3, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceOscEcc_lt_one`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| μ | STANDING | MAIN:510–518 |
| z : source subtype | TYPING | MAIN:510–525 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: μ>0 | SOURCE | MAIN:520 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: Eosc<0 | SOURCE | MAIN:520 |
| z.property: eosc<1 | SOURCE | MAIN:520 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 4, STANDING 3, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceOscEcc_nonneg`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| μ | STANDING | MAIN:510–518 |
| z : source subtype | TYPING | MAIN:510–525 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: μ>0 | SOURCE | MAIN:520 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: Eosc<0 | SOURCE | MAIN:520 |
| z.property: eosc<1 | SOURCE | MAIN:520 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 4, STANDING 3, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceOscAxis_pos`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| μ | STANDING | MAIN:510–518 |
| z : source subtype | TYPING | MAIN:510–525 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: μ>0 | SOURCE | MAIN:520 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: Eosc<0 | SOURCE | MAIN:520 |
| z.property: eosc<1 | SOURCE | MAIN:520 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 4, STANDING 3, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceOscPeri_pos`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| μ | STANDING | MAIN:510–518 |
| z : source subtype | TYPING | MAIN:510–525 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: μ>0 | SOURCE | MAIN:520 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: Eosc<0 | SOURCE | MAIN:520 |
| z.property: eosc<1 | SOURCE | MAIN:520 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 4, STANDING 3, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceOscPeri_le_length`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| μ | STANDING | MAIN:510–518 |
| z : source subtype | TYPING | MAIN:510–525 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: μ>0 | SOURCE | MAIN:520 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: Eosc<0 | SOURCE | MAIN:520 |
| z.property: eosc<1 | SOURCE | MAIN:520 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 4, STANDING 3, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

`KAM.Planetary.Spatial.spatialSourceOscApo_ge_length`:

| Binder/component | Bin | Evidence |
|---|---|---|
| n | TYPING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| μ | STANDING | MAIN:510–518 |
| z : source subtype | TYPING | MAIN:510–525 |
| z.property: all ν_i positive | STANDING | MAIN:11 |
| z.property: μ>0 | SOURCE | MAIN:520 |
| z.property: nonzero positions | SOURCE | MAIN:24,28 |
| z.property: Eosc<0 | SOURCE | MAIN:520 |
| z.property: eosc<1 | SOURCE | MAIN:520 |
| i | TYPING | per-planet property, MAIN L2/L16 |

Counts: SOURCE 4, STANDING 3, TYPING 3, EXCESS 0, CONCLUSION-SHAPED 0.

### Already-frozen definitions as consumed

| Definition | Current frozen declaration evidence | Consumption verdict |
|---|---|---|
| `KAM.Planetary.IsMovingSolutionOn` | `KAM/Frozen/Planetary/Defs/IsMovingSolutionOn.lean:35` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.IsNewtonSolutionOn` | `KAM/Frozen/Planetary/Defs/IsNewtonSolutionOn.lean:36` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Iso.IsHamiltonianSolutionOn` | `KAM/Frozen/Iso/Defs/IsHamiltonianSolutionOn.lean:37` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.MovingUniqueOn` | `KAM/Frozen/Planetary/Defs/MovingUniqueOn.lean:37` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.NoCollision` | `KAM/Frozen/Planetary/Defs/NoCollision.lean:39` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.Phase` | `KAM/Frozen/Planetary/Defs/Phase.lean:37` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.actualMasses` | `KAM/Frozen/Planetary/Defs/ActualMasses.lean:37` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.barycentricPositions` | `KAM/Frozen/Planetary/Defs/BarycentricPositions.lean:39` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.barycentricVelocities` | `KAM/Frozen/Planetary/Defs/BarycentricVelocities.lean:38` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.bodyVector` | `KAM/Frozen/Planetary/Defs/BodyVector.lean:37` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.keplerAction` | `KAM/Frozen/Planetary/Defs/KeplerAction.lean:36` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.keplerAxis` | `KAM/Frozen/Planetary/Defs/KeplerAxis.lean:36` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.keplerEccVector` | `KAM/Frozen/Planetary/Defs/KeplerEccVector.lean:35` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.keplerEnergy` | `KAM/Frozen/Planetary/Defs/KeplerEnergy.lean:35` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.planeCross` | `KAM/Frozen/Planetary/Defs/PlaneCross.lean:35` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.planeDot` | `KAM/Frozen/Planetary/Defs/PlaneDot.lean:37` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.planeLength` | `KAM/Frozen/Planetary/Defs/PlaneLength.lean:38` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.planeSq` | `KAM/Frozen/Planetary/Defs/PlaneSq.lean:37` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
| `KAM.Planetary.totalMomentum` | `KAM/Frozen/Planetary/Defs/TotalMomentum.lean:36` | exact inherited body; source guards supplied by the anchors/predicates; reused unchanged |
Final report checks: the read-only validator confirmed 88 definition rows, 34 characterization rows,
34 expanded characterization binder ledgers, and all 127 exports represented (including the five
explicit anchor identities). `git diff --check` exited 0 with empty output. Final `git status --short`
listed only `?? docs/tracks/LP/freeze/STATEMENT-AUDIT-DRAFT7-1.md`.

## Handoff and limits

Files: this report only. Approach: raw-source reconstruction, expanded binders, all-body and
carrier inspection, semantic-unit check, independent hash/text/import-closure scans, serial
replays and targeted builds. No new suspected MAIN erratum. The reported problems are deviations
in the proposed Lean domain/role certification, not errors in the pinned source. No repair was
silently applied. Future checks: revised F1/F2 approval object, real module/provider rebase,
manifest hashes and post-seal axiom audit. These are not paid by today's simulated-module checks.

Hard rules retained verbatim from the audit brief:

1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules, preserving public import paths as cheap facades.

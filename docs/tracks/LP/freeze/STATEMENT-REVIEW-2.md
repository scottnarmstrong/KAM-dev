# Independent LP statement review 2 — delta F1–F5

Date: 2026-11-01. Independent, refute-first reviewer; no authorship of either proposal. Method: `/root/.claude/skills/lean-statement-audit/SKILL.md`, read in full and applied without delegation. Read the supplied AGENTS rules, `docs/PLAN.md`, `docs/DECISIONS.md`, and the user brief. Only this report is written in the repository; all probes are transient under `/tmp`. No external source is substituted for the pinned MAIN and normative N1–N12.

## Verdict

**PASS for the draft-2 delta to the theorem types, with an OPEN BLOCKING DEFINITION/FREEZE GATE.** F1 is repaired; F2's missing quantitative estimate and ellipse validity are repaired; F3 is repaired on the explicitly identified LP-THR2 branch, pending integration; F4 is correctly exposed as unresolved OD-11, not solved; F5 retains the source normalization. No EXCESS or conclusion-shaped input was found. The exact proposed theorem types have sorry-free producers, independently consumed below. This is not approval to freeze an incomplete definition package.

| Item | Classification and disposition |
|---|---|
| F1: full planar L5 outputs | NOTE — resolved in LP0, proposal:37–59 |
| F2: first (43) estimate, ellipse guards, N10 | NOTE — resolved for the advertised quantitative LP1 conclusion, proposal:78–80,109–119; geometric/standalone-L16 scope caveat below |
| F3: source threshold carriers | NOTE — repaired at `inp-lp-thr2` `5871e3b58585cf8c6a749d5e90847207376ef837`; must integrate the repaired semantic unit before freeze |
| F4: total physical expressions as whole-carrier source objects | **BLOCKING FOR FREEZE, OPEN OWNER DECISION** — correctly logged in OD-11; current total exports still fail the whole-carrier test |
| F5: mass normalization | NOTE — resolved by keeping `hνmax`, `hνle`; no LP1 normalization change |
| Claim that LP1 is literally all of standalone L16 | NOTE — LP1 specializes its quantitative conclusions to the certified orbits; it does not export a standalone safe-compact theorem or a geometric ellipse/tangency object |
| Definition inventory ambiguity | CHANGE-RECOMMENDED — make proposal:24–32 explicitly subordinate to §4b; it currently still lists raw helpers as “freezing … with” the anchor |

For these proposed, unmanifested targets:

```text
DECLARATION_FIDELITY: PASS (the stated planar L5 and T15 quantitative/L16 orbit conclusions, under their guards)
DRAFT_ALLOWLIST: N/A_UNFROZEN
PROOF_STATUS: PROPOSED_UNFROZEN, WITH SORRY_FREE_ORDINARY_PRODUCERS_VERIFIED
FREEZE_PACKAGE: NOT_READY (OD-11 and exact resulting definition/anchor text remain open)
```

An unqualified whole-carrier definition/final-freeze fidelity verdict is **FAIL** until F4 is resolved. There is no LP0/LP1 manifest entry, frozen export, provider registration or seal to certify; proposal:3 explicitly says nothing is frozen. The `sorry`s in the text attachment are hypothetical proof placeholders, not manifest-authorized DRAFT_SORRYs and not proof evidence. No theorem closure of a frozen LP source node is claimed.

## Identity and scope pins

All relative paths are under `/root/code/KAM-inp-lp`; `MAIN` abbreviates `docs/tracks/LP/source/MAIN.md`, `proposal` abbreviates `docs/tracks/LP/FREEZE-PROPOSAL.md`. Branch citations below mean the exact `git show <revision>:<path>` text, with lines numbered from that blob, not the current `inp-lp-ps` worktree. Review HEAD was `cd90623d95ef75230401fbed51efa9d12f3d6e60`. LP-PS is `74ebebb105588b2de61ea227d1c9250e8deeec6b`; its `PlanarSafety/Main.lean` blob is `ee555bfb32017d47f11cf27752e96261f95e5e65`.

| File | SHA-256 |
|---|---|
| proposal | `9fad13744ff4fef83bfe80d3a2e7e5cac6d30ed880064d9ea32a35de4232b726` |
| `freeze/elaboration-draft-2.lean.txt` | `86de63bb60b6ba5f3184267cc3df66bf93b0cf72780364bddf799561a8d90c78` |
| `freeze/verification-draft-2.lean.txt` | `daa64e19b89082b49c9ccf0d23e792d5704ca2bbf0ed8e982bf3f9f175a570ef` |
| MAIN | `68e9167f04e4a04689ea163c74e02ffcaea657b252726080abdbe37bdba48c1b` |
| `source/AMENDMENTS.md` | `c887d1e27354a3db7fb8a20d8bf3e33a9ef95ff3173f925ba5ebfab192651881` |
| `OWNER-DECISIONS.md` | `5d7fe00b5c2372c6564581b181bcb4a75c6eb40e61948cffbef29a4556818250` |
| `SPEC.md` | `ffd8a2793b9b37ca35e4a626d38d9af3c2f79d5cefa7c36e5e2aa844978dad22` |

The LP0 and LP1 text from `theorem <name>` through the type preceding `:=` agrees **exactly**, after trimming boundary whitespace, between proposal, elaboration draft 2 and verification draft 2. The respective type-tail hashes are `99701a2eb915afa4b4e6d0f1b78c1065cc1d53ec65c15f66256e8f01a97aeee4` and `7fce4213b2109c9ac099a706b3a6606c68f1bbfe9c4cfa1f4940f5086e39982c`. The implicit `{n : ℕ}` and `ecc` abbreviation come from the attachment context (`verification:19,21–23`); `ecc` means Euclidean length of the canonical eccentricity vector.

The branch producer types agree after expanding precisely this abbreviation, ignoring whitespace and renaming `_hνmax/_hνle` to `hνmax/hνle`. Actual Lean consumption, rather than that textual comparison alone, passed. `Momentum.lean` and `Osculating/Basic.lean` are byte-identical between the reviewed checkout, LP-PS branch and build checkout. `Threshold/Defs.lean` agrees between review and LP-PS; the build checkout has a different threshold version. The fresh Main compilation and verification therefore use the LP-PS dependency artifacts explicitly. This is not a claim that the build checkout already contains the repaired THR2 semantic unit.

## Reconstructed source and expanded input audit

MAIN:11–15 fixes normalized positive masses, n≥2, compact ordered positive axes, δ,γ>0 and τ>n−1, allowing empty compact sets. MAIN:17–39 fixes physical time, masses μν, canonical p, and C=ΣI−|L|. MAIN:43–55 restricts the threshold objects to the chamber with attained minima. MAIN:64–65 specifies radian frequencies and ℓ¹ modes. MAIN:69–93 chooses all constants before μ and every state. L5:164 includes both the abstract deficit-list statement and compactness/angular-momentum outputs. L16:510–529 defines actual-velocity elements, both errors, nondegeneracy and geometric incidence/tangency. Normative N1–N12 were checked; N8, N10 and N11 touch this delta directly. No proof-internal amendment is turned into an input.

Each row is one binder or independently meaningful expanded premise component. Quantifiers internal to the displayed formulas are retained explicitly. There are no input instance/typeclass binders. Conclusion-local conditionals are outputs, inventoried separately below.

### LP0, proposal:37–51

| Input | Bin | Source/ruling evidence |
|---|---|---|
| implicit `n : ℕ` | TYPING | MAIN:11 |
| `hn : 2 ≤ n` | STANDING | MAIN:11; nonempty adjacent family |
| `ν : Fin n → ℝ` | STANDING | MAIN:11 |
| `hν : ∀ i, 0 < ν i` | STANDING | MAIN:11 |
| `U : Set (Fin n → ℝ)` | SOURCE | L5:164 |
| `hU : IsCompact U` | SOURCE | L5:164; no nonemptiness required |
| `hUch`, `∀ I∈U, ∀ i, 0<I i` | SOURCE | L5:164, chamber MAIN:43 |
| `hUch`, `∀ I∈U, ∀ i j, i<j → (I i/ν i)^2<(I j/ν j)^2` | SOURCE | MAIN:43–45 |
| `m : ℝ` | SOURCE | L5:164 |
| `hm : 0<m` | SOURCE | L5:164 |
| `z : Phase (n*2)` | TYPING | arbitrary planar state, MAIN:26–37 |
| `∀ i, 0<planeLength (bodyVector z.1 i)` | STANDING | nonsingular canonical domain, MAIN:24,28 |
| `∀ i, keplerEnergy ν z i<0` | SOURCE | L5:164; total energy is ν_i times specific E_i |
| `hΛ : (fun i => keplerAction ν z i)∈U` | SOURCE | L5:164 |
| `strongAMD ν z≤orderedStrongThreshold hn ⟨_,hUch hΛ⟩-m` | SOURCE | L5:164, MAIN:35,53 |

Counts: SOURCE 9, STANDING 4, TYPING 2, RULED 0, EXCESS 0. LP0 omits max ν=1 as an explicit static homogeneous extension, already disclosed in proposal:148–149. There is no μ in LP0 to reinterpret. Approval should retain this disclosed extension rather than describe every LP0 binder as literally identical to the globally normalized standing data.

### LP1, proposal:73–89

| Input | Bin | Source/ruling evidence |
|---|---|---|
| implicit `n : ℕ` | TYPING | MAIN:11 |
| `hn : 2≤n` | STANDING | MAIN:11 |
| `ν : Fin n→ℝ` | STANDING | MAIN:11 |
| `hν : ∀ i, 0<ν i` | STANDING | MAIN:11 |
| `hνmax : ∃ i, ν i=1` | STANDING | MAIN:11, OD-3 |
| `hνle : ∀ i, ν i≤1` | STANDING | MAIN:11, OD-3 |
| `A : Set (Fin n→ℝ)` | STANDING | MAIN:11–14 |
| `hA : IsCompact A` | STANDING | MAIN:11,15; empty allowed |
| `hAord`, `∀ a∈A, ∀ i, 0<a i` | STANDING | MAIN:13 |
| `hAord`, `∀ a∈A, ∀ i j, i<j→a i<a j` | STANDING | MAIN:13 |
| `δ : ℝ` | STANDING | MAIN:15 |
| `γ : ℝ` | STANDING | MAIN:15 |
| `τ : ℝ` | STANDING | MAIN:15 |
| `hδ : 0<δ` | STANDING | MAIN:15 |
| `hγ : 0<γ` | STANDING | MAIN:15 |
| `hτ : (n:ℝ)-1<τ` | STANDING | MAIN:15 |
| `μ : ℝ` | SOURCE | MAIN:70 |
| anonymous `0<μ` | SOURCE | MAIN:70 |
| anonymous `μ≤μ₀` | SOURCE | MAIN:70 |
| `z₀ : Phase (n*2)` | TYPING | arbitrary initial state, MAIN:70 |
| `∀ i, 0<planeLength (bodyVector z₀.1 i)` | SOURCE | MAIN:70 |
| `∀ i, keplerEnergy ν z₀ i<0` | SOURCE | MAIN:70 |
| axes vector membership in A | SOURCE | MAIN:72 (6) |
| `∀ k : Fin n→ℤ, k≠0→γ*(modeSize k)^(-τ)≤|Σ_i k_i ν_i³/Λ_i³|` | SOURCE | MAIN:64–65 (5) |
| `hch`, `∀ i, 0<keplerAction ν z₀ i` | TYPING | MAIN:33,43; follows from preceding positive-mass/negative-energy inputs |
| `hch`, `∀ i j, i<j→actionAxis ν Λ i<actionAxis ν Λ j` | TYPING | MAIN:33,43; follows from axes in A and hAord |
| `strongAMD ν z₀≤orderedStrongThreshold hn ⟨_,hch⟩-δ` | SOURCE | MAIN:72 (6) |

Counts: SOURCE 8, STANDING 15, TYPING 4, RULED 0, EXCESS 0. There is no secular-dynamics, chart, torus-selection, normal-form, stopped-drift, ellipse-validity or separation premise. `hch` is a dependent proof argument, not an additional restriction on the allowed initial data; its two components follow from the earlier inputs. The proof argument must still be supplied by a consumer. Proof irrelevance removes any dependence of the threshold value on its choice.

### Output quantifiers and hidden-predicate expansion

LP0 chooses dStar,dPair>0 before **both** the arbitrary list `(I,hI,e)` and every physical z. The deficit-list branch universally binds I, hI:I∈U and e, then assumes `∀ i,e i∈[0,1]` and the literal deficit inequality. These are SOURCE conditions on that output branch (MAIN:164), not extra outer inputs. The one compact K is chosen before z. Its universal `w∈K` certifies every point of K is collision-free and negative-energy. The physical outputs bind i for perihelia/star lengths and angular momenta, a:AdjIdx n for annuli, and i,j with i≠j for pair lengths.

LP1 chooses **nine** positive constants `(μ₀,c,T₀,AΛ,Aa,dStar,dPair,Aosc,Aelem)` and the N10 inequalities before μ and z₀. Aelem is a new output constant for L16's first error, not a hypothesis. All constants depend only on `(d=2,n,ν,A,δ,γ,τ)` and their proof data; they cannot depend on μ, phases, orientations, eccentricities or secular states. T is then the literal expression in proposal:90; z is existential and t is universal on the closed interval. The existential `hcht` asserts chamber membership as an output. All per-planet, adjacent-pair and unequal-pair universals retain their full carriers.

`IsMovingSolutionOn` expands to differentiability-guarded Hamilton equations for `movingHamiltonian 1 1 ν μ` plus `∀ t∈J,NoCollision (z t).1` (frozen file:35–38). `MovingUniqueOn` expands to every U,w with U open and convex, 0∈U, same initial state and solutionhood, then agreement at every t∈U∩J (frozen file:37–40). These local-solution guards are conclusion-local, not new anchor premises. `IsNewtonSolutionOn` expands to all unequal barycentric-body distances positive, Q'=V, and V' equal to the full Newton sum (frozen file:36–42). `NoCollision` expands to all star lengths positive and every unequal planet pair positive (frozen file:39–41). No project-owned assumption bundle hides an analytical input. The finite-interval existence/overlap-uniqueness interface is the disclosed representation of the unique maximal orbit restricted to this interval; it does not export a named maximal-domain object.

## F1–F5 and semantic closure

### F1 — resolved

Proposal:40–45 restores the uniform deficit-list barrier on the entire [0,1]^n. Proposal:46–47,57 restores one compact collision-free negative-energy K containing every guarded state. Proposal:58–59 restores `|L_i|≥m` and `L_i L>0`, equivalent to H_i≥m in the planar invariable frame (MAIN:164). No output is relocated into the hypotheses. Empty U remains allowed. LP-PS `Main.lean:254` and following proves precisely this type. No replacement Lean text is recommended for LP0.

### F2 — repaired quantitative orbit conclusion; geometric scope remains explicit

Proposal:78–80 adds positive Aelem before μ/state and the two N10 smallness inequalities. Proposal:109–115 exports negative osculating energy, positive axis, e_osc<1, radial incidence and the **sum** of axis error plus Euclidean eccentricity-vector error ≤Aelem μ, including vector direction. Proposal:116–119 retains both endpoint errors and half gaps. This resolves the blocking missing-estimate/validity issue; hyperbolic elements can no longer be mislabeled as ellipses merely because their algebraic perihelion is positive.

All of (8)–(9) is present in proposal:98–108: negative energy, chamber membership, AMD margin δ/2, action/axis sup-norm drift, AMD drift, canonical whole-annulus gaps, every star distance and every unequal pair distance. Canonical nondegeneracy follows from positive axis and `a(1-e)≥dStar>0`; an extra initial e<1 assumption would be wrong. Osculating annuli are separated as whole annuli, not merely current positions. No missing collision/crossing conclusion was found.

**Scope NOTE.** L16:525 also says the ellipses pass through the position and are tangent to the actual heliocentric velocity. The printed LP1 output gives only radial inequalities, not the geometric conic incidence equation, a tangent-vector assertion or a two-body flow. `Osculating/Basic.lean:145–151` names its theorem `osc_tangency`, but its actual conclusion is positive axis and the same radial inequalities: its name is not proof of geometric tangency. The actual velocity formula is correct and identified with the q-block of the moving field at :87–92; Newton reconstruction also identifies the actual relative velocity. Thus the formulas determine the standard osculating ellipse on the valid locus, but this audit does **not** certify a separately exported geometric tangency theorem from those radial inequalities. LP1 also is not a universally quantified theorem over arbitrary fixed safe compact sets in dimensions two and three (L16:510,525); it is the planar orbit application. This is compatible with the stated T15/osculating safety anchor, but must remain visible if anyone claims “all of standalone L16.” No additional Lean conjunct is required for the quantitative no-crossing anchor reviewed here. A later geometric-L16 export requires its own exact statement and proof; it is not an owner waiver or a closure claim in this report.

### F3 — repaired on the named branch, integration condition remains

At THR2 revision above, `Threshold/Defs.lean:74` is the chamber subtype, :78–79 requires i<j for the pair, :84–85 requires 2≤n for the adjacent finite infimum, and :88–89 defines the strong threshold as min of this guarded cross threshold and the finite star minimum. n≥2 also ensures the latter is nonempty. The n=1 empty-adjacent-family defect is excluded by the public signature. `orderedStrongThreshold_eq` (:97–98) remains rfl; anchor applications and results therefore retain their meaning.

The companion pair characterization actually exists on this branch: `Threshold/Pair.lean:204–207` is IsLeast of the **entire** objective image, and :210–215 proves its unique scalar least value. Base compactness/nonemptiness/attainment is at Pair:68–100. No minimizer is arbitrarily selected; uniqueness is of the minimum value, not of the pair (u,v). Finite-minimum member/attainment facts are in `Threshold/Strong.lean` (`crossThreshold_le`, `exists_crossThreshold_eq`, `exists_starThreshold_eq`, `strongThreshold_eq_member`). Proposal §4b:160–166 now specifies the right source-facing inventory; its “in progress” description is stale relative to the named branch, not evidence that the code is absent.

For fixed positive ν and the source-facing repaired threshold unit:

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: OK (attained unique scalar minimum)
CHARACTERIZATION: OK (existing companion theorem text, not a future promise)
CHOICE_INDEPENDENCE: N/A (no selected minimizer)
DEFINITION_VERDICT: PASS_AT_THE_REVIEWED_SOURCE_INTERFACE
```

This is a delta statement/carrier assessment, not a new proof-package/kernel audit of every THR2 dependency. Integrate and manifest the repaired definitions and characterization together before freezing; do not certify the old raw helpers as source thresholds off Q. Exact accepted replacement Lean text (already implemented on THR2, no further edit requested):

```lean
noncomputable def orderedCrossThreshold {ν : Fin n → ℝ} (_hn : 2 ≤ n)
    (I : OrderedActions ν) : ℝ :=
  ⨅ a : AdjIdx n, orderedPairThreshold I a.1 a.upperIdx a.lt_upperIdx

noncomputable def orderedStrongThreshold {ν : Fin n → ℝ} (hn : 2 ≤ n)
    (I : OrderedActions ν) : ℝ :=
  min (orderedCrossThreshold hn I) (⨅ i : Fin n, I.1 i)
```

### F4 — correctly logged; still BLOCKING for a final whole-carrier freeze

Proposal:167–178 and OD-11 (`OWNER-DECISIONS.md:19`) state the issue honestly, recommend source subtypes, and explicitly require generated restated anchor text plus re-review. OD-11 is **open**, not an adopted owner ruling. It does not make the existing total expressions into source physical objects on every phase. MAIN:31–35 defines canonical elements under negative energy; L16:510–520 defines the ellipse elements on safe physical states for small positive μ. The current total `oscAxis` includes zero energy/parameter and non-elliptic states. Algebraic division totality is not existence of a physical ellipse.

For the currently proposed raw physical exports (`Momentum.lean:41–42`, `Osculating/Basic.lean:42–81`) considered as source objects on their whole public carriers:

```text
BODY_MATCH: OK_AS_LITERAL_FORMULAS
PUBLIC_CARRIER: FAIL
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: FAIL_AS_WHOLE_CARRIER_SOURCE_OBJECTS
```

The skill's carrier rejection is non-waivable within a source-object PASS. Option (a) could be an explicitly distinguished algebraic API convention, but cannot be reported as an independent whole-carrier physical-object certification. Option (b) is the suitable source-facing repair. Nothing is frozen overnight, so logging this as an owner gate is the correct disposition for this round; it is not evidence that F4 is resolved. No conclusion-shaped premise may be added to make the future restatement easier: LP1 must **prove** the osculating carrier guards before packaging them.

Exact adapter Lean text for recommended option (b) is reproduced below (the same restrictions as review 1 F4). These are literal restrictions; the existing total expressions remain internal helpers. Their defining equalities are rfl; they require no classical ellipse selection or deferred well-definedness theorem. Any additional geometric characterization claim must be proved separately. This is adapter text, not a falsely claimed complete, approved final anchor rewrite.

```lean
variable {n : ℕ}

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

CHANGE-RECOMMENDED (documentation only): replace proposal:24's sentence with: “Dependency inventory only; the exact source-facing freeze inventory is §4b. Raw total helpers are not separately certified as source objects off their indicated carriers. OD-11 remains an open freeze gate.” This recommends no Lean type change before the owner decision; the exact subtype-based theorem rewrite is deliberately still outstanding. Also update proposal:10 to include OD-11 and :165 to identify the completed THR2 branch repair rather than “in progress.”

### F5 — normalization retained; the generalization is not interpretation-neutral

Proposal:74 exactly states max ν=1 by an attained value and a pointwise upper bound; OD-3 (`OWNER-DECISIONS.md:11`) now retains it. LP-PS `Main.lean:136–185` is a normalized wrapper with both binders, even though its proof uses the stronger general theorem at :43. Unused source assumptions are not EXCESS. No Lean change is recommended; retain exactly:

```lean
(hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
```

At fixed ν, deleting these binders generalizes the parameterized equation without altering any displayed formula. However μ then means a mass scale; the largest planet/star ratio is μM with M=max ν, rather than μ. It is not a normalization-neutral source transcription. Set ν'=ν/M, μ'=Mμ, p'=p/M, q'=q. Then I'=I/M, C'=C/M, B'=B/M, δ'=δ/M; a, radian ω, actual V, k=1+μν and physical time are invariant. Applying the normalized theorem at ν',δ' transports constants with α=1/(2(τ+1)) as

`μ₀=μ₀'/M`, `c=c'M^(−α)`, `T₀=T₀'`, `AΛ=AΛ'M^(3/2)`, `Aa=Aa'√M`, `Aosc=Aosc'M`, `Aelem=Aelem'M`, with unchanged dStar,dPair. Allowed dependence on fixed ν is preserved, numerical constants are rescaled; no uniformity over ν follows. MAIN:527's `|k_i−1|≤μ` uses normalization; the generalized bound is Mμ. No source erratum is introduced by keeping the normalized anchor.

## Formula checks touched by the delta

| Object | Body/source check and evidence |
|---|---|
| strongAMD | ΣkeplerAction minus **absolute totalMomentum**, not signed physicalAMD or sum of individual absolute momenta; Momentum:41–42, frozen TotalMomentum:36–37; MAIN:35, N8 |
| canonical energy/action/eccentricity | frozen KeplerEnergy:35–36, KeplerAxis:36–37, KeplerAction:36–37, KeplerEccVector:35–40; total energy is ν_i E_i, action ν_i√a, vector is exactly MAIN:28–35 |
| canonical peri/apo | Osculating/Basic:76–81, a(1∓e), parameter one; not actual-velocity elements |
| actual V,k | Basic:42–46, `p_i/ν_i + μΣp_j`, **1+μν_i**; MAIN:512 |
| actual osculating elements | Basic:49–73, energy |V|²/2−k/r, axis −k/(2E), division of the **whole vector** by k, Euclidean eccentricity length; exactly (42) |
| pair threshold | Threshold/Defs:30–50: source axes, entire [0,1]² feasible set with a_i(1+u)≥a_j(1−v), objective I_iD(u)+I_jD(v), sInf of its image; no numerical optimizer or arbitrary feasible witness |
| physical lengths | frozen PlaneLength:38 is √Σv²; ambient Pi norm is used only for action/axis maximum-norm drift, per SPEC:33 |
| Diophantine | proposal:85–87 has every nonzero integer mode, radian ν_i³/I_i³; Fourier/Derivative:37 has Σ|k_i|, **ℓ¹**, no 2π insertion |
| time | proposal:90 is `T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))`; correct exponent and physical time, closed [-T,T] |
| exact model | frozen MovingHamiltonian:44–50 has the μ diagonal kinetic term plus μ cross kinetic term, together μ|Σp|²/2, and the negative pair potential; no fixed-Sun substitution |
| Newton reconstruction | actual masses `(1,μν)`, frozen ActualMasses:37–38; barycentric positions and velocities are the frozen source reconstruction; velocities:38–41 gives star −μΣp and planets p_i/ν_i, so their relative velocity is V_i |

Literal-formula equality does not override F4's public-carrier failure. No circular-orbit exclusion, prograde premise, initial pair-separation assumption or secular-state restriction was introduced.

## Checks, proof evidence and limitations

Every Lean/Lake invocation ran **from `/root/code/KAM-inp-lp-thr`**, one at a time, under the user's overriding D53 wrapper:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

1. Python exact-type comparison: proposal=draft=verification **True for both**. LP-PS producer types match after only ecc expansion, whitespace removal and unused-binder renaming. Manifest search finds no LP0/LP1 frozen entries.
2. Initial setup attempted to read the attachments relative to the build checkout, where they do not exist; it failed before creating the probe, and the associated Lean invocation reported the missing `/tmp` file. Corrected to absolute review paths. No mathematical failure or repository repair resulted.
3. `lake env bash -c 'export LEAN_PATH=/root/code/KAM-inp-lp-ps/.lake/build/lib/lean:$LEAN_PATH; exec lean /tmp/maud-lp-stmt2-verification.lean'`: **exit 0**, both literal proposed types consumed by the named producers. No placeholders or type-conversion hypotheses were added.
4. Independently extracted the exact `inp-lp-ps:KAM/Planetary/StrongAMD/PlanarSafety/Main.lean` to `/tmp/maud-lp-stmt2/KAM/Planetary/StrongAMD/PlanarSafety/Main.lean`; targeted compilation with `lean -R /tmp/maud-lp-stmt2 -o /tmp/maud-lp-stmt2/KAM/Planetary/StrongAMD/PlanarSafety/Main.olean <that source>` using LP-PS dependencies: **exit 0, no output**. This recompiles the branch text despite the other branch currently checked out at its worktree. No whole-library or application build was run.
5. A first verification import overlay containing only fresh Main failed with missing `Threshold.olean`, because Lean chose the first KAM prefix. Completed the `/tmp` overlay with read-only symlinks to existing LP-PS dependency artifacts (26,632 symlinks), preserving freshly compiled Main. Repeated the unchanged verification with `LEAN_PATH=/tmp/maud-lp-stmt2:$LEAN_PATH`: **exit 0**. Hence the successful exact-type consumption uses the fresh producer artifact, not merely an old Main cache.

The fresh verification printed:

```text
'KAM.Planetary.StrongAMD.Proposal.planar_strongAMD_exponentialSafety' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.Proposal.planar_strongAMD_barrier' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lp1_planar_strongAMD_safety' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

These are sorry-free ordinary producer/consumption checks. They do not independently replay the complete imported dependency graph or replace the pending LP-PS proof audit. The repaired THR2 branch was read directly; it was not silently installed into either checkout for these checks. Fresh Main plus cached dependencies is the precise validation scope. The attachment's “proved verbatim” claim is substantiated for its theorem types, not for future OD-11 restatements or future frozen exports.

6. Required lint, exact wrapped command with `<command> = sh scripts/lint_sources.sh`, from the build checkout: **exit 0**, output:

```text
check_lean_modules: PASS (3702 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

This lint/ABI result belongs to `/root/code/KAM-inp-lp-thr`; it is not a build or lint of the entire review checkout, the LP-PS branch or THR2. The opt-in lunar anchors were checked by file hash only. Waiting for the frozen guard and ABI gate was allowed to finish; no resource cap or compile gate was bypassed. There are no reviewer-owned implementation modules to `lake build`; the exact branch Main was targeted directly with Lean as recorded above.

## Handoff

Files: only `docs/tracks/LP/freeze/STATEMENT-REVIEW-2.md`. Approach: independent source reconstruction, expanded binder/carrier check, F1–F5 delta review, branch-text comparison, fresh targeted producer compilation, exact-type consumption and axiom inspection. Temporary probes and the symlink overlay are removed after checks. No generated root, frozen file, manifest, implementation source or owner-decision file was edited. No commit, root regeneration, application build, heartbeat override or subagent was used.

Uncertainties/gates: OD-11 and exact resulting source-facing definitions/anchor restatement; THR2 integration; final owner exact-text approval; pending independent proof-package/seal audits. Geometric tangency and the standalone two-/three-dimensional L16 theorem are not exported by this anchor. These limitations are not paid by compilation or standard-only axioms. No new suspected defect in pinned MAIN as amended was found; the remaining defects are freeze-interface/scope issues. The disclosed LP0 unnormalized static extension is retained as a deviation to approve explicitly. No errata-ledger change was made.

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

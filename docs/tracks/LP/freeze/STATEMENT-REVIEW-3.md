# Independent LP statement review 3 — short delta review

2026-11-01. Independent refute-first reviewer; no authorship of the declarations; no subagents. Method: `/root/.claude/skills/lean-statement-audit/SKILL.md`, read in full. Only this report is changed in the repository. The explicit pre-freeze review request governs: these are proposed texts, not manifest-bound frozen exports.

## Verdict

**PASS for the §3b delta under OD-11 option (b). F4 is resolved for the proposed source-facing definitions on their entire declared carriers.** The restrictions are exactly review 1 F4's text modulo whitespace, documentation and `noncomputable` supplied by the enclosing section. LP1 preserves draft 2's source premises, quantifier order and every quantitative conclusion. No BLOCKING or Lean CHANGE-RECOMMENDED finding in this delta; no replacement Lean text is required.

**Characterization semantic unit: adequate for the literal source formulas and the quantitative safety interface.** This does not certify a separately exported geometric conic-incidence/tangent-vector theorem. The earlier review's explicit geometric-L16 scope limitation remains.

```text
DECLARATION_FIDELITY: PASS (option-b proposal)
DRAFT_ALLOWLIST: N/A (unfrozen attachments; no proof holes in the option-b files)
PROOF_STATUS: ordinary sorry-free source adapter checked against cached producer dependencies
FROZEN_EXPORT_STATUS: PROPOSED_UNFROZEN; no LP anchor sealed or promoted by this review
```

OD-11 remains an open owner choice (`OWNER-DECISIONS.md:19`); this review supplies the requested technical verdict for (b), not owner approval. LP0 in §2 and LP1 in §3 still display `sorry` placeholders; this report does not treat them as allowed frozen bodies or as proofs. Their draft-2 fidelity assessment is retained, not a new package audit.

## Identity and scope

All relative evidence paths below are under `/root/code/KAM-inp-lp/`, except `thr:` = `/root/code/KAM-inp-lp-thr/` and `src:` = `/root/code/KAM-inp-lp-src/`.

| Reviewed object | SHA-256 |
|---|---|
| `docs/tracks/LP/FREEZE-PROPOSAL.md` | `2fe359bea7b0f08f15c65fcdd9698a091e675530af16eb613cda9b004baeb3c1` |
| `docs/tracks/LP/freeze/elaboration-draft-2.lean.txt` | `86de63bb60b6ba5f3184267cc3df66bf93b0cf72780364bddf799561a8d90c78` |
| `docs/tracks/LP/freeze/odb-SourceCarrier.lean.txt` | `dc120f9769a1b50133282c76b5c5051a6701a393b227db2945106dc7ef3cfbab` |
| `docs/tracks/LP/freeze/odb-PlanarSafety-Source.lean.txt` | `d4db4563448bb0129cb9e351ae308b5b10d75440cd8752a047f48e34b125ba19` |
| `docs/tracks/LP/source/MAIN.md` | `68e9167f04e4a04689ea163c74e02ffcaea657b252726080abdbe37bdba48c1b` |
| `docs/tracks/LP/source/AMENDMENTS.md` | `c887d1e27354a3db7fb8a20d8bf3e33a9ef95ff3173f925ba5ebfab192651881` |

Both odb attachments are byte-identical to `src:KAM/Planetary/StrongAMD/SourceCarrier.lean` and `src:KAM/Planetary/StrongAMD/PlanarSafety/Source.lean`, respectively, at inspection. Proposed normalized export: `KAM.Planetary.StrongAMD.lp1_planar_strongAMD_safety_source` (attachment:132–206); the general helper at :38–128 is not the normalized approval object. Exact section 3b text is proposal:156–208,216–289. No manifest ID, frozen path/hash or sealed provider exists for these proposed declarations; none is invented here.

## Expanded five-bin binder test

LP1 rows refer to `odb-PlanarSafety-Source.lean.txt:132–153` (proposal:216–237). The two components of every bundled input are expanded. SOURCE counts include scalar parameters and the individual physical premises; repeated typing proofs are counted explicitly.

| Input | Bin | Source/evidence |
|---|---|---|
| implicit `n : ℕ` | TYPING | MAIN:11 |
| `hn : 2 ≤ n` | STANDING | MAIN:11 |
| `ν : Fin n → ℝ` | STANDING | MAIN:11 |
| `hν : ∀ i, 0 < ν i` | STANDING | MAIN:11 |
| `_hνmax : ∃ i, ν i = 1` | STANDING | MAIN:11; OD-3 |
| `_hνle : ∀ i, ν i ≤ 1` | STANDING | MAIN:11; OD-3 |
| `A : Set (Fin n → ℝ)` | STANDING | MAIN:11–14 |
| `hA : IsCompact A` | STANDING | MAIN:11,15; empty allowed |
| `hAord.1 : ∀ a∈A, ∀ i, 0<a i` | STANDING | MAIN:13 |
| `hAord.2 : ∀ a∈A, ∀ i j, i<j → a i<a j` | STANDING | MAIN:13 |
| `δ : ℝ` | STANDING | MAIN:15 |
| `γ : ℝ` | STANDING | MAIN:15 |
| `τ : ℝ` | STANDING | MAIN:15 |
| `hδ : 0<δ` | STANDING | MAIN:15 |
| `hγ : 0<γ` | STANDING | MAIN:15 |
| `hτ : (n:ℝ)-1<τ` | STANDING | MAIN:15 |
| `μ : ℝ` | SOURCE | MAIN:70 |
| `0<μ` | SOURCE | MAIN:70 |
| `μ≤μ₀` | SOURCE | MAIN:70 |
| `z₀ : Phase (n*2)` | TYPING | MAIN:26–37,70 |
| initial `∀ i, 0<planeLength (bodyVector z₀.1 i)` | SOURCE | MAIN:70 |
| initial `∀ i, keplerEnergy ν z₀ i<0` | SOURCE | MAIN:70; energy = ν_i E_i |
| initial axes membership in A | SOURCE | MAIN:72 |
| all nonzero integer modes satisfy (5) | SOURCE | MAIN:64–65 |
| `hch.1 : ∀ i, 0<keplerAction ν z₀ i` | TYPING | MAIN:33,43; follows from hν and negative energy |
| `hch.2 : ∀ i j, i<j → actionAxis ν Λ i<actionAxis ν Λ j` | TYPING | MAIN:33,43; follows from ordered axes |
| `h₀.1 : ∀ i, 0<ν i` | TYPING | duplicate of hν, subtype formation |
| `h₀.2.1 : ∀ i, 0<planeLength (bodyVector z₀.1 i)` | TYPING | duplicate initial physical premise |
| `h₀.2.2 : ∀ i, keplerEnergy ν z₀ i<0` | TYPING | duplicate initial physical premise |
| initial `sourceStrongAMD ⟨z₀,h₀⟩ ≤ B−δ` | SOURCE | MAIN:35,72; literal restriction |

Counts: SOURCE 8, STANDING 15, TYPING 7, RULED 0, EXCESS 0. The component notation for `hAord`, `hch`, `h₀` denotes their pointwise expansion, not a claim that function-valued proofs have those projection expressions literally.

No conclusion-shaped input: `h₀` is constructible as `⟨hν,hphys⟩`. The osculating guards `Eosc<0`, `eosc<1` occur only in existential output `ho`, never as an initial premise. The proof explicitly constructs `hs` and `ho` from the producer's outputs (attachment:115–128). Proof irrelevance prevents any dependence on which subtype proofs are supplied.

LP0 is unchanged (proposal:46–68). Its expanded physical-branch input inventory is retained explicitly:

| Input | Bin | Evidence |
|---|---|---|
| implicit n | TYPING | MAIN:11 |
| hn | STANDING | MAIN:11 |
| ν | STANDING | MAIN:11 |
| hν | STANDING | MAIN:11 |
| U | SOURCE | MAIN:164 |
| compactness hU | SOURCE | MAIN:164 |
| hUch, positive actions | SOURCE | MAIN:43,164 |
| hUch, ordered squared axes | SOURCE | MAIN:43,164 |
| m | SOURCE | MAIN:164 |
| hm | SOURCE | MAIN:164 |
| z | TYPING | MAIN:26–37 |
| nonzero initial positions | STANDING | MAIN:24,28 |
| negative energies | SOURCE | MAIN:164 |
| hΛ, actions in U | SOURCE | MAIN:164 |
| AMD margin | SOURCE | MAIN:164 |

Counts: SOURCE 9, STANDING 4, TYPING 2, RULED 0, EXCESS 0. The deficit-list output binds I, membership hI, e, their full [0,1] bounds and deficit inequality (SOURCE conditions, MAIN:164), after the positive dStar,dPair are chosen; compact K is chosen before z. It retains every phase, compact containment, and invariable-frame bound. There is no new LP0 delta to approve. Its unnormalized positive-ν static extension remains disclosed (proposal:313–314), with no μ to reinterpret.

Output predicates hide no inputs: `IsMovingSolutionOn` is Hamilton equations for `movingHamiltonian 1 1 ν μ` plus collision freedom (`KAM/Frozen/Planetary/Defs/IsMovingSolutionOn.lean:35–38`); `MovingUniqueOn` quantifies over every open convex comparison interval containing zero and every competing solution with the same initial state (:37–40); `IsNewtonSolutionOn` exports all unequal barycentric-body separations, Q'=V and the full Newton acceleration sum (:36–42). Their comparison-solution guards are inside conclusions, not additional anchor premises. This is the finite-interval restriction/overlap-uniqueness interface already reviewed, not a new maximal-domain export.

## Findings and semantic unit

**R3.1 — NOTE, F4 resolved under (b).** `odb-SourceCarrier.lean.txt:46–98` implements precisely review 1:314–344, including the radial canonical case e=1 (MAIN:122) and the nondegenerate osculating case e<1. A whitespace/comment/modifier-normalized comparison returned True. No carrier adds interplanet separation: the one-body formulas do not need it. Negative canonical energy and nonzero positions remove undefined Kepler cases; positive ν,μ give k=1+μν>0; negative osculating energy and e<1 ensure genuine nondegenerate elements. All eleven restrictions have rfl equations (:102–133), with no choice/default branch or deferred reconstruction.

For each of `sourceStrongAMD`, `sourceKeplerPeri`, `sourceKeplerApo`, `sourceOscVelocity`, `sourceOscParam`, `sourceOscEnergy`, `sourceOscAxis`, `sourceOscEccVector`, `sourceOscEcc`, `sourceOscPeri`, `sourceOscApo`:

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: OK (defining equations plus stated domain consequences)
CHOICE_INDEPENDENCE: N/A (no choice of physical elements)
DEFINITION_VERDICT: PASS
```

The formulas, not radial inequalities alone, determine these literal source objects. `sourceStrongAMD_eq` (:142–143) expands C=ΣΛ−|L|; nonnegativity/deficit bound (:146–155) hold on the whole canonical carrier; canonical positive axis, e≤1 and endpoints (:158–173) cover the radial limit; osculating positive axis, positive perihelion and radial endpoints (:176–193) hold on the whole osculating carrier. For each characterization, expanded inputs are implicit n (TYPING), ν (STANDING parameter), μ when present (SOURCE parameter), z on its source subtype (TYPING; contains the exact positive-mass/nonzero-position/energy and, for osculating phases, positive-μ/e<1 source-domain guards), and i when present (TYPING index). There is no further assumption, estimate or existence/uniqueness gate. No characterized-by-choice object is involved, so an ∃! construction is unnecessary.

Meaning closure checked against `thr:KAM/Planetary/StrongAMD/Momentum.lean:41–42` and `Osculating/Basic.lean:42–81`: C uses absolute total momentum; peri/apo are a(1∓e); V=p/ν+μΣp; k=1+μν; energy, axis and eccentricity vector are exactly (42), using Euclidean plane lengths, not Pi norms. Frozen energy is ν_i times specific E_i (`KeplerEnergy.lean:35–36`), axis is −ν/(2 energy) (`KeplerAxis.lean:36–37`), action ν√a (`KeplerAction.lean:36–37`), eccentricity vector uses scaled p/ν (`KeplerEccVector.lean:35–40`). These inherited definitions remain guarded uses, not newly certified physical objects on unrestricted phases.

Threshold meaning is unchanged: `thr:KAM/Planetary/StrongAMD/Threshold/Defs.lean:74–89` has OrderedActions=chamber subtype, i<j on the pair export and hn on cross/strong exports. Its chamber, objective and feasible set are literal (3) (:30–50); the strong value is min of the adjacent family and finite star minimum. The nonempty-family guards prevent the n=1 empty-infimum defect. `Threshold/Pair.lean:204–215` gives attained least-value and unique-scalar-value characterization, as already reviewed in review 2:132–159. This round retains that interface assessment; it does not promote raw off-chamber helpers or re-audit the entire threshold proof package.

**R3.2 — NOTE, LP1 delta preserves the source claim.** Section 3b's exact theorem type compiled against the supplied proved adapter. A second, sorry-free reverse adapter recovered the entire draft-2 LP1 type, by supplying h₀=⟨hν,hphys⟩ and eliminating the output subtype witnesses. Hence no quantitative conclusion is lost by regrouping conjunctions under existentials. `ecc` is expanded to the same planeLength expression; underscore-prefixed normalization binder names do not remove their premises. Constants remain nine positive reals chosen before μ and z₀ (attachment:138–153); they may depend only on n,ν,A,δ,γ,τ and fixed d=2. No phase, orientation, eccentricity, torus selection or secular behavior is fixed before those constants. T remains T₀ exp(c μ^(-1/(2(τ+1)))). `KAM/Fourier/Derivative.lean:37` gives modeSize=Σ|k_i|, and the frequency ν³/Λ³ is unchanged; there is no hidden 2π in (5).

Every item in (8)–(9) remains: chamber membership, negative energies, AMD margin δ/2, sup-norm action/axis drift, n AΛ√μ AMD drift, canonical full-annulus gaps, every star distance and every unequal planet-pair distance (attachment:160–180). The entire osculating block retains negative energy, positive axis, e<1, radial endpoint bounds, the SUM of axis error and Euclidean eccentricity-vector error, both endpoint errors, half star/adjacent gaps (:181–205); both N10 smallness conditions remain before μ (:140). These prove no crossing of the entire instantaneous annuli, stronger than current-position separation (MAIN:91–93). Nondegeneracy guards are produced, not assumed.

**R3.3 — NOTE, OD-3 unchanged.** Both normalization premises remain (:134). Dropping them would be an equation-level generalization but would change μ's meaning to a mass scale; the largest planet/star ratio becomes μ max ν. Rescaling ν to ν/M and μ to μM preserves masses but scales canonical momenta and actions by 1/M, normalized AMD/margin by 1/M, and changes numerical constants. It is not a literal unchanged physical-parameter contract. The separately named `_general` theorem is ordinary helper scope, not the proposed normalized anchor. No replacement requested.

**R3.4 — NOTE, retain scope and packaging boundary.** Adequate characterizations must be frozen/versioned with the literal definitions and their internal formula closure, not just the codomain. The source adapter consumes the literal definitions by definitional reduction; its proof has no use of the characterization inequalities because it transports already established conclusions. Future source-object/graph closure must record the companion semantic unit as required by the skill; this review does not certify a graph or manifest that does not exist. “Internal helpers” here means no independent whole-carrier source-object freeze certification; the Lean totals remain public implementation declarations.

The SourceCarrier module documentation (:32–33) describes a genuine ellipse “through the current position,” but the named endpoint theorems alone prove only radial bounds. Full incidence and actual-velocity tangency are mathematical consequences of the audited formulas on the valid carrier, not separately exported geometric assertions in LP1. `thr:Osculating/Basic.lean:87–92` identifies V with the moving field; its `osc_tangency` name does not enlarge its actual radial conclusion. As in review 2:130, no missing (8)–(9) or quantitative (43) conjunct remains; standalone L16 over arbitrary safe compact sets in dimensions two AND three, and a geometric tangency theorem, are not exported. No new Lean replacement is recommended for this quantitative safety anchor. Do not call this full standalone-L16 theorem closure.

## Verification and handoff

Transient `/tmp/maud-lp-review3.lean` concatenated the exact SourceCarrier commands and the two exact source-adapter theorem commands; added the existing Main import and omitted the unavailable SourceCarrier import (its identical commands were local). It then stated §3b verbatim as `review3_exact_proposal`, closed it by the normalized source export with every outer argument, and stated the draft-2 LP1 type verbatim as `review3_back_to_draft2`, closed it by explicit witness unpacking. No repository implementation or import overlay was written. This checks fresh adapter/characterization proof bodies against the thr build's cached Main dependencies, not a fresh proof-package replay.

Command, from `/root/code/KAM-inp-lp-thr`, one invocation at a time:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean /tmp/maud-lp-review3.lean
```

Final exit **0**, no warnings/errors. `#print axioms` for all eleven substantive characterization exports (`sourceStrongAMD_eq`, nonnegativity, deficit bound, four canonical and four osculating consequences), the normalized source LP1, exact proposal consumption, and reverse draft-2 consumption: each reports exactly `[propext, Classical.choice, Quot.sound]`, with no sorryAx. The first scratch run failed only because the reviewer's exact-type application omitted its outer arguments; adding them fixed that harness error. It was not a proposed-statement defect.

Lint, from `/root/code/KAM-inp-lp-thr`:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
```

Exit **0**. Exact output:

```text
check_lean_modules: PASS (3720 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

This lint result belongs to the thr checkout, not the full src branch or review checkout; its application anchors were checked by hash only.

An initial shell-only lint in the review checkout was stopped during its Python guard stage and rerun under the full cap from the mandated thr checkout before any Lean ABI subprocess from that attempt. Its partial output is not an acceptance result.

No reviewer-owned implementation module requires a targeted lake build; the exact changed Lean commands were targeted directly above. No library/application rebuild, heartbeat override, frozen edit, manifest edit, generated root edit or commit was performed. Temporary Lean/check-generation files were removed after verification. The report includes the only owned repository path.

Uncertainties: final owner choice/approval, exact final freeze identity and definition/characterization co-manifestation, integration and independent full producer proof audit. No new suspected erratum in MAIN as normatively amended; no mathematical deviation introduced. LP0's disclosed static normalization extension and the earlier standalone-L16/geometric export limitations persist.

## Hard rules (verbatim)

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

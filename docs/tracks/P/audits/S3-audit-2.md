# S3 independent package audit 2 — delta

Date: 2026-10-28. **Overall: PASS WITH NOTES for the S3 infrastructure slice**,
with the independent validation receipts below. F1 is closed; F2's missing
literal export is closed by `sb_s_geometry`. The design/graph mapping still needs
the orchestrator to name that companion for the full parent conclusion. The signed
`sb_s` alone remains narrower. This is not a frozen theorem sealing verdict.

## Scope and identity

Audited only `KAM/Planetary/SecularBox/Region.lean` in
`/root/code/KAM-inp-p14-s3`, following the named brief and AUDIT FOCUS. The exact
user-specified worktree report path overrides the brief's generic main-worktree path.
Read AGENTS, PLAN, DECISIONS, S3 handoffs (including `.drafts/handoff-S3b.md`), audit 1,
P14 design/node table and design audits, live signed declarations, track-P statement,
blueprint p14b:175–193, graph packet and relevant frozen definitions/theorem anchors.
Applied the lean-statement-audit skill to the new theorem statements. The unchanged
private declarations retain audit 1's review; S0/S1 are outside this delta audit.

- HEAD: `249196db4fd9e7bfc61e1b295153186b3a6dbcf5`.
- Live comparison `inp`: `cc793a7c3e329bd89353f655ccc5630f3f4ddcef`.
- Round-1 baseline: `fb228a66900b09653c0d1a4d7cadfe3dc17c7d22`.
- Region SHA-256: `c2426e1df27a07f806badfc93c38c4cf9bea0b02c58f304d27b3c95ab8d8eca6`.
- Live P14Signatures SHA-256:
  `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`.

`git diff inp...HEAD` adds Chart, Region, audit 1 and the original S3 handoff.
Chart is dependency context, not additional audit scope. `git diff --numstat
fb228a66 HEAD` reports only `80 0 KAM/Planetary/SecularBox/Region.lean`.
This is an append of declarations before the existing closing namespace/section:
byte comparison confirms the entire old prefix and the entire old closing suffix
are preserved. No old declaration, proof, import or definition was modified.
`sb_sdef`'s full defining command and `sb_s`'s full telescope also compare byte-equal
to the live signature file (lines 371–377 and 435–440).

## Finding resolution and node ledger

All public names below have prefix `KAM.Planetary`.

| Node / declaration | Verdict | Reason / exact locator |
|---|---|---|
| `bpP:p14:sb-smooth#data` | PASS retained | `sb_sdef` parameter and `sb_s` interval unchanged. Geometry requires no μ input. |
| `bpP:p14:sb-Sdef` / `sb_sdef` | PASS retained | Region:31–36, signed whole-carrier definition unchanged. |
| Signed `sb_s` | PASS retained | Region:126–170, entire declaration/proof unchanged; exact signature. |
| `stepP:p14:sb-S-1` / `sb_s_radicand` | PASS; F1 CLOSED | Region:174–189 states exactly both strict inequalities requested in audit 1, from the action part of S membership. |
| `bpP:p14:sb-S` / `sb_s_geometry` | PASS WITH NOTES; F2 export CLOSED | Region:194–250 exports all literal geometry clauses. Use this companion for the full node; mapping note below. |
| `stepP:p14:sb-S-2` | PASS retained | Existing `sbRegion_planet`; eccentricity and Jacobian bounds also projected by companion. |
| `stepP:p14:sb-S-3` | PASS | Existing proof retained; companion:224–250 explicitly proves/exports both radii, ordering and separation. |

F1: `sb_s_radicand` has exactly the conjunction

```lean
(99/100 : ℝ) < 1 - secularGamma w i / (2 * fast w.2 i) ∧
  (99 : ℝ) / (100 * fast w.2 i) <
    (1 - secularGamma w i / (2 * fast w.2 i)) / fast w.2 i
```

Its only logical premise is `∀ i, 0 < fast w.2 i ∧ 50 * secularGamma w i < fast w.2 i`,
which is a projection of S membership. It is stronger than a theorem requiring the
full S membership: no mass interval or axis bounds are needed. The proof clears the
positive denominator `2Λ`, obtains Γ/(2Λ)<1/100, then divides the numerator margin
by positive Λ. `field_simp` proves the literal denominator rearrangement; no bound
is replaced by positivity alone. The local nonnegativity proof is harmless and not
an added premise. A transient application probe supplies `hw.1` directly.

F2: `sb_s_geometry` has exactly `sb_s`'s hypotheses and quantifier scopes:
saturn first, its fixed interval premise, then all `w ∈ S` and all `F : Fin 2 → ℝ`.
It exports openness; Λ>0 and 0≤Γ<Λ; k>49/50; both radicand inequalities; e<1/5;
J>4/5; positive individual radii; |q₀|<53/10·6/5; 47/5·4/5<|q₁|; |q₀|<|q₁|;
|q₀−q₁|>0; and literal frozen NoCollision. These are the literal p14b:186
conclusions, with openness and the explicit numerator bound additionally retained.
The radicand matches the expression inside the frozen `secularEccVector` square root.
The axes, plane length, positions, and phase point are the original frozen objects.

The explicit ellipticity and Jacobian/NoCollision clauses give SecularRegular (i),(ii)
with positive weights supplied from saturn's interval. The companion does not claim
integrability or differentiability, i.e. SecularRegular (iii),(iv). Reusing `sb_s`
for openness and collision-freeness is legitimate; the new quantitative claims are
proved from the old pointwise chart helper and S inequalities, rather than assumed.
The pair order in the exported distance is exactly q₀−q₁, using symmetry of plane length.

**Mapping note:** P14-LEAN-DESIGN.md:226 still assigns `bpP:p14:sb-S` to `sb_s`,
and Region:18–21 retains that older shorthand. The handoff S3b expressly flags this.
Under this round's explicit companion-based repair, the literal conclusion now exists
as a public Lean theorem, so there is no remaining mathematical/export gap. The
orchestrator should reconcile the node mapping with `sb_s_geometry`; consumers needing
radii or radicand cannot obtain them by projecting `sb_s` alone. This audit does not
silently modify the signed declaration or claim that the old mapping was updated.

## Expanded binder audit

The following table lists every input binder of the two added declarations, splitting
the conjunction in `h`. Quantifiers inside `h` are shown separately; bound conclusion
variables of the companion are also included. No instance or bundled premise occurs.
Source references are `blueprint-P/parts/p14b-secular-box.tex`.

| Declaration | Input / bound variable | Bin | Source |
|---|---|---|---|
| `sb_s_radicand` | implicit `w : Phase (2+2)` | TYPING | :180, :186 |
| same | `j : Fin 2` inside h | TYPING | :180, “i=0,1” |
| same | h: `0 < fast w.2 j` | SOURCE | :180, Λᵢ>0 |
| same | h: `50 * secularGamma w j < fast w.2 j` | SOURCE | :180, 50Γᵢ<Λᵢ |
| same | explicit `i : Fin 2` | TYPING | :190, per-planet conclusion |
| `sb_s_geometry` | `saturn : ℝ` | TYPING | :177, fixed σ |
| same | hs: `29/100 ≤ saturn` | SOURCE | :177 |
| same | hs: `saturn ≤ 31/100` | SOURCE | :177 |
| same | `w : Phase (2+2)` | TYPING | :186 |
| same | membership action clauses: Λᵢ>0; 50Γᵢ<Λᵢ | SOURCE (2) | :180 |
| same | membership axis endpoints: 51/10<a₀; a₀<53/10; 47/5<a₁; a₁<97/10 | SOURCE (4) | :180 |
| same | `i : Fin 2` inside membership action clauses | TYPING | :180 |
| same | `F : Fin 2 → ℝ` | TYPING | :186, arbitrary F∈ℝ² |

Counts (expanded logical clauses and displayed type binders): radicand SOURCE=2,
TYPING=3; companion SOURCE=8, TYPING=4; STANDING=0, RULED=0, EXCESS=0 for each.
Conclusions' own per-planet quantifiers add no hypotheses. Constants are fixed
rationals, not chosen witnesses with enlarged dependence.

## Definition classification and anchor boundary

No new def, abbrev, structure, instance or choice object is introduced by this delta.
The sole package definition remains the literal set `sb_sdef` on all Phase (2+2).
BODY_MATCH: OK. PUBLIC_CARRIER: OK. WELL_DEFINEDNESS: N/A_LITERAL.
CHARACTERIZATION: N/A_LITERAL. CHOICE_INDEPENDENCE: N/A. DEFINITION_VERDICT: PASS.
Its exact signed formula imposes no fast-angle restriction; it uses total frozen
formulas without introducing an off-domain fallback. Round 1's whole-carrier review
is retained by byte identity and the defining-equation probe.

This is an infrastructure module, with no provider export or frozen seal to test.
The import closure has 53 KAM modules, no Provider or frozen theorem import; all 48
imported frozen modules are definitions marked SEALED in the live manifest.
`secularBoxSafety` and `secularBoxAtCitedMasses` remain DRAFT_SORRY, unavailable as
proof dependencies and not made seal-ready by S3. Provider equality/seal-body probes
are N/A here. No theorem closure claim is made for either anchor.

## Independent validation

All Lean/Lake processes ran serially with LEAN_NUM_THREADS=1 and nice -n 5;
no resource override or clean rebuild was used. The gate wraps its Lake child in nice.

1. Targeted build (no clean):

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s3 KAM.Planetary.SecularBox.Region
   [inp-gate] slot 2 acquired 18:59:08 for KAM.Planetary.SecularBox.Region
   Build completed successfully (9099 jobs).
   exit 0
   ```

   The wrapper waited for a slot, then completed without warnings. This is the
   targeted dependency job graph, not a clean full-library build.

2. Transient signature/geometry/membership, axiom and environment probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S3Audit2.lean
   'KAM.Planetary.sb_sdef' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sb_s' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sb_s_radicand' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sb_s_geometry' depends on axioms: [propext, Classical.choice, Quot.sound]
   root sb_sdef: false
   root sb_s: false
   root sb_s_radicand: false
   root sb_s_geometry: false
   exit 0
   ```

   The probe copied the live signed definition to `auditExpectedRegion`, checked
   equality with `sb_sdef` by rfl, and proved the signed sb_s telescope with its
   actual export. It also checked the companion's complete telescope under a fresh
   name and applied `sb_s_radicand hw.1 i` at exactly audit 1's requested conjunction
   from full S membership. It imported no signature file or draft anchor. Root
   checks queried the actual elaborated environment, rather than only source text.

3. Independent kernel replay, one invocation for the sole in-scope module:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.Region
   replaying KAM.Planetary.SecularBox.Region
   exit 0
   ```

4. Static checks:

   - `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-p14-s3 KAM.Planetary.SecularBox.Region`
     printed `short-name check OK (no reused public short name)`, exit 0.
   - Forbidden-token, all set_option, and EuclideanSpace scan of Region: no matches
     (`rg` exit 1). No new imports, premise bundles or local instances occur.
   - Module copyright, module command, public imports, docstring and exposed public
     section are present. Region has 254 total lines, maximum 98 Unicode characters;
     every line is ≤100 and the file is below 1500 lines.
   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   - `git diff --check inp...HEAD` and `git diff --check`: empty, exit 0.
   - Python byte extraction returned True for preserved old prefix, preserved old
     closing suffix, exact signed definition command, and exact signed sb_s telescope.
   - Recursive source import/manifest check: 53 KAM modules, 48 frozen SEALED
     definitions, no provider or frozen theorem imports.

5. Full source lint, after kernel replay completed:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (824 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The only failing diagnostic is the generated-root exception explicitly permitted
   by the audit brief. The root was not regenerated. Module checks, frozen-anchor
   guard and all 144 ABI hashes passed. No other lint diagnostic appeared.

## Uncertainties, suspected errata and deviations

No suspected pinned-source defect or mathematical counterexample was found. The source
inequalities are correct and are now proved with their literal constants. The delta
introduces two distinct public companion lemmas, as explicitly requested, while
preserving the signed declarations and proofs. No auditor source repair was made.
The remaining documentation mapping note is located at P14-LEAN-DESIGN.md:226 and
Region:18–21: the old text identifies `sb_s` as the full node, whereas its exact signed
type omits the quantitative clauses now furnished by `sb_s_geometry`. This is the
inherited contract/mapping discrepancy from audit 1, not a new source erratum.

This report retains the unchanged declarations' prior audit status by byte identity,
and independently validates the current module. It does not re-audit S0/S1 or assert
any downstream smoothness, ODE, full regularity or frozen-anchor closure. The exact
companion is available for downstream use; graph remapping and actual consumer
integration belong to the orchestrator.

Workflow memory was used only for report/scratch-only scope and serial validation;
all package-specific claims and validation receipts were checked against live files.

Final cleanup: removed `.lake/abi-scratch/S3Audit2.lean`. Final source hash/HEAD checks
match the audited snapshot; `git diff --check` passes. The only working-tree change
is this new report. All required checks are complete; there are no pending probes.

# Handoff LP-FREEZE7: FREEZE-PROPOSAL draft 7 (D59), exact freeze text of LP0, LP1, LP2 and the τ = n − 1/2 corollaries

Branch `inp-lp-freeze7` (worktree `/root/code/KAM-inp-lp-freeze7`), base `701c239b`. Nothing was created or edited
under `KAM/Frozen/` or `manifest/` (not even transiently); `git diff 701c239b -- KAM/Frozen manifest KAM.lean
README.md` is empty.

## Result

Draft 7 is ready for the independent statement audit. **No ruling had to be bent and no premise was added**: every
D59 ruling is implementable as stated, and every draft-7 anchor and characterization theorem is closed by an existing
or newly proved, sorry-free implementation theorem with axioms exactly `[propext, Classical.choice, Quot.sound]`.

- **Anchors (5):** LP0 `KAM.Planetary.StrongAMD.planar_strongAMD_barrier`, LP1
  `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety`, LP1-H `…_exponentialSafety_halfInteger`, LP2
  `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety`, LP2-H `…_halfInteger`. Paths, providers and closing
  theorems: FREEZE-PROPOSAL §2.
- **New definitions (88)** and **characterization theorems (34)**: FREEZE-PROPOSAL §4.2 and §5 (tables with path,
  role, implementation module, semantic unit). **Already-frozen reused (19)**: §4.1.
- **Recommendation on the corollaries:** freeze LP1-H and LP2-H as anchors (OD-4 rules them in; the headline
  exponent `1/(2n+1)` is otherwise only implicit); they add no mathematical content, and dropping them loses nothing
  provable. Texts drafted either way, in the explicit-exponent ("Zohar's headline") form.
- **LP0** applied the total `strongAMD` to a physical state, so it is restated through `sourceStrongAMD ⟨z, h⟩` on
  `SourceCanonicalPhase n ν` with a typing binder `h` after `hΛ`, exactly as §3b did for LP1; proved
  (`lp0_planar_barrier_source`).

## Files

New implementation (track LP, non-frozen; module docstrings carry the package id, MAIN lines, "track LP,
non-frozen" and the exact sentence "The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md."):
- `KAM/Planetary/StrongAMD/PlanarSafety/SourceCorollary.lean` (149 lines): `lp0_planar_barrier_source`,
  `lp1_planar_strongAMD_safety_source_halfInteger`.
- `KAM/Planetary/Spatial/SpatialSafety/SourceCorollary.lean` (122 lines):
  `lp2_spatial_strongAMD_safety_source_halfInteger`.
- `KAM/Planetary/StrongAMD/PlanarSafety/SourceThreshold.lean` (75 lines): `orderedCrossThreshold_isLeast`,
  `orderedStrongThreshold_isLeast` (attained-minimum characterizations of the carrier `⨅`s, MAIN (3)).

Docs:
- `docs/tracks/LP/FREEZE-PROPOSAL.md`: draft 7 (rewritten as the approval object; history/alternatives in
  Appendix A).
- `docs/tracks/LP/freeze/draft7/KAM/Frozen/**/X.lean.txt`: the 127 exact frozen file texts;
  `docs/tracks/LP/freeze/draft7/manifest-entries.json`: 127 manifest entry drafts.
- `docs/tracks/LP/freeze/verification-draft-7.txt`: commands and exact outputs of every check.
- This handoff (`docs/tracks/LP/audits/LP-FREEZE7-handoff.md`; copy `.drafts/handoff-LP-FREEZE7.md`).

Generator and scratch (gitignored, `.drafts/freeze7/`): `extract_anchors.py` (anchor texts derived from the proved
implementation statements by asserted textual substitutions), `gen.py` (all draft texts: definition and
characterization texts extracted verbatim from the implementation), `mk_checks.py`, `mk_bc.py`, `mk_manifest.py`,
`mk_proposal.py` (every proposal code block asserted to be a byte-identical excerpt of a draft file),
`mk_verification.py`, the scratch Lean files `a/*.lean`, `b_bodies_equal.lean`, `b2_value_diff.lean`,
`c_verification.lean`, `closure.lean`, `ax_freeze7.lean`.

## Main statements proved (new)

```lean
-- KAM.Planetary.StrongAMD (PlanarSafety/SourceCorollary.lean)
theorem lp0_planar_barrier_source  -- type = the LP0 draft text (§3.1), alpha-equivalent (check (c))
theorem lp1_planar_strongAMD_safety_source_halfInteger  -- type = LP1-H text (§3.3)
-- KAM.Planetary.Spatial (SpatialSafety/SourceCorollary.lean)
theorem lp2_spatial_strongAMD_safety_source_halfInteger  -- type = LP2-H text (§3.5)
-- KAM.Planetary.StrongAMD (PlanarSafety/SourceThreshold.lean)
theorem orderedCrossThreshold_isLeast {ν : Fin n → ℝ} (hn : 2 ≤ n) (I : OrderedActions ν) :
    IsLeast {b | ∃ (i j : Fin n) (hij : i < j), (j : ℕ) = i + 1 ∧
        b = orderedPairThreshold I i j hij}
      (orderedCrossThreshold hn I)
theorem orderedStrongThreshold_isLeast {ν : Fin n → ℝ} (hn : 2 ≤ n) (I : OrderedActions ν) :
    IsLeast ({b | ∃ (i j : Fin n) (hij : i < j), (j : ℕ) = i + 1 ∧
        b = orderedPairThreshold I i j hij} ∪ Set.range I.1)
      (orderedStrongThreshold hn I)
```

The full statements of the first three are the anchor texts of FREEZE-PROPOSAL §3 (with the implementation names);
check (c) confirms the elaborated types are alpha-equivalent (`Expr.eqv`) to the draft anchor texts.

## Checks run (exact commands; outputs in the verification file)

Wrappers only (`lp_build.sh`, `lp_lean.sh`, `lp_lint.sh`), one Lean process at a time.

- **Build** `/root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-freeze7
  KAM.Planetary.StrongAMD.PlanarSafety.SourceThreshold KAM.Planetary.StrongAMD.PlanarSafety.SourceCorollary
  KAM.Planetary.Spatial.SpatialSafety.SourceCorollary`: exit 0, "Build completed successfully" for each (9051 / 9316
  / 9366 jobs); no warning or error in the three new files. (Before that, `lp_build.sh … PlanarSafety.Source
  Spatial.SpatialSafety.Source` to bring the worktree's LP oleans up to date: exit 0.)
- **Axioms** (`lp_lean.sh … .drafts/freeze7/ax_freeze7.lean`, exit 0): `lp0_planar_barrier_source`,
  `lp1_planar_strongAMD_safety_source_halfInteger`, `lp2_spatial_strongAMD_safety_source_halfInteger`,
  `orderedCrossThreshold_isLeast`, `orderedStrongThreshold_isLeast`: each `[propext, Classical.choice, Quot.sound]`.
- **Root:** `python3 scripts/gen_root_imports.py` (KAM/Root/Planetary.lean +3 imports; committed).
- **Lint** `/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-freeze7`: exit 0 (tail: "check_lean_modules:
  PASS (3780 Lean files …)", "FROZEN-ANCHOR GUARD OK", "ABI HASHES OK (177 frozen declarations …)"). (A first lint run
  failed only with "KAM.lean is out of date" before the root regeneration.)
- **Short names** `main_shortname_check.py /root/code/KAM-inp-lp-freeze7` on the three new modules: exit 0.
- **Closure** (`lp_lean.sh … closure.lean`, exit 0): Lean's constant closure of the 39 closing theorems = the 85
  new definitions in the closure + 21 already-frozen ones (verification §1).
- **(a) Text elaborates** (`lp_lean.sh … .drafts/freeze7/a/<module>.lean`, one per draft file): 127/127 exit 0; the
  only messages are 39 "declaration uses `sorry`" warnings, exactly one per theorem file. (A first full run found a
  missing `Fintype (Fin n)` import in the two barycentric files; fixed by `Mathlib.Algebra.BigOperators.Fin`, and the
  four affected files re-run.)
- **(b) Bodies equal** (`lp_lean.sh … b_bodies_equal.lean`, exit 0, no error or warning): 88/88 `rfl`; 88 types
  alpha-equivalent with equal reducibility; 77 values alpha-equivalent; **(b2)** (`b2_value_diff.lean`, exit 0) shows
  the other 11 differ only in auxiliary proof constants (and the intended `AdjIdx.lt_upperIdx` replacement).
- **(c) Verification** (`lp_lean.sh … c_verification.lean`, exit 0, no error or warning): all 39 draft theorems
  stated verbatim close by `exact` of the implementation theorem; 39/39 types alpha-equivalent to the implementation
  statements; `#print axioms` exactly `[propext, Classical.choice, Quot.sound]` for all 39. (An earlier run exposed a
  generator bug — characterization statements ending in `:= term` on the same line swallowed the next declaration —
  fixed before the definitive run.)
- `git diff 701c239b -- KAM/Frozen manifest KAM.lean README.md`: empty.

## Items not done

- Nothing in the brief is left undone. Not in scope (by the brief): creating anything under `KAM/Frozen/`,
  `manifest/` or `KAM/Provider/`; computing hashes (`TBD at freeze`); the statement audit itself.

## Choices between conventions (for the audit to check)

1. **Paths and namespaces** mirror the namespace, as for every existing track: planar
   `KAM/Frozen/Planetary/StrongAMD/{Defs,Theorems}/`, spatial `KAM/Frozen/Planetary/Spatial/{Defs,Theorems}/`,
   `KAM/Frozen/Fourier/Defs/ModeSize.lean`; providers `KAM/Provider/Planetary/{StrongAMD,Spatial}/<Name>.lean`
   exporting `KAM.Provider.Planetary.{StrongAMD,Spatial}.<name>`. File name = CamelCase of the declaration name.
2. **Frozen names = current implementation names** for all 88 definitions and all 34 characterizations (so no LP
   theorem changes at rebase); the 5 anchors have new names (draft-6 §1 / R4.2), distinct from every implementation
   name.
3. **Characterization theorems as frozen theorem anchors** (brief): the 32 existing carrier lemmas listed in draft-6
   §3b/§4b plus 2 new threshold ones. The `_def`/`rfl` equations are not frozen separately (the frozen bodies are those
   equations). Characterizations are frozen only where draft 6 listed them; the literal restrictions without one are
   `N/A_LITERAL` (proposal §5).
4. **Frozen set = anchor/characterization closure + the §4b source set.** Lean's closure computation (verification
   §1) shows 85 new definitions in the closure; the 3 others (`sourceOscVelocity`, `sourceOscParam`,
   `spatialSourceOscVelocity`) are frozen only because draft-6 §3b/§4b list them. Draft-6 §4b listed
   `crossThreshold/starThreshold/strongThreshold` and `spatialStrongAMD/spatialStrongAMDOn` as closure members;
   they are not, so they are not frozen (corrected in §4.2).
5. **`KAM.Fourier.modeSize` is frozen** (it is in the anchors' text and not yet frozen) rather than switching the
   Diophantine premise to the frozen `KAM.IsDiophantine` (equivalent pointwise, but a change of the reviewed text).
   Rebase consequence: a two-line edit of the shared `KAM/Fourier/Derivative.lean` (rebase point 1).
6. **`orderedCrossThreshold`'s frozen body inlines `(Nat.lt_succ_self a.1.val)`** for the unfrozen theorem
   `AdjIdx.lt_upperIdx` (one declaration per frozen file). `rfl`-equal to the implementation (check (b)).
7. **Mathlib imports** of the new frozen files are minimal and explicit (no `import Mathlib`), plus `public import`
   of the frozen files of the directly referenced declarations; check (a) elaborates every file in exactly the
   environment those imports give.
8. **`definition_closure`** lists the complete transitive closure of imported frozen definition files, including the
   core `KAM/Frozen/Defs/*` (the R/W/core-theorem convention; the P/N/I entries omit the core files). The guard only
   checks membership and hashes; the orchestrator may prefer the P convention.
9. **Module docstrings** follow the D25/SO template, with `<APPROVAL-DATE>`, `<DECISION>` placeholders as the only
   bytes to fill at freeze, and a "Freeze role" paragraph per definition (literal / carrier / source / internal).
10. **Docstring fixes in frozen texts:** `spatialKeplerAxis` (canonical, not osculating; R4.6), four spatial
    "Tangency" → "Radial incidence" (R4.5). All other docstrings are the implementation's. Line breaks of five or so
    signatures were reflowed (whitespace only) after making `{n : ℕ}` explicit, to keep ≤ 100 columns.
11. **LP1 binder layout:** `(hν …) (hνmax …) (hνle …)` on one line, as in LP2 (whitespace only vs §3b).
12. **Split policy** `NOT_SPLIT`, one source group per entry (SO precedent for definition + characterization pairs);
    `ruling_ref` `docs/DECISIONS.md D59`.

## AUDIT FOCUS

- **LP0 under (b)** (§3.1): the only new anchor text. Binder `h` after `hΛ` (TYPING: from `hν` and the physical
  premise); the canonical radii still use the frozen `keplerAxis`/`keplerEccVector`; the deficit clause uses
  `actionAxis`/`eccDeficit` on abstract `I ∈ U`, `e ∈ [0,1]ⁿ`.
- **Corollaries** (§3.3, §3.5): exactly four textual changes each vs LP1/LP2 (`diff` in the verification file).
- **Threshold semantic units** (§5): `orderedCrossThreshold_isLeast`, `orderedStrongThreshold_isLeast` — the
  `(j : ℕ) = i + 1` encoding of adjacency and the set `… ∪ Set.range I.1` for `min(B_cross, B_⋆)`.
- **Internal helpers** (§4.4): every raw total helper occurs in an anchor only as a sign condition inside a guarded
  predicate; check the role paragraph of each "internal" file.
- **`orderedCrossThreshold` body** (proof term inlined) and the 11 definitions whose values are `rfl`-equal but not
  syntactically identical to the implementation's (check (b2) shows the only differences).
- **Rebase plan** (§7), in particular the shared-module edit for `modeSize` and the move of characterization proofs
  into providers.

## Uncertainties

- The provider files and the freeze/seal commits are not drafted as files (outside the owned paths); §7 describes
  them. The sealed-body strings are in each theorem file's docstring.
- Check (a) simulates each module's environment in a single scratch file (dependencies concatenated); it cannot
  build real modules at the frozen paths (forbidden), so module-system visibility subtleties (e.g. `@[expose]`
  across real module boundaries) are not exercised. All files use `@[expose] public noncomputable section` (defs)
  or `@[expose] public section` (theorems), as the existing frozen files do.

## Suspected errata, deviations, design signals

- **Errata in MAIN:** none new.
- **Deviations:** none from MAIN. Relative to draft 6: LP0 restated through `sourceStrongAMD` (required by the
  brief), anchor names (R4.2), the four §4b closure corrections (item 4 above), and the docstring fixes (item 10).
- **Design signals:** none. No heartbeat issue; largest scratch file 1049 lines; the new Lean files are ≤ 149
  lines.
- **Open note for the orchestrator:** R4.6's `KAM/Planetary/Spatial/Model.lean` module docstring ("no
  totalization") is an implementation docstring outside this package; still to fix by its owner.

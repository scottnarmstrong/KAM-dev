# Package LP-FREEZE7: FREEZE-PROPOSAL draft 7, the exact freeze text of LP0, LP1, LP2 and the τ = n − 1/2 corollaries under D59 (approval object)

Freeze preparation. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers,
handoff). Base: `inp-lp-freeze7` = `inp-lp-w4e` (every planar and spatial LP package, including LP-SRC, SP-SAFE,
SP-SRC/SRCB/SRCB2) + `inp-lp`.

## The rulings (D59; read `git show main:docs/DECISIONS.md`, entry D59, and `docs/tracks/LP/OWNER-DECISIONS.md`)

The owner approved the recommended rulings (D59, 2026-11-01). They are binding:
- **OD-1:** `strongAMD = ΣΛ − |L|`; no prograde premise.
- **OD-2 + OD-11 (b):** every frozen meaning-carrying definition lives on its source carrier, as one semantic unit with
  its characterization theorem. That means the thresholds on `OrderedActions` (`2 ≤ n` where §4b says), and the strong
  AMD, Kepler and osculating elements through the source subtypes. The spatial anchors go through `spatialSource*`
  (review 4, resolution (A)). The total formulas stay internal helpers. Option (a) and resolution (B) are **not**
  chosen.
- **OD-3:** the anchors keep `max ν = 1` (`hνmax`, `hνle`). The general-mass versions stay ordinary theorems.
- **OD-4:** `τ > n − 1` is free, plus the `τ = n − 1/2` corollary (exponent `1/(2n+1)`).
- **OD-5 + OD-9:** canonical annuli, all-pair distances, and actual-velocity osculating annuli with half gaps. The
  `μ₀` ordering is internal.
- **OD-6:** new anchors only; P-EXP-SAFE is untouched.

**Scope:** D59 approves the rulings, not the freeze. Draft 7 is the **approval object**: exact text only, with no
alternatives left in it. **Nothing may be created under `KAM/Frozen/` or `manifest/`, even transiently.**

## Inputs (read in full)

- `docs/tracks/LP/FREEZE-PROPOSAL.md` (draft 6): §1, §2 (LP0), §3/§3b (LP1, and LP1 under (b)), §3c/§3d (LP2, and LP2
  under (b)), §4, §4b (definition freeze inventory, planar and spatial).
- The statement reviews `docs/tracks/LP/freeze/STATEMENT-REVIEW-{1,2,3,4,5}.md`, especially the open notes: R4.2
  (anchor names), R4.4–R4.9, R5.1–R5.7.
- The repository conventions for frozen files and the manifest:
  - an existing definition file, e.g. `KAM/Frozen/Planetary/Defs/PlanetaryTimeExponent.lean`, and a theorem anchor,
    e.g. `KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean`;
  - their entries in `manifest/frozen-anchors.json` (fields `id`, `kind`, `author_approval`, `source`, `contract`,
    `path`, `export`, `split_policy`, `definition_closure`, `abi_sha256`);
  - `AGENTS.md` rules 3, 4, 5 and 9 (DRAFT_SORRY anchors, providers `KAM/Provider/<Name>.lean` proving
    `KAM.Provider.<name>`);
  - `docs/DECISIONS.md` D20/D25 (how tracks I, N, P were frozen).
- The proved LP theorems:
  - planar: `KAM/Planetary/StrongAMD/PlanarSafety/*`, `SourceCarrier.lean`, `PlanarSafety/Source.lean`;
  - spatial: `KAM/Planetary/Spatial/SpatialSafety/*`, `SourceCarrier.lean`, `SpatialSafety/Source.lean`;
  - the elaborated texts in `docs/tracks/LP/freeze/odb-*.lean.txt`.

## Deliverables

1. **`docs/tracks/LP/FREEZE-PROPOSAL.md`, draft 7.** Rewrite it as the approval object. It contains:
   - an anchors table: LP0 (planar barrier), LP1 (the §3b text), LP2 (the §3d text), and the planar and spatial
     `τ = n − 1/2` corollaries, exponent `1/(2n+1)`;
   - for each anchor, its proposed name and namespace, frozen path, export, provider name, and the proved
     implementation theorem that will close it;
   - the complete frozen-definition set under (b), as §4b lists it;
   - the history and alternatives moved to an appendix or removed, so that the body has one text per item.

   **Corollaries.** "Zohar's headline form" means the corollary stated with the explicit exponent
   `μ^(-1/(2n+1))` rather than through `scaleExponent`. If you conclude that a corollary should **not** be its own
   anchor (for example because it is a one-line consequence of the anchor and freezing it adds no meaning), say so
   with the reason. Draft its text anyway.

   **LP0.** If its current text (§2) applies a total helper (`strongAMD`, the thresholds, …) to a physical state, it
   must be restated through the source carriers under (b), exactly as §3b did for LP1.
2. **Exact frozen file contents**, one file per public declaration. Store them as
   `docs/tracks/LP/freeze/draft7/<proposed path>.txt`, where the proposed path is `KAM/Frozen/…/X.lean`. Use the
   `.txt` suffix so no linter or build picks them up. Each file has the copyright header (copy the existing frozen
   files' header verbatim), `module`, `public import`s of frozen modules only, the module docstring, the
   `public section` (`@[expose] public noncomputable section` for definitions, as in the existing files), and exactly
   one public declaration. Theorems have body `by sorry` (`DRAFT_SORRY` until a provider seals them, in the
   repository's convention). Characterization theorems are separate theorem files, each paired in the inventory
   with its definition as one semantic unit.

   **Definition closure.** Enumerate the full closure of every anchor and split it into:
   - definitions **already frozen** (cite their path; no new file);
   - **new** definitions (new file). This includes the internal total helpers that a source definition unfolds to:
     they enter the frozen closure, certified only on their carriers, and §4b says so.
3. **Manifest entry drafts** for every new anchor and definition. Give them as a JSON block in draft 7 or as
   `docs/tracks/LP/freeze/draft7/manifest-entries.json`, never in `manifest/`. Each entry has:
   - `id` and `contract` with version `"1"`, in the existing style (for example `planetary.d59.<name>.v1`);
   - `kind`, `path`, `export`;
   - `source`: revision = `KAM-inp@<commit>`, `docs/tracks/LP/source/MAIN.md` with its sha256, and `AMENDMENTS.md`;
     range = the MAIN theorem/lemma and line numbers;
   - `split_policy`;
   - `definition_closure` as paths (leave the sha256 fields `"TBD at freeze"`);
   - the provider name;
   - `author_approval` left as `"PENDING (D59 approves rulings only)"`.
4. **Rebase plan.** For every new frozen definition, name the implementation module that defines it today and say how
   it is replaced at freeze time (delete the `def`, import the frozen file). The fully qualified name must stay the
   same, so that no LP theorem changes. Flag any name that would need renaming.
5. **Missing proofs.** If a draft-7 anchor (for example LP0 or a corollary under (b)) has no proved implementation
   theorem yet, prove it in a new implementation file. Use `KAM/Planetary/StrongAMD/PlanarSafety/SourceCorollary.lean`
   and/or `KAM/Planetary/Spatial/SpatialSafety/SourceCorollary.lean`, or another new file next to the existing
   `Source.lean`. Never add a premise.
6. **Transient elaboration and verification**, under `lp_lean.sh` only, with scratch files in `.drafts/freeze7/`
   (each under 1,500 lines; split if needed):
   - **(a) Text elaborates.** One or more scratch files that concatenate the exact declaration texts of all new
     draft-7 definitions and anchor statements, in dependency order. They import only already-frozen modules and
     Mathlib, never the LP implementation, so that the would-be frozen names do not clash. The anchors use `sorry`
     there, so expect "declaration uses sorry" warnings only.
   - **(b) Bodies equal.** For every new definition, an `rfl` check that the draft body equals the implementation
     definition the proofs use. For example, after importing the implementation,
     `example : @KAM.…strongAMD = fun … => <draft body> := rfl`, or an equivalent check. Record every check.
   - **(c) Verification.** A scratch file that imports the LP implementation, states **every draft-7 anchor
     verbatim** (the same text as its draft file, under a scratch name), and closes it by the proved theorems (`exact`
     or a one-line term). Then `#print axioms` for each. Record the exact output in
     `docs/tracks/LP/freeze/verification-draft-7.txt`, with the command lines.

## Owned files

- Everything under `docs/tracks/LP/freeze/draft7/`.
- `docs/tracks/LP/FREEZE-PROPOSAL.md`.
- `docs/tracks/LP/freeze/verification-draft-7.txt`.
- `.drafts/freeze7/`.
- The new `SourceCorollary.lean` implementation files, if needed.

Never create or edit anything under `KAM/Frozen/` or `manifest/`. Never edit other implementation files.

## Checks and stop condition

- Every scratch file elaborates under `lp_lean.sh`. The only warnings allowed are "declaration uses sorry" on draft
  anchors in (a).
- Every anchor verifies in (c), with axioms exactly `[propext, Classical.choice, Quot.sound]`.
- Any new implementation file: `lp_build.sh`, `lp_lint.sh` exit 0, `main_shortname_check.py` exit 0.
- If a ruling cannot be implemented as stated, or an anchor cannot be proved without a new premise, STOP and report
  exactly. Never add a premise, and never substitute a weaker statement.

## Handoff

`docs/tracks/LP/audits/LP-FREEZE7-handoff.md` (committed). It lists the anchors and definitions with their paths, the
verification output, every place where you chose between conventions (for the audit to check), and every
uncertainty. Also write `.drafts/handoff-LP-FREEZE7.md`, then `touch .drafts/READY-LP-FREEZE7`.

# FREEZE-PREP handoff (T2-CONF): staging of the D76 freeze-and-seal pass

Worker g2-n6, 6 November 2026. Status: **staged and dry-run clean.** Everything is under `.drafts/g2/freeze/`.
Nothing was written under `KAM/Frozen/`, `manifest/`, `KAM/Provider/`, `scripts/build_roots.json`,
`lakefile.lean` or any root. The dry run of the full pass (in a throwaway copy) gives `ROOTS CHECK OK` and
`FROZEN-ANCHOR GUARD OK`. The ABI hashes are the documented placeholder until the KAMSJSU build;
`sjsu_secular_confinement_proof` does not exist yet, and nothing in the staging depends on it beyond the
provider's import.

## Files (`.drafts/g2/freeze/`)

| path | content |
|---|---|
| `stage.py` | the generator. It verifies the texts and writes `tree/`, `patches/`, `manifest-entries.json`, `manifest-changes-rows.md` and `check/ExprEq.lean` (idempotent; `apply.sh` reruns it) |
| `tree/KAM/Frozen/EffectiveStability/SJSU/SJSUTerm.lean`, `SJSU18O2Part0..5.lean`, `SJSU18O2Terms.lean`, `SJSU18O2.lean` | 9 whole-file definition anchors (30 / 1354×5, 1351 / 34 / 35 lines) |
| `tree/KAM/Frozen/EffectiveStability/SJSU/SecularConfinement.lean` | the theorem anchor in the HH format (prefix/proof/suffix markers). The body is `by exact KAM.Provider.EffectiveStability.sjsu_secular_confinement z₀ hz₀` (77 bytes, 1 line ≤ the 3-line/240-byte seal limit) |
| `tree/KAM/Provider/EffectiveStability/SJSUSecularConfinement.lean` | the provider. It states the v2 statement verbatim under `open KAM.EffectiveStability`, proved by `KAM.EffectiveStability.SJSU.sjsu_secular_confinement_proof z₀ hz₀`, and imports `KAM.EffectiveStability.SJSU.Confinement.Proof` (module and name confirmed by g2-n5b and kam-g2) |
| `tree/KAM/EffectiveStability/SJSU/Model/*.lean` (9) | the dev copies as facades (`public import` of the frozen module) |
| `patches/build_roots-app.json` | application `KAMSJSU` (prefixes `KAM.EffectiveStability.SJSU`, `KAM.Frozen.EffectiveStability.SJSU`, `KAM.Provider.EffectiveStability.SJSUSecularConfinement`); `application_only` += `KAM.EffectiveStability.SJSU` |
| `patches/lakefile-block.lean` | `lean_lib «KAMSJSU»` (`gen_root_imports.py` writes only the generated block, not library declarations) |
| `patches/lint-width-allow.txt` | 17 exact entries (path TAB sha256-of-line TAB line) for the overlong lines of the approved text, in the anchors and the provider |
| `manifest-entries.json` | the 10 entries `effectiveStability.d76.{sjsuTerm, sjsu18O2Part0..5, sjsu18O2Terms, sjsu18O2, sjsu_secular_confinement}.v1` |
| `manifest-changes-rows.md` | 10 rows for `docs/MANIFEST-CHANGES.md` |
| `apply_merge.py`, `apply.sh` | the pass (`--dry-run`: same, in `.drafts/g2/freeze/dry/`) |
| `fill_abi.py` | fills the 10 `abi_sha256` from `abi_hashes.py --lib KAMSJSU` output (refuses partial fills) |
| `check/ExprEq.lean` | the pre-swap Expr check (scratch, non-module) |
| `gen/v2/` | `gen_t2conf.py --out` output (texts, `Check.lean`) used for the byte comparisons |
| `RUNBOOK.md` | the ordered commands after apply, with expected outputs |

## Manifest entries

- **Common fields.** Approval: Scott Armstrong, 2026-11-06, D76 (relayed by kam-38), version 1. Source:
  `KAM-inp@793d59797 docs/explorations/sjsu-g2-t2conf-proposal.md (draft v2; D76 recorded at 1043ebed2)`.
  Each anchor is its own `NOT_SPLIT` source group (the guard requires one anchor per `NOT_SPLIT` group),
  with ruling `docs/explorations/sjsu-g2-decisions.md D76`.
- **Definitions.** `full_file_sha256` of the staged file. The `definition_closure` is the frozen definition
  anchors reachable through imports, the provider excluded, as in the D73 entry: parts → `SJSUTerm`;
  `Terms` → 7; `sjsu18O2` → 8.
- **Theorem.** Closure 13: the 9 SJSU definitions plus `HamiltonianVectorField`, `IsDiophantine`,
  `SymplecticForm`, `OscillatorAction`. `prefix_sha256 = 0a5f720c…855c` and
  `suffix_sha256 = 1f2d3361…9caa8` are cut exactly as `check_theorem_region` cuts them (the suffix equals
  HH's: same suffix text). Implementation:
  `KAM.Provider.EffectiveStability.SJSUSecularConfinement` / `…sjsu_secular_confinement`; empty
  `draft_allowlist`; state SEALED.
- **ABI.** `abi_sha256` is `0` × 64 until RUNBOOK step 5.

## Checks run and their outputs

1. **Byte identity** (`python3 .drafts/g2/freeze/stage.py`):
   `OK: 6 parts match the v2 sha256 table; 9 dev declaration texts identical to the generator; statement,
   docstring, sjsuTerm, sjsu18O2Terms, sjsu18O2 verbatim in the v2 proposal`.
   - The six part texts hash to the v2 table (sha256 of the declaration text without a trailing newline,
     which is what the table hashes).
   - Every declaration text written into the anchors is the generator's text verbatim.
   - The `SJSU/Model` dev declarations are byte-identical to them.
   - The statement, its docstring, `sjsuTerm`, `sjsu18O2Terms` and `sjsu18O2` occur verbatim in the v2
     proposal file.
   - `gen_t2conf.py --roundtrip`: `roundtrip OK: 7941 rows byte-identical to complex_form.terms`.
2. **v2 typecheck.** `.drafts/g2/g2lake env lean .drafts/g2/freeze/gen/v2/Check.lean`: the definitions, the
   statement as a `Prop` and `terms_length = 7941` (`decide +kernel`) elaborate. The only output is the
   unused-variable linter note on `hz₀` in the statement-as-`Prop` example; 10 s.
3. **Pre-swap Expr check.** `.drafts/g2/g2lake env lean .drafts/g2/freeze/check/ExprEq.lean` gives
   `'eq_sjsu18O2' depends on axioms: [propext, Classical.choice, Quot.sound]`, no error, 17 s. The 9 frozen
   declaration texts are elaborated in the scratch namespace `KAM.FreezeCheck` and compared:
   - `sjsuTerm` by `rfl`;
   - each part equal to the dev constant by `decide +kernel` (list equality);
   - `sjsu18O2Terms` and `sjsu18O2` by rewriting with the part equalities.

   Two design signals came up, both fixed without options. Elaborator `rfl` on a 1,324-row list hits the
   recursion depth; `DecidableEq` synthesis gives up on the 7-tuple row type, so it is built one product
   level at a time.
4. **Dry run.** `sh .drafts/g2/freeze/apply.sh --dry-run` (2 min 10 s) printed:
   `applied: 20 files, 10 manifest entries, KAMSJSU in build_roots and lakefile, 10 MANIFEST-CHANGES rows, 17 lint allowances`,
   `ROOTS CHECK OK`, `FROZEN-ANCHOR GUARD OK`.
   The diffs against the live files are append-only:
   - `manifest/frozen-anchors.json`: entries appended, the existing formatting reproduced byte for byte
     (`indent=1`, `ensure_ascii=False`);
   - `scripts/build_roots.json`: a textual insert keeps the hand formatting;
   - `lakefile.lean`: the block before the template comment.

   Width/size scan of the 24 new or changed `.lean` files in the dry tree (with the allowances): 0
   violations, all ≤ 1500 lines. The dry copy was removed afterwards.

## Uncertainties and notes for kam-g2

- **`KAMSJSU` cannot build until `Proof.lean` exists.** The generated root `KAMSJSU.lean` imports every
  KAMSJSU module, the provider included, so apply only after `Proof.lean` exists (RUNBOOK step 0), or expect
  the root build to fail until then. Targeted builds of the frozen definitions work before that.
- **Library move.** With the `KAMSJSU` prefix `KAM.EffectiveStability.SJSU`, every SJSU module (N5a,
  N5b, N5c, N6, N7 ledger) moves to the opt-in library. A plain `lake build` no longer builds them.
  `gen_root_imports.py --check` passed, so no core module imports an SJSU module.
- **Provider kept verbatim.** It keeps the statement text verbatim (overlong lines allow-listed) rather
  than reflowed. kam-g2 allowed a reflow and g2-n5b asked for byte identity; the Expr is the same either
  way.
- **Wrappers.** The frozen data modules keep the dev copies' `@[expose] public section`, computable;
  `sjsu18O2` and the theorem use `noncomputable section`, as the dev copy and the HH anchor do. The module
  docstrings are new (D76 frozen-file note); only the declaration texts are approved bytes.
- **Not typechecked in module form.** The staged frozen modules themselves were not typechecked as
  modules, because the brief forbids writing `KAM/Frozen` in the tree. Their declaration texts were
  typechecked in `Check.lean` and `ExprEq.lean`, and RUNBOOK step 3 builds them.
- **abi_hashes runs lake directly.** `abi_hashes.py` and `kernel_replay.sh` call lake outside `g2lake`;
  the RUNBOOK wraps them in `flock .drafts/g2/lake.lock`.

## Suspected defects in the approved text

None. The approved part docstrings (110 columns) and statement lines (up to 196 columns) exceed the lint
width; they are allow-listed by exact line hash (MagHamC.lean precedent), not changed.

## Hard rules

No `set_option` of any kind, no heartbeat or recursion override, no `sorry` in any staged file. All staged
Lean files are ≤ 1354 lines.

READY g2-freeze-prep

## Update (17:46 UTC): re-staged against HEAD 498a8ccf6

At HEAD, `scripts/build_roots.json` already has the `KAMSJSU` entry (prefix `KAM.EffectiveStability.SJSU`
only, and the prefix in `application_only`). `lakefile.lean` already declares `lean_lib «KAMSJSU»`, and
`scripts/lint-width-allow.txt` has 6 entries for `SJSU/Model/SJSU18O2Part*.lean`. `apply_merge.py` now
handles that state:
- it adds the missing prefixes `KAM.Frozen.EffectiveStability.SJSU` and
  `KAM.Provider.EffectiveStability.SJSUSecularConfinement` to the existing entry (textual edit);
- it leaves an existing lakefile block untouched;
- it drops allow-list rows for files the mirror tree replaces (the 6 Model rows; those files become
  facades) before appending the 17 frozen/provider rows.

Re-run of `sh .drafts/g2/freeze/apply.sh --dry-run`:
`applied: 20 files, 10 manifest entries, KAMSJSU prefixes in build_roots; lakefile.lean already declares
lean_lib KAMSJSU (unchanged); 10 MANIFEST-CHANGES rows, 17 lint allowances added, 6 stale allowances
dropped`, `ROOTS CHECK OK`, `FROZEN-ANCHOR GUARD OK`.
- The diffs are minimal: 2 prefix lines in `build_roots.json`; the lakefile unchanged; 6 allow-list rows
  replaced by 17.
- `stage.py` re-verified the texts against the current dev copies (still byte-identical).
- The width scan of the 24 new or changed files in the dry tree gives 0 violations.
- `RUNBOOK.md` is updated with the new expected output.

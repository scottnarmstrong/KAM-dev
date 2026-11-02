# V2-PACKED-APPLY handoff: the packed route made application-agnostic, on paper and in a thin driver

Orchestrator's request (2026-11-02, ~02:30 UTC; worker kamx-pk-cons): write `docs/campaign/design/V2-PACKED-APPLY.md`
(what an application must provide) and a generic entry point `scripts/packed/apply_packed.py` that reads a
certificate dump and a small app config and drives the existing emitters, with no Lean changes. Test it by
regenerating LG00 T′'s packed sources byte for byte. For the magnetic pilot and later lunar certificates.
Branch `v2-packed-apply`, from `origin/main` `cd23fc09e` (local, not pushed).

## Result

- **Byte for byte, both layouts, both tori.**
  - The copy layout's 286 files per torus (the certificate copy, the port, the packed modules) equal the integration
    package's, `v2-packed-gen-int/.lake/lg00p`: the package that proved T′ and T″.
  - The own layout's 115 per torus (`LG00.<T>.PK`) equal the LG00 release package's.
  - The module lists and `gen_packed`'s records are equal too. Receipts:
    `docs/campaign/studies/V2-PACKED-APPLY/README.md`.
- **No Lean and no emitter changed.** One commit of kamx-pk-gen is cherry-picked: `59ea55407` (`gen_packed.py`
  `--pk-root`/`--pk-format`, 5 lines, the release's emitter; on `v2-packed-gen` and `lg00-release`, not on `main`).
  The `own` layout needs it.
- **The design note** (`V2-PACKED-APPLY.md`):
  - the route, and who provides what (§1);
  - the certificate dump: the LG00-format tree, file by file and definition by definition (§2);
  - the config (§3);
  - the jet literal, the jet bridge and the chains, with their cut options and costs (§4);
  - the chart, chain-free proofs and statement: modules, lemmas and the statement's shape (§5);
  - **what the emitters still fix to LG00** (§6), the gap list for the pilot;
  - memory and cost caps (§7); eight lessons (§8); the test (§9).
- **For the magnetic pilot, the finding is that a thin layer is not enough yet** (§6). The emitters hard-code
  LG00's names (about 230 occurrences in `gen_packed.py`), the namespace, the box half-widths 25/48, the sharp-site
  engine and LG00's statement template. The pilot differs in all of these:
  - its names are `mag*`;
  - its route uses classical sites (the core has `routeARefinedPackedJ`, but the jet assembly emits only the sharp
    form);
  - its headline is a barrier theorem.
  - The driver fails closed on all of this today (`mag_pilot.example.json`, `fail_closed.txt` case 1).
  - The next step is a parameterized `gen_packed`: a names table in `Emit`, box options, a classical/sharp switch,
    and an assembly ending at `Asm.CheckJ`. It should be gated by this same byte-identity test on LG00.
  - The pilot also has no Lean certificate tree yet: its data is sofx JSON, and the emitters read Lean (§2).

## Files

- `scripts/packed/apply_packed.py` (new).
  - Config checks: names, layout, steps.
  - Dump checks: every file and definition the reader reads, and the namespace.
  - Steps: `extract`, `mirror`, `cert`, `port`, `chains`, `packed`, each under `py_capped.sh`.
  - The SHA-256 manifest `apply_<T>.json`, and `--check=REF`.
  - Guards: never writes outside `--out`; refuses an `--out` it did not create; `extract`/`mirror` never overwrite.
- `scripts/packed/apply/lg00_{tp,tpp}_{copy,own}.json`: LG00's configs.
- `scripts/packed/apply/mag_pilot.example.json`: the pilot's shape. It fails closed today, by design.
- `scripts/packed/gen_packed.py`: the cherry-pick of `59ea55407`.
- `docs/campaign/design/V2-PACKED-APPLY.md`, this handoff, and `docs/campaign/studies/V2-PACKED-APPLY/` (receipts).

## Checks

- **The byte-identity runs and the 8 fail-closed checks** (receipts README). Each step is one Python process
  under 8 GB. T′'s three steps: 78 s wall, 1.29 GB.
- `python3 -I scripts/gen_root_imports.py --check`: exit 0. No Lean file is added or changed.
- **Lint** (`scripts/lint_sources.sh`): every step before the ABI step passes: `check_lean_modules: PASS (4456 Lean
  files)`, 25 anchor tests OK, `FROZEN-ANCHOR GUARD OK`.
  - The ABI step (elaborated statement hashes) fails for an environmental reason: this worktree has no build
    snapshot (`unknown module prefix 'KAM'`). The branch adds no anchor and no Lean.
  - That step ran Lake, which fetched the dependency sources into this worktree's `.lake/packages` (198 MB, git
    checkouts only; nothing was compiled). Do not build in this worktree without first seeding its `.lake` from
    `main`'s snapshot (`cp -al`).
- **No Lean was built, and none needed building.** There is no Lean change, so there are no axioms to print.

## Uncertainties and deviations

- **The chains are not tested byte for byte** (`chains`, `extract`, `mirror` are wired and dry-run only).
  - The measured T′ chains came from an older `jet_prod_gen.py`, patched afterwards (V2-PACKED-PROD).
  - kamx-packed is regenerating T″'s chains as groups now (`v2-packed-group`), so there is no fixed reference.
- **The cherry-pick.** `59ea55407` is kamx-pk-gen's commit, applied here as the same patch, so landing both branches
  should not conflict.
- **No errata.**

## Resume after reboot (lemma.farm reboots 2026-11-02 05:00 UTC)

- Everything is committed on `v2-packed-apply` (worktree `/home/scott/KAM-dev-worktrees/v2-packed-apply`, under
  `/home`). The outputs are in `~/kam-data/v2-packed-apply/` and are regenerable. Nothing runs.
- To rerun the test: the commands at the end of the receipts README (Python only, about 80 s per torus and layout).

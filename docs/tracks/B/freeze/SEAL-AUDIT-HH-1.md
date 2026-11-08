# Seal audit HH-1: `henonHeiles_confinement` (D73), refute-first

Independent auditor. I wrote none of the audited files. Brief: `/root/code/KAM-inp-b1/.drafts/B/brief-B-SEAL-HH.md`.
Procedure: the `lean-statement-audit` skill. Worktree `/root/code/KAM-inp-b3cert`, branch `inp-b3cert`.

**Audited HEAD:** `de3c14ef0`. The relevant commits in `inp...HEAD` are:
- `278634c8f`: B3-CERT implementation.
- `400a4223b`: the anchor, the provider, the `*_proof` rename and the application library `KAMHenonHeiles`.
- `5c304d0c1`: the manifest entry and the MANIFEST-CHANGES rows.
- `de3c14ef0`: the graph manifest pin.

No Lean file changed after `400a4223b` (`git diff 400a4223b HEAD --stat`: manifest, MANIFEST-CHANGES and graph files only).
Every Lean, guard and ABI check below ran at `de3c14ef0`. The byte-identity and structure checks ran at `400a4223b`;
the Lean bytes are identical at `de3c14ef0`.

## Pinned identity

| Field | Value |
|---|---|
| Manifest id | `effectiveStability.d73.henonHeiles_confinement.v1` (`manifest/frozen-anchors.json:24537`) |
| Kind / state | theorem / SEALED |
| Path / export | `KAM/Frozen/EffectiveStability/HenonHeilesConfinement.lean` / `KAM.EffectiveStability.henonHeiles_confinement` |
| Implementation | `KAM.Provider.EffectiveStability.HenonHeilesConfinement` / `KAM.Provider.EffectiveStability.henonHeiles_confinement` |
| Approval | Scott Armstrong, 2026-11-03, D73, version 1 |
| Split | NOT_SPLIT, ruling D73 |
| Source | program-b-plan §4 "A first instance with literal acceptance criteria"; CL20 Appendix B |

D73 is in `main:docs/DECISIONS.md:630-636`, which quotes Scott: "i approve the Hénon–Heiles theorem text". It approves
the theorem "exactly as in `.drafts/B/brief-B3-CERT.md` step 4" and says it is to be "frozen and sealed in one pass once
it is proved", in the application library `KAMHenonHeiles` (D51).

## 1. Byte identity — PASS

Method: awk/sed slicing to files, then `cmp` and `sha256sum`.
- **Approved text.** The ```` ```lean ```` block of `brief-B3-CERT.md` step 4 (`:34-56`), 1289 bytes.
- **Anchor statement.** From `theorem henonHeiles_confinement` up to the line ending ` :=`, with the trailing ` :=`
  stripped (`HenonHeilesConfinement.lean:30-50`).
- **Proposal.** The ```` ```lean ```` block of `FREEZE-PROPOSAL-HH.md` (docstring + statement).
- **Anchor docstring + statement.** From `/-- **Hénon` to the same end (`:25-50`).

```
approved.txt      06e9a2aa27206cbf…  (1289 B)
anchor_stmt.txt   06e9a2aa27206cbf…   cmp approved = identical
prov_stmt.txt     06e9a2aa27206cbf…   cmp approved = identical   (provider statement)
proposal_stmt.txt 06e9a2aa27206cbf…   cmp approved = identical   (proposal statement part)
proposal.txt      11cbf9835430826b…
anchor_doc_stmt   11cbf9835430826b…   cmp proposal = identical   (docstring + statement)
```

The elaborated types are also syntactically equal (`Expr ==`) to a theorem elaborated from the approved text (§3).

## 2. Anchor structure — PASS

`KAM/Frozen/EffectiveStability/HenonHeilesConfinement.lean` (57 lines) contains, in order:
- the copyright header `:1-5`;
- `PREFIX_BEGIN` `:6`, then `module` `:7`;
- the imports `:9-11`:
  - `public import KAM.Frozen.Defs.HamiltonianVectorField`;
  - `public import KAM.Frozen.Planetary.Defs.OscillatorAction` (frozen definitions only);
  - a private `import KAM.Provider.EffectiveStability.HenonHeilesConfinement`;
- the module docstring, `@[expose] public noncomputable section` and `namespace KAM.EffectiveStability`.

Each of the five markers occurs exactly once, in order (counted by script). The seal body, sliced as the guard slices it,
is

```
'  by exact KAM.Provider.EffectiveStability.henonHeiles_confinement z₀ hz₀\n'   (1 line, 78 bytes)
```

That is within `seal_limits` (3 lines, 240 bytes) and applies both explicit binders in order. The prefix and suffix
sha256 that I recomputed equal the manifest values (§6).

## 3. Provider — PASS

`KAM/Provider/EffectiveStability/HenonHeilesConfinement.lean:23-42` restates the type, byte-identical (§1). Its proof is
`KAM.EffectiveStability.HenonHeiles.henonHeiles_confinement_proof z₀ hz₀`, and its only import is
`KAM.EffectiveStability.HenonHeiles.Confinement`.

The implementation diff `278634c8f..HEAD` of `Confinement.lean` contains only the docstring rewording and the rename
`henonHeiles_confinement` → `henonHeiles_confinement_proof`. (Its statement is line-wrapped differently at `:39-40`; the
elaborated type is identical, see below.)

### Transient check

I ran a scratch file `SealAuditHH.lean` with `lake env lean` under the D53 wrapper (rc 0, 3.8 s, max RSS 3.2 GB). It is
not in the repository. It declares `SealAudit.chk_henonHeiles_confinement` with the approved text, sliced by script, and
the body `KAM.EffectiveStability.henonHeiles_confinement z₀ hz₀`. It then compares `ConstantInfo.type`:

```
KAM.EffectiveStability.henonHeiles_confinement vs KAM.Provider.EffectiveStability.henonHeiles_confinement: type == true; levelParams [] / []
KAM.EffectiveStability.henonHeiles_confinement vs SealAudit.chk_henonHeiles_confinement: type == true; levelParams [] / []
KAM.EffectiveStability.henonHeiles_confinement vs KAM.EffectiveStability.HenonHeiles.henonHeiles_confinement_proof: type == true; levelParams [] / []
```

### Quarantine

`grep -rln "import KAM.Provider.EffectiveStability.HenonHeilesConfinement|import KAM.Frozen.EffectiveStability.HenonHeilesConfinement"`
over all `.lean` files except `.lake` finds three importers:
- the anchor;
- `KAMHenonHeiles/Provider.lean`;
- `KAMHenonHeiles/Frozen.lean`.

The last two are generated root parts, as `KAM/Root/Provider.lean` is for the sealed D72 providers. Nothing else
imports them.

## 4. Meaning — PASS (refute-first; no weaker, vacuous or time-reversed reading found)

### (a) The model

The frozen definitions involved are:
- `KAM.hamiltonianVectorField H z = (fun i => fderiv ℝ H z (0, e_i), fun i => -fderiv ℝ H z (e_i, 0))`
  (`KAM/Frozen/Defs/HamiltonianVectorField.lean`).
  - With `z = (q, p) = (z.1, z.2)`, this gives `q̇_i = ∂H/∂p_i` and `ṗ_i = -∂H/∂q_i`: the standard Hamilton equations,
    **not** the time-reversed system.
  - The conclusion is also symmetric in `t`: a symmetric interval, `|t| ≤ 10¹⁰`, and uniqueness on any interval
    through 0.
- `KAM.Planetary.oscillatorAction p q j = (p j ^ 2 + q j ^ 2) / 2`, called as `oscillatorAction z.2 z.1`.
  - This gives `I_j = (q_j² + p_j²)/2`, as in plan §4 (HH).

The displayed function is `(q₁² + p₁²)/2 − (√2/2)·(q₂² + p₂²)/2 + q₁² q₂ − q₂³/3`, with `q₁ = w.1 0`, `q₂ = w.1 1`,
`p₁ = w.2 0`, `p₂ = w.2 1`. That is literally `I₁ − (√2/2) I₂ + q₁² q₂ − q₂³/3`, the plan's (HH)
(`docs/explorations/program-b-plan.md:533-537`).

The statement uses only Mathlib reals and these two sealed frozen definitions: no project polynomial type, no
`cartEval`, no `QSqrt2`. Its meaning therefore cannot be shifted by any implementation definition.

### (b) The conclusion against plan §4 (`program-b-plan.md:539-543`)

| Plan §4 | Anchor |
|---|---|
| Hypothesis `I_j(z₀) ≤ (1/12500)²` | `hz₀`, the same |
| Unique solution through `|t| ≤ 10¹⁰` | `∃ T₁ > 10¹⁰` and a genuine `HasDerivAt` solution on all of `(-T₁, T₁)` with `z 0 = z₀`, unique among all solutions `y` on any order-connected `I ∋ 0` (equal on `I ∩ (-T₁, T₁)`) |
| `I_j(z(t)) < 101/10¹⁰` | the same |
| `|I_j(z(t)) − I_j(z₀)| ≤ 12/10¹⁰` | the same, for all `|t| ≤ 10¹⁰` and both `j` |

Quantifier order is `∃ T₁, ∃ z` before `∀ I y` and `∀ t`. The conclusion is at least as strong as the plan's target.

Refutation attempts:
- **Vacuous premise.** The premise holds at the equilibrium `z₀ = 0`. I proved this in the transient check
  (`example … oscillatorAction 0.2 0.1 j ≤ (1/12500)^2`, by `simp`).
- **`fderiv` junk.** H is a real polynomial, hence differentiable everywhere, so `fderiv` is the true derivative.
- **Weak uniqueness.** The uniqueness hypothesis asks `y` to have `HasDerivAt` (two-sided) at every point of `I`,
  including endpoints. That is the same shape as the sealed D72 anchors and the frozen checker theorems; this is not a
  loss.

### (c) The certificate chain

**`hhCert_check`** (`Check.lean:63`) has the type `checkOscChain hhCert = true`; the transient `#check` with the
explicit expected type succeeded. Its proof unfolds `checkOscChain`, rewrites with `hhCert_chain` and `hhCert_bound`,
then closes with `decide +kernel`. It has no hypotheses.

**`hhCert_chain`** follows from:
- `hhSteps_ok` (`decide +kernel`);
- the shard theorems `hhLie{1,2,3}_check` and `hhFin_check`.

Each shard theorem is assembled from:
- chunk theorems proved by `decide +kernel`;
- `chunk_step` and `cartEqCheck_of_merge` (`ChunkMerge.lean:35-52`), which are **proved** lemmas, by
  `List.take_append_drop` and `foldr_append`, with no hypotheses beyond their chunk data.

**`hhCert_bound`** is built the same way, from `supBound_chunk`, `width_chunk`, `cartBracket_width` and the
`BracketChunk` lemmas, all proved.

None of the following occurs under `KAM/EffectiveStability/HenonHeiles` or in the anchor or provider: `axiom`, `sorry`,
`admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `ofReduceBool`, `set_option` (grep: no
match). The axiom sets in §7 exclude `Lean.ofReduceBool` and `sorryAx`.

**`hhH_eval`** (`Eval.lean:23`) proves `cartEval hhH w = <the displayed function>` through `algebraMap_qsqrt2_real`.

The `Algebra QSqrt2 ℝ` instance:
- A repository-wide grep finds exactly one instance, the global `instAlgebraQSqrt2Real` at
  `KAM/EffectiveStability/Poly/Coeff.lean:214`; the only other hit is a docstring.
- The transient `#synth Algebra QSqrt2 ℝ` resolves to it.
- Its `algebraMap` is `a + b·√2` (`Coeff.lean:224`, by `rfl`).

**`henonHeiles_confinement_proof`** (`Confinement.lean:33-124`) applies `oscillatorChain_physical_disc`
(`OscillatorChainPhysicalDisc.lean:52`, a core theorem, audit B3-CHAINK-1).
- Every premise of that theorem is discharged inside the proof:
  - `hH`, `hN`, `hP`, `hok` and `hdom` come from the unpacked `hhCert_check`, through the soundness lemmas
    `cartFitsB_sound`, `oscChainOKB_sound` and `oscDomOKB_sound`;
  - the numeric margins are closed by `norm_num` on literals, with `σ = 1/12500`, `a' = (1/12500)²`,
    `s = 5657/50000000` and `d = 209/10¹³`;
  - `OscPhysDom` is closed by `simp`/`norm_num`.
- The displayed H replaces `cartEval hhCert.H` by `funext hhH_eval`.
- The two outer bounds are then derived:
  - the drift bound from `2d + ηT = 4.18·10⁻¹¹ + 10⁻⁹ ≤ 12·10⁻¹⁰`;
  - the outer bound from `a + ηT + d < 101·10⁻¹⁰`.
- The theorem has no hypotheses other than `z₀` and `hz₀`, and nothing conclusion-shaped is assumed.

### Five-bin table

| Binder | Bin | Source |
|---|---|---|
| `z₀ : (Fin 2 → ℝ) × (Fin 2 → ℝ)` | TYPING | phase point `(q, p)` of the 2-dof model |
| `hz₀ : ∀ j, I_j(z₀) ≤ (1/12500)²` | SOURCE | plan §4 `I_j(z₀) ≤ (1/12500)²`, `j = 1, 2` |

Counts: SOURCE 1, STANDING 0, TYPING 1, RULED 0, **EXCESS 0**. There are no implicit or instance binders.

## 5. Library placement — PASS

- **`scripts/build_roots.json`.** The application `KAMHenonHeiles` has the prefixes `KAM.EffectiveStability.HenonHeiles`,
  `KAM.Frozen.EffectiveStability.HenonHeilesConfinement` and `KAM.Provider.EffectiveStability.HenonHeilesConfinement`.
  `KAM.EffectiveStability.HenonHeiles` is also added to `application_only`.
- **Root parts.** All 65 HenonHeiles modules are imported by `KAMHenonHeiles/EffectiveStability.lean` (checked per file,
  none missing). The anchor is in `KAMHenonHeiles/Frozen.lean` and the provider in `KAMHenonHeiles/Provider.lean`.
- **Generator check.** `python3 scripts/gen_root_imports.py --check` gives rc 0. That check enforces that core modules
  import only core modules.
- **Core is untouched.** `grep HenonHeiles KAM.lean KAM/Root/*.lean` gives no match. No module outside the application
  imports a HenonHeiles module (grep).
- **`lakefile.lean`.** `lean_lib «KAMHenonHeiles»` has `roots := #[\`KAMHenonHeiles]`. `quarantinedModules` contains no
  HH entry, so the core `lake build` (root `KAM`) does not include these modules.
- **Line caps.** The largest HH file has 1109 lines. The anchor has 57, the provider 44 and `Confinement` 126.

## 6. Manifest — PASS

The entry is at `manifest/frozen-anchors.json:24536-24590` (commit `5c304d0c1`). It has:
- kind `theorem`, state `SEALED`;
- approval D73, version 1;
- the path, export and implementation from the identity table;
- `contract` id and version 1;
- NOT_SPLIT with D73;
- an empty `draft_allowlist`.

Field checks:

| Field | Check |
|---|---|
| `prefix_sha256` = `40c40e75…91ab` | Recomputed: bytes up to and including the `PROOF_BEGIN` line. Equal. |
| `suffix_sha256` = `1f2d3361…caa8` | Recomputed: bytes from the `PROOF_END` line on. Equal. |
| `definition_closure` | HamiltonianVectorField, IsDiophantine, SymplecticForm, OscillatorAction. `sha256sum` equal to all four. This is the import closure: `OscillatorAction.lean:18-20` imports the other three. |
| `abi_sha256` = `ecd0cc37…95ea` | Checked by `abi_hashes.py --lib`, below. |

Script runs:
- `python3 scripts/check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json` → `FROZEN-ANCHOR GUARD OK`,
  rc 0.
- `python3 scripts/abi_hashes.py . manifest/frozen-anchors.json --check --lib KAMHenonHeiles` (D53 wrapper) →
  `ABI HASHES OK (1 frozen declarations of KAMHenonHeiles; …)`, rc 0.
- `scripts/lint_sources.sh` (run at `400a4223b`; no Lean change since) → `check_lean_modules: PASS (4653 Lean files)`,
  25 tests OK, guard OK, `ABI HASHES OK (316 … KAM)`. There is no out-of-date-root line.

Related records:
- `docs/MANIFEST-CHANGES.md` has a D73 row (and late D72 rows).
- The graph `docs/graph/B/DEPGRAPH.md` header `FROZEN_MANIFEST` sha256 `fd93ee6b…b45a` equals `sha256sum` of the
  manifest at HEAD.

## 7. Axioms and kernel replay — PASS

`#print axioms` (transient check at `de3c14ef0`):

```
'KAM.EffectiveStability.henonHeiles_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.EffectiveStability.henonHeiles_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.HenonHeiles.henonHeiles_confinement_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.HenonHeiles.hhCert_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.HenonHeiles.hhH_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` and no `Lean.ofReduceBool`.

Kernel replay used `leanchecker --verbose` with the project's `LEAN_PATH`, under the D53 wrapper (4G scope,
`LEAN_NUM_THREADS=1`, nice 10), one process at a time:

| Modules | Result | Wall | User CPU | Max RSS |
|---|---|---|---|---|
| anchor, provider, `HenonHeiles.Confinement`, `.Check`, `.Eval` | 5 × `replaying`, rc 0 | 52.4 s | 16.4 s (sys 35.8 s) | 4.28 GB |
| `HenonHeiles.Shard.Lie2` | rc 0 | 27.0 s | 19.6 s | 3.63 GB |
| `HenonHeiles.Shard.Bound2P1` | rc 0 | 50.9 s | 42.7 s | 3.80 GB |

The other shard modules are not replayed here (the brief allows at most two); their kernel checks ran at elaboration
by `decide +kernel`.

## Notes (non-blocking)

- **N1 (guard gap).** At `400a4223b` the frozen file `KAM/Frozen/EffectiveStability/HenonHeilesConfinement.lean` had no
  manifest owner, yet `check_frozen_anchors.py` reported `FROZEN-ANCHOR GUARD OK`. The guard therefore does not enforce
  the skill's rule "every Lean file in the frozen tree has exactly one manifest owner". It is satisfied at HEAD. I
  recommend adding an ownership check to the guard.
- **N2 (provenance label).** `source.revision` reads `KAM-inp@400a4223b`. That commit is currently only on
  `inp-b3cert`; it becomes reachable from `inp` at landing. It is the right commit; only the branch label is premature.
- **N3 (replay RSS).** The `/usr/bin/time` max RSS of the 5-module replay (4.28 GB) is above the nominal 4G scope. The
  process was not killed, presumably because shared memory-mapped `.olean` pages are counted by `time` but not charged
  in full to the cgroup. Memory use was within the box's limits.
- **N4.** The anchor imports no `SymplecticForm`, but the closure lists it transitively (through `OscillatorAction`).
  That is consistent with the D72 practice.

Suspected errata in pinned sources: none. Deviations introduced by the audited commits: none. The anchor is exactly
the D73-approved text, and the docstring is approved freeze-time commentary.

## Verdict

```
DECLARATION_FIDELITY: PASS (byte-identical; Expr == to the approved text)
BINDERS: SOURCE 1, TYPING 1, EXCESS 0
SEAL (proof-body-only, provider assembly, limits): PASS
MEANING (model, orientation, conclusion vs plan §4, certificate chain): PASS
LIBRARY PLACEMENT / QUARANTINE: PASS
MANIFEST: PASS (guard OK, ABI OK --lib KAMHenonHeiles, hashes recomputed)
AXIOMS: propext, Classical.choice, Quot.sound; KERNEL REPLAY: PASS (5 modules + Shard.Lie2 + Shard.Bound2P1)
PROOF_STATUS: PROVED
```

**PASS WITH NOTES — seal-ready.** Notes N1–N4 are non-blocking. N1 is a guard improvement and is not a defect of
this seal.

# Seal audit 1: B1-T / B1-E (D72), refute-first

Independent auditor (not an author of any audited file). Brief: `/root/code/KAM-inp-b1/.drafts/B/brief-B-SEAL.md`;
procedure: `lean-statement-audit` skill. Worktree `/root/code/KAM-inp-bfreeze`, branch `inp-bfreeze`.

**Audited HEAD:** `0acbc48d0` (Track B freeze (D72): manifest entries …, SEALED). Commits in `inp...HEAD`:
`7c96296da` (anchors, providers, `*_proof` rename, facades), `7010f5007` (seal-body continuation indent only),
`6d8b3bfb5` (facades also re-export the proof modules), `0acbc48d0` (manifest). All checks below were run on
or re-run after `0acbc48d0`, except where stated.

## Pinned identity

| | B1-T | B1-E |
|---|---|---|
| Manifest id | `effectiveStability.d72.torus_confinement.v1` (`manifest/frozen-anchors.json:24427`) | `effectiveStability.d72.oscillator_confinement.v1` (`:24482`) |
| Path | `KAM/Frozen/EffectiveStability/TorusConfinement.lean` | `KAM/Frozen/EffectiveStability/OscillatorConfinement.lean` |
| Export | `KAM.EffectiveStability.torus_confinement` | `KAM.EffectiveStability.oscillator_confinement` |
| Kind / state | theorem / SEALED | theorem / SEALED |
| Implementation | `KAM.Provider.EffectiveStability.TorusConfinement` / `KAM.Provider.EffectiveStability.torus_confinement` | `…OscillatorConfinement` / `…oscillator_confinement` |
| Approval | Scott Armstrong, 2026-11-03, "approve all", D72; version 1 | same |
| Source | `KAM-inp@c0a551843 FREEZE-PROPOSAL.md §2`; plan §2.2; GLS17 §4.3 (56)–(58) | same commit; plan §2.3; CL20 §4.1 (32)–(37) |
| Split | NOT_SPLIT, ruling D72 | NOT_SPLIT, ruling D72 |

D72 (main `db03246d9:docs/DECISIONS.md:620-629`) approves "B1-T `KAM.EffectiveStability.torus_confinement` and B1-E
`.oscillator_confinement`, in the exact text of `docs/tracks/B/FREEZE-PROPOSAL.md` §2 … frozen and sealed in one pass
… with no DRAFT_SORRY stage", plus OD-B2 (minimal premise list) and confirmation of the other overnight defaults.
`c0a551843` exists; the only change to `FREEZE-PROPOSAL.md` after `e243dd5d7` is the appended addendum (§2 unchanged).

## 1. Byte identity of docstring + statement with §2 — PASS

Method: Python, UTF-8. Anchor slice = from `/-- **B1-T` (resp. `**B1-E`) up to (excluding) the first ` :=\n` after it.
Proposal slice = from the same `/-- **B1-…` in `docs/tracks/B/FREEZE-PROPOSAL.md` up to (excluding) the first
` := by\n`. Compared as strings and by SHA-256; re-run after `7010f5007`.

```
B1-T True 2570 2570 cd3ee48f636c69c4 cd3ee48f636c69c4   (bytes anchor/proposal, sha256 prefix)
B1-E True 3005 3005 638a99bb358c0135 638a99bb358c0135
```

Anchor ranges: `TorusConfinement.lean:29-59`, `OscillatorConfinement.lean:29-67` (proposal `FREEZE-PROPOSAL.md:24-54`,
`57-95`). The surrounding context matches as well: both are inside `namespace KAM.EffectiveStability` with `open Set`,
as in the proposal's code block. In addition (item 3) the elaborated types equal the types elaborated from the
proposal text, syntactically (`Expr ==`).

## 2. Anchor file structure — PASS

Both files (`TorusConfinement.lean`, `OscillatorConfinement.lean`, 69 / 77 lines):
- copyright `:1-5`; `FROZEN_ANCHOR_PREFIX_BEGIN` `:6`; `module` `:7`;
- imports `:9-12`: `public import KAM.Frozen.Defs.HamiltonianVectorField`, `KAM.Frozen.Defs.SymplecticForm`,
  `KAM.Frozen.Planetary.Defs.OscillatorAction` (frozen definitions only, exactly the list of proposal §1) and a
  private `import KAM.Provider.EffectiveStability.<Name>`;
- module docstring; `@[expose] public noncomputable section`; namespace; `open Set`;
- markers `PROOF_BEGIN`, `PROOF_END`, `SUFFIX_BEGIN`, `SUFFIX_END`, each exactly once and in order (counted);
- seal body (as the guard slices it: from after the `PROOF_BEGIN` line to the start of the `PROOF_END` line):

```
  by exact KAM.Provider.EffectiveStability.torus_confinement a b η ε T hε hT hη hmargin V hV H hH Ψ
      Ψinv hΨ hΨV hΨsymp hΨinv N R hR hRper hHΨ hRη w₀ hw₀
```
  2 lines, 175 bytes (B1-T); oscillator analogous without `hRper`, 2 lines, 174 bytes. Limits (`seal_limits`):
  3 lines, 240 bytes. Arguments are exactly the explicit binders, all of them, in order (also enforced by the guard).
- `7010f5007` changed only the continuation indentation inside the proof body (`+2` spaces, one line per file); no
  byte of prefix or suffix changed.

## 3. Provider — PASS

`KAM/Provider/EffectiveStability/TorusConfinement.lean:25-53` and `OscillatorConfinement.lean:25-60` (lines in the
provider files) restate the anchor type in namespace `KAM.Provider.EffectiveStability` and are proved by the term
`KAM.EffectiveStability.{torus,oscillator}_confinement_proof <all explicit binders>`. Provider imports only
`KAM.EffectiveStability.{Torus,Oscillator}Proof`.

Implementation: `KAM/EffectiveStability/TorusProof.lean` / `OscillatorProof.lean` are the previously landed proofs.
`diff` against `$(git merge-base inp HEAD):KAM/EffectiveStability/{Torus,Oscillator}.lean` shows only: module title
line, docstring rewording ("Implementation of the frozen **B1-…**"), and the rename `…_confinement` →
`…_confinement_proof`. Statement and proof bytes otherwise unchanged (136 / 146 lines).

Transient check (scratch file outside the repository, `lake env lean`, D53 wrapper, rc 0; kept in the session scratchpad,
never in the repository): it imports both anchors, both providers and `KAM.EffectiveStability.Examples`; declares
`SealAudit.chk_torus_confinement` / `chk_oscillator_confinement` with the **proposal §2 text** (sliced from
`FREEZE-PROPOSAL.md` by script) and body = the frozen export applied to all binders, and `chkP_…` with the same text and
body = the provider; then compares `ConstantInfo.type` with `==`:

```
KAM.EffectiveStability.torus_confinement vs KAM.Provider.EffectiveStability.torus_confinement: syntactic type equality = true; levelParams [] / []
KAM.EffectiveStability.oscillator_confinement vs KAM.Provider.EffectiveStability.oscillator_confinement: syntactic type equality = true; levelParams [] / []
KAM.EffectiveStability.torus_confinement vs SealAudit.chk_torus_confinement: syntactic type equality = true; levelParams [] / []
KAM.EffectiveStability.oscillator_confinement vs SealAudit.chk_oscillator_confinement: syntactic type equality = true; levelParams [] / []
```

Quarantine: `grep -rn "import KAM.Provider.EffectiveStability" KAM *.lean lakefile.lean` →
only `KAM/Frozen/EffectiveStability/OscillatorConfinement.lean:12` and `TorusConfinement.lean:12`. The only other
references to the providers are their own files. No consumer uses `*_confinement_proof`
(`grep -rn confinement_proof KAM` → the two proof files, the providers, and facade docstrings only); every downstream
use (`TorusStep`, `TorusChain`, `TorusNormalForm`, `OscillatorStep`, `OscillatorChain`, `ChartChain`, `Examples`)
calls the frozen export.

Facades: `KAM/EffectiveStability/Torus.lean`, `Oscillator.lean` (`public import` of the anchor and, since `6d8b3bfb5`,
of the proof module; no declarations). The re-export of `*Proof` is harmless for the seal (proof modules are ordinary
implementation modules, not providers; rule 9 is respected).

## 4. Meaning — PASS (no weaker or vacuous reading found)

Frozen definitions used (all SEALED in the manifest; file hashes recomputed and equal to `definition_closure`):
- `KAM.hamiltonianVectorField H z = (fun i => fderiv ℝ H z (0, e_i), fun i => -fderiv ℝ H z (e_i, 0))`
  (`KAM/Frozen/Defs/HamiltonianVectorField.lean`), i.e. `θ̇ = ∂_I H`, `İ = -∂_θ H` in coordinates `(θ, I) = (w.1, w.2)`;
- `KAM.symplecticForm v w = ∑ i, (v.2 i * w.1 i - v.1 i * w.2 i)` (`Σ dI_i ∧ dθ_i`);
- `KAM.Planetary.oscillatorAction p q j = (p j ^ 2 + q j ^ 2) / 2`.

Sign check. B1-T: `J̇_j = -∂_{φ_j}(N(J) + R) = -fderiv R w (e_j, 0)`, which is what `hRη` bounds (`:49-50`). B1-E:
`w = (q, p)`, `I_j = (p_j² + q_j²)/2`, `İ_j = p_j ṗ_j + q_j q̇_j = q_j ∂_{p_j}K − p_j ∂_{q_j}K`, and `hRη`
(`:121-124`) bounds `|w.1 j * ∂_{(0,e_j)} R − w.2 j * ∂_{(e_j,0)} R| = |q_j ∂_{p_j}R − p_j ∂_{q_j}R|`. Matches the
docstring and the source bracket `{I_j, R}` (with `{I_j, N∘I} = 0`).

Five-bin binder table (both anchors; B1-E differs only in the domain predicate `I_j(w) < b_j + ε` / `≤ b_j` and has no
`hRper`). Citations: plan §2.2/§2.3 via proposal §3 table (`FREEZE-PROPOSAL.md:101-120`), OD-B2–OD-B6
(`docs/tracks/B/OWNER-DECISIONS.md:10-14`), confirmed by D72.

| Binder | Bin | Source / ruling |
|---|---|---|
| `{n : ℕ}` | TYPING | dimension; `n ≥ 1` dropped (OD-B6, D72) |
| `a b η : Fin n → ℝ`, `ε T : ℝ` | TYPING | "a,b,η : Vec n, ε, T" |
| `hε : 0 < ε` | SOURCE | `ε > 0` |
| `hT : 0 ≤ T` | SOURCE | `T ≥ 0` |
| `hη : ∀ j, 0 ≤ η j` | SOURCE | `η_j ≥ 0` |
| `hmargin : ∀ j, a j + T * η j < b j` | SOURCE | strict margin `a_j + Tη_j < b_j` |
| `V`, `hV : IsOpen V` | SOURCE | V open (periodicity dropped: RULED OD-B2) |
| `H`, `hH : ContDiffOn ℝ 2 H V` | SOURCE | H `C²` on V |
| `Ψ`, `hΨ : ContDiffOn ℝ 2 Ψ D_{b+ε}` | SOURCE | Ψ `C²` on the chart domain |
| `hΨV : Ψ (D_{b+ε}) ⊆ V` | SOURCE | Ψ maps into V |
| `hΨsymp` | SOURCE | "symplectic", via frozen `symplecticForm` on `fderiv` |
| `Ψinv`, `hΨinv : Ψinv ∘ Ψ = id on D_{b+ε}` | RULED | left inverse only (OD-B3; weakening of "C² inverse") |
| `N`, `R` | TYPING | normal part and remainder |
| `hR : DifferentiableOn ℝ R D_{b+ε}` | RULED | weakened from R `C²` (OD-B2) |
| `hRper` (B1-T only) | SOURCE | "R angle-periodic" (plan §2.2) |
| `hHΨ : H ∘ Ψ = N(action) + R on D_{b+ε}` | SOURCE | `H∘Ψ = N(J) + R` / `N∘I + R` |
| `hRη` on closed `D_b` | SOURCE | `|∂_φ R| ≤ η` / `|{I_j,R}| ≤ η` on the closed region |
| `w₀`, `hw₀` (closed level `a`) | SOURCE | initial point in the closed level set |

Counts: SOURCE 13 (B1-T) / 12 (B1-E), STANDING 0, TYPING 4 rows, RULED 2, **EXCESS 0**. All RULED rows are
weakenings of source premises (the anchor is stronger than the source statement), approved in D72.

Refute-first attempts (none succeeded):
- *Vacuity of premises.* `hw₀` and `hmargin` force `0 ≤ |w₀.2 j| ≤ a_j < b_j` (B1-T) / `0 ≤ I_j(w₀) ≤ a_j < b_j`, so
  the domains are non-empty around `w₀`; the examples instantiate all premises nontrivially (below). `n = 0` is a
  harmless degenerate case (the conclusion still asserts a genuine solution with `T < T₁`).
- *Junk `fderiv`.* All `fderiv` uses are on open sets where the function is differentiable: `D_{b+ε}` is a finite
  intersection of open sets (`hΨ` on it; `hΨsymp` there); `hRη` is on the closed `D_b ⊆ D_{b+ε}` (since `ε > 0`),
  where `hR` gives differentiability at an interior point of the open domain; `hamiltonianVectorField H (z t)` with
  `z t ∈ V`, `V` open, `H` `C²`. So no premise or conclusion can be satisfied through the `0` junk value of `fderiv`.
- *Junk `Ψinv`.* `Ψinv` is arbitrary off `Ψ(D_{b+ε})`, but the conclusion gives `Ψ (Ψinv (z t)) = z t` together with
  `|(Ψinv (z t)).2 j| ≤ a_j + η_j T < b_j` (resp. action bound), so `Ψinv (z t) ∈ D_b` and is the unique chart preimage
  (injectivity from `hΨinv`). The bounds therefore speak about the true chart coordinates of the orbit.
- *Weak solution clause.* `z` is a genuine `HasDerivAt` solution on all of `Ioo (-T₁) T₁ ⊋ [-T, T]`, stays in `V`,
  starts at `Ψ w₀`, and is unique among all solutions in `V` on any order-connected `I ∋ 0` (on `I ∩ Ioo (-T₁) T₁`).
  Quantifier order: `∃ T₁, ∃ z` before `∀ I y` and `∀ t`; nothing is chosen after the data it should not depend on.
- *Domain conventions.* B1-E stated in actions, `b_j` an action level (`ρ_j²`-type), consistent on both sides.

Examples: `KAM/EffectiveStability/Examples.lean:26-39` (`torus_confinement_example`: identity chart, `N = ∑ J_j²`,
`R = 0`, `η = 0`, `V = univ`) and `:42-56` (`oscillator_confinement_example`: harmonic oscillator at the origin, zero
action) apply the frozen exports (imported through the facades) with every premise discharged. Rebuilt at HEAD
(`lake build KAM.EffectiveStability.Examples`: facades rebuilt, "Build completed successfully (2883 jobs)") and
imported by the transient check; axioms below.

## 5. Manifest — PASS

Entries `manifest/frozen-anchors.json:24426-24480` and `:24481-24535`: kind theorem, state SEALED, approval ref D72
(owner reply "approve all", 2026-11-03 07:27 UTC, version 1), path/export as above, `contract` id/version 1,
NOT_SPLIT with ruling D72, implementation module/export = the providers, empty `draft_allowlist`.
- `prefix_sha256` / `suffix_sha256` independently recomputed (bytes up to and including the `PROOF_BEGIN` line /
  from the `PROOF_END` line on): both equal for both anchors.
- `definition_closure`: `HamiltonianVectorField`, `IsDiophantine`, `SymplecticForm`, `OscillatorAction`, sha256
  recomputed and equal. `IsDiophantine` enters transitively (`OscillatorAction.lean:18`
  `public import KAM.Frozen.Defs.IsDiophantine`); it is the import closure, as for earlier anchors.
- `python3 scripts/check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json` → `FROZEN-ANCHOR GUARD OK`,
  rc 0.
- `python3 scripts/abi_hashes.py . manifest/frozen-anchors.json --check` → `ABI HASHES OK (316 frozen declarations of
  KAM; …)`, rc 0.

## 6. Axioms and kernel replay — PASS (the scripted `--fast` run is incomplete; see N4)

`#print axioms` (transient check at HEAD `0acbc48d0`):
```
'KAM.EffectiveStability.torus_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscillator_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.EffectiveStability.torus_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.EffectiveStability.oscillator_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torus_confinement_example' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscillator_confinement_example' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorryAx`.

Kernel replay, targeted (same `leanchecker --verbose` invocation and `LEAN_PATH` as `scripts/kernel_replay.sh`, D53
wrapper): modules `KAM.Frozen.EffectiveStability.{Torus,Oscillator}Confinement`,
`KAM.Provider.EffectiveStability.{Torus,Oscillator}Confinement`, `KAM.EffectiveStability.{Torus,Oscillator}Proof`:
all six `replaying …`, rc 0, wall 63 s, max RSS 2.76 GB.

Kernel replay, scripted (`scripts/kernel_replay.sh --fast`, D53 wrapper, at `0acbc48d0`): 389 expected modules.
**Incomplete.** The run was stopped from outside after batch 26 (`Terminated`, 1086 s elapsed) because the machine was
low on memory, not because of a replay error. Before the stop, 104 modules had been replayed, every batch rc 0, and the
log had no lines other than `replaying …`. These included `KAM.Frozen.EffectiveStability.TorusConfinement` and
`KAM.Frozen.EffectiveStability.OscillatorConfinement` (log lines 23–24). The providers and proof modules come later
in the sorted order and were not reached in this run. They are covered by the targeted replay above. I did not
restart the run. The orchestrator should rerun `--fast` (or `--full` at landing) when the machine has memory to spare.

## Other checks

- `scripts/lint_sources.sh` at HEAD: rc 1, **only** because `KAM.lean is out of date; run scripts/gen_root_imports.py
  (KAM/Root/EffectiveStability.lean, KAM/Root/Frozen.lean, KAM/Root/Provider.lean)`. All other sub-checks pass
  (`check_lean_modules: PASS (4577 Lean files…)`, 25 tests OK, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`). The
  generated root is not regenerated on this branch yet (rule 10: generated, not hand-edited).
- Line caps: anchors 69 / 77, providers 57 / 64, proof modules 136 / 146 lines (≪ 1500). No heartbeat or other
  option overrides in any audited file (`grep set_option` → none).

## Notes (non-blocking)

- **N1 (landing hygiene).** Run `scripts/gen_root_imports.py` before landing (lint rc 1 above). Not a seal defect.
- **N2 (cosmetic).** `KAM/EffectiveStability/OscillatorProof.lean:34` (docstring of `oscillator_confinement_proof`) begins
  a line with `- p_j ∂_{q_j} R`, which doc-gen renders as a list item, splitting the formula. Not frozen; fix at leisure.
- **N4 (replay coverage).** The targeted leanchecker replay of all six track-B modules passed. The scripted
  `kernel_replay.sh --fast` run was stopped at 104/389 modules because the machine ran low on memory; every replayed
  module passed, both anchors included. Rerun the scripted gate before landing.
- **N3.** The B1-T anchor imports `KAM.Frozen.Planetary.Defs.OscillatorAction`, unused by its statement. This is the
  approved import list of proposal §1 and is recorded in its closure; harmless.

Suspected errata in pinned sources: none new. Deviations introduced by the audited commits: none beyond those approved
in D72 (OD-B2/B3/B4/B6).

## Verdict

```
B1-T DECLARATION_FIDELITY: PASS   B1-E DECLARATION_FIDELITY: PASS
BINDERS: EXCESS 0 (both)
SEAL (proof-body-only, provider assembly, limits): PASS (both)
AXIOMS: propext, Classical.choice, Quot.sound (both); KERNEL REPLAY: PASS (targeted, 6 modules; scripted --fast incomplete, N4)
MANIFEST: PASS (guard OK, ABI OK)
PROOF_STATUS: PROVED (both)
```

**PASS WITH NOTES — seal-ready.** Notes N1–N4 are non-blocking. Before landing, regenerate the root (N1) and rerun the scripted kernel replay (N4).

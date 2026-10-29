# N-PARTIAL-CONVEX seal-key audit 1

Lane N (Zohar's team), 2026-10-29. Independent seal-key audit (handoff §3, step 2) of
`nekhoroshev.d25.partialConvex_nekhoroshev.v1`, the frozen theorem `KAM.Nekhoroshev.partialConvex_nekhoroshev`
and its provider `KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev`.
- **Static part:** read-only, by an auditor that did not write the provider. The pre-seal base was
  `zohar/n11` merged with `main` a14c4247 (tree `dfd75d67`). The repository's own `check_frozen_anchors.py`,
  `gen_root_imports.py`, `check_lean_modules.py` and `lint_sources.sh` (without the ABI step) were run on an
  overlay of the sealed files.
- **Remote evidence:** from the integrator's Codespace build of the merged and sealed tree, recorded below.

## Verdict

**PASS WITH NOTES.** No soundness or fidelity defect. The notes (S-1 to S-5) concern the seal commit's
records and are applied in it.

## Checklist

| # | Item | Result | Evidence |
|---|---|---|---|
| 1 | Type equality | PASS | Provider statement and anchor statement: 320 whitespace-separated tokens, identical; the only byte difference is `:= by` vs `:=`. Every unqualified identifier resolves to the same constant in both contexts (homonym scan). The sealed build elaborates the body against the frozen type. |
| 2a | Seal body names all binders in order | PASS | The guard's `explicit_binders` returns the 23 names `hn hk G G' D hG hGc hG' hGc' hD ρ g m Mcomplex hρ hMc hcollar h hhol hC2 hreal hHess hdef`; the body applies the export to exactly these. |
| 2b | Body within limits | PASS | 2 lines, 160 bytes (limits 3 lines, 240 bytes); longest line 99 characters. |
| 2c | Continuation indentation | PASS | Continuation indented past `exact`, as in `7c254d1a`. |
| 2d | Prefix and suffix unchanged | PASS | Both before and after the seal: prefix `40b1b8eb…dee5d4`, suffix `1efcbce4…6b8da8`, equal to the manifest. |
| 3 | Manifest | PASS | Only `state` changes, DRAFT_SORRY → SEALED; formatting reproduced byte for byte. 141 SEALED, 3 DRAFT (all Planetary); all 26 track-N anchors SEALED. |
| 4a | Frozen-anchor guard | PASS | `FROZEN-ANCHOR GUARD OK` on the overlay and in the remote lint. |
| 4b | Root imports | PASS | Regenerated `KAM.lean` adds 16 imports: the anchor, the provider and 14 N11 `Partial.*` modules. |
| 4c | Quarantine | PASS | Only the anchor and `KAM.lean` import the provider; its closure (180 project modules plus Mathlib) has no frozen theorem module, other provider or draft anchor. |
| 5 | Provider soundness | PASS | Uses `threshold`, `block`, `domain_field`, `orbit`, `theta`, frozen definitions; no `sorry`, `admit`, `axiom`, `set_option`. Empty-`G` branch correct. The σ = −1 branch (`y u = θ(z(−u))` on `[−C, 0]`, derivative `(−1)•F₀`, `t₁ = −t`) is correct. μ₀ is fixed by `threshold` before μ, P, C, z, t. |
| 6 | Remote evidence | PASS | Merged and sealed tree (merge `72ce86d4`, tree `dfd75d67`; anchor `5ca2484c84dd`, manifest `a65b76f16bc7`, `KAM.lean` `3c5d53701d31`): full root `lake build` OK (`Build completed successfully (10186 jobs)`, 0 errors, no `sorry`); lint: check_lean_modules PASS (1140 files), FROZEN-ANCHOR GUARD OK, root/errata/size/line checks clean; ABI HASHES OK for all 144 frozen declarations, checked per id prefix with the hashing code of `abi_hashes.py` (`kam.*` 25, `iso.*` 19, `nekhoroshev.*` 26, `planetary.*` 74; the single-process run thrashes the 16 GB Codespace page cache); `#print axioms KAM.Nekhoroshev.partialConvex_nekhoroshev`: propext, Classical.choice, Quot.sound; `lake env leanchecker --verbose` (LEAN_NUM_THREADS=1) of the frozen module and the provider: exit 0 each. |

## Findings

- **S-1 (medium).** The `MANIFEST-CHANGES` row was missing. Fixed in the seal commit, with the evidence below.
- **S-2 (medium).** The regenerated `KAM.lean` must be committed with the seal (lint fails otherwise). Done.
  14 of its 16 new imports are N11 modules root-imported for the first time; the full root build is their
  first whole-library name-clash test.
- **S-3 (low).** The evidence log now records the merge tree and the hashes of the sealed files.
- **S-4 (low).** Records stated this audit's verdict before the remote evidence existed. This file is committed
  with the seal, after the evidence.
- **S-5 (low).** The seal is committed separately from the K-audit fixes and the graph sync.

The anchor docstring's bare `by exact …` sentence is in the frozen prefix and stays; D26 correction 2 requires
the body with all binders.

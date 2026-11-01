# Package LP-SP-TUBE: the complex-tube theorem for unequal fast/slow blocks (audit note N12)

Wave 4 (spatial infrastructure). Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules,
capped wrappers, handoff; module docstrings carry the SPEC §4 sentence). Base: `inp-lp`.

## Why (AMENDMENTS N12)

Track P's `KAM/Planetary/Exponential/ComplexTube.lean` proves `tube` for `Phase (n+n)`: `periodicOrbitSet`,
`complexTube` and `tube` all use `n + n`. That size is right for the planar chart (`n` fast and `n` slow pairs) but
not for the spatial chart, which has `n` fast and `2n` slow pairs: `Phase (n + m)` with `m = 2n`, or whatever
layout LP-SP-PROD chooses. The underlying tools are already dimension-generic:
- `fastShift {a b}` (frozen) is typed on `Phase (a + b)`;
- `real_trace_identity {d}` and `local_analytic_complexification {d}` are generic in `d`.

Only the three `n+n` declarations need re-typing.

## Owned files

`KAM/Planetary/Spatial/ComplexTube.lean` (new; do NOT edit track P's file).

## Statements

Generic in `n m : ℕ`, on `Phase (n + m)`:
- `periodicOrbitSetNM K := {w | ∃ k : Fin n → ℤ, ∃ x ∈ K, w = x + fastShift k}`;
- `complexTubeNM K r` (same formula as `complexTube`);
- `tubeNM`: the statement of `tube` verbatim with `n+n` replaced by `n+m`, proved by the same argument (copy and
  adapt the proof of `tube` and its local lemmas: `mem_ball_shift`, the cover and gluing).
- Also: `complexTubeNM` is open, monotone in `r`, and invariant under complexified fast shifts; and
  `complexTubeNM K r` for `m = n` coincides with track P's `complexTube` (an `rfl`/`ext` lemma), so nothing is
  duplicated in meaning.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0 (names must not clash with track P's).
- `#print axioms`.

Expected size 250–600 lines. Stop when done or blocked.

## Handoff

`docs/tracks/LP/audits/LP-SP-TUBE-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-TUBE.md`,
then `touch .drafts/READY-LP-SP-TUBE`.

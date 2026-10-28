# S9-Q independent audit 2 — delta audit

2026-10-28. **Overall verdict: PASS WITH NOTES, subject to verification receipts below. F1 is resolved.** The exact signed `SecularSpectrum.diagonalize` theorem retains PASS, and the formerly missing `stepP:p9:d-c` domain implication is now exported. No frozen theorem anchor is implemented or sealed by this infrastructure package. The expected generated-root lint exception is recorded separately.

## Scope and immutable delta

Audited worktree and report destination: `/root/code/KAM-inp-s9q`. The explicit user destination overrides the brief's generic main-worktree destination. Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the AUDIT FOCUS in `S9-Q-handoff.md`, Round 1, and `.drafts/handoff-S9-Q.md` including “Round 2 fix”. Checked the P810 design package/graph ownership and proof plan, both design audits, signed signatures, Track P conventions, current Part 9 blueprint/packet, real polydisc and Euclidean-length definitions, and relevant frozen oscillator/average/Birkhoff definitions. This is a delta audit: unchanged proofs retain Round 1's mathematical review, with fresh whole-module verification below.

HEAD/fix: `f26fc7d31aebb665d7d7dcfd97c7d7b92ffb8adc`; Round 1 baseline: `fe989f97`; observed `inp`: `d9183adae208ecf2e726620694b69c8168e33006`; merge base: `cbc738ce2a4017c3c06bf565c99f028ec013fcd2`. `git diff inp...HEAD` contains 17 files / 2483 insertions, including inherited S8-Q modules and prior audit documents; only `KAM/Planetary/SecularSpectrum/Diagonalize.lean` is scoped proof code.

`git diff --numstat fe989f97 HEAD` outputs exactly:

```text
36  0  KAM/Planetary/SecularSpectrum/Diagonalize.lean
```

Removing the single inserted block before the three closing namespace/section lines reproduces the entire baseline file byte for byte. Thus all original imports, declarations, statements and proof bodies, including `diagonalize`, are unchanged. The file has **290 lines**, rather than the handoff's informal 291. SHA-256: `f80d7c4669fdc459ff5186168d6564aa612e51ad0a82c5d06981b3b8dc4d82ec`. The `diagonalize` header is byte-identical to `/root/code/KAM-inp/.drafts/design/P810Signatures.lean:364–386`, including unused `hAn`.

## Finding disposition and literal source fidelity

**F1 CLOSED.** Blueprint `blueprint-P/parts/p9-secular-spectrum.tex:142` states: “as soon as $\sqrt n\,\delta_0\le\rho_*$” together with the strict action-distance guard. Line 151 gives the Euclidean-to-max comparison. Packet `docs/graph/P/packets/P-p9.nodes.md:859–868` explicitly retains `delta_0>0`, the oscillator-disc hypothesis and that domain conclusion. `diagonalize_mem_realDisc` at lines 268–286 proves precisely the missing implication, instantiated at `r = rho_*` and `R = varrho(I)`:

```text
forall j, xi_j^2 + eta_j^2 < delta_0^2;
sqrt(n)*delta_0 <= r;
forall i, |I_i - action(D,a)_i| < r
  => (R*xi,I,R*eta) in realDisc(D,a,r).
```

The quantifier and hypothesis checks are substantive:

- `0 < n` is weaker than the containing source theorem's explicit `n >= 2` (p9:135), and follows also from Part 9's `n >= 1` convention (p9:15). It adds no source restriction. The existing `Data n` itself carries positive dimension.
- `0 < delta_0` is exactly the packet's `SOURCE_QUANTIFIERS`, consistent with the positive oscillator widths in the frozen epsilon-delta predicate. It is not inferred from squaring an arbitrary signed radius.
- `R.transpose * R = 1` follows from the supplied `isSO` rotation. Determinant one, analytic dependence, spectral simplicity and diagonalization are unnecessary for this domain fact, so omitting them strengthens the helper.
- The coordinatewise strict action guard is equivalent, in positive finite dimension, to the source's `norm(I - Lambda*)_inf < r`; the center is literally `Lambda* = action D a`. A fresh probe uses the source max-norm guard directly. No slow-coordinate factor is inserted into the action guard.
- `r` is arbitrary rather than restricted to the analytic radius. Specializing it to the source radius gives the exact domain implication. No extra independent positivity hypothesis on `r`, axes membership, domain membership, remainder bound or conclusion-shaped field is required.

`rotDiag_length2_mulVec` at lines 253–262 rewrites the sum of squares as a dot product and cancels `R.transpose * R`; it proves exact Euclidean-length preservation, not max-norm invariance. For each of xi and eta, the oscillator condition implies coordinate square < delta_0 squared, hence max norm < delta_0. Existing literal norm comparisons then give

```text
norm(R*x)_inf <= length2(R*x) = length2(x)
  <= sqrt(n)*norm(x)_inf < sqrt(n)*delta_0 <= r.
```

`rotDiag_mem_realDisc` translates these estimates into the original complex-polydisc real slice with slow order `(xi,I,eta)`. Strictness survives equality in the radius guard. This discharges the exact domain conclusion that Round 1 found missing. The original factor-n witnesses in the signed existential remainder theorem remain valid; they no longer substitute for this sharper domain statement. The intermediate Euclidean strict estimate is available from the displayed chain, while the exported target is the literal requested domain membership.

**N1: resolved upstream, not an S9-Q obligation.** Read `inp-s8q:docs/tracks/P/audits/S8-Q-audit-2.md` at upstream HEAD `af08fbac8f13effb1b7c13a0ecac1fdb81ebf0a2`: its verdict is PASS WITH NOTES and accepts the three `qf-diag2` exports. Those changes are not claimed present in this older inherited S8-Q checkout and were not imported or repaired here. The new length lemma proves just the preservation fact this adapter needs; it does not purport to replace the upstream symplecticity package.

**N2: retained ownership boundary.** Transport, period-one wrappers and Q1/Q2 remain S9-T's assignment (`P810-LEAN-DESIGN.md:442`). This audit closes the assigned S9-Q slice, not the full transport node, quartic beta, frozen integrability/little-o predicate, or a physical/campaign theorem.

## Declaration and node inventory

All declarations below have prefix `KAM.Planetary.SecularSpectrum.`. Prior eight declaration reviews are retained only after verifying their byte identity.

| Node / role | Declaration and source line | Verdict | Reason |
|---|---|---|---|
| d-a conjugation | `rotDiag_quad_conj`, 41 | PASS retained | Exact arbitrary-matrix quadratic conjugation. |
| d-a cancellation | `rotDiag_quad_rot`, 56 | PASS retained | Orthogonality cancels the transpose. |
| d-b existential radius | `rotDiag_norm_le`, 61 | PASS retained | Valid coarse factor-n max-norm bound. |
| d-b real slice | `rotDiag_mem_realDisc`, 83 | PASS retained | Literal polydisc membership and coordinate order. |
| d-b inverse expression | `rotDiag_liftInv_assemble`, 99 | PASS retained | Exact fast-angle shift formula. |
| d-b average shift | `rotDiag_avg_shift`, 107 | PASS retained | Translation of the original periodic cell integral. |
| d-b matched average | `rotDiag_avg_lift`, 116 | PASS retained | Same Boolean selects both models. |
| Signed S9-Q, d-a/d-b/dictionary terms | `diagonalize`, 124 | PASS | Exact signed statement; all original proofs unchanged. |
| d-c Euclidean preservation | `rotDiag_length2_mulVec`, 253 | PASS new | All dimensions, any real orthogonal matrix. |
| d-c source domain implication | `diagonalize_mem_realDisc`, 268 | PASS new | Literal oscillator and action guards, sqrt(n), original realDisc. |
| stepP:p9:d-c as assigned | `diagonalize` plus domain adapter | PASS | Previously accepted dictionary terms plus the missing domain implication. |
| stepP:p9:d-d | S9-T exports | Separate owner | No transport closure claimed. |
| stepP:p8:qf-diag2 | Upstream S8-Q | Separate owner | Upstream Round 2 accepts its repair; no new S9-Q requirement. |

## Definitions and hygiene

No new `def`, `abbrev`, `structure`, class or instance occurs in either the delta or the whole audited module. No new fallback or surrogate object. `length2`, `realDisc`, `polydisc`, `action` and frozen `oscillatorAction` retain their literal bodies.

The recursive local import closure has 137 modules, including 56 frozen modules; all 56 match manifest `kind=definition`, `state=SEALED`. No provider or frozen theorem is imported, so no DRAFT_SORRY dependency. Provider/frozen theorem equality and sealing probes are inapplicable; the signed draft is checked without importing its unproved bodies.

All ten short theorem names were searched against declaration commands throughout KAM: no outside declaration occurrence. No `_root_` qualification, new namespace or root shadow. A comment/string-masked code scan finds no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option`. Copyright, `module`, public imports, module docstring and exposed public section remain unchanged. 290 total lines are below 1500.

## Independent verification receipts

PENDING_RECEIPTS

## Uncertainties, errata and deviations

No new suspected pinned-paper or blueprint defect was found. This delta audit does not reverify the existing paper errata ledger. The positive dimension and width hypotheses match source quantifiers as detailed above. The 290/291 handoff line-count discrepancy is bookkeeping only. No production code, source, frozen file, manifest, graph record, generated root or README was edited. No auditor-introduced mathematical deviation; no delegation or state-changing git. The auditor wrote only this report and temporary `.lake/abi-scratch/` probes, removed at closeout.

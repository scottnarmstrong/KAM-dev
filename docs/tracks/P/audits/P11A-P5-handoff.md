# P11A-P5 prover handoff (branch inp-p11ap5, c51ac530; contains P11A-P2; offloaded package run by the main orchestrator)


Branch `inp-p11ap5` (worktree /root/code/KAM-inp-p11ap5). Scope per ruling 21:50: parametric core only; `avg_fast` and
`p11FastData` are NOT stated (they need `holo_chart`).

## Files (all new, under KAM/Planetary/Preparation/)
- `LogBounds.lean` (51 lines): `e4` (signed, verbatim), `log_inv_ge_one` (first clause of the node: `log(1/ε) ≥ 1` on `(0,e⁻¹]`).
- `Fast.lean` (409): signed `p11K1, p11Alpha1, p11s1, p11d1, p11eta1, P11FastData, P11FastSpec` verbatim; parameter lemmas
  (`fast_consts, p11K1_ge_one, exp_p11K1, p11s1_pos, p11_budget, p11_sK, p11_alpha_le, p11d1_le`); `P11SecularHReal`;
  `fast_spec_at` (af-apply/af-concl at one ε); exported core theorem **`avg_fast_of_spec`**.
- `FastBridge.lean` (211): oscillator dictionary (`oscDom_eq_workingDom`: `oscDom {J0} r rz rz S = p11WorkingDom n J0 S r rz`,
  `p11Flat`, `oscFunction_flat`, `coeff_zero_flat` (zero mode = `eps * p11FastMean`), weighted spectator conversion
  `spectator_wsummable/spectator_wsum_eq`, `oscBound_of_sup` = sup-weighted (b) on the oscillator carrier) and
  `oscHyp_fast` (= **af-apply**: builds `OscHyp {J0} s1 rz rz 0 σ K α (ε MF) h (ε F)` from the spec).
- `FastDivisor.lean` (173): `omega_lipschitz` (ext-mvt), `re_dotC_omega`, `fast_divisor` (= **af-o1**).
- `FastParams.lean` (143): `fast_rhs_lower`, `fast_small_eventually` (= **af-o2**: (S1) and `εM ≤ e⁻¹` for all small ε, via `e4`).
(No new module touches KAM.lean, Frozen, manifest, providers; no `sorry/axiom/maxHeartbeats/EuclideanSpace`.)

## Node -> declaration
- `bpP:p11:e4` -> `KAM.Planetary.e4` (+ `log_inv_ge_one`); `bpP:p11:sec-C#data` -> the five defs above.
- `stepP:p11:af-apply` -> `oscHyp_fast` + `osc_averaging`; `stepP:p11:af-o1` -> `fast_divisor`; `stepP:p11:af-o2` ->
  `fast_small_eventually`; `stepP:p11:af-concl` -> `fast_spec_at`; `bpP:p11:avg-fast` -> `avg_fast_of_spec`:
  `P11SecularSpec D C → P11SecularHReal C → ∃ eps1, 0<eps1 ∧ eps1<1 ∧ ∀ eps, 0<eps → eps ≤ eps1 →
   2^12*(1+n)*p11K1 C eps*eps*C.MF*C.sigma ≤ p11Alpha1 C eps*p11d1 C eps ∧ ∃ A, P11FastSpec C eps A` (same conclusion as the signed
  `avg_fast` with `C` abstract). The signed `avg_fast` becomes a wrapper once `holo_chart`/`p11SecularData` exist and
  `P11SecularHReal (p11SecularData D)` is discharged (see E1).

## Approach
Dictionary of the working carrier with `osc_averaging` (D={J0}, r=s1, rp=rq=rz, s̄=0, s=σ, K=K1, α=α1, E=εMF, h=h̃, f=εF; x ↔ q, y ↔ p);
G(J,(x,y)) := ε⁻¹ g(append 0 x, append J y) (g is θ-independent); f1 := f_*; sup bounds via `oscBound.norm_le`; spectator
bounds via the flat parameter `(J,y,x)`; (O1) by mean value inequality + Diophantine; (S1) by explicit polynomial-in-log lower
bounds on α1·d1 and `e4`.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-p11ap5 KAM.Planetary.Preparation.Fast KAM.Planetary.Preparation.LogBounds`: success
  (also each of FastDivisor/FastBridge/FastParams built); no sorry warnings in my files.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK (the only remarks: "KAM.lean out of date"
  (generated; not edited) and the repository-wide >100-char line listing, which includes a few of my lines).
- `#print axioms avg_fast_of_spec`, `e4`, `fast_spec_at`: `[propext, Classical.choice, Quot.sound]`.

## Suspected errata / deviations (for docs/errata/ledger.json)
- **E1 (spec gap, blocks the one-line wrapper).** `P11SecularSpec` records only `(C.h (realInclusion J)).re = -∑...` and
  `(C.omega ..).re = varpi`; it never says `(C.h (realInclusion J)).im = 0` (nor `omega` real). `OscHyp.real_h` (source premise of
  `osc_averaging`, `bpP:p2:osc-averaging` hypothesis "h real on real points") needs it, and without it the reality of `Φ^1`
  (clause 7 of `P11FastSpec`) is genuinely false in general (a complex frequency makes the generator complex). I therefore added the
  explicit hypothesis `P11SecularHReal C` (a reality/typing datum, not conclusion-shaped). Recommended fix: add `.im = 0` of `C.h`
  (equivalently `C.h` real) at real points of the ball `2 r_C` to `P11SecularSpec` (P2/holo_chart owns it; source: bpP:p11:holo-chart
  says the secular form `h̃` is real analytic / `H_fix = h̃ + εF` real). Then `avg_fast_of_spec` loses the hypothesis `hh`.
- **E2 (signature precedence).** Signed `p11d1 := min (p11s1 C eps*C.sigma) C.rz^2` parses as `(min (s1 σ) r_z)^2`, not the source
  `d_1 = min{s_1σ_F, r_z²}` (bpP:p11:sec-C, eq par1). Copied verbatim as required. It is still sufficient: `p11d1_le` shows
  `p11d1 ≤ min (s1σ) (rz*rz)` (uses `s1 ≤ rC ≤ 1`, `σ ≤ 1/4`), so (S1) with the signed `d1` implies the osc smallness and the η1 bound
  (with the signed, larger η1) follows. Suggest changing to `min (p11s1 C eps*C.sigma) (C.rz^2)` in a future signature revision.
- Deviation: extra unsigned exports (`log_inv_ge_one`, `P11SecularHReal`, `fast_spec_at`, helper modules FastBridge/FastDivisor/FastParams;
  all within the design budget idea of the row but split to respect modularity).

## Uncertainties / design signals
No heartbeat problems (no override used anywhere). All files < 450 lines.
`avg_fast_of_spec` takes `P11SecularSpec` (not FullSpec); the `euclid ≤ L` clause of FullSpec is not needed.

Round 1b: ruling 22:50 amends the signed P11SecularSpec with (C.h (realInclusion J)).im = 0, so P11SecularHReal will be derivable from the spec once P11A-P2f lands. P11SecularHReal and avg_fast_of_spec are deliberately unchanged now. This round only rewrapped 12 lines over 100 columns (Fast, FastBridge, FastDivisor, LogBounds); no code meaning changed.

ORCHESTRATOR RULINGS: (21:50) P11A-P5 delivers a PARAMETRIC CORE: its signed definitions (p11K1, p11Alpha1, p11s1, p11d1, p11eta1, P11FastData, P11FastSpec, e4) and avg_fast_of_spec for an arbitrary C with P11SecularSpec; the signed avg_fast and p11FastData are NOT stated here (they need holo_chart, assembled by P11A-P2f) and are not findings. (22:46) The handoff's E1 is resolved by amending the signed P11SecularSpec: its second conjunct now also states (C.h (realInclusion J)).im = 0 (P11ASignatures.lean lines 688-690), which P2f proves; so the hypothesis P11SecularHReal of avg_fast_of_spec will be derivable from the spec and the wrappers need no extra premise. Judge whether P11SecularHReal is exactly that clause (up to the ball/norm form).

AUDIT FOCUS: design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-P5 (Preparation/Fast, LogBounds; P2 osc_averaging, weighted spectator conversion, e4) and its node table incl. bpP:p11:avg-fast and af-* steps; P11A design audits; signatures /root/code/KAM-inp/.drafts/design/P11ASignatures.lean. Note the handoff's E2 (p11d1 precedence) and whether p11d1_le makes the verbatim signed definition sufficient. Audit ONLY KAM/Planetary/Preparation/{Fast,FastBridge,FastDivisor,FastParams,LogBounds}.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
Orchestrator note: helpers coth_pos, norm_dotC_le, oscUnpack_flat were renamed p11_coth_pos, p11fd_norm_dotC_le, p11_oscUnpack_flat (reused short names; the clash check refused the first launch).

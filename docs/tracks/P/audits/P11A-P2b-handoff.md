# P11A-P2b prover handoff (branch inp-p11ap2b, 20c39731; offloaded package run by the main orchestrator)


Hard rules observed: no `set_option maxHeartbeats`/overrides, all files < 300 lines, no
sorry/axiom/admit/unsafe/opaque, no `EuclideanSpace`, no frozen/manifest/KAM.lean/README edits, no
provider import, lines <= 100. Signatures were not changed (no signature in scope; only new helpers).

## Files (all new; all committed)
* `KAM/Planetary/Preparation/HoloFrame.lean` (222 lines)
  - `p11_pos_of_close`, `p11_axis_mem_axes`: actions `delta/8`-close to the physical action are the
    actions of ORDERED axes (forward tube: `|a'_i - a_i| < p11Zeta <= gap/6`, via
    `circularPoint_eq_poincareProd`).
  - `p11_sorted_eq_patch`: `SecularSpectrum.sigma E (axis L) = (p11PatchData D).sigma (2 pi L)`.
  - `p11_holo_frame`: from `J0 in K`: `t1 > 0`, real frame `R` entrywise analytic on
    `ball ((2 pi)^-1 J0) t1`, and on that ball: `2 pi L in V`, `L in actionDomain`, `isSO (R L)`,
    `coeffs (axis L) = R diag(sigma) R^T`, patch sigma = `SecularSpectrum.sigma`, and
    `R^T p11SecularMatrix R = diagonal (patch sigma)`.
* `KAM/Planetary/Preparation/HoloScalar.lean` (189): explicit Keplerian `p11HoloH`, `p11HoloFreq`
  (`omega = grad h`, `fderiv_p11HoloH`), real parts (`p11HoloH_re`, `p11HoloFreq_re`),
  non-vanishing ball, `p11_jet_bound_complex` (L and the Euclid bound by compactness).
* `KAM/Planetary/Preparation/HoloData.lean` (279): **`structure P11HoloData D`** and
  **`p11_holo_data D : Nonempty (P11HoloData D)`** — the single interface for P2c–P2f. Fields:
  data `J0 gamma tau rC L Brho Bdrho h omega Omega rho` + real frame `R`, `t1`, `t2`; Prop fields are
  the conjuncts of `P11SecularSpec`/`P11SecularFullSpec` NOT involving `F`, `chart`, `MF`, `rz`,
  `sigma`(strip), `C`, the mean (verbatim shapes, `C.x` replaced by the field): `freq`, `h_re`,
  `omega_diff`, `Omega_diff`, `tau_eq`, `h_diff`, `omega_eq`, `jets`, `euclid_le`, `J0_interior`,
  `gamma_*`, `dio` (+`dio_fast`, `dio_slow`), `rC_*` (incl. `rC <= pi delta/8`), `one_le_*`,
  `rho_clause`, `rho_bounds`; plus rotation facts used by later steps: `R_analytic`, `R_frame`
  (as in `p11_holo_frame`), `rho_diff`, `rho_real` (`rho (iota y) = (R y).map ofReal` for
  `|y - Lambda0| < t2`), `rho_orth_t2`, `rC_le_t2` (`rC <= pi t2/2`), `nonvanishing`
  (`ball (iota J0) (2 rC)` avoids coordinate hyperplanes). `h = p11HoloH D`, `omega = p11HoloFreq D`,
  `Omega J = 2 pi * G J` with `G` the complexification of `varpi(natAdd)`.
* `KAM/Planetary/Preparation/HoloLift.lean` (193), step `hc-lift`:
  - `p11_fderiv_rho_real`: `fderiv C rho (iota L) (iota v) = (fderiv R L v).map ofReal`.
  - `p11ChartInput_eq_liftInv` / `P11HoloData.chartInput_eq_liftInv`: for `C.rho = d.rho` and real
    `z` with `|fast z.2/(2pi) - Lambda0| < t2`:
    `p11ChartInput C z = SecularSpectrum.liftInv d.R (assemble (fast z.2/(2pi))
    (fun l => 2 pi fast z.1 l) (slow z.2) (slow z.1))` (the `T1`-converted real lift).
  - `p11_mulVec_bound` (`|A x| <= B|x|`), `p11_angle_correction_bound`
    (`|sum y A x| <= n B |y||x|`), `P11HoloData.lift_bounds` (both, on `ball .. (rC/pi)`).

## How P2f uses it
`P11SecularData` fields from `d : P11HoloData D`: `J0, gamma, tau, rC, L, Brho, Bdrho, h, omega,
Omega, rho` copy; `sigma, rz, MF, F, C, chart` are P2c–P2e. Each scalar/rotation conjunct of
`P11SecularSpec` is the corresponding field. `chart := poincareProd D.m (D.G D.m0) o liftInv d.R o T1`
(T1 as in `chartInput_eq_liftInv`; `lift` needs `AnalyticOnNhd R` on the `Matrix.Norms.Elementwise`
instance, obtained from `d.R_analytic` entrywise via `analyticAt_pi_iff`).

## DESIGN NOTE (patch spec gap, resolved locally)
`P11PatchSpec`/`p11PatchData_spec` do not state that `V/(2 pi)` lies in the actions of ordered axes
(so `p11SecularMatrix_eq` and the analytic family `coeffs (axis .)` were not directly applicable).
Resolved without changing any signature: the physical delta-tube bound gives it on `K`
(`p11_axis_mem_axes`), and the frame is built on `actionDomain` (open) around `Lambda0`. No change
requested.

## Checks (all one process at a time, LEAN_NUM_THREADS=1)
* Gate: `inp_lake_build.sh /root/code/KAM-inp-p11ap2b KAM.Planetary.Preparation.{HoloFrame,HoloScalar,
  HoloData,HoloLift}` -> "Build completed successfully (9269 jobs)"; no warnings in my files.
* `scripts/lint_sources.sh`: only "KAM.lean is out of date; run scripts/gen_root_imports.py"
  (generated; not edited — orchestrator must regenerate); `check_lean_modules: PASS`,
  FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
* `#print axioms` of `p11_holo_data`, `p11_holo_frame`, `p11_axis_mem_axes`,
  `p11_jet_bound_complex`, `fderiv_p11HoloH`, `p11ChartInput_eq_liftInv`,
  `P11HoloData.chartInput_eq_liftInv`, `P11HoloData.lift_bounds`: all
  `[propext, Classical.choice, Quot.sound]`.
* grep: no `sorry`, `maxHeartbeats`, `EuclideanSpace`; all lines <= 100 columns.

## Uncertainties / errata / deviations
No errata found; no deviation. Not done (out of scope): P2c strip/F, P2d chart (hc-id/lat), P2e
mean, signed `holo_chart`.

ORCHESTRATOR RULING (OVERNIGHT 20:40): P11A-P2 is split; P2b owns items 1-2 of the P2 handoff map (data choice for holo_chart as ONE interface P11HoloData with an existence theorem, and step hc-lift). holo_chart itself is assembled later by P2f; hc-strip/hc-F (P2c), hc-id/hc-lat (P2d), hc-mean (P2e) are not findings here.

AUDIT FOCUS: design docs/tracks/P/design/P11A-LEAN-DESIGN.md (holo_chart and steps stepP:p11:hc-rot, hc-lift) and its node table; P11A design audits; signatures /root/code/KAM-inp/.drafts/design/P11ASignatures.lean (P11SecularSpec, P11SecularFullSpec, p11ChartInput). Check: every P11HoloData Prop field is VERBATIM the corresponding P11SecularSpec/FullSpec conjunct (with C.x replaced by the field) and p11_holo_data proves them; hc-lift (p11ChartInput = SecularSpectrum.liftInv of the T1-converted real lift on real points; the two bounds) is the literal step. P11A-P2 files (Holomorphic, HolomorphicRotation, Polar) are in their own audit. Audit ONLY KAM/Planetary/Preparation/{HoloFrame,HoloScalar,HoloData,HoloLift}.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

# P11A-P2e prover handoff (branch inp-p11ap2e, acf60b35; contains P11A-P2b, P2c and P2; offloaded package run by the main orchestrator)


Hard rules observed: no heartbeat overrides; all files <= 343 lines; no sorry/axiom/admit/unsafe/opaque;
no EuclideanSpace; no frozen/manifest/KAM.lean/README edits; no provider import; lines <= 100.

## Files (new; committed)
- `Preparation/HoloMeanSchwarz.lean` (147): `p11_iteratedDeriv_eq_factorial_dslope`, `p11_jets_zero_of_real_bound`
  (holomorphic g with |g t| <= C|t|^k on the real axis has jets < k zero), `p11_radial_schwarz_diag`
  (radial Schwarz on any finite-dim complex normed space, jet hypothesis on diagonal values, v in the ball).
- `Preparation/HoloMeanReal.lean` (149): `p11hsInput_real` (complexified lift at a real point = `liftInv R` after T1),
  `p11hsF_real_eq` (F at real working points = `perturbation D false (liftInv R (assemble Λ (2π θ) y x))`).
- `Preparation/HoloMeanAvg.lean` (66): `p11_torusAverage_eq_avg` (unit-cube average of φ(2π·) = `SecularForm.avg φ`).
- `Preparation/HoloMeanHolo.lean` (147): `p11_fastMean_differentiableOn` (F_0 jointly holomorphic in (J,z) on
  `p11MeanDom`, via `holomorphic_parametric_integral_gen`), `isOpen_p11WorkingDom`, `p11MeanDom`.
- `Preparation/HoloMeanJets.lean` (189): `p11_jets_zero_gen` (real O(|z|^k) bound for each real J ⇒ all complex
  z-jets < k vanish for every complex J, via line restriction, `p11_real_slice_identity` in z, then in J).
- `Preparation/HoloMean.lean` (343): `p11_mean_real_value`, `p11_mean_Omega_real`, `p11_mean_real_bound`
  (uses `SecularSpectrum.diagonalize` (d)), `p11_Omega_norm_le`, `p11MeanM0`, and the main result:

```
theorem p11_hc_mean (D) (d : P11HoloData D) {a} (ha : a ∈ axes n)
  (h : P11HsHyp (p11PhysicalData D) a d.rho d.J0 d.rC σ rz B B' r' σ')
  (hΩ : ∀ J, ‖J - d.J0‖ < 2*d.rC → ∀ i, (d.Omega (ι J) i).im = 0)
  {M} (hM : p11MeanM0 D d a rz ≤ M) :
  ∀ J ∈ ball (ι d.J0) (2*d.rC), ∀ z : P11Phase n, ‖z‖ < rz →
    ‖p11FastMean F J z - p11FastMean F J 0 - ∑ i, d.Omega J i*(z.1 i^2+z.2 i^2)/2‖ ≤ M*(‖z‖/rz)^4
```
with `F = p11hsF (p11PhysicalData D) d.rho`. This is the mean clause of `P11SecularSpec` with `C J := F_0(J,0)` and
`MF := M` (any M >= `p11MeanM0 = 2 MInf + n (2π L) rz²`; P2f takes MF >= max(coth^n * MInf, p11MeanM0, 1); enlarging MF keeps
the sup-bound clause true).

## For P2f
- Use `C := fun J => p11FastMean F J 0`; mean clause = `p11_hc_mean` with `MF`.
- PREMISE `hΩ` (realness of `d.Omega` on real points) is NOT a field of `P11HoloData` (its `freq` field only gives `.re`).
  It holds for the construction in `p11_holo_data` (Omega = 2π • G, G the `p11_complexification` of varpi∘natAdd, so
  `Omega (ι J) = ι (2π varpi ..)`); P2b/P2f should add `Omega_real` as a field/lemma. Not a conclusion-shaped hypothesis
  (typing datum on the data).
- `P11HsHyp` instantiation is the same as for `p11hs_F` (same `h`).

## Checks
- Gate: `inp_lake_build.sh .. KAM.Planetary.Preparation.HoloMean` -> "Build completed successfully (9280 jobs)".
- `#print axioms` of `p11_hc_mean`, `p11_mean_real_bound`, `p11_jets_zero_gen`, `p11_radial_schwarz_diag`,
  `p11_fastMean_differentiableOn`: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: only "KAM.lean is out of date" (generated; not edited); check_lean_modules PASS; frozen/ABI OK.
- grep: no sorry / maxHeartbeats / EuclideanSpace; lines <= 100.

## Uncertainties / errata / deviations
- No errata; no signature touched. Deviation from brief: the result is `p11_hc_mean` parametric in `P11HoloData`/`P11HsHyp`
  (as P2c), and `p11_radial_schwarz` (signed, on `Fin n → ℂ`) is not used directly: `p11_radial_schwarz_diag` is the same
  proof on `P11Phase n` with a diagonal jet hypothesis (the signed lemma needs full multilinear jets, which the
  identity theorem does not give without polarisation). Extra premise `hΩ` as above.
- `diagonalize` needs `2 ≤ n` (`D.n_ge`) — supplied.

ORCHESTRATOR RULING (OVERNIGHT 20:40): P11A-P2 is split; P2e owns item 5 (hc-mean), parametric where P2c is parametric; P2f assembles holo_chart. holo_chart itself is not a finding here.

AUDIT FOCUS: design docs/tracks/P/design/P11A-LEAN-DESIGN.md (holo_chart, step stepP:p11:hc-mean) and its node table; P11A design audits; signatures /root/code/KAM-inp/.drafts/design/P11ASignatures.lean (the mean clause of P11SecularSpec/P11SecularFullSpec: F_0 holomorphic, real values, |F_0| <= MF (|z|/rz)^4). Check the exported result has exactly that clause's shape (or a form P2f can instantiate without new mathematics), with no hypothesis the assembly cannot discharge from P2b/P2c data. P2b/P2c files passed their own audits. Audit ONLY KAM/Planetary/Preparation/HoloMean*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

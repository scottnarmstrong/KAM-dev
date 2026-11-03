# Handoff B2-CAUCHY

Files: `KAM/EffectiveStability/Cauchy.lean` (214 lines, new). Namespace `KAM.EffectiveStability`.

Lemmas (signatures; `P := (Fin n → ℂ) × (Fin n → ℂ)`, `ι := realInclusion₂ n`):
- `norm_fderiv_le_of_closedDisc {E} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {U} (hU : IsOpen U)
  (hf : DifferentiableOn ℂ f U) {z} (e : E) {δ M} (hδ : 0 < δ) (hsub : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → z + ζ • e ∈ U)
  (hM : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → ‖f (z + ζ • e)‖ ≤ M) : ‖fderiv ℂ f z e‖ ≤ M / δ`  (item 1, general direction)
- `norm_fderiv_coord_le`: same with set-form hypotheses `{w | ∃ ζ : ℂ, ‖ζ‖ ≤ δ ∧ w = z + ζ • e}`.
- `cpolydisc z δ`, `fst_mem_cpolydisc`, `snd_mem_cpolydisc`.
- `norm_fderiv_fst_le_of_cpolydisc` / `norm_fderiv_snd_le_of_cpolydisc` (item 2): `(hU) (hf) (hδ : 0<δ)
  (hsub : cpolydisc z δ ⊆ U) (hM : ∀ w ∈ cpolydisc z δ, ‖f w‖ ≤ M) (i) : ‖fderiv ℂ f z (Pi.single i 1, 0)‖ ≤ M/δ` (resp. `(0, Pi.single i 1)`).
- `fderiv_realPart_eq (hU) (hf) (hx : ι x ∈ U) (v) : fderiv ℝ (fun y => (f (ι y)).re) x v = (fderiv ℂ f (ι x) (ι v)).re` (item 3, no reality hypothesis).
- `abs_fderiv_realPart_fst_le`, `abs_fderiv_realPart_snd_le` (item 3 bounds, premises at `z = ι x`).
- `abs_actionBracket_le_of_cauchy` (item 4): `|x.1 j * F' x (0, single j 1) - x.2 j * F' x (single j 1, 0)| ≤ (|x.1 j| + |x.2 j|) * (M/δ)` with `F' = fderiv ℝ (fun y => (f (ι y)).re)`.
- `geometric_tail_identity` (helper), `hasSum_nat_mul_geometric_tail`, `sum_range_nat_mul_geometric_tail_le` (item 5), as requested.
- `smoke_coord` (item 6): `‖fderiv ℂ (fun w : P => w.1 i) z (single i 1, 0)‖ ≤ (‖z.1 i‖ + δ)/δ`.

Approach: one-variable `g ζ = f (z + ζ • e)`, `DiffContOnCl` on the ball, `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`;
`deriv g 0 = fderiv ℂ f z e` by the chain rule. Real slice by `HasFDerivAt.restrictScalars` and `Complex.reCLM`. Tail by
`hasSum_coe_mul_geometric_of_norm_lt_one` + `hasSum_nat_add_iff'` + induction on `d`.

Signature changes: none (item 1 stated generally in `norm_fderiv_le_of_closedDisc`; the requested set-form is `norm_fderiv_coord_le`).

Checks: `b_build.sh ... KAM.EffectiveStability.Cauchy`: Build completed successfully, no warnings.
`sh scripts/lint_sources.sh`: 25 tests OK, FROZEN-ANCHOR GUARD OK, ABI HASHES OK. Line-length check output: `[]`.
`#print axioms` of all 11 declarations: `[propext, Classical.choice, Quot.sound]`.

Design signals: none (no heartbeat issue). Uncertainties: none. Errata/deviations: none.

## AUDIT FOCUS (kam-b1)
Track B, program B2 (overnight D71; nothing frozen; scope OD-B7). Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B2-CAUCHY.md
and brief-B1-common.md; design: program-b-plan §3.2 (/root/code/KAM/docs/explorations/program-b-plan.md lines 341-420:
"an analytic tail bounded by E ... contributes at most E/δ"). Consumer: B1-E's hRη (KAM/EffectiveStability/Oscillator.lean),
via the bracket form `x.1 j * ∂_{p_j}F - x.2 j * ∂_{q_j}F`. Check: (1) each lemma true as stated, minimal premises, no
conclusion-shaped hypotheses; (2) the Cauchy estimate's disc/radius bookkeeping (closed disc of radius δ in U, M bound
on it); (3) the real-slice identity holds without any reality hypothesis; (4) the tail identity and partial-sum bound
(edge cases d = 0, x = 0); (5) hygiene (AGENTS rules 3, 4, 7, line length ≤ 100), names, axioms. Memory rule: every
lean/lake call wrapped in `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.

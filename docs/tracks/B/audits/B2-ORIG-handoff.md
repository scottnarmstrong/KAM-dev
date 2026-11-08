# Handoff B2-ORIG

Files: KAM/EffectiveStability/OscillatorPhysical.lean (249 lines), OscillatorPhysicalSmoke.lean (60).

Lemmas (namespace KAM.EffectiveStability; premises of the step theorem copied):
- realFlow_coord_sub_le: |t|<=1 displacement |t|*eps*delta per coordinate of realFlow on realInterior W Ω 1.
- stepChart_sub_le / stepChartInv_sub_le: ∀ i, |(Ψ x).1 i - x.1 i| ≤ ε*δ ∧ |(Ψ x).2 i - x.2 i| ≤ ε*δ
  (premises: hχ hδ hε0 hε ρl hρl hq hp, hx : x ∈ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) 1).
- stepChart_stepChartInv: stepChart χ ρ (stepChartInv χ ρ z) = z for z in that realInterior.
- oscillatorAction_sub_le (x y j) {e s s'} (|x.1 j - y.1 j| ≤ e) (|x.2 j - y.2 j| ≤ e)
  (|x.1 j|,|x.2 j| ≤ s) (|y.1 j|,|y.2 j| ≤ s') : |A x j - A y j| ≤ e*(s+s')   [sharp, asymmetric form].
- oscillatorStep_physical: premises of oscillatorStep_confinement, plus (a' s d : Fin n → ℝ),
  hs0: 0 ≤ s i; hs1: 2*a' i ≤ s i^2; hs2: s i + ε*δ + δ < ρ; hs3: (s i + ε*δ)^2 ≤ a i;
  hd: ε*δ*(2*r j + ε*δ) ≤ d j; z₀ with A z₀ j ≤ a' j.
  Conclusion: ∃ T₁>T, z, z 0 = z₀, ODE on Ioo(-T₁,T₁), uniqueness (as B1-E, y 0 = z₀), and ∀|t|≤T, ∀j:
  |A(z t) j - A z₀ j| ≤ 2*d j + η j*|t| ∧ A(z t) j ≤ a j + η j*T + d j.
- physicalSmoke_zeroDrift (harmonic oscillator, χ=0, ε=0, d=0).

Approach: w₀ = Ψinv z₀; displacement gives Ψ w₀ = z₀ and A(w₀) ≤ a (via hs3). Apply the step theorem at w₀.
For each t, u = Ψinv(z t): A(u) ≤ a+ηT < b, so u ∈ oscClosed b ⊆ realInterior 1 and |u coords| ≤ r (from 2b ≤ r^2);
displacement of Ψ at u (Ψ u = z t from the theorem) gives |z t - u| ≤ εδ, so |z t coords| ≤ r+εδ. Same for z₀ vs w₀
(|w₀| ≤ r since A(w₀) ≤ a ≤ b). Triangle inequality with the sharp perturbation lemma. Hence only ONE d-premise (uses r,
not s) is needed; the Ψinv displacement is needed only at z₀ (not at z t).

Signature changes: none (d premise is exactly ε*δ*(2*r j + ε*δ) ≤ d j, as requested). hs3 and the s-bounds are used only
at t=0.

Checks: b_build of OscillatorPhysical and OscillatorPhysicalSmoke succeed, no warnings; scripts/lint_sources.sh OK
(25 tests, guards OK); line-length check empty after rewrapping one line; main_shortname_check rc=0;
#print axioms of all six main results: propext, Classical.choice, Quot.sound only.
Design signals: none. Errata: none. Uncertainties: none.

## AUDIT FOCUS (kam-b1)
Track B, program B2 (overnight D71; nothing frozen; scope OD-B7). Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B2-ORIG.md
and brief-B1-common.md; plan §2.2 last paragraph ("To claim a user-specified original box Q, prove Q ⊆ Ψ({|J_j|≤a_j}) using
the inverse chart. Defining an image region alone does not prove that it contains the requested physical initial data")
and (B1-transfer) (/root/code/KAM/docs/explorations/program-b-plan.md lines 140-160). Dependencies landed and audited:
B2-STEP oscillatorStep_confinement, B2-REALFLOW, B2-DOM. Scope: prover commit a8599414c and the merge of inp-b1. Check:
(1) oscillatorStep_physical's premises are B2-STEP's plus explicit finite inequalities (hs0-hs3, hd) only; the initial
condition is on the PHYSICAL point z₀ (original coordinates), and the conclusion's solution starts at z₀ itself;
(2) the inverse-chart step genuinely proves z₀ = Ψ(Ψinv z₀) with Ψinv z₀ in the chart initial box (no assumption that
z₀ lies in an image); (3) the displacement bounds (realFlow_coord_sub_le: max-norm, gauge δ) and the perturbation
lemma; (4) the physical drift 2d + η|t| and level bound a + ηT + d follow; uniqueness clause as in B1-E; (5) smoke
test; (6) hygiene (AGENTS rules 3, 4, 7; widths ≤ 100), names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.

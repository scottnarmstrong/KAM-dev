# Handoff B2-STEP (branch inp-b2step)

## Files (all under KAM/EffectiveStability/)
- `Poly/Lie.lean` (new, 187 lines): `cartLieSum`, `cartEval_lieSum`, `cartEval_lieSum_complex`, `cartFits_lieSum`,
  `cartPow`, `cartActProd`, `cartActSubst`, `cartActOnly` (Bool), `cartEval_actSubst`, `cartEval_actSubst_real`, smoke `decide +kernel`.
- `OscillatorStep/Remainder.lean` (145): `stepRem`, `smallField_of_supBound`, `differentiableOn_stepRem`,
  `norm_stepRem_le`, `stepRem_realInclusion₂`, `cartEval_realInclusion₂(_im)`, `differentiableOn_cartEval`.
- `OscillatorStep/Drift.lean` (142): `differentiableAt_realPart`, `chartRemainder_eq`, `stepDrift_le`.
- `OscillatorStep.lean` (121): `stepChart`, `stepChartInv`, `oscillatorStep_confinement`.
- `OscillatorStep/Smoke.lean` (60): `stepSmoke_zeroDrift` (harmonic oscillator, chi=0, H=cartAction 0, Nact=cartQVar 0, P=0, L=1).
- `Poly.lean` (facade, edited): added `public import ...Poly.Lie`; rewrapped one >100-char docstring line (pre-existing B2-POLY line 16).

## Main signature (exact)
```lean
def stepChart (χ : CartPoly) (ρ : ℝ) : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w) (cpolyOpen ρ) 1
def stepChartInv ... := realFlow ... (cpolyOpen ρ) (-1)

theorem oscillatorStep_confinement {H χ Nact P : CartPoly}
    (hH : CartFits n H) (hχ : CartFits n χ) (hN : CartFits n Nact) (hP : CartFits n P)
    (hA : cartActOnly Nact = true) {L : ℕ} (hL : 1 ≤ L)
    (hid : cartEqCheck (cartLieSum χ H L) (cartAdd (cartActSubst Nact) P) = true)
    {ρ δ δc ε : ℝ} (hδ : 0 < δ) (hδc : 0 < δc) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (ρl : List ℚ) (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ)
    (hq : ∀ i : Fin n, ((cartSupBound (cartDq i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    (hp : ∀ i : Fin n, ((cartSupBound (cartDp i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    (a b η : Fin n → ℝ) (εb T : ℝ) (hεb : 0 < εb) (hT : 0 ≤ T)
    (rl : List ℚ) (r : Fin n → ℝ) (hrl : ∀ i : Fin n, ((rl.getD i 0 : ℚ) : ℝ) = r i)
    (hr0 : ∀ i, 0 ≤ r i) (hdom1 : ∀ i, 2 * (b i + εb) ≤ r i ^ 2) (hdom2 : ∀ i, r i + δ < ρ)
    (hdom3 : ∀ i, r i + δc + δ / 2 < ρ) (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((cartSupBound (cartBracket (cartAction j) P) rl rl : ℚ) : ℝ) ≤
      η j - 2 * r j * ((cartSupBound (cartAdPow χ L H) ρl ρl : ℚ) : ℝ) / ((L.factorial : ℝ) * δc))
    (hmargin : ∀ j, a j + T * η j < b j) (w₀) (hw₀ : ∀ j, oscillatorAction w₀.2 w₀.1 j ≤ a j) :
    ∃ T₁, T < T₁ ∧ ∃ z, z 0 = stepChart χ ρ w₀ ∧ (...B1-E conclusion with V = univ,
      H := fun w => cartEval H w, Ψ := stepChart χ ρ, Ψinv := stepChartInv χ ρ ...)
```
Full conclusion = that of `oscillator_confinement` (copied verbatim, `z t ∈ univ` kept).
Proved by instantiating `oscillator_confinement` with `N I := cartEval Nact (I, 0)`,
`R w := cartEval H (Ψ w) - N (oscillatorAction w.2 w.1)`.

## Deviations from the brief (names/shape; not mathematical)
- B2-POLY actual names used (`cartEval`, `cartAdPow`, `cartSupBound`, `cartEqCheck`, `CartFits`); the brief's "supBound ... ρ"
  takes `List ℚ` radii, so radii enter as rational lists `ρl`, `rl` plus typing equalities `hρl`, `hrl` (data, not conclusions).
  `ρ δ δc ε η r` stay real; the majorant/drift inequalities are real inequalities between casts of `ℚ` values.
- `ActOnly` is the Bool `cartActOnly`. `cartActSubst Nact` replaces `q_i ↦ cartAction i`; the eval lemma needs `CartFits n Nact`.
- Remainder bound `B/L!` on the Cauchy disc, via `taylor_lie` directly (not `real_taylor_lie_bound`), because Cauchy needs the complex `Rem`.
- `hdom1` is `2*(b+εb) ≤ r²` as requested; `2 b ≤ r²` (used for the radius bridge) is derived.

## Checks
- Builds (b_build.sh, one module at a time, no warnings): Poly.Lie, Poly, OscillatorStep.Remainder, .Drift, OscillatorStep, .Smoke: all "Build completed successfully".
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, unit tests OK, FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
- Line length script: `[]` (exit 0). Short-name check: "short-name check OK (no reused public short name)" (renamed one helper `getD_eq_zero_of_all` -> `cartGetD_eq_zero_of_all` after a collision).
- `#print axioms` of `oscillatorStep_confinement`, `stepSmoke_zeroDrift`, `stepDrift_le`, `norm_stepRem_le`, `smallField_of_supBound`,
  `cartEval_actSubst`, `cartEval_lieSum_complex`: all `[propext, Classical.choice, Quot.sound]`.
- No `maxHeartbeats`, no file > 190 lines.

## Design signals / uncertainties / errata
- No heartbeat problems. No defects found in B2-POLY / B2-DOM / B2-REALFLOW / B2-CAUCHY statements used.
- Only erratum: pre-existing `Poly.lean` docstring line was 101+ chars (landing-lint failure); fixed by rewrap.
- The theorem as stated was true; no extra premise needed. Note `hL : 1 ≤ L` is required (taylor_lie order ≥ 1).
- Smoke test uses `ε = 0`, `η = 0`, rational lists `[5]`, `[2]` with n = 1.

## Post-handoff changes (kam-b1)
Merged inp-b1 (B2-POLY F1 fix, B2-DOM/B2-COMPOSE audits, B2-COMPOSE ChartChain.lean); resolved the Poly.lean facade
docstring conflict by keeping the B2-STEP wording (which documents Poly.Lie). Rebuilt; widths and short names OK.

## AUDIT FOCUS (kam-b1)
Track B, program B2 (overnight D71; nothing frozen; scope OD-B7). This is the plan's "checker soundness" for ONE
generator (program-b-plan §3.1 soundness shape and §3.2 (Lie), /root/code/KAM/docs/explorations/program-b-plan.md lines
300-420). Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B2-STEP.md and brief-B1-common.md. Audit scope: the B2-STEP commit
4e0cba8e3 (Poly/Lie.lean, OscillatorStep{,/Remainder,/Drift,/Smoke}.lean, the Poly.lean facade import) and the merge.
B2-POLY, B2-DOM, B2-REALFLOW, B2-CAUCHY, B2-COMPOSE and B1 are already audited (docs/tracks/B/audits/). Check:
(1) `oscillatorStep_confinement`: EVERY premise is finite data, an exact Bool check (cartEqCheck, cartActOnly), a typing
fact (CartFits) or a real/rational inequality between explicit numbers — none mentions the flow, the remainder, the
chart, or confinement (no conclusion-shaped premise); (2) its conclusion is exactly oscillator_confinement's for
V = univ, physical H = cartEval H, Ψ = stepChart, Ψinv = stepChartInv; (3) TRACE the remainder chain: the exact
identity (hid) + real-coefficient reality gives R = P + Re Rem∘ι on the real chart domain; |Rem| ≤ B/L! on the Cauchy
discs via taylor_lie with the trajectory in the polydisc; Cauchy gives the 2 r_j B/(L! δc) term; the poly part
by cartSupBound; their sum ≤ η_j by hdrift; (4) the domain premises (hdom1-3, ρl/rl typing equalities) suffice for all
inclusions used; (5) smoke test genuinely instantiates the theorem; (6) hygiene (AGENTS rules 3, 4, 7; widths ≤ 100),
names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.

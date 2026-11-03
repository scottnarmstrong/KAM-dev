# Handoff B2-MULTI (branch inp-b2multi, off inp-b2step)

## Status
COMPLETE for general m (list of generators); no two-generator fallback needed. 918 lines total, no file > 230.

## Files (new, all under KAM/EffectiveStability/)
- `OscillatorChain.lean` (106): `osc_subset_oscBox`, main theorem `oscillatorChain_confinement`.
- `OscillatorChain/Basic.lean` (153): data `OscStep`, `oscStepFlow`, `oscChainTheta`, `oscChainRem`, `oscTail`,
  `oscChainBound`, predicates `OscStepOK`, `OscLieOK`, `OscChainOK`, `OscDomOK`, `OscBound`.
- `OscillatorChain/Remainder.lean` (165): complex side. `oscChainDom`, `oscChainDom_isOpen_and_differentiableOn`,
  `oscChainTheta_oscBound`, `differentiableOn_oscChainRem`, `norm_oscChainRem_le`.
- `OscillatorChain/Domain.lean` (229): real side. `oscBox`, `oscChainMap`, `oscChainInv`, `oscStep_isCanonicalChart`,
  `oscChain_isCanonical` (via `ChartChain.lean`), `oscChainMap_realInclusion`, `oscChain_identity` (telescoped Lie identity).
- `OscillatorChain/Drift.lean` (139): `driftAbstract_le` (abstract Cauchy argument, generalizes `stepDrift_le`),
  `chainDrift_le`.
- `OscillatorChain/Smoke.lean` (126): `oscillatorStep_of_chain` (B2-STEP's theorem for rational radii, derived from the
  chain theorem on a one-element chain), `chainSmoke_zeroDrift` (2 zero generators, harmonic oscillator).

## Data and premises (no Prop field states a conclusion)
```lean
structure OscStep where  gen out : CartPoly;  order : ℕ;  ρ δ ε : ℚ
def OscLieOK (gen Q out : CartPoly) (L : ℕ) : Prop :=
  out = cartLieSum gen Q L ∨ cartEqCheck (cartLieSum gen Q L) out = true
structure OscStepOK (n) (s : OscStep) : Prop   -- 0<δ, 0≤ε≤1/2, 1≤order, CartFits gen/out, and
   -- cartSupBound (cartDq/cartDp i gen) (replicate n ρ) (replicate n ρ) ≤ ε*δ   (∀ i)
def OscChainOK (n) (Nact P) : List OscStep → CartPoly → Prop
  | [], Q => cartEqCheck Q (cartAdd (cartActSubst Nact) P) = true
  | s :: l, Q => OscStepOK n s ∧ OscLieOK s.gen Q s.out s.order ∧ OscChainOK n Nact P l s.out
def OscDomOK (n) (r : Fin n → ℝ) (δc : ℝ) : List OscStep → Prop
  | [] => True
  | s :: l => (∀ i, r i + oscTail l + δ_s < ρ_s) ∧ (∀ i, r i + δc + oscTail l + δ_s/2 < ρ_s) ∧ OscDomOK n r δc l
-- oscTail (s::l) = ε_s δ_s + oscTail l ;  oscChainBound n (s::l) Q = cartSupBound (cartAdPow gen L Q) ρl ρl / L! + oscChainBound n l s.out
```
List order: outermost generator first, chart `Ψ = oscChainMap l = Φ_1 ∘ ⋯ ∘ Φ_m` (`oscChainMap (s::l) = stepChart s.gen s.ρ ∘ oscChainMap l`);
`oscChainInv (s::l) = oscChainInv l ∘ stepChartInv s.gen s.ρ` (reversed composition of time -1 flows). `Q_{k-1}` of the first
step is `H`; `OscLieOK` lets `out` be literally the unnormalized Lie sum (used for the 1-element reduction, avoids a reflexive
`cartEqCheck`).

## Main theorem (exact signature, KAM/EffectiveStability/OscillatorChain.lean)
```lean
theorem oscillatorChain_confinement {H Nact P : CartPoly}
    (hH : CartFits n H) (hN : CartFits n Nact) (hP : CartFits n P)
    (hA : cartActOnly Nact = true) {l : List OscStep} (hok : OscChainOK n Nact P l H)
    {δc : ℝ} (hδc : 0 < δc) (a b η : Fin n → ℝ) (εb T : ℝ) (hεb : 0 < εb) (hT : 0 ≤ T)
    (rl : List ℚ) (r : Fin n → ℝ) (hrl : ∀ i : Fin n, ((rl.getD i 0 : ℚ) : ℝ) = r i)
    (hr0 : ∀ i, 0 ≤ r i) (hdom1 : ∀ i, 2 * (b i + εb) ≤ r i ^ 2) (hdom : OscDomOK n r δc l)
    (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((cartSupBound (cartBracket (cartAction j) P) rl rl : ℚ) : ℝ) ≤
      η j - 2 * r j * (oscChainBound n l H : ℝ) / δc)
    (hmargin : ∀ j, a j + T * η j < b j) (w₀ : (Fin n → ℝ) × (Fin n → ℝ))
    (hw₀ : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = oscChainMap l w₀ ∧ ... 
```
The conclusion is `oscillator_confinement`'s with V = univ, physical H = `cartEval H`, Ψ = `oscChainMap l`,
Ψinv = `oscChainInv l` (full statement in the file; identical in shape to `oscillatorStep_confinement`).

## Approach
1. Per step, `OscStepOK.smallField` (from `smallField_of_supBound`) and `oscStep_isCanonicalChart`: real time-1 flow is a
   canonical chart (C², symplectic, left inverse `time -1`) from `oscBox r c` into `oscBox r (c+εδ)`, using
   `realFlow` lemmas of B2-REALFLOW and the displacement bound `norm_realFlow_sub_le`.
2. Chain: `oscChartSteps` feeds `ChartChain.chartChain_isCanonical` (B2-COMPOSE): `oscChain_isCanonical` on `oscBox r 0`;
   `mono_chart` to `osc (b+εb)` (`osc_subset_oscBox`) and target `univ`.
3. Telescoping (`oscChain_identity`): by induction on the list (peeling the OUTER generator),
   `Q(Ψ w) = Nact(I w) + P w + Re(oscChainRem l Q (ι w))`, `oscChainRem (s::l) Q z = stepRem s.gen Q ρ L (Θ_l z) + oscChainRem l s.out z`
   (B2-STEP's `stepRem`, pushed through the complex flows `Θ_l`; `oscChainMap_realInclusion`: `ι ∘ Ψ_l = Θ_l ∘ ι`).
4. Complex side: `oscChainDom l` (open; `Θ_l` stays in the half interior of every outer polydisc), `OscBound` (coordinates ≤ r+c)
   propagated by the displacement `‖flow z - z‖ ≤ εδ`; `norm_oscChainRem_le`: `‖oscChainRem l Q‖ ≤ ∑ B_k/L_k!` on Cauchy discs.
5. One Cauchy estimate on the SUM (`driftAbstract_le`), so the drift premise has the single term `2 r_j (∑ B_k/L_k!)/δc`; then
   `oscillator_confinement` exactly as B2-STEP.
Reduction: `oscillatorStep_of_chain` (rational ρ δ ε) is B2-STEP's statement proved from the chain theorem on
`[⟨χ, cartLieSum χ H L, L, ρ, δ, ε⟩]` (hid becomes the final check, step check is `Or.inl rfl`). Smoke: `chainSmoke_zeroDrift`.

## Checks (all run in /root/code/KAM-inp-b2multi)
- `b_build.sh` of Basic, Remainder, Domain, Drift, OscillatorChain, Smoke (in this order): each "Build completed successfully",
  no warnings from my files. (All under the default heartbeats; no `set_option` anywhere.)
- `sh scripts/lint_sources.sh`: `check_lean_modules: PASS ... OK (25 tests) / FROZEN-ANCHOR GUARD OK / ABI HASHES OK`.
- Line length (>100) script: `[]`.
- `main_shortname_check.py` on all 6 modules: `short-name check OK (no reused public short name)`.
- `#print axioms` of `oscillatorChain_confinement`, `oscillatorStep_of_chain`, `chainSmoke_zeroDrift`, `chainDrift_le`,
  `oscChain_isCanonical`, `oscChain_identity`: all `[propext, Classical.choice, Quot.sound]`.
- No `sorry/axiom/admit/maxHeartbeats` in the new files; nothing outside `KAM/EffectiveStability/OscillatorChain*` touched.

## Signature changes / deviations
None requested beyond the brief's free choice of formulation. Choices to note: data radii are `ℚ` (`ρ δ ε`), `δc`, `r`, `b`, `η` real
as in B2-STEP; `OscLieOK` is a disjunction (literal equality OR `cartEqCheck`); the final identity is a separate check at the end
of the list (`OscChainOK [] Q`), so the last `out` must be checked against `Nact(I)+P` (for a 1-step chain one may take `out` = the
literal Lie sum). Drift premise uses `oscChainBound` (sum of B_k/L_k!), not per-step terms (equivalent, one Cauchy estimate).

## Design signals
None (no heartbeat or memory problems; largest module Domain.lean builds in seconds in the 4 GB scope).

## Errata / defects in B2-STEP
None found. Observations (not defects): `oscillatorStep_confinement` takes real `ρ δ ε` plus a rational list `ρl` with `hρl`; this
package uses ℚ radii and `List.replicate n ρ` instead, which is why the reduction is stated for rational radii.

## Remaining work
Nothing for this package. Possible follow-ups: an `OscChainOK`/`OscDomOK` `Decidable` instance or Bool wrapper for a certificate
runner (the Props are conjunctions of `cartEqCheck` Bools, ℚ inequalities, and real inequalities on data; the real ones are
inequalities between rational data after casting).

## AUDIT FOCUS (kam-b1)
Track B, program B2 (overnight D71; nothing frozen; scope OD-B7). Generalizes the landed, audited B2-STEP
(oscillatorStep_confinement) to a finite chain of generators. Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B2-MULTI.md and
brief-B1-common.md; plan §3.2 (/root/code/KAM/docs/explorations/program-b-plan.md lines 341-420: composition of exact
flows; remainders propagated through later charts before adding). Scope: prover commit 6821b4bb5 (six
OscillatorChain modules) and the merge of inp-b1. Check: (1) every premise of oscillatorChain_confinement is finite data,
an exact Bool/structural check, typing or an explicit rational/real inequality — in particular OscStepOK, OscLieOK,
OscChainOK, OscDomOK are Props of finite checks only, none mentions flows, remainders or confinement; (2) the
TELESCOPING identity (oscChain_identity) and its list order (outermost first; Ψ = Φ_1 ∘ ⋯ ∘ Φ_m; Ψinv reversed);
(3) the complex-domain bookkeeping: inner flows keep Cauchy discs inside each outer step's half interior under
OscDomOK's radius budget (oscTail = Σ ε δ displacement); norm_oscChainRem_le's Σ B_k/L_k! bound; (4) one Cauchy
estimate on the sum is valid (holomorphy of the summed remainder on an open set containing the discs);
(5) oscillatorStep_of_chain really is B2-STEP's statement (for rational radii) and the 2-step smoke test instantiates the
theorem; (6) hygiene (AGENTS rules 3, 4, 7; widths ≤ 100), names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.

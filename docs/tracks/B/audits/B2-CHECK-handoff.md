# Handoff B2-CHECK

## Files
- `KAM/EffectiveStability/OscillatorCheck.lean` (198 lines, new; commit 4aaff24bc on `inp-b2check`).

## Declarations (KAM.EffectiveStability)
- `structure OscStepCert (n : ℕ)`: data only. `H χ Nact P : CartPoly`, `L : ℕ`, `ρ δ δc ε εb T : ℚ`,
  `a b η r : List ℚ`. (`n` is a phantom parameter, as requested.)
- `def cartFitsB (n) (P : CartPoly) : Bool`; `theorem cartFitsB_sound (h : cartFitsB n P = true) : CartFits n P`.
- `def OscStepCert.Bmaj (c) : ℚ` = `cartSupBound (cartAdPow c.χ c.L c.H) (replicate n c.ρ) (replicate n c.ρ)`.
- `def checkOscStep (c : OscStepCert n) : Bool`: cartFitsB for H χ Nact P, `cartActOnly`, `1 ≤ L`, `cartEqCheck` (Lie-sum
  identity), `0<δ`, `0<δc`, `0≤ε≤1/2`, `0<εb`, `0≤T`, and for all `i < n` (`List.range n`): hq, hp, `0≤r_i`,
  `2(b_i+εb) ≤ r_i²`, `r_i+δ<ρ`, `r_i+δc+δ/2<ρ`, `0≤η_i`, drift
  `cartSupBound (cartBracket (cartAction i) P) r r ≤ η_i - 2 r_i Bmaj/(L!·δc)` (computed in ℚ), `a_i+Tη_i<b_i`.
  The radius list for χ-majorants is `List.replicate n c.ρ`.
- `theorem checkOscStep_sound (c) (hc : checkOscStep c = true) (w₀) (hw₀ : ∀ j : Fin n, oscillatorAction w₀.2 w₀.1 j ≤ (c.a.getD j 0 : ℝ))`:
  conclusion of `oscillatorStep_confinement` with `ρ := (c.ρ:ℝ)`, `T := (c.T:ℝ)`, `a j := (c.a.getD j 0 : ℝ)`,
  `η j := (c.η.getD j 0 : ℝ)`, `H := c.H`, `χ := c.χ` (full statement in the file).
- Smoke: `harmonicCert : OscStepCert 1` (H=I₀, χ=0, Nact=q₀, P=0, L=1, ρ=5, δ=δc=1, ε=0, εb=1, T=1, a=[0], b=[1], η=[0], r=[2]);
  `harmonicCert_check : checkOscStep harmonicCert = true := by decide +kernel`; `harmonicCert_zeroDrift` feeds it to the soundness theorem.

## Approach
Unfold the Bool conjunction (`simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]`), project
each premise, cast ℚ→ℝ with `exact_mod_cast` (drift via `Rat.cast_le` + `simp`), supply `hρl` for `replicate`, then apply
`oscillatorStep_confinement`. `hrl` is `rfl` since `r i := (c.r.getD i 0 : ℝ)`.

## Checks
- `b_build.sh … KAM.EffectiveStability.OscillatorCheck`: Build completed successfully, no warnings.
- Kernel check elaboration: profiler for `decide +kernel` on `checkOscStep harmonicCert`: type checking 77.7 ms (whole file
  checks in ~3.5 s wall).
- `sh scripts/lint_sources.sh`: OK, FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
- Line-length script output: `[]`. Short-name check: OK (rc 0).
- `#print axioms`: `checkOscStep_sound`, `harmonicCert_zeroDrift`: [propext, Classical.choice, Quot.sound]; `cartFitsB_sound`: [propext, Quot.sound].
- `git diff --cached --stat`: only `KAM/EffectiveStability/OscillatorCheck.lean`.

## Deviations / signals / errata
None. No signature of `oscillatorStep_confinement` changed. No heartbeat issues. No suspected source errata.

## AUDIT FOCUS (kam-b1)
Track B, program B2 (overnight D71; nothing frozen; scope OD-B7). Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B2-CHECK.md
and brief-B1-common.md; target shape program-b-plan §3.1 ("checkNormalForm Hexpr c = true -> ... trajectory ... bounds",
/root/code/KAM/docs/explorations/program-b-plan.md lines 300-340). Dependency (landed, audited): B2-STEP's
oscillatorStep_confinement (KAM/EffectiveStability/OscillatorStep.lean). Check: (1) checkOscStep is a total computable
Bool over DATA only and encodes EVERY non-binder premise of oscillatorStep_confinement, faithfully (no premise dropped,
weakened or mis-indexed; i < n ranges; ℚ→ℝ casts of the drift term B/(L!·δc); replicate radius lists); (2)
cartFitsB_sound is correct; (3) checkOscStep_sound's conclusion is oscillatorStep_confinement's with the data cast
from c, and its only hypotheses are hc and the initial-box condition; (4) the smoke certificate is checked by kernel
evaluation (no native_decide / ofReduceBool in axioms); (5) hygiene (AGENTS rules 3, 4, 7; widths ≤ 100), names, axioms.
Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.

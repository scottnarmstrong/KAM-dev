# Handoff B2-ORIGCHAIN

## Files (new, in KAM/EffectiveStability/)
- OscillatorChainPhysical.lean (254 lines), OscillatorChainPhysicalSmoke.lean (67 lines). Nothing else touched.

## Declarations (public)
- `OscPhysDom (n) (s : Fin n → ℝ) : List OscStep → ℝ → Prop` — inverse-chain radius budget:
  `[] , _ ↦ True`; `st :: l, c ↦ (∀ i, s i + c + st.δ < st.ρ) ∧ OscPhysDom n s l (c + st.ε * st.δ)`.
- `oscStep_chart_sub_le`, `oscStep_inv_sub_le`, `oscStep_chart_chartInv` (OscStepOK wrappers of B2-ORIG lemmas).
- `oscChainMap_sub_le (hl : ∀ st ∈ l, OscStepOK n st) (hdom : OscDomOK n r δc l) (hx : x ∈ oscBox r 0) :
  ∀ i, |(oscChainMap l x).1 i - x.1 i| ≤ (oscTail l : ℝ) ∧ |(oscChainMap l x).2 i - x.2 i| ≤ (oscTail l : ℝ)`
- `oscChainInv_sub_le {s} (hl) {c z} (hdom : OscPhysDom n s l c) (hz : ∀ i, |z.1 i| ≤ s i + c ∧ |z.2 i| ≤ s i + c) :
  (∀ i, |(oscChainInv l z).1 i - z.1 i| ≤ oscTail l ∧ (same for .2)) ∧ oscChainMap l (oscChainInv l z) = z`
- `oscillatorChain_physical`: premises of `oscillatorChain_confinement` plus
  `(a' s d) (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, 2 * a' i ≤ s i ^ 2) (hs2 : OscPhysDom n s l 0)
  (hs3 : ∀ i, (s i + oscTail l) ^ 2 ≤ a i) (hd : ∀ j, oscTail l * (2 * r j + oscTail l) ≤ d j)
  (z₀) (hz₀ : ∀ j, oscillatorAction z₀.2 z₀.1 j ≤ a' j)`.
  Conclusion exactly as `oscillatorStep_physical` (T₁ > T, z 0 = z₀, ODE on Ioo (-T₁) T₁, B1-E uniqueness,
  `|A(z t) - A z₀| ≤ 2 d j + η j |t|` and `A(z t) ≤ a j + η j T + d j` for |t| ≤ T). Full signature in the file.
- `chainPhysicalSmoke_zeroDrift`: two zero generators on the harmonic oscillator (tails 0).

## Approach
Induction on the chain: forward displacement via `oscChain_isCanonical` (image in `oscBox r (tail)`) +
`stepChart_sub_le`; inverse displacement and `Ψ∘Ψinv = id` by induction generalizing the start point and
the offset c (OscPhysDom tracks prefix sums ε_jδ_j). Main theorem = B2-ORIG's proof with `ε δ ↦ oscTail l`;
w₀ = Ψinv z₀ feeds `oscillatorChain_confinement`; z 0 = Ψ w₀ = z₀. Used osc(b+εb) ⊆ oscBox r 0 for u = Ψinv(z t).
No requested signature changed; no extra premise beyond the OscPhysDom domain predicate (a finite radius
inequality, as requested "domain checks for the inverse chain").

## Checks
- `b_build.sh` of OscillatorChain, OscillatorPhysical, OscillatorChainPhysical, OscillatorChainPhysicalSmoke: all succeed, no warnings from my files.
- `sh scripts/lint_sources.sh`: 25 tests OK; FROZEN-ANCHOR GUARD OK; ABI HASHES OK.
- line-length script: `[]`. main_shortname_check.py: "short-name check OK", exit 0.
- `#print axioms` of oscillatorChain_physical, oscChainMap_sub_le, oscChainInv_sub_le, chainPhysicalSmoke_zeroDrift: all [propext, Classical.choice, Quot.sound].

## Design signals / uncertainties / errata
None (no heartbeat issues; files ≤ 254 lines). No suspected errata.

## AUDIT FOCUS (kam-b1)
Track B, program B2 (overnight D71; nothing frozen; OD-B7). Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B2-ORIGCHAIN.md and
brief-B1-common.md. Combines the landed, audited B2-ORIG (oscillatorStep_physical) with the audited B2-MULTI chain theorem
(batch 8 in landing); plan §2.2 last paragraph (original box via the inverse chart, /root/code/KAM/docs/explorations/
program-b-plan.md lines 140-160). Check: (1) oscillatorChain_physical's premises are oscillatorChain_confinement's plus
explicit finite inequalities only (hs0-hs3, hd, OscPhysDom — a finite radius budget, not conclusion-shaped); the initial
condition is on the PHYSICAL point z₀ and the solution starts at z₀; (2) the inverse-chain step genuinely proves
z₀ = Ψ(Ψinv z₀) with Ψinv z₀ in the chart box (OscPhysDom's prefix sums track displacements correctly, list order
outermost-first); (3) forward/inverse chain displacement bounds by oscTail; (4) physical drift and level bounds;
uniqueness as in B1-E; (5) smoke test; (6) hygiene (AGENTS rules 3, 4, 7; widths ≤ 100), names, axioms. Memory rule:
every lean/lake call wrapped in `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.

# Handoff B4-TORIGCHAIN

## Files (new, both under KAM/EffectiveStability/)
- `TorusChainPhysical.lean` (181 lines), `TorusChainPhysicalSmoke.lean` (59 lines). No other file touched.

## Declarations (exact signatures in the files)
- `def TChPhysDom (n) (q : Fin n → ℝ) : List TChStep → ℝ → Prop` — inverse-chain radius budget:
  per step `∀ i, q i + c + ρ' < ρ`, then `c + ε ρ'`.
- `theorem tchChainMap_sub_le {l} (hl : ∀ s ∈ l, TChStepOK n s) (hdom : TChDomOK n b r εb δc l)
  {x} (hx : x ∈ cyl (fun j => b j + εb)) (i) :
  |(tchChainMap l x).1 i - x.1 i| ≤ tchTailA l ∧ |(tchChainMap l x).2 i - x.2 i| ≤ tchTailJ l`
  (cast to ℝ).
- `theorem tchChainInv_sub_le {q l} (hl) {c z} (hdom : TChPhysDom n q l c) (hz : ∀ i, |z.2 i| ≤ q i + c) :
  (∀ i, |(tchChainInv l z).1 i - z.1 i| ≤ tchTailA l ∧ |(tchChainInv l z).2 i - z.2 i| ≤ tchTailJ l) ∧
  tchChainMap l (tchChainInv l z) = z`  (Ψ(Ψinv z) = z).
- `theorem torusChain_physical`: premises of `torusChain_confinement` (with `w₀ hw₀` replaced) plus
  `a'`, `hpa : ∀ i, a' i + tchTailJ l ≤ a i`, `hpd : TChPhysDom n a' l 0`, `z₀`,
  `hz₀ : ∀ j, |z₀.2 j| ≤ a' j`. Conclusion: ∃ T₁ > T, z with z 0 = z₀, Hamiltonian equation for
  `ftEvalR H` on Ioo (-T₁) T₁, B1-T-style uniqueness, and for |t| ≤ T, all j:
  `|(z t).2 j - z₀.2 j| ≤ 2 * tchTailJ l + η j * |t|` and
  `|(z t).2 j| ≤ a j + η j * T + tchTailJ l` (D = Σ ε_k ρ'_k = `tchTailJ l`).
- Smoke `tchChainPhysicalSmoke_zeroDrift`: two zero generators (`tchSmokeStep` twice), n = 1, a' = 0.

## Approach
Mirrors B2-ORIGCHAIN/B4-TORIG: forward/inverse displacement by induction on the chain using
`torusChart_sub_le`/`torusChartInv_sub_le`/`torusChart_torusChartInv` per step (real interior from
`cylClosed_subset_realInterior_cstrip`; forward uses `tchChain_isCanonical.chart_maps`). Then
w₀ = Ψinv z₀, apply `torusChain_confinement` to w₀, rewrite z 0 via Ψ(Ψinv z₀) = z₀, and bound
physical actions via |z t .2 − u .2| ≤ D with u = Ψinv (z t) ∈ cyl(b+εb). No signature change
from the brief; no conclusion-shaped premise (hpa/hpd are finite inequality checks).

## Checks
- `b_build.sh … KAM.EffectiveStability.TorusChainPhysical` → Build completed successfully; same for `…PhysicalSmoke`.
- `sh scripts/lint_sources.sh` → ABI HASHES OK, exit 0.
- line-length script → `[]`.
- `main_shortname_check.py` → short-name check OK (no reused public short name), exit 0.
- `#print axioms` of `torusChain_physical`, `tchChainInv_sub_le`, `tchChainMap_sub_le`,
  `tchChainPhysicalSmoke_zeroDrift`: all `[propext, Classical.choice, Quot.sound]`.

## Design signals / errata / uncertainties
None. No heartbeat issues; no changes to `torusChain_confinement` (under audit). Note `TChPhysDom` is
independent of `TChDomOK`; callers must supply both.

## AUDIT FOCUS (kam-b1)
Track B, program B4 (overnight D71; nothing frozen; OD-B11). Mirrors the landed, audited B2-ORIGCHAIN (OscillatorChainPhysical.lean) and B4-TORIG (TorusPhysical.lean) for the torus chain theorem
torusChain_confinement (B4-TMULTI, audit 1 PASS WITH NOTES; batch 12 in landing). Brief:
/root/code/KAM-inp-b1/.drafts/B/brief-B4-TORIGCHAIN.md and brief-B1-common.md. Scope: prover commit 4b4cb5c91 and the inp-b1 merge. Check:
(1) torusChain_physical's premises are torusChain_confinement's plus explicit finite inequalities only (TChPhysDom a finite radius budget); the initial condition is on the PHYSICAL z₀ and the solution starts at z₀; the inverse-chain step proves z₀ = Ψ(Ψinv z₀) with Ψinv z₀ in the chart box; chain displacement by the tails in the scaleCLE gauges; physical drift/level bounds; B1-T uniqueness; (2) smoke test genuinely instantiates the theorem; (3) hygiene (AGENTS rules 3, 4, 7; widths ≤ 100), names,
axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.

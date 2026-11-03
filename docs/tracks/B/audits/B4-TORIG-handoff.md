# Handoff B4-TORIG

## Files
- KAM/EffectiveStability/TorusPhysical.lean (~190 lines)
- KAM/EffectiveStability/TorusPhysicalSmoke.lean (~55 lines)

## Declarations (namespace KAM.EffectiveStability)
- `torusFlow_coord_sub_le (hσ' hρ') (hS : SmallField (scaleCLE ρ' σ' ..) (cstripOpen σ ρ) (hamiltonianVectorFieldℂ ftEvalC χ) ε) (hx : x ∈ realInterior .. (1/2)) (ht : t ∈ Icc (-1) 1)`:
  angles `≤ |t| ε σ'`, actions `≤ |t| ε ρ'` (via `norm_realFlow_sub_le`, `scaleCLE` gauge).
- `torusChart_sub_le`, `torusChartInv_sub_le`: `|Ψ x - x|` (resp. Ψinv) `.1 ≤ ε σ'`, `.2 ≤ ε ρ'` on realInterior (1/2).
- `torusChart_torusChartInv`: `Ψ (Ψinv z) = z` on realInterior W Ω 1.
- `torusStep_physical`: premises of `torusStep_confinement` plus
  `a' : Fin n → ℝ`, `hpa : ∀ i, a' i + ε * ρ' ≤ a i`, `hpρ : ∀ i, a' i + ρ' < ρ`, `z₀`, `hz₀ : ∀ j, |z₀.2 j| ≤ a' j`
  (w₀, hw₀ dropped). Conclusion: T₁ > T, z 0 = z₀, Hamiltonian equation for `ftEvalR H` on Ioo (-T₁) T₁,
  uniqueness, and for |t| ≤ T: `|(z t).2 j - z₀.2 j| ≤ 2*(ε*ρ') + η j*|t|` and `|(z t).2 j| ≤ a j + η j*T + ε*ρ'`.
- `torusPhysicalSmoke_zeroDrift`: n=1, H=J²/2, χ=0, ε=0.
- private `torus_smallField` (packages the SmallField derivation, same as in torusStep_confinement).

## Approach
Mirror of B2-ORIG. w₀ = Ψinv z₀ (z₀ in cylClosed a' ⊆ realInterior 1 since a'+ρ'<ρ); |w₀.2| ≤ a'+ερ' ≤ a; apply
torusStep_confinement at w₀ (Ψ w₀ = z₀); u = Ψinv(z t) has |u.2| ≤ a+ηT < b, so lies in cylClosed b ⊆ realInterior
(b+ρ'<ρ from hdom1); Ψ u = z t gives |z t - u| ≤ ερ'. Triangle inequality.

## Checks
- `b_build.sh` TorusPhysical, TorusPhysicalSmoke: Build completed successfully, no warnings.
- `sh scripts/lint_sources.sh`: 25 tests OK, FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
- line-length check: `[]`.
- main_shortname_check: OK, exit 0.
- `#print axioms` of all declarations above: [propext, Classical.choice, Quot.sound].

## Signature changes / design signals / errata
None. No heartbeat issues. TorusStep.lean untouched (under audit); no defects observed.
Note: `a' i + ρ' < ρ` is implied-style check; hdom1 gives b+ρ' ≤ ρ, so hpρ is a separate finite check (a' ≤ a ≤ b makes it automatic when a'+ερ'≤a and ε ≤ 1/2 only if ρ' > ... not in general; kept explicit).

## AUDIT FOCUS (kam-b1)
Track B, program B4 (overnight D71; nothing frozen; OD-B11). Torus analogue of the landed, audited B2-ORIG
(oscillatorStep_physical); plan §2.2 last paragraph (original box via the inverse chart; transfer with L = id),
/root/code/KAM/docs/explorations/program-b-plan.md lines 140-160. Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B4-TORIG.md
and brief-B1-common.md. Base torusStep_confinement (B4-TSTEP) is in a parallel audit; scope here: commit 11f02053c
(TorusPhysical{,Smoke}.lean). Check: (1) torusStep_physical's premises are torusStep_confinement's plus explicit finite
inequalities only (hpa, hpρ); the initial condition is on the PHYSICAL z₀ and the solution starts at z₀; (2) the
inverse-chart step proves z₀ = Ψ(Ψinv z₀) with Ψinv z₀ in the chart box; displacement bounds in the scaleCLE gauge
(angles ε σ', actions ε ρ'); (3) physical action drift/level bounds and B1-T uniqueness; (4) smoke; (5) hygiene
(AGENTS rules 3, 4, 7; widths ≤ 100), names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.

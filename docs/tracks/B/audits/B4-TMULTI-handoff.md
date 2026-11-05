# Handoff B4-TMULTI (worktree /root/code/KAM-inp-b4tmulti, branch inp-b4tmulti)

## Files (all new, under KAM/EffectiveStability/)
- TorusChain.lean (142 lines): `torusChain_confinement`, `tchChainMap_singleton`, `tchChainInv_singleton`, `torusStep_of_chain`
- TorusChain/Basic.lean (301): `TChStep`, `TChStepOK`, `TChChainOK`, `TChDomOK`, `TChBound`, `tchTheta`, `tchRem`, `tchDom`, `tchChainBound`, `tchTailA/J`, `tchTheta_bound`
- TorusChain/Remainder.lean (67): `differentiableOn_tchRem`, `norm_tchRem_le`
- TorusChain/Domain.lean (243): `tchChainMap/Inv`, `tchStep_isCanonicalChart`, `tchChain_isCanonical`, `tchChainMap_realInclusion`, `tchChain_identity`, `tchChainMap_angleShift`
- TorusChain/Drift.lean (84): `tchChainDrift_le`
- TorusChain/Smoke.lean (67): `tchSmokeStep`, `tchChainSmoke_zeroDrift` (2 steps, n=1, H=J0^2/2)

## Main signature
```lean
theorem torusChain_confinement {H Nact P : FTPoly}
    (hH : FTFits n H) (hP : FTFits n P) (hA : ftActOnly Nact = true) {l : List TChStep}
    (hok : TChChainOK n Nact P l H) {δc : ℝ} (hδc : 0 < δc) (a b η : Fin n → ℝ) (εb T : ℝ)
    (hεb : 0 < εb) (hT : 0 ≤ T) (bl : List ℚ)
    (hbl : ∀ i : Fin n, ((bl.getD i 0 : ℚ) : ℝ) = b i) (r : Fin n → ℝ) (hbr : ∀ i, b i ≤ r i)
    (hdom : TChDomOK n b r εb δc l) (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((ftAngleDriftBound P j ftPiUB bl : ℚ) : ℝ) +
      (tchChainBound n l H : ℝ) / δc ≤ η j)
    (hmargin : ∀ j, a j + T * η j < b j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j, |w₀.2 j| ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = tchChainMap l w₀ ∧ ...
      -- conclusion of torus_confinement with V = univ, H = ftEvalR H, Ψ = tchChainMap l, Ψinv = tchChainInv l
```
`torusStep_of_chain`: same with `l = [s]` and chart `torusChart s.gen σ ρ` (`tchChainMap [s] = torusChart ..` by `rfl`);
inputs are the step checks, `ftEqCheck (ftLieSum s.gen H s.order) s.out`, `ftEqCheck s.out (ftAdd Nact P)`, and the one-step radius inequalities.

## Approach
Torus counterpart of B2-MULTI built from B4-TSTEP pieces. Step record `TChStep` = (gen, out, order, σ, ρ, σ', ρ', ε, lam), all ℚ/FTPoly.
`TChChainOK`: per-step `TChStepOK` (positivity, σ'<σ, ε∈[0,1/2], strip check 2·ftPiUB·σ<1 and 1/(1-2 ftPiUB σ) ≤ lam, FTFits, majorants
`ftSupBound (ftDJ i gen) ≤ ε σ'`, `ftSupBound (ftDφ i gen) ≤ ε ρ'`) plus exact `ftEqCheck` per step and final `ftEqCheck Q_m (Nact+P)`.
`TChDomOK`: per step, `b+εb+(Σ_inner ε ρ')+ρ'_k ≤ ρ_k` (real chart), `δc+(Σ_inner ε σ')+σ'_k/2 < σ_k` and
`r+δc+(Σ_inner ε ρ')+ρ'_k/2 < ρ_k` (Cauchy disc). Complex side: Θ_l = composite complex flows, Rem_l = Σ pushed-forward `torusRem`s on
`tchDom l` (intermediate points in `cstripOpen (σ-σ'/2)(ρ-ρ'/2)`); budget propagation via `flow_a` (angles +εσ', actions +ερ').
Real side: each step is `IsCanonicalChart` from `cyl c` into `cyl c'` (c+ερ' ≤ c'); composed by `chartChain_isCanonical` (ChartChain),
domain `cyl (b+εb)`. Telescoped identity `Q(Ψw) = Nact(0,J) + P + Re Rem_l(ιw)`. Periodicity of `R = H∘Ψ - Nact∘J` from lattice
equivariance of every step chart (`realFlow_angleShift_equivariant`, `ftEvalC_add_period`) and `ftEvalR_add_period H`. One Cauchy estimate
(`abs_fderiv_realPart_fst_le`) on the summed remainder; polynomial part by `abs_fderiv_ftEvalR_le`. Then `torus_confinement`.

## Design choices / deviations (no requested signature was changed; the brief gave none)
- `π` is bounded by the fixed `ftPiUB` (not a free `πub`); the strip constant `lam` is per step.
- `ftEqCheck` only (no "literal Lie sum" alternative, unlike `OscLieOK`).
- Single global `δc` for all Cauchy discs; `bl`/`b`/`r` as in `torusStep_confinement`; per-step radius lists are `List.replicate n ρ_k`.
- Chain drift premise is stated with `tchChainBound = Σ_k B_k/L_k!` and one division by `δc`, as in the brief.
- No general-induction size problem: whole development is 904 lines (every file ≤ 301).

## Checks
- `b_build.sh` of TorusChain.{Basic,Remainder,Domain,Drift}, TorusChain, TorusChain.Smoke in import order: all "Build completed successfully", no warnings.
- `sh scripts/lint_sources.sh`: `OK / FROZEN-ANCHOR GUARD OK / ABI HASHES OK`.
- Line length check: `[]`.
- `main_shortname_check.py` over the 6 modules: `short-name check OK` (rc 0) after renaming 3 collisions (`tchStepsOK`, `tchLam_pos`, `tchSmallField`).
- `#print axioms` (scratch file) for `torusChain_confinement`, `torusStep_of_chain`, `tchChainSmoke_zeroDrift`, `tchChain_identity`,
  `tchChainDrift_le`: each `[propext, Classical.choice, Quot.sound]`.
- No `maxHeartbeats`, `sorry`, `axiom` in the new files; nothing outside KAM/EffectiveStability/TorusChain* touched.

## Design signals / errata
None. No elaboration or memory problems (each module builds in ~2 s). No errata found in pinned sources.

## AUDIT FOCUS (kam-b1)
Track B, program B4 (overnight D71; nothing frozen; OD-B11). Torus counterpart of the landed, audited B2-MULTI
(oscillatorChain_confinement), built on B4-TSTEP (audited) and B4-TDOM/FT (landed). Brief:
/root/code/KAM-inp-b1/.drafts/B/brief-B4-TMULTI.md and brief-B1-common.md; plan §3.2 (composition of exact flows;
remainders propagated through later charts), /root/code/KAM/docs/explorations/program-b-plan.md lines 341-420. Scope:
prover commit 5529d264c (six TorusChain modules) and the inp-b1 merge. Check: (1) every premise of torusChain_confinement
is finite data, exact Bool checks, typing or explicit rational/real inequalities — TChStepOK, TChChainOK, TChDomOK are
Props of finite checks only; (2) the telescoped identity and list order (outermost first; Ψinv reversed);
(3) complex-domain bookkeeping: inner flows move angles by ≤ Σ ε σ' and actions by ≤ Σ ε ρ', keeping Cauchy discs in
each step's half interior; Σ B_k/L_k! bound; (4) periodicity of R from per-step lattice equivariance (composition);
(5) one Cauchy estimate on the summed remainder; (6) torusStep_of_chain really is B4-TSTEP's content for a single step,
and the 2-step smoke instantiates the theorem; (7) hygiene (AGENTS rules 3, 4, 7; widths ≤ 100), names, axioms.
Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.

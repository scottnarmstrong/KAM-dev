# Handoff W1-ALGEBRA (track W, branch inp-wpf)

Off-frontier infrastructure; dependency graph still being built. Namespace `KAM.Wave`, ℤ-indexed sequences are plain `ℤ → ℂ`
(no Fin), memberships/norms are `Summable`/`tsum` predicates, with an `lp (fun _ : ℤ => ℂ) 2` transport.

## Files (new) — all under `KAM/Wave/Algebra/`, plus regenerated `KAM/Root/Wave.lean`
- `Young.lean` (231 lines): convolution, Cauchy–Schwarz, Young, ℓ² triangle, comm/assoc/mono/abs.
- `TwoSided.lean` (~263): weights, `WaveTwoMem`/`waveTwoNorm`, lp transport, ζ-sum, ℓ¹ control, convergence of convolution for a,s ≥ 0.
- `Algebra.lean` (205): weight inequality, the algebra, three-factor form.
- `Extension.lean` (381): E^±, even majorant, restriction with gain, pairing J.
Imports: Mathlib + `KAM.Frozen.Wave.Defs.{EllWeight,Lam}` only (no Seq/Normal, no theorem anchors/providers).

## Blueprint label -> Lean declarations
- `bpW:w1:twosided-transport`: `waveJap`, `waveTwoWeight`, `WaveTwoMem`, `waveTwoNorm`, `waveTwoToLp`, `waveTwoToLp_norm` (isometry),
  `waveTwoMem_of_lp` (inverse direction), `waveConv` (tsum convolution; summability proved before use).
- `bpW:w0:twosided` (convolution defined for a ≥ 0, s ≥ 0): `WaveTwoMem.summable_sq` (‖c‖_ℓ² ≤ ‖c‖_{a,s}), `wave_conv_summable`.
- `bpW:w1:twosided`:
  (i) `waveExt` (E^σ, any ‖σ‖=1 so both ±), `wave_ext_mem` (Mem a (p+1/2) and norm ≤ √2‖q‖), `waveExt_add`, `waveExt_smul`
      (linearity); majorant |E^+ q| is the same norm via `waveExt_norm_pos/neg`; even sequence `waveEvenMaj`,
      `wave_evenMaj_norm_sq` (‖x‖² = 2‖q‖²).
  (ii) `waveRestr`, `wave_restr_mem` (membership in ℓ^{a,p+1}, bound by the partial sum ≤ ‖X‖, and √2·(…) ≤ ‖X‖ if |X| even).
  (iii) `waveJ`, `waveJ_add`, `waveJ_smul`, `wave_J_norm_sq` (isometry), `wave_J_norm_le` (≤ √2 max), `wave_J_surj` (onto {w_0=0}).
- `bpW:w1:young`: (i) `wave_young`, `wave_young_sqrt_le`, `wave_young_real`; (ii) `wave_jap_hasSum_zeta` (Σ⟨l⟩^{-2s} = 1+2ζ(2s), Mathlib `riemannZeta`),
  `wave_l1_le_of_mem` (ℓ¹ ≤ √(1+2ζ(2s))‖·‖_{0,s} ≤ √(…)‖·‖_{a,s}), `wave_expl1_le` (weighted version used by the algebra);
  (iii) `waveConv_comm`, `waveConv_mono`, `norm_waveConv_le` (|c*d| ≤ |c|*|d|), `waveConv_assoc_l1` (ℓ¹), `wave_conv_assoc_of_mem` (ℓ^{0,s}, s>1/2).
- `bpW:w1:algebra` (= `bpW:w0n:algebra`): `wave_algebra` (absolute convergence, `WaveTwoMem a s (c*d)`, ‖c*d‖ ≤ `waveAlgConst s`·‖c‖‖d‖,
  `waveAlgConst s = 2^s * √(1 + 2 (riemannZeta (2s)).re)`), `wave_algebra_three` (K_s², left-assoc (c*d)*e).
- `bpW:w1:algebra-half`: not done (blueprint says not part of the plan, only s ≥ 1 is proved).

## Notes / deviations
- Statements are slightly more general than the blueprint where free: `wave_ext_mem` does not need a ≥ 0 and takes σ with ‖σ‖=1;
  `wave_expl1_le` needs only s>1/2 (a any real). Pairing/extension are stated at the level of functions ℕ+ → ℂ / ℤ → ℂ, not as bundled linear maps
  (linearity lemmas given); mono/|c*d| are generic with explicit summability hypotheses (use `wave_conv_summable`), stated for real nonneg / complex
  sequences, not wrapped for ℓ^{0,s}.
- Associativity (Young (iii)) is proved for ℓ¹ ⊇ ℓ^{0,s}(s>1/2) complex sequences (hence for nonneg ones cast to ℂ).
- Blueprint defects: none found. Cosmetic: in Step stepW:w0n:young "D' = D/⟨i⟩^s" is exactly `e^{a|i|}|d_i|` (used that way in Lean).

## Checks
- Gate builds (one at a time): `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpf KAM.Wave.Algebra.Extension KAM.Wave.Algebra.Algebra`
  tail: `✔ Built KAM.Wave.Algebra.Algebra` / `Build completed successfully (3255 jobs).` (Young and TwoSided built earlier and as dependencies.)
- `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpf`: exit 0 (`check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (158 frozen declarations)`)
  after `python3 scripts/gen_root_imports.py` (adds 4 lines to `KAM/Root/Wave.lean`, committed).
- `#print axioms` of wave_young, wave_young_sqrt_le, wave_l1_le_of_mem, wave_expl1_le, wave_algebra, wave_algebra_three, wave_conv_summable,
  wave_conv_assoc_of_mem, waveConv_comm, waveTwoToLp_norm, waveTwoMem_of_lp, wave_ext_mem, wave_evenMaj_norm_sq, wave_restr_mem, wave_J_norm_sq,
  wave_J_norm_le, wave_J_surj, wave_jap_hasSum_zeta: all `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, no `maxHeartbeats`/option overrides; all files < 400 lines. Names checked by grep against KAM and KAM-inp: no clashes
  (renamed `le_lam`/`lam_pos`/`ellWeight_sq_succ` to `wave_…`).

## Design signals
None; everything elaborates at default heartbeats. One recurring tip: `waveConv_summable_comm` needed explicit `(c := …) (d := …)` (higher-order unification timed out otherwise).

## AUDIT FOCUS (sub-orchestrator kam-d4)

This package is off the frontier: source-faithful infrastructure (blueprint-W w1-sequences.tex `bpW:w1:twosided-sec`;
w0-conventions `bpW:w0:twosided`). It has no provider and no seal, so skip audit item 1.
1. Statement fidelity: the two-sided weight ⟨l⟩, the norm, the convolution domain (a ≥ 0, s ≥ 0), the extension maps
   E^± with norm ≤ √2, the restriction with gain, the pairing J, Young (i)–(iii), and the algebra constant
   K_s = 2^s(1+2ζ(2s))^{1/2} for s ≥ 1, matching `bpW:w0n:algebra`.
2. Definitions on their whole carrier: `waveTwoNorm`, `waveConv` (a tsum convolution; is summability always proved
   before use, and is no junk value relied on?), `waveExt`, `waveRestr`, `waveJ`.
3. Function-level statements instead of bundled linear maps: is that adequate for the consumers (W1 trilinear and
   selection; W3 majorants)?
4. Hygiene. This is a SLIM worktree, so run lint only via `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpf`.
   Run the kernel replay of the 4 modules. Regenerated roots are authorized by the prover brief.

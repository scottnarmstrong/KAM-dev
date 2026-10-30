# Handoff SO-SHARPLINK (branch inp-sosharplink)

## Files
- `KAM/SpinOrbit/Graph/Cert.lean` (changed, 285 lines). New: `soGraph_exactTorus_of_certified`,
  `checkStatic_of_checkTorusCertificate`, `soRotBarrier_of_certified`. Landed statements unchanged;
  the PROOFS of `soGraph_exactTorus` and `soRotBarrier_of_cert` are now one-liners through the new
  lemmas (same statements, same names). `soBarrier_of_cert` (original frame) untouched.
- `KAM/SpinOrbit/Graph/CertSharp.lean` (new, 46 lines; imports Graph.Cert + KAM.CertificateSharp.Sound):
  `checkStatic_of_checkTorusCertificateSharp`, `soRotBarrier_of_certSharp`.
- `KAM/SpinOrbit/LunarAssemblySharp.lean` (new, 226 lines; imports LunarAssembly + Graph.CertSharp):
  `isDiophantine_of_le_gamma`, `lunarRotFreq_isDiophantine_params`, `soBarriers_of_band`,
  `soBarriers_of_band_rat`, `lunar_barriers_of_sharp`, `lunar_barriers_of_band`,
  `lunar_spin_confinement_of_band`, sanity `lunar_barriers_of_viaBand`,
  `lunar_spin_confinement_of_viaBand`.
- `LunarAssembly.lean`, `LunarParams.lean`, `RotFreq.lean` unchanged. `KAM.lean` NOT regenerated
  (rule 10): the orchestrator must run `scripts/gen_root_imports.py` (two new modules).

## Approach
Task 1: both certifiers yield `CertifiedTorus g.base ωstar` and both contain `checkStatic`. The
common lemma `soRotBarrier_of_certified` takes `checkStatic g.base = true`, `checkSoGraph g = true`,
`CertifiedTorus g.base ωstar` and the cert-form Diophantine premise (still needed by the graph
step for the Diophantine fact at `s∞ ω*`). `soRotBarrier_of_cert` and `soRotBarrier_of_certSharp`
are one-liners over it (old / sharp black box + static conjunct extraction).
Task 2: per torus, the cert-form Diophantine premise is derived from the SO-DION-shaped fact by
`τ = 1` and γ-antitonicity (`PL.γ ≤ κ γd`); then the barriers are combined by pure band algebra
(`soBarriers_of_band`, with `SoBarrier.widen`).
Task 3: done. `lunar_barriers_of_band` is the old-checker twin of `lunar_barriers_of_sharp` (same
hypotheses except the checker); `lunar_barriers_of_viaBand` has the landed `lunar_barriers_of`
statement verbatim and is proved from it (PL = lunarR1 errL dispL, κ = lunarR1Kappa, γd = 1/42,
band 967/1000..1033/1000, ν± = lunarNuMinus/Plus). Likewise `lunar_spin_confinement_of_viaBand`
(landed `lunar_spin_confinement_of` verbatim, δ = 33/1000). The sharp theorem cannot reproduce the
landed one directly because the landed one assumes the old check, not the sharp one.

## Full statements (namespace KAM.SpinOrbit)

```lean
theorem soRotBarrier_of_certified {α : Type} [CertArith α] [LawfulCertArith α]
    (g : SoGraphCert α) {c : ℚ} (hc0 : 0 < c) (hham : g.base.ham = soRotHamExprScaled c)
    (hs : checkStatic g.base = true) (hg : checkSoGraph g = true) {ωstar : Fin 2 → ℝ}
    (hT : CertifiedTorus g.base ωstar)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar) :
    Nonempty (SoBarrier ((g.pLo : ℝ) - g.base.params.disp) ((g.pHi : ℝ) + g.base.params.disp))

theorem soRotBarrier_of_certSharp [LawfulCertArith α] (g : SoGraphCert α) {c : ℚ} (hc0 : 0 < c)
    (hham : g.base.ham = soRotHamExprScaled c) (hc : checkTorusCertificateSharp g.base = true)
    (hg : checkSoGraph g = true) {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 g.base.freqBox ωstar)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar) :
    Nonempty (SoBarrier ((g.pLo : ℝ) - g.base.params.disp) ((g.pHi : ℝ) + g.base.params.disp))

theorem lunar_barriers_of_sharp (gL gU : SoGraphCert SoBackend) (PL PU : CertParams)
    (c κ γdL γdU lo hi pLo pHi : ℚ) (νL νU : ℝ) (hc0 : 0 < c)
    (hhamL : gL.base.ham = soRotHamExprScaled c) (hhamU : gU.base.ham = soRotHamExprScaled c)
    (hparL : gL.base.params = PL) (hparU : gU.base.params = PU)
    (hτL : PL.tau = 1) (hτU : PU.tau = 1) (hγL : PL.γ ≤ κ * γdL) (hγU : PU.γ ≤ κ * γdU)
    (hcL : checkTorusCertificateSharp gL.base = true)
    (hcU : checkTorusCertificateSharp gU.base = true)
    (hgL : checkSoGraph gL = true) (hgU : checkSoGraph gU = true)
    (hωL : FreqEncloses 2 gL.base.freqBox (lunarRotFreq νL κ))
    (hωU : FreqEncloses 2 gU.base.freqBox (lunarRotFreq νU κ))
    (hdL : IsDiophantine ((κ : ℝ) * γdL) 1 (lunarRotFreq νL κ))
    (hdU : IsDiophantine ((κ : ℝ) * γdU) 1 (lunarRotFreq νU κ))
    (hbandL : lo ≤ gL.pLo - PL.disp) (hbelow : gL.pHi + PL.disp < pLo) (hlt : pLo < pHi)
    (habove : pHi < gU.pLo - PU.disp) (hbandU : gU.pHi + PU.disp ≤ hi) :
    ∃ (Bm : SoBarrier lo hi) (Bp : SoBarrier lo hi),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ)

-- lunar_barriers_of_band: identical, with checkTorusCertificate in place of the sharp check.

theorem lunar_spin_confinement_of_band (lo hi δ pLo pHi : ℚ) (hlo : 1 - δ ≤ lo)
    (hhi : hi ≤ 1 + δ)
    (hB : ∃ (Bm : SoBarrier lo hi) (Bp : SoBarrier lo hi),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ))
    (q₀ p₀ φ₀ : ℝ) (hp : (pLo : ℝ) < p₀ ∧ p₀ < pHi) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).2.1 - 1| ≤ δ) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z
```

## Exact hypotheses the data must discharge (for `lunar_barriers_of_sharp`)
With `PL := R2 errL dispL`, `PU := R2 errU dispU` (the SO-GEN3 package), time scale `c`, `κ = c/s`:
- signed data conclusions (verbatim shape): `gX.base.ham = soRotHamExprScaled c`,
  `gX.base.params = PX`, `checkTorusCertificateSharp gX.base = true`, `checkSoGraph gX = true`,
  `FreqEncloses 2 gX.base.freqBox (lunarRotFreq νX κ)`;
- SO-DION facts: `IsDiophantine ((κ : ℝ) * γdX) 1 (lunarRotFreq νX κ)` with `γdX : ℚ` (if SO-DION
  states γ(N) as a real expression, a one-line cast bridge `((γdX : ℚ) : ℝ) = γ(N)` is needed);
- rational, `decide +kernel` (or `rfl`): `0 < c`, `PX.tau = 1`, `PX.γ ≤ κ * γdX`,
  `lo ≤ gL.pLo - PL.disp`, `gL.pHi + PL.disp < pLo`, `pLo < pHi`, `pHi < gU.pLo - PU.disp`,
  `gU.pHi + PU.disp ≤ hi`;
- confinement: `1 - δ ≤ lo`, `hi ≤ 1 + δ` (rational).
The final data theorems are then one-liners: `lunar_barriers_of_sharp gL gU PL PU c κ γ γ lo hi pLo
pHi νm νp (by decide +kernel) … ` and `lunar_spin_confinement_of_band lo hi δ pLo pHi (by decide
+kernel) (by decide +kernel) (lunar_barriers_of_sharp …)`.

## Checks
- Gate build `inp_lake_build.sh … KAM.SpinOrbit.Graph.Cert KAM.SpinOrbit.Graph.CertSharp
  KAM.SpinOrbit.LunarAssembly KAM.SpinOrbit.LunarAssemblySharp`: `Build completed successfully
  (3398 jobs)`; no warnings in my files, no sorry.
- `main_shortname_check.py` on the three modules: `short-name check OK (no reused public short name)`.
- Lines ≤ 100 columns (checked by script); no heartbeat options; files ≤ 285 lines.
- `scripts/lint_sources.sh`: as committed, fails ONLY with `KAM.lean is out of date; run
  scripts/gen_root_imports.py` (two new modules; rule 10 forbids me editing KAM.lean). With
  KAM.lean regenerated temporarily (+2 import lines, then reverted): exit 0,
  `check_lean_modules: PASS (1458 Lean files)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (146 frozen
  declarations)`. The orchestrator should regenerate KAM.lean on landing.

## Axioms
`soRotBarrier_of_certSharp`, `soRotBarrier_of_cert`, `soRotBarrier_of_certified`,
`lunar_barriers_of_sharp`, `lunar_barriers_of_band`, `lunar_spin_confinement_of_band`,
`lunar_barriers_of_viaBand`, `lunar_spin_confinement_of_viaBand`: `[propext, Classical.choice,
Quot.sound]`.

## Uncertainties / design notes
- The type of SO-DION's γ(N) is not yet known (SO-DION has not landed); I assumed a rational γd
  multiplied by κ, `IsDiophantine ((κ : ℝ) * γd) 1 …`, per the brief. Separate γdL, γdU allowed.
- The package is abstracted as any `CertParams` `PX` with `gX.base.params = PX`; only `tau`, `γ`,
  `disp` are used (rhoInf etc. come from `checkStatic`).
- D38 is not yet recorded in this branch's docs/DECISIONS.md (only D36, D37); I followed the brief.
- No heartbeat design signals.

## Suspected errata / deviations
None in pinned sources. Deviation: proofs (not statements) of the landed `soGraph_exactTorus` and
`soRotBarrier_of_cert` were refactored through the shared lemma, as the brief prefers.

AUDIT FOCUS: (1) the landed statements of KAM/SpinOrbit/Graph/Cert.lean (soGraph_exactTorus, soRotBarrier_of_cert, soBarrier_of_cert, SoGraphCert, checkSoGraph) are byte-identical in statement (only two proofs changed into one-liners); (2) soRotBarrier_of_certified: from CertifiedTorus, checkStatic, checkSoGraph and the Diophantine premise to the barrier, with no hidden extra premise and no use of the old checker; soRotBarrier_of_certSharp correctly extracts checkStatic from checkTorusCertificateSharp and uses checkTorusCertificateSharp_sound; (3) lunar_barriers_of_sharp and lunar_spin_confinement_of_band: PARAMETRIC FIDELITY, i.e. every hypothesis is a data conclusion in verbatim shape, an SO-DION-shaped Diophantine fact (`IsDiophantine (κ * γd) 1 (lunarRotFreq ν κ)`, compatible with the landed SO-DION lemmas on inp: lunarRotFreq{Minus,Plus}N_isDiophantine at κ/(N+2)), or a rational inequality decidable by the kernel; no hypothesis encodes a conclusion; the band algebra is correct (the barrier bands inside [lo, hi], separation through pLo < pHi); δ with 1 − δ ≤ lo and hi ≤ 1 + δ gives |p − 1| ≤ δ; (4) the sanity theorems really reproduce the landed lunar_barriers_of / lunar_spin_confinement_of verbatim; (5) names, kernel replay, axioms (standard three), lint, size.

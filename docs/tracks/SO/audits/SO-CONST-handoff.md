# SO-CONST prover handoff (branch inp-soconst, 3c5a747b; off inp; track SO package run by the main orchestrator)


## Files
- New: `KAM/Certificate/Constants.lean` (740 lines, one module, committed on branch inp-soconst).
- Not touched: KAM/Frozen, manifest, KAM.lean, README.md. `scripts/lint_sources.sh` reports only
  "KAM.lean is out of date" (the new module is not yet in the generated root; the orchestrator
  runs `scripts/gen_root_imports.py`); every other lint check passes.

## Approach
- `cRUpQ n τ = max 1 ((2·pl)⁻¹ (τ/(el·pl))^τ (8n/pl)^n)`, pl = 3.141592, el = 2.718
  (Real.pi_gt_d6, Real.exp_one_gt_d9); `cR_le_cRUpQ` by gcongr after `rpow_natCast`.
- Rational mirror (suffix `Q`) of each constant in the chain: mSizeQ, ThetaQ, CXQ, CTQ, COmegaQ,
  CsymQ, CredQ, Cxi0Q, CGQ, CBQ, CDNQ, CDXQ, CDTQ, CYQ, CDTbordQ, hatCSQ ... hatcStarQ, delta0Q,
  with c_R := cRUpQ and rpow exponents turned into ℕ powers (2a = 4(τ+n)+4, a = 2(τ+n)+2).
  Each has `<X>Q_ge : X ≤ ↑XQ` (hypothesis `Params n τ M σK σB σT` built by `params_of_rat` from the
  signed hypotheses), proved by unfold + push_cast + gcongr, using track K/I `one_le_*` lemmas
  for the nonnegativity side goals.
- `isoC1Q`, `isoC2Q`, `isoC1_le_isoC1Q`, `isoC2_le_isoC2Q` exactly as signed in
  SOSignatures.lean (types verbatim; the hypothesis `hγbar` is unused, named `_hγbar`).
- All short names checked unused in KAM beforehand (grep).

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-soconst KAM.Certificate.Constants`:
  `✔ [3193/3193] Built KAM.Certificate.Constants (12s)  Build completed successfully`.
- No sorry/axiom/maxHeartbeats; no line > 100 columns.
- `#print axioms` of isoC1_le_isoC1Q, isoC2_le_isoC2Q, cR_le_cRUpQ, isoPilotThreshold_enclosure,
  isoC1Q_pilot: `[propext, Classical.choice, Quot.sound]` each.

## Pilot (all by `decide +kernel`)
n=2, τ=1, ρ=1/200, ρinf=1/400, μ=1/1000, M=σK=σB=σT=4, γbar=1/42, ν=1/4 (ν-branch inactive):
- `cRUpQ 2 1 = 1`
- `hatCDeltaQ = 3525311976177664` (matches report Ĉ_Δ)
- `hatcStarQ = 19888413388084648309626446997880832000` (matches report ĉ_*)
- `isoC2Q = 1938060754672665339606597632000000000000`
- `isoC1Q = 1502726028501549837873490441646465003847653084860516401152000000000000000000000000000`
- `isoPilotThreshold = (1/42)^4 (1/200)^4 / isoC1Q ≈ 1.33660489387e-100`
  (exact 1/7481642515174653798898541941295261706580362741677007109438518067200000000000000000000000000000000000);
  `isoPilotThreshold_enclosure`: within factor 2 of 13366/10^104 (actual ratio 1.0000037).

## Uncertainties / errata
- `hP` of ThetaQ_ge, CXQ_ge, COmegaQ_ge, CGQ_ge, CredQ_ge is unused (named `_hP`, kept for a uniform API).
- Mirrors are polymorphic only in ℚ; the real `isoC1` takes τ real, `τ ∈ ℕ` cast is as signed.
- No defects found in pinned sources. No deviations from the signatures.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md). Draft signatures: /root/code/KAM-inp/.drafts/design/SOSignatures.lean (isoC1Q, isoC2Q, isoC1_le_isoC1Q, isoC2_le_isoC2Q around lines 595-615). The pilot's constants: /root/code/KAM/docs/explorations/lunar-spin-orbit-feasibility-report.md §3.

AUDIT FOCUS: (1) the four signed declarations match the draft signatures verbatim; (2) every rational mirror XQ is an UPPER bound of the sealed real constant X it mirrors (KAM/Iso/Apost/Defs.lean isoC1/isoC2 and the chain in KAM/Apost/Constants.lean), in the direction the consumer needs (an upper bound of isoC1 makes the checked smallness inequality imply the real one); check the cR bound cR_le_cRUpQ (pi and e enclosures in the right directions), every rpow-to-natural-power conversion (exponents 2a = 4(tau+n)+4, a = 2(tau+n)+2), and that no step silently assumes more than Params; (3) the pilot evaluation (hatCDeltaQ, hatcStarQ, isoC1Q, the threshold) is by kernel evaluation only and matches the report; (4) the unused hypotheses (_hgammabar, _hP) are harmless. Audit ONLY KAM/Certificate/Constants.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.

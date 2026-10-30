# Handoff DESIGN-LOCK, revision 2 (after design audit 1 FAIL), 2026-10-30

**Files (committed on inp-lockdesign):** `docs/tracks/SO/design/SO-LOCK-DESIGN.md` (rev 2; response table §9),
`docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md` (rev 2, Q1–Q7), `.drafts/design/SOLockSignatures.lean` (342 lines,
tracked draft). Audit report `SO-LOCK-design-audit-1.md` committed unedited. Nothing frozen; no KAM/ file touched.

**Fixes:**
- F1 (orchestrator's change adopted): `sqrtE` total real-preserving (0 on nonpositive reals, principal root
  elsewhere). No landed statement changes; `exists_real_eval`/`eval_real` get one case each (`sqrtE_ofReal`);
  domain safety via ball check r < s² + `SlpSqrtGood` (analogue of `SlpInvGood`) + new `NonvanishingOn` arm.
  13 landed files get match cases (inventory with line counts, design §4.6).
- F2: `SqrtWitness` with positive anchor s, margin 0 ≤ d < s, error ε/(s−d); typed `sqrtWitnessRadius`,
  `sqrtWitness_sound`, pointwise `sqrtE_model_error`.
- F3: exact real/complex maps (`lockToRotR`, P₀ = 1+c′+Y; `lockToPhysicalR` = soRotMap∘…; `lockHamiltonianR`
  = J̃+Y²/2−c′²/2+Xc″+V−1/2), 2-form dY∧dX = dI∧dα, `lock_conjugacy` with `ContDiff ℝ 3 c`, `lockToRotC`,
  `lockHamExpr_eval` (all z), `_clock` (Re I > 0), inverse contract `lockToPhysicalR_surj`.
- N1: literals from proved rational majorants (L ≤ 0.03377, η ≤ 5.354e-4): |ψ*| ≤ 17/10⁶, |ψ*′| ≤ 27/200000;
  from LOCK-GEN-1: Ω = 8/65, I_in = 129/10000, Rψ = 21/100, Rp = 26/1000 (provisional until kernel pass).
- N2: typed `LockGraphCert`, `lockBarrier_of_certV2`, `lockLiteralCheck`, `lunar_sync_lock_of_cert`.
- N3: `DifferentiableAt.cpow_const` (Pow.Deriv). N4: odd-free uniqueness claim deleted. N5: inventory,
  ownership note, no `#eval` in production.

**For owner review:** Q1 global odd characterisation of ψ*; Q2 orbit eq. via `soField`; Q3 ellipse spin bound
2.6 %; Q4 drop trivial non-vacuity; Q5 freeze orbit bound; Q6 literal rules; Q7 keep rational centre c for coords.

**Packages:** start now LOCK-PO, LOCK-CONF, LOCK-COORDS-R, ASSEMBLY glue; LOCK-SQRT after BALLFIX lands and an
owner for the 13 checker files is assigned; then COORDS-C → GRAPH → DATA → instance. ≈3.6–4.8k new lines +
0.3–0.6k case lines. Sizing (§7): v2 refined first at |k|≤55, |l|≤11 (≈1.3k half-terms, ≈R2 cost); sharp fallback
110×22 (≈17× R2); full 129×27 data available.

**Risks:** checker-file contention (BALLFIX/V2); lock-package constants not yet computed (thresholds reuse R1's
M, σ); √ inflates majorants; arg-continuity in LOCK-CONF; three placeholder defs (`lockHamExpr`,
`sqrtWitnessRadius`, `lockLiteralCheck`) have `sorry` bodies until the constructor exists.

**Errata (non-pinned):** SO-LOCK-SCOPE §1 L3 (NK not needed); §2 dated certifier name. Own rev-1 errors
corrected (listed design §8).

**Sig-check** (`inp_sig_check.sh … .drafts/scratch/SOLockSignatures.lean`, slot 1, 16:21 UTC): exit 0, 29
warnings `declaration uses 'sorry'`, no other diagnostics (a first run failed on a missing
`open KAM.CertificateSharp.V2`, fixed). Scratch deleted. Lint not run: worktree has no `.lake/build` (audit saw
the ABI phase fail for that reason); no KAM/ file changed. Axioms: n/a.

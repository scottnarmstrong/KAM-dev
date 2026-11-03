# Handoff B4-TCHECKCHAIN

Files: `KAM/EffectiveStability/TorusChainCheck.lean` (new, ~215 lines). No other file touched.

Declarations (namespace KAM.EffectiveStability): `TorusChainCert n` (data only: H Nact P steps δc εb T a b η r),
`tchStepOKB`/`tchStepOKB_sound` (⇒ `TChStepOK`), `tchChainOKB`/`tchChainOKB_sound` (⇒ `TChChainOK`, induction),
`tchDomOKB`/`tchDomOKB_sound` (⇒ `TChDomOK` with b,r read by `getD`), `checkTorusChain : Bool`,
`checkTorusChain_sound (c) (hc : checkTorusChain c = true) (w₀) (hw₀ : ∀ j, |w₀.2 j| ≤ (c.a.getD j 0 : ℝ))`
with exactly `torusChain_confinement`'s conclusion (T := c.T, η/a read by getD, `tchChainMap c.steps`,
`tchChainInv c.steps`). Smoke: `torusChainSmokeCert` (n=1, J²/2, two zero steps `tchSmokeStep`),
`torusChainSmokeCert_check` by `decide +kernel`, `torusChainSmokeCert_zeroDrift`.

Approach: mirrors OscillatorChainCheck/TorusCheck. Checker encodes: FTFits H, P; ftActOnly Nact; chain identities
and step typing; domain budget; δc>0, εb>0, T≥0; per i∈range n: b≤r, 0≤η, ftAngleDriftBound P i ftPiUB b +
tchChainBound n steps H / δc ≤ η, a+Tη<b. π bound is the fixed `ftPiUB` (as in torusChain_confinement), so no πub field.
No signature changes to torusChain_confinement (untouched).

Checks: `b_build.sh … KAM.EffectiveStability.TorusChainCheck` succeeded, no warnings; `lint_sources.sh` OK
(25 tests, frozen guard OK, ABI OK); line-length script prints `[]`; short-name check OK (rc 0).
Kernel time: whole-file elaboration incl. the `decide +kernel` smoke ≈ 3.7 s wall (imports cached); the check itself negligible.
`#print axioms` of checkTorusChain_sound, torusChainSmokeCert_check, torusChainSmokeCert_zeroDrift: [propext, Classical.choice, Quot.sound].

Design signals: none. Errata: none found.

## AUDIT FOCUS (kam-b1)
Track B, program B4 (overnight D71; nothing frozen; OD-B11). Mirrors the landed, audited B2-CHECKCHAIN (OscillatorChainCheck.lean) and B4-TCHECK (TorusCheck.lean) for the torus chain theorem
torusChain_confinement (B4-TMULTI, audit 1 PASS WITH NOTES; batch 12 in landing). Brief:
/root/code/KAM-inp-b1/.drafts/B/brief-B4-TCHECKCHAIN.md and brief-B1-common.md. Scope: prover commit 0d9553dcf and the inp-b1 merge. Check:
(1) checkTorusChain is a total computable Bool over data only and encodes EVERY non-binder premise of torusChain_confinement faithfully (TChStepOK/TChChainOK/TChDomOK Bool mirrors with soundness by induction; casts; ranges); checkTorusChain_sound's only hypotheses are hc and the chart initial box; kernel evaluation only; (2) smoke test genuinely instantiates the theorem; (3) hygiene (AGENTS rules 3, 4, 7; widths ≤ 100), names,
axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.

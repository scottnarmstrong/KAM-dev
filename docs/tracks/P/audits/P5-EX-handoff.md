# P5-EX prover handoff (branch inp-p5ex, 0466c50; contains inp-p5cg, inp-p45s and inp-design-p45r4; offloaded package run by the main orchestrator; prover on claude-12; session 1 stopped on a design defect, fixed by P45 revision 4)

## Session 1 (stop report)

Per the brief ("if a statement looks false or under-hypothesised, stop on it and report"), I stopped before writing code.
Branch inp-p5ex is unchanged (clean, nothing new committed). Files: none. Builds/lint: none run. `#print axioms`: n/a.

## Defect: `PGExtension.agrees` is not implied by the P-G hypotheses (so `ext` is false for some PGData)

Signature (P45Signatures.lean ~l.540, design l.1255):
  agrees : ∀ mu ∈ Icc 0 d.mu0, ∀ w : Phase (a+b), realInclusion₂ w ∈ extensionDomain d delta → P mu (realInclusion₂ w) = (d.P mu w : ℂ)

`extensionDomain d delta` contains real points w within delta of a point whose fast action is in `closure d.V` and
slow norm <= r0/2, with ARBITRARY fast angles. Such w may have fast action outside `closure V` (distance < delta),
i.e. outside `closure (cylinder V r0)`. There the data give nothing:
 * `hP` is `AnalyticOnNhd` only at points of Icc 0 mu0 ×ˢ closure (cylinder V r0) (so analytic on SOME open nbhd W0 of
   that set, with no uniformity in the angle); `d.P` is a total function, arbitrary off W0.
 * `hperiod` holds only on `cylinder V r0`.
 `PGExtension.periodic` forces P~(real w) = P~(real (w - fastShift k)), so `agrees` forces d.P to be 2π-periodic on the
 whole real delta-neighbourhood of the box, for the delta *we* choose.
Counterexample sketch (for every delta>0): take P_per analytic, 2π-periodic, satisfying all PGData fields; let
W0 = {w : dist(w, closure cyl) < 1/(1+|fast angle|)} (open, contains closure cyl) and set d.P := P_per + 1_{w ∉ W0,

## Session 2

Branch inp-p5ex, worktree /root/code/KAM-inp-p5ex (design revision 4 merged: `agrees` restricted to
`w ∈ closure (cylinder d.V d.r0)`). Declarations copied verbatim from the amended
`/root/code/KAM-inp/.drafts/design/P45Signatures.lean` (checked by whitespace-normalised comparison):
`PGComplexPhase, assembleComplex, extensionDomain, PGExtension` (ExtensionDefs), `ext, pgExtension, pgWidth,
pgOscRadius, complexAverage, complexAverage_real, consts` (Extension facade). Only the body of `ext` differs
(`pgExtension_exists d` instead of `sorry`).

## Files (all new, KAM/Planetary/PGAssembly/, 1275 lines total, largest 182)
ExtensionDefs (statement carriers) · ExtensionPeriodic (identity theorem near closure of an open set,
`exists_delta_shift_eq`, `tube_glue`) · ExtensionPack (`packVec`/`unpackL`: (mu,w) ↦ ℝ^(n+n+1)) ·
ExtensionTube (compact period box `pgX`, closure/cylinder facts) · ExtensionTubeData (`PGTube`, `pgTube_exists`)
· ExtensionTubeP (`PGTube.P`, shift-independence) · ExtensionProps (domain, holo, continuity, periodic, bound,
agrees) · ExtensionExists (H0 tube + Cauchy bounds, `pgExtension_exists`) · ExtensionConsts (strip membership,
angle periodicity, `PGExtension.summable_torus`) · Extension (facade).

## Approach
Pack (mu,w) into one real vector; compact X = [0,mu0] × one-period box (angles ∈ [0,2π], fast action ∈ closure V,
slow part ≤ r0/2) ⊆ packed closed cylinder where `hP` gives analyticity. P5-CG `compact_real_complexification` gives F
on a tube. Identity theorem (open packed cylinder, `hperiod`) + compactness gives uniform δ with f(y−s)=f(y) for the
finitely many shifts |m_i|≤1; `tube_glue` (real_slice_identity on a ball around a real point) gives F x = F(x−ι s) on
a thin tube (radius ≤ min(ρ/3, δ, 1/2)). `PGTube.P mu z := F(pack mu (z − ι(fastShift k)))` for any valid k (value
independent of k; |k−k'|≤1 from the angle windows). Holomorphy/continuity are local (valid set is open), periodicity
is automatic, bound M. `agrees` uses `hreal` + continuity-closure argument `pg_period_closure` (d.P mu (w−fastShift k)
= d.P mu w on closure cylinder; only there is the closed cylinder needed). H0: CG on compact `closure V` with `hfreq.1`,
Cauchy bounds via `KAM.norm_fderiv_le_of_closedBall_bound` / `norm_iteratedFDeriv_two_le_of_closedBall`, delta ≤ ρ_H/4.
delta = min(T.rho, ρ_H/4, 1/2) < 1. `consts` via `KAM.summableWeighted_torusCoeff` (ρ = δ/(2π), δ' = δ/(4π)),
LP = max 1 (coth(δ/4)^a · MP). `complexAverage_real` from `agrees` pointwise + `integral_complex_ofReal`.

## Checks
* `inp_lake_build.sh /root/code/KAM-inp-p5ex KAM.Planetary.PGAssembly.Extension` → Build completed successfully (9097 jobs).
* `sh scripts/lint_sources.sh`: only message `KAM.lean is out of date; run scripts/gen_root_imports.py` (generated root
  file, not edited per rule 10; new modules need regeneration by the orchestrator); check_lean_modules PASS,
  FROZEN-ANCHOR GUARD OK, ABI HASHES OK. No lines >100.
* `#print axioms` of `ext`, `complexAverage_real`, `consts`, `pgExtension_exists`: [propext, Classical.choice, Quot.sound].
* No maxHeartbeats/sorry/axiom/unsafe/opaque; no provider or DRAFT_SORRY import.

## Uncertainties / errata / deviations
* Source imprecision (already recorded in design rev 4): p5-pg-assembly.tex Lemma bpP:p5:ext "P~ = P at real points"
  of X_delta holds only at real points of closure(C(V,r0)).
* No deviations from the signatures. No heartbeat design signals.
* Helper names that other modules may notice (not in the signature file): `PGTube`, `pgX`, `packVec`, `unpackL`, `pgF`,
  `tube_glue`, `exists_delta_shift_eq`, `PGExtension.summable_torus`, `pgExtension_exists`.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P5-EX, its proof plan and section 'Revision 4'; audits DESIGN-P45-design-audit-{1,2,3,4}.md; signatures .drafts/design/P45Signatures.lean): (1) statements/definitions = design signatures AS AMENDED BY REVISION 4 (PGExtension with agrees restricted to w ∈ closure (cylinder d.V d.r0); ext, pgExtension, consts, complexAverage, complexAverage_real), the hypotheses hP/hperiod/hfreq exactly as designed; (2) proofs sound (P5-CG compact complexification, analytic identity theorem, thickening argument); no added premises; Classical.choice only from proved existence; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/PGAssembly/Extension*.lean.

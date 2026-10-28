# P23-16 prover handoff (branch inp-p2316, e7874f8; contains inp-p2314 (P23-14, audited); offloaded package run by the main orchestrator; prover on claude-12)


Branch inp-p2316 (off inp + P23-14). Nothing merged/pushed. KAM.lean not touched (lint reports it out of date: orchestrator must regenerate).

## Files (new)
- KAM/Planetary/TwoScale/IterationCompose.lean: `PhaseProps` (diff/inj/real/lattice/symplectic bundle), `PhaseProps.id/comp`, `isOpen_coefficientDom`, `KamHyp.restrict` (smaller base set).
- KAM/Planetary/TwoScale/IterationReal.lean: `KamHyp.ihat_real_of`: reality of ĩ₊ at real points of D, derived from step's outputs (see deviation note), `eHat_lt_small`, `sup_norm_le`.
- KAM/Planetary/TwoScale/IterationStage.lean: `Stage`, `StageInv`, `StepRel`, `stage_zero`, `stage_step`, `seq_*` lemmas (γ, τ unchanged; Mbar₁/Mbar, Mbar₂/Mbar, Mhat/M constant along seq).
- KAM/Planetary/TwoScale/Iteration.lean (facade/main): `KAM.Planetary.iterative`, signature verbatim from the design/P23Signatures (checked equal modulo whitespace; one long line wrapped).
Line counts: all < 250.

## Approach
Dependent induction through the subtype {S // StageInv j S}: stage 0 = (dioBase D h p, h, f, id) (via KamHyp.restrict); stage j+1 from `step` applied to stage j (Diophantine hypothesis from the invariant `realFreq (hs j) '' Ds j = realFreq h '' dioBase`), `Φ(j+1) = Φ j ∘ Ψ(j+1)`, with Ψ restricted from the large averaging domain to the small one (this is the G3 treatment: same total function, smaller source domain). Chosen with `choose`/`Nat.rec`; the shared witnesses are exactly those of the one existence theorem. cutoff bound by induction from step's 24-factor.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-p2316 KAM.Planetary.TwoScale.Iteration` : Build completed successfully (9163 jobs); no warnings in my files.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only complaint "KAM.lean is out of date" (expected, not mine to edit).
- `#print axioms KAM.Planetary.iterative` : [propext, Classical.choice, Quot.sound].
- No sorry/axiom/maxHeartbeats anywhere in new files. No provider / frozen-theorem imports.

## Deviations / uncertainties / errata
- No extra premises; signature unchanged and proved with only `H : KamHyp D sbar p h f`.
- `step`'s statement does not expose reality of ĩ₊ (`MapsTo (is (j+1)) (realBase (Ds j)) (realBase (Ds (j+1)))` is required by `iterative`). I derive it in `ihat_real_of` from step's *outputs* only (new KamHyp, Dp = re-image of ĩ₊, freq identity, block bounds, ÊR-smallness from `small`): ĩ₊(I) is within 10ÊR<R/16 of real q = Re ĩ₊(I) ∈ D₊, Schwarz reflection + injectivity of ω₊ on that ball. Not an erratum, but an observation: step's signature could expose it (design suggestion only).
- Possible source-level note (not an error): the source says Ψ₊ displacement on D_{ρ̂/2} (G3 already in the design); handled as the design states.
- No heartbeat problems; all declarations elaborate at default budget.
- Downstream (P23-17..21): witnesses are `T j` of the proof; the proof term is opaque (existential), so limit packages must use the conclusion of `iterative` (or reuse `stage_step`/`StepRel` for a joint construction, which expose the same relations with named structures `StageInv`/`StepRel`).

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md revision 2 row P23-16 and proof plan; audits DESIGN-P23-design-audit-{1,2}.md; signatures .drafts/design/P23Signatures.lean; blueprint-P p3a iterative): (1) statement = design signature (iterative: existential dependent induction, maps-to/reality/lattice invariants) EXACTLY; (2) proof sound (P23-14 step consumed as designed); no added premises; (3) hygiene. Audit ONLY KAM/Planetary/TwoScale/Iteration*.lean (compare with branch inp-p2314).

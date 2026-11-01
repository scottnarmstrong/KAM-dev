# LP-W4B: combined audit handoff for LP-SRC + LP-SP-GEO + LP-SP-OSC + LP-SP-CONF + LP-SP-TUBE + LP-SP-ADAPT

Branch `inp-lp-w4b` (worktree `/root/code/KAM-inp-lp-w4b`) = `inp-lp-src` + `inp-lp` (landed through W4A, main
b2308bac) + `inp-lp-spconf` (SP-GEO, SP-OSC, SP-CONF) + `inp-lp-sptube` + `inp-lp-spadapt`, plus pre-audit SPEC §4
docstring sentences in SP-GEO's two modules. The package diff is `git diff inp-lp...HEAD -- KAM`: 12 modules plus the
regenerated root, about 2,900 lines. Nothing in track LP is frozen.

| Package | Modules | Handoff / brief | Source |
|---|---|---|---|
| LP-SRC (planar, freeze prep, OD-11 (b)) | `StrongAMD/SourceCarrier.lean`, `StrongAMD/PlanarSafety/Source.lean` | `LP-SRC-handoff.md`, `packages/LP-SRC.md` | freeze review 1 F4; FREEZE-PROPOSAL §3b; review 3 PASS for the text |
| LP-SP-GEO | `Spatial/Geometry.lean`, `Spatial/Continuation.lean` | `LP-SP-GEO-handoff.md` | MAIN L5–L6, d = 3 |
| LP-SP-OSC | `Spatial/Osculating*` | `LP-SP-OSC-handoff.md` | MAIN L16, d = 3 |
| LP-SP-CONF | `Spatial/Confinement.lean` | `LP-SP-CONF-handoff.md` | MAIN L14, d = 3 (conditional helper) |
| LP-SP-TUBE | `Spatial/ComplexTube.lean` | `LP-SP-TUBE-handoff.md` | AMENDMENTS N12 |
| LP-SP-ADAPT | `Spatial/NonresonantAdapter*` | `LP-SP-ADAPT-handoff.md` | MAIN L13 adapter for `Phase (n+m)` |

Handoffs are in `docs/tracks/LP/audits/`; briefs in `/root/code/KAM-inp-lp/docs/tracks/LP/packages/`. Planar
templates are landed and audited: LP-GEOMOD, LP-OSC, LP-CONF, LP-DICT (Part B), and track P's `ComplexTube`.

## Orchestrator checks (kam-lp)
- `lp_build.sh` of all LP modules (70) in import order: built. `lp_lint.sh`: exit 0. Short-name check: OK.
  `git diff --check`: clean. Every module docstring carries the SPEC §4 sentence.

## REPORT FORMAT
One section per package (LP-SRC, SP-GEO, SP-OSC, SP-CONF, SP-TUBE, SP-ADAPT), each with a verdict, then a combined
verdict. Write each section to the report as you finish it.

## AUDIT FOCUS
- LP-SRC: the source carriers and definitions equal review 1 F4's text; the characterizations; that
  `lp1_planar_strongAMD_safety_source` is faithful to the landed `lp1_planar_strongAMD_safety_normalized` (only the
  typing binder `h₀` and existential subtype proofs added) and is proved from it.
- The spatial packages are twins of audited planar packages. Check faithful transcription to `d = 3` (Euclidean
  `spaceLength`, vector `L` with `spatialUnit`, `Fin 3` elements); no added premise; the strict `hstop` in SP-CONF;
  the specific-energy scale in SP-OSC (LP-OSC-1 note); SP-OSC's F2 clauses and OD-11 (b) subtypes.
- SP-TUBE: `tubeNM` is `tube` with `n + n` replaced by `n + m` (agreement at `m = n`).
- SP-ADAPT: the slot and sign convention for `m ≠ n` (slow positions in `w.1`, momenta in `w.2` → engine `(q, p)`);
  the conditional composition helper.

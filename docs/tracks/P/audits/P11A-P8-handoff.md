# P11A-P8 (PreparedData) handoff (branch inp-p11ap8, 3a1ff30b; offloaded package run by the main orchestrator)


## Files
- NEW `KAM/Planetary/Preparation/PreparedData.lean`: verbatim signed `P11PreparedData`, `p11PreparedFreq`,
  `p11PreparedFreqR`, `P11PreparedSpec`, `p11M0`, `p11SlowNormalizedFreq`, `P11PreparedFullSpec`,
  `p11PreparedData` (one line of `P11PreparedSpec` re-wrapped to 100 columns; no content change).
  It imports SlowSigned, HoloAssembly, Patch, WeakMeasure.Basic, FixedHamiltonian. No sorry.
- Merged `inp-p11ap7d` (P7db, READY marker present) after the definitions commit; rebuilt afterwards.

## Not done
- `prepared` (Preparation/Prepared) and `amount` (Preparation/Amount), with nodes pr-basic, pr-a, pr-in, pr-b,
  pr-c, pr-d, am-norm, am-dir, am-scale: not started beyond reading the plan. They need, from `avg_slow`,
  `avg_fast`, `holo_chart`: construction of Q (N, P, chain, checkW), holomorphy/periodicity/reality on the
  rescaled strip, Cauchy estimates for all J-jets of `Z`, `g2`, `h0` (only a sup bound on `g2` and a jet bound
  on `Z`'s rho-derivative are in `P11SlowSpec`), the vector/scalar jet bounds (pr-c, pr-d), and the amount
  transfer via W1 Stability and `chart_scaling`. This is several thousand lines; I judged it too large to
  finish responsibly in this session. `chart_scaling*` already exist on inp (WeakMeasure/ChartScaling).
- No `Prepared.lean`/`Amount.lean` facades exist yet; P8D/P10/P13-C remain blocked.

## Checks
- Gate build `KAM.Planetary.Preparation.PreparedData`: success (before and after merge).
- `scripts/lint_sources.sh`: only "KAM.lean is out of date" (expected, generated; not edited); module check,
  frozen guard and ABI hashes PASS.
- No `#print axioms` (no theorems). No heartbeat overrides.

## Uncertainties / errata / deviations
- None found in sources. No statement judged false. The only deviation is the line re-wrap above.

ORCHESTRATOR RULING (OVERNIGHT 01:05): P11A-P8 was split into P8a/P8b/P8c/P8e after its first module. This audit covers ONLY the first module, KAM/Planetary/Preparation/PreparedData.lean: the signed data and spec DEFINITIONS (P11PreparedData, P11PreparedSpec, P11PreparedFullSpec, p11JetBound and any other signed definition in it). The theorems prepared and amount are NOT in this file and are not findings (P8e assembles them).

AUDIT FOCUS: every declaration in PreparedData.lean that appears in /root/code/KAM-inp/.drafts/design/P11ASignatures.lean must equal the signature file EXACTLY (binders, field names and types, body); any unsigned declaration must be a helper with a distinct name. Check against design docs/tracks/P/design/P11A-LEAN-DESIGN.md (prepared/amount rows) that the definitions say what the blueprint's prepared normal form says (N, P, chain, checkW, the bounds). Audit ONLY KAM/Planetary/Preparation/PreparedData.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

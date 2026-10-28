# S2 prover handoff (branch inp-p14-s2, 2229cdee; contains S1 at round 1 (S1b adds positivity lemmas only); offloaded P14 package run by the main orchestrator)


**Files:** KAM/Planetary/SecularBox/Covariance.lean (new, ~125 lines). Nothing else touched.
**Declarations:** `secularRotation` (verbatim), `sb_cov` (verbatim, proved). Graph steps sb-cv-1..3 are internal
to `sb_cov` (private helpers `sbCov_*`: fast/slow blocks of the rotation, Gamma invariance, ecc vector
covariance, orbitalUnit = rot theta (orbitalUnit (F-theta)), Jacobian shift, position/momentum covariance).
Nothing assigned to other packages found.
**Approach:** unfold; slow pair of rotated point = `rot theta` of the old pair; Gamma invariance by sin²+cos²;
rot is linear/commutes with quarterTurn; planeDot_rot, rot_ex, rot_quarterTurn from KAM.Kepler.Plane.
No positivity needed (all points), per Departure D3.
**Checks:** gate build KAM.Planetary.SecularBox.Covariance: success, no warnings. `#print axioms KAM.Planetary.sb_cov`:
[propext, Classical.choice, Quot.sound]. lint_sources.sh: check_lean_modules PASS, frozen guard OK, ABI hashes OK;
only note is "KAM.lean is out of date" (generated; not edited per rules; orchestrator regenerates).
Name grep: `secularRotation`, `sb_cov` unused elsewhere in KAM before this.
**Uncertainties / errata / deviations:** none. No heartbeat options; file far below the cap.

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row S2 and its node rows/proof plan; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean lines ~377 (secularRotation) and ~426 (sb_cov)): (1) secularRotation and sb_cov = signature file EXACTLY; the definition means the source rotation on its whole carrier; the S2 slice COMPLETE: every graph node the node table maps to Covariance established; an exported lemma under a node's name must state that node's literal conclusion; internal steps may stay internal if the design says so; (2) proof soundness: the Kepler rotation covariance of the chart quantities; no added premises; (3) hygiene (no EuclideanSpace; no reused public short name; no root shadow; lines <= 100). Audit ONLY KAM/Planetary/SecularBox/Covariance.lean.

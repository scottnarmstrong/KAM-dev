# Track P graph closure audit (main orchestrator, 16:00, 2026-10-29)

All 22 frozen theorems of the original project are SEALED (planetaryExponentialSafety sealed at 32090afa). The owner
asked to finish track P. Graph P (docs/graph/P/DEPGRAPH.md) still has 28 nodes with LEAN_STATUS NOT_STARTED:

- (a) owner and definition items (7): bpP:p0:totality, bpP:p1:order (claims/remarks); bpP:p3:conv#data,
  bpP:p7:conv#data, bpP:p11:sec-conv#data, bpP:p11:sec-D#data, bpP:p11:sec-E#data (definition nodes).
- (b) p14 (20): bpP:p14:geometry, stepP:p14:geo-b, cl-b, cl-c; bpP:p14:moving-ode, stepP:p14:mo-reg, mo-eq;
  stepP:p14:pt-input, pt-rho, pt-def, pt-p12, pt-p3, pt-p4; bpP:p14:hnu; bpP:p14:sec-domain#data,
  bpP:p14:sec-stopped#data; bpP:p14:sb-cov, stepP:p14:sb-cv-1, sb-cv-2; bpP:p14:sb-smooth#data.
- (c) bpN:p6:iterative-special (a P-owned remark of N).

Campaign rules for resolving a node (docs/DECISIONS.md; docs/campaign/OVERNIGHT.md):
- PROVED only when one declaration states the node's literal SOURCE_CONCLUSION from its SOURCE_HYPOTHESES (or, ruling
  (b), a local step under a PROVED parent is confirmed by an audit row citing the declaration or line range that proves
  it).
- BYPASSED (D27) for a route or step that no sealed proof takes: justify by showing the sealed proof's actual route.
- Definition nodes: name the Lean definitions plus a definitions-audit row judging their fidelity to the source.
- Never invent a status; a node whose literal content is not in Lean and is needed stays open with the exact missing
  statement.

AUDIT TASK: for EACH of the 28 nodes, read its record (statement/proof locators, SOURCE_* fields, NOTE, DEPS, EDGE
records) and the relevant Lean (KAM/Planetary/**, the sealed providers, E11's KAM/Planetary/Exponential/Stopped.lean,
E12's Safety.lean, design docs/tracks/P/design/P14-LEAN-DESIGN.md and others), and give one row:
  node | proposed status (PROVED / BYPASSED / definition-confirmed / NEEDS-LEAN / OWNER) | Lean declaration(s) and
  file:line range | justification (one or two sentences).
Hints from the sub-orchestrator: hnu's note says openness of calV is E11's obligation and E11 proves
isOpen_workingCylinder (E11-audit-1 row 19); sec-stopped#data and sec-domain#data may be covered by E11's fastBox,
slowBall, workingCylinder and fastBox_eq_pi; the pt-* steps may be internal to `perturbation` (E7) and confirmable by line
range; geometry's radial bound and moving-ode's -H clause were reported missing: decide whether a sealed proof needs them
(if not, BYPASSED with the route actually taken; if yes, NEEDS-LEAN with the exact statement). For (a), the totality and
order remarks and the conv/sec definition nodes may need an OWNER row (fidelity of totalized or choice definitions was
listed for owner review in OVERNIGHT); say what exactly the owner must decide.
Write docs/tracks/P/audits/P-GRAPH-CLOSE-audit-1.md: the table, then a short list of NEEDS-LEAN items (exact statements
and estimated lines) and OWNER items (exact question). Do not edit the graph or any Lean file.

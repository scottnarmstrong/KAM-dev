# Graph N sync: independent spot-check audit, plus the definitions row for bpN:p9#data (main orchestrator, 16:55)

After the lane N work landed (partialConvex_nekhoroshev sealed; all six frozen N theorems sealed), the sub-orchestrator
synced docs/graph/N/DEPGRAPH.md against the landed code and the package audits under docs/tracks/N/audits/ (commit
257bf902): +235 PROVED, +20 BYPASSED, now 657 PROVED / 48 EXTERNAL / 20 BYPASSED / 3 NOT_STARTED. Three Sonnet mapping
agents proposed the rows; a script checked that every cited declaration exists. Campaign rules (docs/DECISIONS.md):
PROVED only when one declaration states the node's literal SOURCE_CONCLUSION from its SOURCE_HYPOTHESES, or (ruling (b))
a local step under a PROVED parent is confirmed by an audit row citing the declaration or line range; BYPASSED (D27)
only for a route no sealed proof takes, with the route actually taken; definition nodes need named definitions plus a
definitions-audit row.

AUDIT (refute-first; do not edit the graph or any Lean file):
1. Check every judgment call the sub-orchestrator flagged: p10 cf-setting / cf-orbit / cf-branch / cf-trans /
   hc-setting closed by naming `confinement` although the exported signatures are narrower; p12 ext-dep#picard and
   #complete-contraction (delta versus 2 delta trap); p9 s-blocks#data and p3 s-N#data (definition nodes closed by
   combining audit rows across packages); p1 co-pert / co-exc / co-time (const_perturbation / const_exceptional /
   const_time); every p3 step whose audit row cites a blueprint line range rather than the step id; and all 20 BYPASSED
   rows (in particular l2-cone, where Lean proves the cone with 347/360 instead of 0.941, and cj-real).
2. Draw a random sample of 30 of the other newly PROVED nodes (state your seed) and check each the same way.
3. Write the definitions-audit row for bpN:p9#data: Part 9's fixed parameters (q = 9, p = 9/8, b = 1/8) and its section
   conventions: name the Lean definitions and judge their fidelity to the blueprint.
For each checked node: CONFIRMED / WRONG (with the correct status and why). Write
docs/tracks/N/audits/N-SYNC-audit-1.md: the table, the list of WRONG rows, and the p9#data row.

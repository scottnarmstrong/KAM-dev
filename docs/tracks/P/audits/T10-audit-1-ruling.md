# T10 audit 1: orchestrator ruling (OVERNIGHT 22:50, route substitution under D27)

Audit 1 failed T10 only on F1: the graph step `stepP:p11b:li-ord` (the orders {R,chi} = O(|z|^8),
{K,chi} = -(F-<F>) + O(|z|^6), {{K,chi},chi} = O(|z|^6) and its trajectory bound) is not stated or proved. The audit
confirms the signed `lie` and `real_lie_taylor` statements and proofs pass, and that `lie` follows another valid route:
Taylor on N0 only, the first bracket of N0 replaced by -D, brackets of the quartic families F and D bounded, and the
remainder R(I, g 1) bounded directly by `p11cN_remainder_bound` (NormalForm.lean lines 108-184).

Ruling: T10 is accepted. Under DECISIONS D27, `stepP:p11b:li-ord` is recorded `BYPASSED`: its only consumer in the
graph is `bpP:p11b:lie` (DEPGRAPH.md line 30650), whose Lean proof does not use it. LEAN_NOTE: "route substitution
(D27): lie bounds R directly via p11cN_remainder_bound and brackets only N0, F, D; orders never formalized; T10 audit 1
F1 and this ruling". No code change.

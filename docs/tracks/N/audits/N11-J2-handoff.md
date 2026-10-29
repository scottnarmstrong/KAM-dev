# N11-J2 prover handoff (branch inp-n11j2, 27261da5; offloaded package run by the main orchestrator)


**Files:** new `KAM/Nekhoroshev/Partial/Transfer.lean` (≈420 lines). Nothing else touched.

**Declarations:** `KAM.Nekhoroshev.slowTube` (signed def, verbatim; not previously in KAM) and
`KAM.Nekhoroshev.transfer_conditional` (signature verbatim; whitespace-normalised diff against
`N11Signatures.lean` is identical). Nodes `bpN:p11:transfer` and steps `tr-orbit, tr-E, tr-bounds,
tr-open, tr-closed, tr-concl` are internal to the private `transfer_core` (as the node table says).

**Approach:** `transfer_core` is abstract in the map `P`, the fields `F`, `Ft` (C¹ on `realDom R`,
`realDom r`, `Ft` periodic), a conjugation property (`conj` gives it) and T3 stated for
`IsSolutionIn`. Time `t1 ≥ 0`: maximal `Ft`-solution `z` through the T2 preimage (`gen_maximal`);
good set `E = {τ ∈ [0,t1] | [0,τ] ⊆ (Tm,Tp), y = P∘z on [0,τ]}`; prefix bounds from T1+T3;
openness from `gen_uniqueness`; closedness from `KAM.Nekhoroshev.continuation` with the compact
tail `{|Ĩ-Ĩ(0)|_* ≤ a} × cthickening dx (slow pairs of y([0,t1]))` (real part of ER splits as
angle × `Fin (n+(k+k)) → ℝ`, so no regrouping is needed); `sSup E = t1`; conclusion by the
triangle inequality. `t1 < 0`: the same core applied to `-F`, `-Ft`, `u ↦ y(-u)` (`gen_symmetry_neg`).
Field periodicity/C¹/orbit conjugation come from `real_system` and `conj`. Preimage (J1) is not
needed here (T2 is the hypothesis `hpre`).

**Checks:** `inp_lake_build.sh … KAM.Nekhoroshev.Partial.Transfer` builds; only warnings are
unused-variable for `hd ha hT` of the signed statement (kept verbatim). `scripts/lint_sources.sh`:
check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK, but exit code 1 solely because
"KAM.lean is out of date; run scripts/gen_root_imports.py" (new module `Transfer` not yet in the
generated root; I did not edit KAM.lean, per rule 10 -- the orchestrator must regenerate it). No `sorry`, no heartbeat option, no
`EuclideanSpace`, lines ≤ 100.

`#print axioms KAM.Nekhoroshev.transfer_conditional`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / errata / deviations:** none. The helper hypotheses `0 < a`, `0 ≤ d`, `0 < T` of the
signature are unused by the proof (harmless). KAM.lean needs regeneration by the orchestrator (see above).



AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-J2 (transfer_conditional; D, E1, J1, ODE uniqueness/maximal) and its node table (bpN:p11:transfer and tr-* steps internal); both N11 design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean (slowTube, transfer_conditional). Flow/Symplectic*/Preimage are N11-E1/J1 (own audits). Audit ONLY KAM/Nekhoroshev/Partial/Transfer.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

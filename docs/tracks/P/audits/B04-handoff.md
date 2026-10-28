# B04 prover handoff (P11B; branch inp-p11b-b04, c9b021e5; contains inp-p11b-b01 (audited); offloaded package run by the main orchestrator; prover on claude-10)


Files (new): KAM/Planetary/WeakKAM/{CutoffBump,CutoffTensor,CutoffScale,CutoffConv,Cutoff}.lean (648 lines total;
chain of public imports, Cutoff.lean is the facade/module named in the design).
Declarations: selectionBumpRaw, selectionBump, selectionBumpL1, selectionCutoffC, selectionExtensionC (verbatim, in
CutoffBump); `smooth_cutoff` (verbatim statement, in Cutoff, namespace KAM.Planetary). Helpers have distinct
names (selectionPosPow_*, selectionBump_*, selectionMult*, selectionKernel*, selectionBumpScaled*, selectionConv_*).
No signature declaration of B04 belonged to another package. (selectionExtensionC is only a def here; its
boundedness/use belongs to B05.)

Approach: x ↦ max(s,0)^(N+1) is C^N by induction (HasDerivAt incl. s=0 via little-o), bump = raw/∫raw, ∫raw>0,
L1 constants integrable for j ≤ μ. Kernel φ = ∏ ψ_δ(w_j), δ=t/4; coordinate k-th derivative formula
(iteratedFDeriv at e_{i_1..i_k} = ∏ ψ^{(mult)}), exact L1 = δ^{-k} ∏ L1(mult), then multilinear expansion
(n^k index tuples, sSup over multiindices, BddAbove proved). χ = 1_A ⋆ φ with A = {infDist ≤ t/4}; derivative of the
convolution proved by induction from HasCompactSupport.hasFDerivAt_convolution_right.
E nonempty / compact, hn, hμ, ht1 are unused (statement kept verbatim; only unused-variable warnings).

Checks: gate build `inp_lake_build.sh <wt> KAM.Planetary.WeakKAM.Cutoff` -> Build completed successfully (9084 jobs),
no sorry/error. `#print axioms KAM.Planetary.smooth_cutoff` -> [propext, Classical.choice, Quot.sound].
scripts/lint_sources.sh: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; "KAM.lean is out of date"
is expected (generated; not edited). Long lines wrapped. No maxHeartbeats anywhere; no heartbeat design signals.
Uncertainties / errata / deviations: none. A few deprecated-name warnings remain (e.g. ContinuousLinearMap.coe_sum')
in CutoffTensor; harmless.

AUDIT FOCUS (design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B04 and Appendix; audits DESIGN-P11B-design-audit-{1,2}.md; signatures .drafts/design/P11BSignatures.lean): (1) selectionBumpRaw, selectionBump, selectionBumpL1, selectionCutoffC, selectionExtensionC and smooth_cutoff = signature file exactly, and the B04 slice COMPLETE; (2) definitions mean the source objects (bump, exact bump integral constants); smooth_cutoff proof sound (iterated derivative of convolution via HasCompactSupport.hasFDerivAt_convolution_right, tensor kernel, scaling); no added premises; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM: compare with Q1's p11c_bump/p11c_mollifier family and the many selection* helpers). Audit ONLY KAM/Planetary/WeakKAM/Cutoff*.lean.

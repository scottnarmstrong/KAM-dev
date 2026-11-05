GLOBAL recheck (sonnet-global-B) of docs/graph/B/DEPGRAPH.md (revised, 18 nodes), roots b:2.2#B1-T and b:2.3#B1-E

VERDICT: ACCEPT WITH FINDINGS

Prior findings 1-6: all resolved.
1. Root and step hypotheses now follow the frozen premises (L351, L501). Ψinv is a left inverse, N is arbitrary, R is differentiable, and there is no open-image or C^2-inverse premise. chart-transport (L184) no longer assumes inverse regularity. normal-form-commutes (L413) uses g = H∘Ψ − R = N∘I with g differentiable and N arbitrary, which is dischargeable from the root hypotheses.
2. chart-transport is the push-forward (L186): DΨ·X_{H∘Ψ} = X_H∘Ψ, with invertibility from symplecticity and nondegeneracy. The roots' conclusions include Ψ(Ψinv z) = z (L353, L503). See finding A below for a residual gap.
3. periodic-reduction (L315-342) is new and states its hypotheses as follows. hRper makes the field angle-periodic. Confinement to closed C_b comes from first-exit. Continuation is applied on the compact fundamental cell and transported by integer shifts. ext:ode#local covers uniqueness and restart. The external compact-K contract (L158) is now applied only to a compact cell, which is consistent. The B1-T chain is: periodic-reduction → first-exit → action-derivative → chart-transport.
4. The uniqueness → hamiltonianVectorField edge is present (L246, L250).
5. The first-exit quantifiers no longer assume existence (L294-295, L441-442). The conclusion is "for any such w on I ∋ 0 while in the chart domain".
6. Roots state `exists T1 > T`, `Ioo(-T1,T1)` (L352-353, L502-503).

Also re-verified:
- Root identity and contract ids are unchanged.
- The bracket node b:defs#bracket is consistent with `d/dt F = {F,G}` under X_G = (G_J, -G_φ) and with the frozen `q_j R_{p_j} − p_j R_{q_j}`.
- The closure is purely conjunctive, with no alternative routes.
- Shared steps are used consistently by both roots.
- The plan and FREEZE-PROPOSAL line citations I spot-checked are accurate.
- I did not re-read DEPGRAPH_COVERAGE.md in this pass, so the coverage count (20 items, 6 excluded) is not rechecked.

Remaining findings, all minor:

A. chart-transport contract does not carry Ψ(Ψinv z) = z.
- The roots' edges (L365, L515) attribute "Psi(Psiinv(z t)) = z t" to chart-transport.
- chart-transport's SOURCE_HYPOTHESES (L184) omit `hΨinv` (the NOTE at L203 lists only hPsi, hPsiV, hPsisymp), and its SOURCE_CONCLUSION (L186) omits the clause.
- Fix: add `Ψinv∘Ψ = id on D` to the hypotheses and "Ψ(Ψinv(z t)) = z t, with (φ,J)(t) = Ψinv(z t) = w t" to the conclusion. Otherwise the edge justification at L365 and L515 is unsupported.

B. Undischarged regularity premises in the continuation steps.
- periodic-reduction (L322) and b:2.3#compact-continuation (L471) assume "field C^1 on the chart domain" and, for B1-T, "X_{H∘Ψ} 1-periodic in phi".
- Neither step depends on chart-transport or on b:defs#hamiltonianVectorField, where this regularity is derived (H∘Ψ is C^2 on the open chart domain from hH, hΨ, hΨV; periodicity from hRper and hHΨ).
- They also use local existence for the chart field X_{H∘Ψ}, so the edge to ext:ode#local needs this C^1 premise.
- Fix: add DEPS on b:brief2#chart-transport and b:defs#hamiltonianVectorField with EDGE rationale "C^2 regularity of H∘Ψ gives C^1 chart field". Alternatively, state in the contracts that the premise is discharged by the root hypotheses hH, hΨ, hΨV.

C. (Cosmetic) First-exit uses of the derivative premise.
- The first-exit contracts assume the derivative bound only on closed C_b or closed E_b. The stopped-drift contract requires |f'| ≤ eta on the whole interval.
- The step must apply stopped-drift on the stopped sub-interval before the first exit. This is already implied by "stopped drift up to the first exit time" (L306), and no change is needed unless the reviewer wants it explicit.

No new problems in carriers, constant scope, AND/OR structure, or external inputs.

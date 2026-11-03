GLOBAL review (sonnet-global-B) of docs/graph/B/DEPGRAPH.md (GRAPH_VERSION 4), roots b:2.2#B1-T and b:2.3#B1-E

VERDICT: ACCEPT WITH FINDINGS

Checked and found sound:
- Root identity: FROZEN_DECL KAM.EffectiveStability.torus_confinement and oscillator_confinement match the two frozen files. The contract ids effectiveStability.d72.* are consistent. The three definition anchors (hamiltonianVectorField, symplecticForm, oscillatorAction) are the ones imported by both frozen files. I did not recompute the ABI hashes.
- Quantifier order: the frozen conclusion is `exists T1 > T, exists z`, stated after `w0`. Bounds are stated for every `|t| <= T`. The uniqueness clause is over order-connected `I` containing 0, restricted to `Ioo (-T1) T1`. The graph's SOURCE_QUANTIFIERS and SOURCE_CONCLUSION agree with this (DEPGRAPH L323-324, L468-469).
- Carriers use `Fin n -> R` and max norm, and no Euclidean norm occurs in the closure. Margins for B1-E are in actions (L6). The bracket in the frozen B1-E `hRη` is `q_j R_{p_j} - p_j R_{q_j}`. This is consistent with `dI/dt = {I,H}` under `X_H = (∂_p H, -∂_q H)`.
- AND/OR: the closure is purely conjunctive and no node has alternative routes. This is correct, because every dependency is genuinely needed.
- Shared steps (chart-transport, stopped-drift, uniqueness, ext:ode#local, ext:ode#compact-continuation) are used by both roots with consistent contracts.
- Line citations into the plan (L847-855, L90-99, L157-163, L195-196) are accurate.
- No unquantified constants.

Findings:

1. (Moderate) Node hypotheses describe the plan, not the frozen OD-B2 statements. Steps consume premises that no root hypothesis supplies.
   - Root SOURCE_HYPOTHESES (L322, L467) state "Psi ... with C^2 inverse on its image" and, for B1-E, "N C^2 near prod[0,b+eps], R C^2".
   - Frozen text: `Ψinv` is only a left inverse on the chart domain (`hΨinv`). There is no openness of the image and no differentiability of `Ψinv`. `N` is an arbitrary function. `R` is only `DifferentiableOn`. Differentiability of the normal part comes only from `H ∘ Ψ - R` (see the frozen docstrings).
   - b:brief2#chart-transport (L157) assumes "onto an open subset with C^2 inverse". It is therefore not dischargeable from the root hypotheses.
   - b:2.3#normal-form-commutes (L382) assumes "N C^1". This is false as a root premise, so the step as written is not dischargeable. The true route is rotation invariance of the differentiable function `g = H∘Ψ - R = N∘I`, so that `{I_j, g} = 0` without differentiating `N`.
   - Fix: amend these SOURCE_HYPOTHESES to the frozen premises. Rewrite normal-form-commutes as "g differentiable on E_(b+eps) and g = N∘I imply {I_j, g} = 0 (rotation invariance)". Remove the "C^2 inverse" and "open image" premises from chart-transport and the roots. Keep the plan text as provenance only.

2. (Moderate) The chart-transport direction and conclusion do not match the frozen use.
   - The graph says "w = Psi^{-1}∘z solves w' = X_{H∘Psi}(w)" with `z` given (L152, L159).
   - The frozen statement is an existence result, so the needed step is the push-forward. One solves `w' = X_{H∘Ψ}(w)` in chart space, then `z = Ψ∘w` solves `z' = X_H(z)`. Here `fderiv Ψ` is injective hence invertible, because Ψ is symplectic and `symplecticForm` is nondegenerate. Then `Ψinv(z t) = w t` by `hΨinv`.
   - The frozen conclusion clause `Ψ(Ψinv(z t)) = z t` is in neither the root SOURCE_CONCLUSION (L324, L469) nor the chart-transport conclusion.
   - Fix: restate the contract as push-forward, `DΨ·X_{H∘Ψ}(w) = X_H(Ψ w)` on the chart domain. State the nondegeneracy of `symplecticForm` as part of the step. Add `Ψ(Ψinv(z t)) = z t` to the root conclusions and to the transport conclusion. Note that `H∘Ψ` is C^2 on the (open) chart domain because `hΨV` and `hH` hold.

3. (Moderate) The B1-T continuation step is mis-modelled against its external input.
   - b:2.2#periodic-continuation (L293) assumes "Psi image of the fundamental cell compact in V" and angle periodicity. Neither the compactness in V nor Ψ-equivariance is a frozen premise. The frozen statement has only `hRper` (periodicity of `R`). Periodicity of `H∘Ψ = N(J) + R` is automatic in the angle.
   - ext:ode#compact-continuation (L131) requires a compact `K` inside the open domain. The lifted cylinder `{|J| <= b}` is non-compact in `φ` (plan L162-163 says exactly this). So the external input cannot be applied as stated.
   - The actual argument must either (a) use periodicity of the chart field to bound it and reduce to a compact quotient, or (b) use a bounded-field or uniform-margin continuation variant. The graph neither states this nor says which variant is used.
   - The edge to ext:ode#local is justified by "T=0 and the start of continuation" (L306). Uniqueness plus translation invariance of the chart field is the more likely real use, because the reduction to the fundamental cell needs it.
   - Fix: restate the hypotheses as "first-exit confinement in closed C_b; H∘Ψ periodic in φ (from hRper); closed fundamental cell inside C_(b+eps)". Add an explicit periodic-reduction step or contract, or replace ext:ode#compact-continuation for B1-T by an external contract for continuation with a bounded field at uniform distance from the boundary. Drop "compact image in V". The statement "stays in V" comes from `hΨV`, which is a root hypothesis.
   - B1-E is fine here. Closed E_b is compact (`q²+p² <= 2b`) and lies inside E_(b+eps).

4. (Minor) Missing edge: b:brief2#uniqueness (L219) depends only on ext:ode#local. It also needs the regularity of the field `X_H` on V, since the field is C^1 because `H` is C^2. The edge to b:defs#hamiltonianVectorField is therefore missing. The root has this edge (L337), so the closure is unaffected, but the step's own DEPS are incomplete.

5. (Minor) Quantifier of the first-exit steps. The conclusions (L267, L411) should say "for any solution `w` on an interval `I ∋ 0` inside the chart domain, and every `t ∈ I` with `|t| <= T`". Existence of `w` is supplied by continuation, not by first-exit. The graph direction (continuation depends on first-exit) is correct and not circular, but the contract wording should say so. Also note that `a_j >= 0` and `b_j > 0` are not frozen premises. They follow from `hw₀` and `hmargin`, and the compactness of closed E_b uses them. Mention this in the continuation contracts.

6. (Minor) Statement-strength wording. The roots' SOURCE_CONCLUSION says "an open interval U containing [-T,T]". The frozen text is the symmetric `Ioo (-T1) T1` with `T < T1`. The frozen form implies the graph form, so this is only a wording mismatch. State it exactly for consumers.

Nothing found for: carriers, constant scope, edge line citations, coverage inventory, cross-section sharing, AND/OR structure, or missing externals beyond finding 3. The ODE local-existence and uniqueness contract and the compactness argument are the only external inputs.

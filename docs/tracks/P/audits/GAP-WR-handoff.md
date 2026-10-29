# GAP-WR prover handoff (branch inp-gwr, b09722a1; off inp-p11ap10 (landed, fixedSunPlanetaryKAM sealed); package run by the main orchestrator)


## Files (all new)
- `KAM/Planetary/Preparation/WrapperNodeCore.lean` (192 lines): `p11_wr_chain_dom`, `p11_wr_ham_core` -- copies of
  `p11PreparedCoreOf_chain_dom` / `_chain_eq` taking "rescaled point lies in the slow half-box" as hypothesis
  instead of membership in the complex prepared domain.
- `KAM/Planetary/Preparation/WrapperNodeChain.lean` (328): F2.
- `KAM/Planetary/Preparation/WrapperNodeTube.lean` (204): F3.
- `KAM/Planetary/Preparation/WrapperNodes.lean`: facade importing both.

## F2 stepP:p11:wr-chain
Carrier `p11WrR n = {z | |r_i| < 2 ∧ |ρ'_i| < π/2}` (r = first n actions, ρ' = last n), all real angles.
- `p11_wr_chain_node`: AnalyticOnNhd, `IsSymplecticOn eps`, full lattice equivariance `Ξ(z+k)=Ξ(z)` on all of
  `Fin (n+n) → ℤ` (and `z+k ∈ ℛ`), and injectivity modulo the lattice, all on `p11WrR n`.
- `p11_wr_xi_node`: `IsChart eps (p11WrXi D nu eps) (p11WrR n)` + lattice/injectivity (Part-1 form).
- `p11_wr_ham_node`: `H_fix (Ξ z) = eps * ((h0+g2)(A_ε z).2/eps + f3(A_ε z)/eps).re` on `p11WrR n`
  (the Hamiltonian Ĥ_ε = N+P extended to ℛ; physical-time identity). Note `p11WrO` came from the
  complex prepared domain `T_{σ/72}×(K+1)`, where the prepared data N,P are *defined*; the factors
  (Ψ₂, Θ̂, chart) are analytic on larger sets, the true limit being the slow half-box.
- Only change of hypotheses: `hpe : π ε ≤ s₂` replaced by `h4 : 4 ε ≤ s₂` (needed since |ε r| < 2ε must lie in
  the half-box of radius s₂/2; π ε ≤ s₂ gives only 1.57ε). `p11_four_eps_le_s2_ev` proves `4ε ≤ s₂`
  eventually (same proof as `slow_pe_eventually`). All other hypotheses unchanged (hC hF hS heps hsm).
  Consumers: the existing eventual choice of ε0 must additionally include `p11_four_eps_le_s2_ev`.
  Literal statement is TRUE; no new mathematics; no erratum. (The older exports are untouched, so the signed
  wrapper still uses `p11_wr_chain`.)

## F3 stepP:p11:wr-tube
`p11_wr_tube_node`, for every real `z` with `|z.2 j| ≤ 1` (no domain hypothesis; membership in `p11WrO` is
derived), with `v` = real fast-map output:
 `∑_j (v.1_j² + v.2_j²) ≤ 4 n ε` ∧ `∀ i, Γ_i(planetBlock (p11ChartInput C v) i) ≤ 2 n ε` ∧
 `p11WrChain z ∈ circularTube`.
Smallness hypotheses (all eventual): those of `p11_wr_tube` except `hR2`, which is replaced by
`hd : 28 d² ≤ ε` (d = 9εM_F/(2π α₁ r_z), the fast displacement) and `hΓε : 2 n ε ≤ δ`.
`p11_ev_tube_node` proves hd and hΓε eventually (d ≤ ε^{1/2}/6 eventually; ε<δ/(2n)); hP1, hP2, hR1, hεM,
hpe, hsm come from `p11_ev_slowDisp`, `p11_ev_tube.1`, `p11_wr_small` as in `Wrapper.lean`. Key new
inequality `p11_tube_sq4`: (u+e)² ≤ 7/6 u² + 7 e², so x²+y² ≤ 3.5ε + 14d² ≤ 4ε. Literal statement true.

## Checks
- Gate builds of WrapperNodeCore, WrapperNodeChain, WrapperNodeTube, WrapperNodes: success, no warnings from my files.
- `#print axioms` of p11_wr_chain_node, p11_wr_xi_node, p11_wr_ham_node, p11_wr_tube_node, p11_ev_tube_node,
  p11_four_eps_le_s2_ev: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK, but prints
  "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated root; I did not edit it -- the orchestrator
  must regenerate to include the 4 new modules).
- No sorry/axiom/maxHeartbeats; lines ≤ 100; all names unique in KAM.

## Uncertainties / deviations
- Wrapper is not rewired to use the nodes (append-only). The eventual-ε0 lemma bundle for the nodes is left to the
  orchestrator (components listed above).
- Deviation: `4ε ≤ s₂` instead of `π ε ≤ s₂` for the chain node. No suspected errata in the source.

ORCHESTRATOR RULING (OVERNIGHT 04:40): append-only literal exports for the two step nodes left open by audit P11A-P10-audit-1 (F2 wr-chain carrier, F3 wr-tube constants); no existing declaration changes.

AUDIT FOCUS: (1) stepP:p11:wr-chain (DEPGRAPH.md:21036-21037; blueprint p11-cp09-preparation.tex:250): do p11_wr_chain_node / p11_wr_xi_node / p11_wr_ham_node state the literal conclusion on the source carrier |r| < 2, |rho'| < pi/2 (all real angles)? Judge the hypothesis change pi eps <= s2 -> 4 eps <= s2: is it an eps-smallness premise of the node's 'for eps small' kind (proved eventually by p11_four_eps_le_s2_ev), not conclusion-shaped? (2) stepP:p11:wr-tube (DEPGRAPH.md:21137; blueprint :253): does p11_wr_tube_node state sum <= 4 n eps and Gamma_i <= 2 n eps and the tube inclusion literally, under the node's hypotheses? (3) WrapperNodeCore's copies of the prepared-chain lemmas are sound. Audit ONLY KAM/Planetary/Preparation/WrapperNodeCore.lean, WrapperNodeChain.lean, WrapperNodeTube.lean and WrapperNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

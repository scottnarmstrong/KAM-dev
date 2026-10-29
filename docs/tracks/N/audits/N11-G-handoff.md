# N11-G prover handoff (branch inp-n11g, 983942ad; offloaded package run by the main orchestrator)


## Files
- new: `KAM/Nekhoroshev/Partial/BlockData.lean` (about 330 lines; imports Partial.{Setting,Constants,Domain,Hessian},
  ResonanceGeometry.{Covering,Projection}, Stability.ResonantStabilityHess)

## Graph nodes
- `bpN:p11:block-data`, `stepN:p11:bd-cover`, `stepN:p11:bd-24`, `stepN:p11:bd-5`: `KAM.Nekhoroshev.block_data`
  (signature copied verbatim from `.drafts/design/N11Signatures.lean`; the 5 private helpers have distinct `bd_*` names).

## Approach
- Reconciled with the landed Part 8: `KAM.Nekhoroshev.covering` / `cutoffs` exist (ResonanceGeometry/Covering.lean), no
  invention needed. `CoverParams := ⟨9/8, 1/32, r0, M1, m1, K, A⟩`, validity needs `36 M1/m1 + √2 ≤ A = 40 Mc/m`
  (uses `m ≤ Mc` from `hessian_at_sign`). Covering on `{Ic}` with `freqR = frequencyMap (signedH a σ)`.
- bd-cover: `radius_bounds` gives `rTheta ≤ r ≤ r0/(AK) = R0/K` for `Λ ≠ ⊤`. `Λ = ⊤` is excluded: cutoffs (4) gives
  `‖Π_⊤ ω‖ = euclid ω < m1 r0/32 ≤ g1 ≤ ‖ω‖` (needs `lattice ⊤ = ⊤`, `r0 ≤ 32 g/m`).
- bd-24: nonresonance on the ℓ¹ ball `K/√n` by `cutoffs` (3) (`K/√n ≤ K` since `n ≥ 1`), with
  `freq = ι ∘ frequencyMap` via `freq_realInclusion`; `NearResonance` witness `δ = resonanceDistance Λ ω` (strict by
  cutoffs (4), valid for Λ = ⊥ too: projection 0 gives δ = 0 < m1 r/32); `|ω·v| ≤ δ|v|` by perpendicularity + Cauchy-Schwarz;
  Lipschitz by `freqLipschitz_of_complex` with the `FastConvex` Hessian bound on radius r (transport of the column form by
  `bd_hess_form`).
- bd-5: `ε = m1 rΘ²/2^14` exactly (from `K^(2n) ε = ε0`), then `rΘ ≤ r`; second bound from `m1 ≤ √n M1 2^4`.

## Checks
- gate build `inp_lake_build.sh /root/code/KAM-inp-n11g KAM.Nekhoroshev.Partial.BlockData`: succeeds, no warnings in the file.
- `#print axioms KAM.Nekhoroshev.block_data`: `[propext, Classical.choice, Quot.sound]`.
- `sh scripts/lint_sources.sh`: line-width, module, frozen guard, ABI hashes all OK; only message is
  "KAM.lean is out of date" (generated file, not edited per rules: needs `scripts/gen_root_imports.py` by the orchestrator).
- No `set_option`, no sorry/axiom; no `EuclideanSpace`.

## Uncertainties / errata / deviations
- Hypothesis `hκ` (kappa ≥ 6) is not used by the conclusion (kept verbatim; consumed by `have _hκ := hκ`). Likewise `hμ`
  only enters through positivity of ε. No source defect found; no deviation. Strict closeness for Λ=⊥ checked separately as the design asked.
- No design signals (no heartbeat issues).

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-G (block_data; Part 8 covering/cutoffs reconciled first) and its node table; both N11 design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. Contains N11-E3 at round 1 (its round-2 fix appends companions only). Audit ONLY KAM/Nekhoroshev/Partial/BlockData.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

# GAP-P9dict prover handoff (branch inp-gp9d, ee06ef0f; off inp; graph-gap programme package run by the main orchestrator)


Files: new `KAM/Planetary/SecularSpectrum/DictNodes.lean` (committed on inp-gp9d; imports
`PlanarTorsion.SpectralAdapter`, `Nondegeneracy.SymmetricRelation.Limits`; nothing imports it).
No landed file edited. KAM.lean not regenerated (lint prints "KAM.lean is out of date": orchestrator).

Node -> declarations (all in `KAM.Planetary.SecularSpectrum`):
- `charpoly_smul_eq_prod_sorted`: charpoly (c • A) = ∏ (X - C (c * sorted A)) (spectral theorem +
  `charpoly_mul_comm`; no Mathlib charpoly-smul lemma needed).
- `sorted_smul` (general): A Hermitian, c > 0 => sorted (c • A) = c • sorted A.
- `p9_dict` (literal conclusion), conjunction:
  (n ≥ 2, any Data D, a ∈ axes n): sorted (2•coeffs D a) = fun j => 2 * sigma D a j; charpoly of
  2•Q_h = ∏ (X - 2σ_j); ∀ j, σ_j < 0 ∧ 2σ_j < 0.
  (n = 1, any D : Data 1, a): coeffs D a = 0; sorted (2•coeffs) = 0; 2 * sigma = 0 (Ω₁ = 0).
  Premises: only n ≥ 2 and a ∈ axes n (source hypotheses); no dependency output taken as premise.
- `p9_dict_planar`: the landed frozen Omega (`fun _ I j => 2 * p11c_sigma p (p.axes I) j` in
  `p11cB_fhat_clause`) at a ∈ p11c_axes equals sorted (2 • coeffs (p11cSecularData p hp) a), and all
  entries negative. No mismatch found: the frozen Omega IS literally 2 * (explicit sorted eigenvalues
  of Q_h); `p11c_sigma_eq_sigma` links it to `SecularSpectrum.sigma`.

Checks: `inp_lake_build.sh ... KAM.Planetary.SecularSpectrum.DictNodes` succeeded (9198 jobs, no
warnings from this file); `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK
(only the expected "KAM.lean is out of date"). `#print axioms` of p9_dict, p9_dict_planar,
sorted_smul: [propext, Classical.choice, Quot.sound]. Lines ≤ 100, no heartbeat options.

Not Lean content (no landed CP10 (8) declaration exists; grep found none):
- "CP10 (8) insensitive to the overall sign": convention only (|Σ Ω_j k_j| unchanged under Ω ↦ -Ω).
- Labelling/index conventions (Remark items 3): conventions; `sorted` is the increasing labelling.
- Source-side "the matrix printed in Fej04r is Q_h^F = 2Q_h" is the E-P-Fej04r-3 erratum, already
  recorded; nothing new.
Uncertainties: the "S = C_0 + Σ 2σ_j R̃_j" part of item (1) is the already-proved `diagonalize`
(first clause), not re-exported. Suspected errata/deviations: none. Design signals: none.

ORCHESTRATOR RULING (OVERNIGHT 03:55): bpP:p9:dict has real content (Omega_j = 2 sigma_j via the eigenvalues of 2 Q_h); this package exports it. The labelling-convention clauses with no Lean content are listed in the handoff, not findings. KAM.lean regeneration is the sub-orchestrator's job at merge.

AUDIT FOCUS: read NODE bpP:p9:dict in docs/graph/P/DEPGRAPH.md (SOURCE_CONCLUSION) and blueprint-P/parts/p9-secular-spectrum.tex L155-L160; verdict: does p9_dict (with p9_dict_planar for the frozen Omega) state the node's literal conclusion: Omega_j = 2 sigma_j with sigma_j the eigenvalues of the halved Q_h, Omega the eigenvalue list of 2 Q_h, all negative, the n = 1 clause; is the general sorted_smul / charpoly_smul_eq_prod_sorted sound; is the n >= 2 split a faithful case split of the source (n >= 1) rather than an added premise; is the 'CP10 (8) insensitive to the overall sign' clause handled honestly? Audit ONLY KAM/Planetary/SecularSpectrum/DictNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

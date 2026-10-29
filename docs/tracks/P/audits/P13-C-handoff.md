# P13-C prover handoff (branch inp-fx13c, e0a53043; built on inp with P8e (prepared/amount/data_star, landed); offloaded package run by the main orchestrator)


## Files
- KAM/Planetary/FixedAssembly/General.lean: `FixedAssembly.n_general_of_wrapper`
- KAM/Planetary/FixedAssembly/Main.lean: `FixedAssembly.fixed_of_wrapper`
- KAM/Provider/Planetary/FixedSunPlanetaryKAM.lean: `KAM.Provider.Planetary.fixedSunPlanetaryKAM_of_wrapper`
  (the provider imports only the frozen FixedKolmogorovSet Def and FixedAssembly.Main).

## Statements
Each takes `{n} (hw : ∀ {n : ℕ} (D : P11Physical n), ∃ eps0, 0 < eps0 ∧ ∀ eps, 0 < eps → eps < eps0 →
∃ S : Set (Phase (n*2)), MeasurableSet S ∧ 0 < volume S ∧ volume S < ⊤ ∧
S ⊆ circularTube D.G D.m0 D.m D.a (p11Zeta D) ∧ ∀ z ∈ S, ∃ w K theta0, z = K theta0 ∧
Set.range K ⊆ S ∧ IsPhysicalTorus (fixedHamiltonian D.G D.m0 D.m eps) w K)` (signed wrapper, verbatim,
quantified over n), then the binders of the signed signature.
1. `n_general_of_wrapper`: conclusion = signed `n_general` (let d := tubeD (axisGap a), D := tubeBigD ..).
2. `fixed_of_wrapper`: conclusion = signed `fixed` = frozen anchor type.
3. `fixedSunPlanetaryKAM_of_wrapper`: conclusion = frozen anchor type exactly.
Orchestrator one-liners once wrapper lands: `n_general ... := n_general_of_wrapper (fun D => wrapper D) ...`
(hw is implicit in n, so `fun D => wrapper D`), likewise fixed / provider.

## Discharge
- ng-const/ng-wrap: `hw` at `P11Physical` built from the data (`StrictMono a` from `hsep`; injectivity
  from hsep); eps0 taken from hw before eps; d, D = canonical constants, `0<d`, `d<D` by
  `axisData_canonical`, `tubeD_lt_tubeBigD`.
- ng-phys: `fixedKolmogorovSet_of_tube` at gamma = axisGap a, A = axisMax a; `p11Zeta P` is
  definitionally `tubeRadius eta (axisGap a)`; torus witness `z = K theta0` is flipped with `.symm`.
- fx-split: `hn.eq_or_lt`; fx-2: `rfl` substitution then `FixedAssembly.n2`; fx-n: general route, packaging
  `(eps0, tubeD.., tubeBigD..)`.

## Checks
- Gate build of Main and the provider module: success (9649 jobs), no sorry/warnings in my files.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; only message:
  "KAM.lean is out of date" (orchestrator regenerates; I did not touch it).
- `#print axioms` of all three: [propext, Classical.choice, Quot.sound].
- No use of p11_pr_b, so the h.2 -> h.2.1 projection fix is not needed here.

## Uncertainties / errata / deviations
None. hw is quantified with implicit n inside; signed wrapper has `{n} (D)`, so `fun D => wrapper D` fits.

ORCHESTRATOR RULING (OVERNIGHT 03:50): parametric form while P11A-P10 proves the signed wrapper. Each of n_general_of_wrapper, fixed_of_wrapper, fixedSunPlanetaryKAM_of_wrapper has ONE extra hypothesis hw that must be exactly the signed KAM.Planetary.wrapper statement (P11ASignatures.lean ~1196) universally quantified over n and D, nothing else. The signed n_general, fixed and the provider theorem fixedSunPlanetaryKAM are one-line applications added by the orchestrator when wrapper lands; their absence is NOT a finding.

AUDIT FOCUS: (1) hw's type is VERBATIM the signed wrapper's conclusion (compare with /root/code/KAM-inp/.drafts/design/P11ASignatures.lean); (2) n_general_of_wrapper's conclusion is VERBATIM the signed n_general and fixed_of_wrapper's the signed fixed (/root/code/KAM-inp/.drafts/design/P1213Signatures.lean ~330, ~343); (3) fixedSunPlanetaryKAM_of_wrapper's conclusion is EXACTLY the frozen anchor's type: run the exact-type probe in a scratch file: example : (forall hw, type_of% @KAM.Frozen...fixedSunPlanetaryKAM) style, i.e. check that (fun hw => @KAM.Provider.Planetary.fixedSunPlanetaryKAM_of_wrapper hw) has, after instantiating hw, the frozen theorem's type (read KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.lean; never edit it); (4) provider quarantine: the provider module imports only frozen Defs and FixedAssembly.Main, nothing imports the provider, no DRAFT_SORRY anchor is imported; (5) graph nodes bpP:p13:n-general, ng-const, ng-wrap, ng-phys, bpP:p13:fixed, fx-split, fx-2, fx-n are established in the proofs; (6) #print axioms: propext, Classical.choice, Quot.sound only. Audit KAM/Planetary/FixedAssembly/General.lean, KAM/Planetary/FixedAssembly/Main.lean and KAM/Provider/Planetary/FixedSunPlanetaryKAM.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

# GAP-I1c independent audit 1

Overall verdict: **FAIL for literal closure of both graph nodes**. The arbitrary-frequency
repair itself **PASSes**: the tested `ω` is independent of `ω₀`, with no Diophantine premise
on `ω`. Build, axiom inspection, and kernel replay pass. The remaining blocker is the
inherited stronger setting (F1), not a proof-soundness failure.

Audited 2026-10-29 in `/root/code/KAM-inp-gi1c`, HEAD
`8511ce7241dc9071ca66b6908a2883035938ed63`, comparison branch `inp` at
`74976f317ab6852d2a7222801accf8ce39ba0615`. Full `git diff inp...HEAD` contains only the
317-line addition `KAM/Iso/Linear/FullRangeAnyOmega.lean`. Initial untracked handoff was
preserved. Scope is this module only; no frozen anchor is proved or sealed by this package.
The prompt's exact worktree report path overrides the generic brief's main-worktree destination.

## F1 — retained N1 prevents literal source-hypothesis closure

Both main exports take `hS : Setting n τ M σK σB σT D H ω₀ γ`
(`FullRangeAnyOmega.lean:128`, `:265`). `Setting` extends `Standing`
(`KAM/Iso/Linear/Defs.lean:45-49`), which extends `Params`
(`KAM/Apost/Standing.lean:41-52`), including
`tau_ge : (n : ℝ) - 1 ≤ τ` and positivity of all three σ parameters.

The actual source setting says:

> “Let $n\ge2$ and $\tau\ge0$ (I-G1 has $\tau\ge n-1$; only $\tau\ge0$ is used here)”

Locator: `blueprint-I/parts/p1-iso-linear.tex:31`; graph source hypotheses at
`docs/graph/I/DEPGRAPH.md:2396` and `:2719` refer to this setting. Thus the exports do not
have just the literal source setting as their input. This is the existing N1/D2 issue,
expressly left unchanged by the handoff, rather than a newly discovered false mathematical
claim. No `SettingSrc` or `IsDiophantine.n_sub_one_le_tau` is present under `KAM/` in this
checkout (`rg` finds no matches). The package neither imports nor supplies that bridge.

The controlling gap plan, `/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-I.md`,
§2.1 explicitly says the stronger τ range blocks every literal Part-1 parent and assigns
the missing source-setting bridge to GAP-I1a. It also explains why Dirichlet emptiness should
make the extra τ condition derivable from the setting's Diophantine `ω₀`. That explanation
is not an elaborated bridge here. No ruling changing this source contract was supplied.
This report does not claim a counterexample or lost mathematical content.

Required closure: compose these any-ω results with an established literal source-setting
bridge (with the necessary σ parameter treatment), or obtain an explicit applicable ruling
on D2/N1. Merely reusing `Setting` does not close the recorded source contract.
The module docstring's “literal” descriptions at lines 21-22 therefore overstate full node
closure; they correctly describe the frequency generalization alone.

## Declaration and node table

All names below are in `KAM.Iso.Linear.AnyOmega`; line numbers refer to the audited module.
No new declaration is SIGNED in the old Appendix-A signature collection: the signed landed
`Linear.reduced` and `Linear.perturbation_noA5` are untouched. These are distinct, unsigned
exports, assessed against the literal graph contracts and the GAP-I1c plan.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| `bpI:p1:reduced`, (a)-(d) | `reduced_anyOmega` :128 | FAIL (literal node); PASS frequency repair | All principal conclusions and residual equivalence match, at arbitrary tested ω; F1 remains. |
| `bpI:p1:perturbation-noA5`, (a)-(e) | `perturbation_noA5_anyOmega` :265 | FAIL (literal node); PASS frequency repair | All five bounds, carriers, strips, smallness and constants match; only tested-frequency bound is `‖ω‖ ≤ Theta`; F1 remains. |
| `fi-dl`, conditional helper | `fi_dL_anyOmega` :44 | PASS as helper | Differentiates the true invariance error at independent ω; local holomorphy and domain hypotheses suffice under supplied Standing. |
| `fi-22`, conditional helper | `fi_LtOXN_anyOmega` :70 | PASS as helper | Symplectic Hamiltonian derivative and differentiated Gram identity give the exact signed formula. |
| `fi-blocks`, conditional helper | `fi_reduced_anyOmega` :83 | PASS as helper | Block identity is re-established using the any-ω derivative identities; no assumed reduced output. |
| `rd-expand`, conditional helper | `reducer_mulVec_isoResidual_anyOmega` :101 | PASS as helper | Product-rule expansion, QP and QE identities give the unconditional projected residual. |
| Track-K `pt-xn`, conditional helper | `norm_normalField_sub_le_strip_anyOmega` :185 | PASS as conditional helper only | Takes previously obtained frame estimates `hNN`, `hG'`, `hAb`; not a standalone literal Part-I parent/node closure. |
| Track-K `pt-torsion`, conditional helper | `norm_torsion_sub_le_anyOmega` :217 | PASS as conditional helper only | Takes `hNN` and normal-field estimate `hXX`; these are discharged in the parent proof, not assumed by its export. |

The declared GAP-I1c slice consists of the two parent nodes. Every requested conclusion is
present in those exports under Setting. No additional graph closure is claimed for the
conditional helper exports. Full literal slice completion fails solely on F1.

## Frequency, premises, conclusions, and quantifiers

The use of a standing `ω₀` is legitimate for the question specifically posed in the handoff:
the source setting itself contains a Diophantine frequency. Renaming that standing frequency
and then binding a fresh tested `ω` avoids imposing Diophantine conditions on the tested
one. The printed elaborated types bind `ω₀` in the outer setting and bind tested `ω`
separately after the setting. In particular `reduced_anyOmega` permits tested `ω = 0`;
`perturbation_noA5_anyOmega` permits it subject only to its displayed norm bound. No premise
relates these two frequencies.

The uses of `ω₀`-standing data are for `differentiableOn_ham`, `ham_symplectic`,
`FrameAux.norm_linMat_le`, `PerturbationAux.norm_linMat_sub_le` (via `ham_mvt`), and Params.
These are Hamiltonian regularity, Taylor, and constant facts independent of tested ω.
Directional differentiation involving tested ω is established separately by the new helpers
or the existing arbitrary-direction Cauchy estimate. No outgoing conclusion is fed back
as a parent premise.

In particular, the perturbation parent obtains `hb, hc, hdN` from `frame_items` at :296,
then derives `hG'`, `hKD`, `hAb`, `hXX`, and finally the torsion bound at :297-305. Its public
type contains neither `hNN` nor `hXX`. The reduced parent likewise derives the block/projected
identity internally, and requires the bordered equation only for the source's conditional
residual clause. Invertibility of P is required exactly for clause (d).

Reduced (a)'s displayed matrix identity gives its stated “hence” vector identity by matrix
multiplication; the latter also appears explicitly as `hQLω` in the projected-identity proof
at :113-119. Clause (b) is expressed through the existing `isoResidual`, `bordOp`, and
`isoLinError`, whose bodies give exactly the source signs. The error bound is stronger
in that it is unconditional. Pointwise bordered-equation premises are also stronger than
requiring the equation everywhere first. Source primary/reality assumptions on K are not
needed by these local identities and are omitted, strengthening the result.

For reduced, setting data precede tested ω, r', ξ, ξω as required. Perturbation keeps all
constants/setting data outside the pointwise conclusions; it introduces β,d as implicit
universals before K/K' rather than following the prose list literally. All these are
universal inputs; there is no existential constant with enlarged dependence. The constants
are the unchanged `mSize`, `Theta`, `C_B`, `C_DN`, `C_DT`. The strip radii and matrix row-sum
operator norm agree with the node records. There is no A5 or bordered-twist premise.

## Definitions and totality

There are **no new def, abbrev, or structure declarations**. Local `set` bindings are proof
abbreviations for the displayed derivative and complexified frequency. Existing frozen
`gramMatrix`, `normalFrame`, `torsion`, `invarianceError`, and `IsDiophantine`, and existing
`isoResidual`, `isoLinError`, `bordOp` were inspected for the used meanings. Gram inverses
are used with `IsUnit det G` on the applicable strips; the residual inverse is used with
`IsUnit det P` and the proved invertibility of Q. Holomorphy on open domains supplies genuine
derivatives. No junk inverse or derivative fallback supplies a conclusion.

## Independent checks

All Lean-related commands were run serially with `LEAN_NUM_THREADS=1`, at nice level 5.
No heartbeat, recursion, or synthesis override was used. Scratch files were confined to
`.lake/abi-scratch/` and removed after recording results.

1. Targeted gated build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gi1c KAM.Iso.Linear.FullRangeAnyOmega
   [inp-gate] slot 1 acquired 05:25:02 for KAM.Iso.Linear.FullRangeAnyOmega
   Build completed successfully (3198 jobs).
   exit 0
   ```

   The compile-gate script invokes `nice -n 5 lake build`.

2. Axiom and fresh-declaration application probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPI1cAudit.lean
   exit 0; no errors or warnings
   ```

   The probe imported the audited module; ran `#print` and `#print axioms` on all eight
   declarations; and copied each main theorem's statement under a fresh audit name with
   a direct application body listing its explicit binders in order. This confirms the
   displayed exported statements elaborate and their applications impose no hidden premise.
   It is not a claimed comparison against a nonexistent any-ω frozen signature.

   Each of the following printed exactly the axiom set
   `[propext, Classical.choice, Quot.sound]` (line wrapping normalized):

   ```text
   KAM.Iso.Linear.AnyOmega.fi_dL_anyOmega
   KAM.Iso.Linear.AnyOmega.fi_LtOXN_anyOmega
   KAM.Iso.Linear.AnyOmega.fi_reduced_anyOmega
   KAM.Iso.Linear.AnyOmega.reducer_mulVec_isoResidual_anyOmega
   KAM.Iso.Linear.AnyOmega.reduced_anyOmega
   KAM.Iso.Linear.AnyOmega.norm_normalField_sub_le_strip_anyOmega
   KAM.Iso.Linear.AnyOmega.norm_torsion_sub_le_anyOmega
   KAM.Iso.Linear.AnyOmega.perturbation_noA5_anyOmega
   ```

   Provider/frozen-type equality and frozen seal-body probes: **not applicable**; neither
   graph node names a frozen declaration, and no provider is added.

3. Kernel replay (one invocation; the package has one module):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.Linear.FullRangeAnyOmega
   replaying KAM.Iso.Linear.FullRangeAnyOmega
   exit 0
   ```

4. Source hygiene and protected paths:

   - `git diff --check inp...HEAD`: exit 0, no output.
   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty.
   - Module has 317 lines; maximum line length is 100 Unicode characters.
   - Module header, copyright, public imports, docstring, public section: present.
   - All eight public short names occur only once as declarations under `KAM/`; no root
     declaration or reused public helper short name is introduced.
   - Recursive local import traversal found 69 KAM modules and no frozen theorem or
     provider module. Thus no DRAFT_SORRY theorem import; manifest-state lookup of imported
     frozen theorem anchors is vacuous. Frozen definition imports are allowed.

5. Lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1267 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   **PASS WITH NOTES** under the brief's explicit generated-root exception: the only
   failure is the expected stale `KAM.lean`. No generated file was regenerated. No forbidden
   token, resource override, EuclideanSpace, line-length, file-size, or other lint failure
   was reported. ABI checking ran after kernel replay, with no concurrent Lean invocation.


## Source/blueprint defects, deviations, and limits

No new suspected defect in a pinned external source was found. The pre-existing wording
ambiguity at blueprint p1 :484 (“Assume setting” and “ω … any”) is resolved here in the
frequency sense requested by the overnight ruling; :567 similarly permits arbitrary tested
frequency with its bound. This does not resolve the independent source-setting range issue F1.

The source setting is not refuted: the missing Dirichlet/setting bridge is a formalization
obligation, not evidence that τ ≥ 0 is a source erratum. No source or graph text was edited.
The only audit repository write is this report. Existing signed declarations and consumers
remain unchanged; consumer adequacy under stronger Part-2 data does not establish the literal
Part-1 node contracts.

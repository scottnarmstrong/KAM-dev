# GAP-DEF independent package and definitions audit

Audited worktree: `/root/code/KAM-inp-gdef`. HEAD `7123b45772fe326f4d467f98c477a8a27f7f32a1`; comparison `inp...HEAD` against current inp `9976b4dd0d8e59de945b6af97947f1ac87e778a9`. The complete three-dot diff contains only the two new modules below (211 lines). The pre-existing untracked handoff was read and preserved. This report follows the user's explicit worktree destination, overriding the generic brief's main-worktree destination.

## Verdict and scope

**PASS WITH NOTES for GAP-DEF.** No frozen theorem/provider is supplied or proposed for sealing; provider/frozen-type and seal-body probes are therefore inapplicable. These are unsigned, formula-defined additions under the handoff's overnight definition-node ruling, which remains for owner review.

- `bpP:p3:limitmap#data`: **CLOSABLE**, with the object-by-object LEAN_REF inventory below. The general checked map and scaled Lipschitz predicate fill the two previously missing objects.
- `bpP:p11:sec-E#data`, scoped F1/F2: **PASS; both resolved**. LEAN_REF: `KAM.Planetary.p11SecE`, `KAM.Planetary.mem_p11SecE`, `KAM.Planetary.p11Rescale_polydisc_iff` and `KAM.Planetary.p11Rescale_secE_iff`.
- The **whole `sec-E#data` node is not certified CLOSABLE** by this package. DEFS-P3-audit-1.md:34–38 also retains the signed selector F3 and coverage of the complex H₂ identity, domain table and normalized frequency formulas. The handoff expressly excludes these. Adding E does not extend existing theorems from `p11WrV` to E.

Read authority: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the named package brief and handoff; docs/tracks/P/statement.md; P23-LEAN-DESIGN.md (node table and Appendix A), P11A-LEAN-DESIGN.md (node table and sec-E object inventory); the two named blueprint passages; DEFS-P2/P3 audit findings. Imported frozen carrier/strip/neighbourhood definitions were inspected. No frozen theorem anchor is imported by this slice.

## Definition fidelity: limitmap data

Here TS = `KAM/Planetary/TwoScale/`, AV = `KAM/Planetary/Averaging/`. Source: blueprint-P/parts/p3b-two-scale-limit.tex:43.

| Source object | Lean declaration / LEAN_REF | Classification | Reason on public carrier |
|---|---|---|---|
| S | `KAM.Planetary.sc`, TS/LimitMapScale.lean:42 | FAITHFUL-WITH-NOTE | `(θ,I)` and flattened `(2πθ/s,I/R)` permute the source's action-first blocks. Use `R=rhoHat p`, `s=p.s`. This preserves the max norm. |
| S⁻¹ | `KAM.Planetary.unsc`, TS/LimitMapScale.lean:37; `sc_unsc`, `unsc_sc` | FAITHFUL-WITH-NOTE | Literal inverse factors `s/(2π)` and `R`; inverse theorems explicitly require nonzero radii. Zero radii use Lean division, and are not certified as invertible source rescalings. No conditional fallback or witness. |
| absolute value star | `KAM.Planetary.limitmap_data`, TS/LimitMapScale.lean:30; `limitmap_data_eq_norm_sc` | FAITHFUL-WITH-NOTE | Literal scaled max formula, with positive radii for its norm meaning. Exactly the signed P23 Appendix A definition (line 1143). Negative/zero parameters are outside the source norm regime. |
| Gcheck | `KAM.Planetary.limitmapCheck`, TS/LimitMapDefs.lean:32 | FAITHFUL-WITH-NOTE | Formula `sc ∘ G ∘ unsc` for every G and every RCLike carrier, with no chosen map or fallback. Conjugation/inverse interpretation requires nonzero radii; all relevant laws carry those premises. |
| L_star | `KAM.Planetary.LipStar`, TS/LimitMapDefs.lean:71 | FAITHFUL-WITH-NOTE | Predicate that L bounds pairwise scaled differences on the supplied set, exactly the requested reading of “Lipschitz constants”. It does not select an optimal scalar. Its explicit real carrier matches the real stage maps; checked-map equivalent uses `sc '' S` parametrized by x,y in S. The formula is total even for empty sets or arbitrary real L; no claim of a nonnegative optimal constant is made. |
| calD_j | `KAM.Planetary.realTube`, AV/Setting.lean:48; `KAM.Planetary.phaseTube`, TS/LimitMapPsi.lean:36; `mem_realTube_iff` | FAITHFUL-WITH-NOTE | Substitute `Ds j`, `(seq p j).ρ/2`; action tube is literal real neighbourhood, and `phaseTube` adds unrestricted real angles with Lean's angle-first order. No arbitrary stage sequence is asserted to satisfy the iteration. |

## New declarations and slice completeness

All names below are in `KAM.Planetary`. LM = TS/LimitMapDefs.lean; SE = `KAM/Planetary/Preparation/SecEDefs.lean`. The design node tables name the older LimitMapScale/Prepared interfaces; neither names additional graph nodes assigned to these two new files. GAP-DEF's explicit supplemental slice is complete for general checked maps, scaled Lipschitz notation, E and F2. It is not a proof of the entire preparation node.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| limitmap data | `limitmapCheck` (LM:32) | PASS WITH NOTE | Literal general composition; source parameter regime as above. |
| characterization | `limitmapCheck_apply` (LM:36) | PASS | Definitional equality. |
| composition | `limitmapCheck_comp` (LM:40) | PASS | Uses `unsc_sc`; nonzero premises necessary. |
| identity | `limitmapCheck_id` (LM:46) | PASS | Uses `sc_unsc`; same premises. |
| coordinate identification | `limitmapCheck_sc` (LM:51) | PASS | Literal conjugacy application, no domain restriction or added map property. |
| displacement identification | `limitmapCheck_sub_id` (LM:57) | PASS | Linearity and round trip, not an assumed displacement estimate. |
| limitmap data | `LipStar` (LM:71) | PASS WITH NOTE | Set-indexed bound predicate, not a chosen infimum. |
| characterization | `lipStar_iff_check` (LM:75) | PASS | Pairwise max-norm bound in scaled coordinates; positivity gives literal norm equivalence. |
| restriction/enlarged bound | `LipStar.mono` (LM:82) | PASS | Ordinary conditional monotonicity helper, distinct qualified name; assumes an input bound only for this monotonicity claim. |
| stepP:p3:pl-lip view | `PsiSteps.psi_lipStar` (LM:97) | PASS | Definitional repackaging of proved `psi_lip_step`, exact constant 192(a+b)c^j Ehat_j and half-radius stage domain. No Lipschitz conclusion in PsiSteps fields: fields are inherited iteration regularity, reality, domain and displacement premises, produced together by `iterative_steps` (LimitMapPsi.lean:92). |
| F1 action factor | `p11SecEPolydisc` (SE:25) | PASS | All complex actions, radii 2 and π/2, zero centre, strict coordinate norms. |
| F1 full E | `p11SecE` (SE:28) | PASS | Exact product of strip sigma_F/72 and the full polydisc. Unsigned formula; no selected prepared record. |
| F1 characterization | `mem_p11SecE` (SE:31) | PASS | Literal coordinate inequalities on entire carrier, including n=0. |
| F2 mapping iff | `p11Rescale_polydisc_iff` (SE:39) | PASS | Entire polydisc maps into the half V₂ action box iff `2 eps ≤ s₂/2`. Only premises `0<n`, `0<eps`, with C and nu unrestricted; no hidden positivity on s₂/nu or small-eps assumption. |
| mapping over E | `p11Rescale_secE_iff` (SE:89) | PASS | Adds exactly strip nonemptiness `0<C.sigma`; otherwise an empty angle strip could make mapping vacuous. |

The four new definitions are `limitmapCheck`, `LipStar`, `p11SecEPolydisc`, `p11SecE`; all are direct formulas on their full public carriers. There are no new abbrevs, structures, choice/default branches or arbitrary witnesses. Noncomputable/expose section follows the repository module convention.

F2 necessity was checked independently: if r=s₂/2<2eps, use the real fast coordinate t=max(0,r/eps)<2 and zero slow coordinates. Its image has distance eps*t≥r, contradicting strict target membership. Positive dimension supplies a fast coordinate. Sufficiency uses eps times the strict input norms and the weak boundary comparison; equality `2eps=s₂/2` is valid for open polydiscs. This works even if s₂ is nonpositive (both sides then fail). The E theorem inserts zero angles; the action projection is independent of angles.

No changed declaration is SIGNED. Existing signed definitions such as `limitmap_data` and `p11Rescale` remain unchanged; the former matches P23 Appendix A:1143 and the latter P11A Appendix:1911. There is consequently no newly narrowed signed theorem whose consumers need an applicability exception. `psi_lipStar` is a conditional stage-output view, not a replacement proof of the iteration theorem.

## Validation receipts

All Lean/Lake checks are serialized in this audit, with `LEAN_NUM_THREADS=1`. Probe and kernel commands use `nice -n 5`; lint runs under nice so its internal ABI Lean subprocess inherits that priority. No resource-budget overrides were used.

1. Targeted compile gate:

```sh
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gdef KAM.Planetary.TwoScale.LimitMapDefs KAM.Planetary.Preparation.SecEDefs
```

Exit 0. Gate output: `[inp-gate] slot 1 acquired 07:26:19 for KAM.Planetary.TwoScale.LimitMapDefs KAM.Planetary.Preparation.SecEDefs`; final output: `Build completed successfully (9450 jobs).` Existing dependencies replay deprecation warnings (including `PreparedBasic.lean`'s `dif_pos`); neither audited file emits a new warning.

2. Temporary formula/axiom probe:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GapDefAudit.lean
```

Exit 0. Four examples independently check the general composition, LipStar's literal inequality, full E formula and F2's exact type with only positive n/eps. Provider-type/seal-copy checks are N/A because there is no provider export or frozen theorem in this package. Every new public theorem was probed; exact axiom output:

```text
'KAM.Planetary.limitmapCheck_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.limitmapCheck_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.limitmapCheck_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.limitmapCheck_sc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.limitmapCheck_sub_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lipStar_iff_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.LipStar.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.psi_lipStar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_p11SecE' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_polydisc_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_secE_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay (one invocation after the probe completed):

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.LimitMapDefs KAM.Planetary.Preparation.SecEDefs
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.Preparation.SecEDefs
replaying KAM.Planetary.TwoScale.LimitMapDefs
```

4. Source lint, after kernel replay completed:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the explicitly permitted generated-root difference. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1281 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No forbidden token, overlong line/file, module-system, errata-rendering, frozen-anchor or ABI failure was reported. `KAM.lean` was deliberately not regenerated, as both AGENTS.md and the audit brief require.

5. Static integrity: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty (exit 0). `git diff --check inp...HEAD` is silent (exit 0). A recursive local import-closure scan finds 499 module names, 64 frozen files, all manifest `SEALED` definitions; no frozen theorem or provider occurs. Thus no DRAFT_SORRY import is hidden transitively.

Both files have copyright/module/public import/docstring/public section (the latter via `@[expose] public noncomputable section`). LM has 108 physical lines, maximum 97 characters; SE has 103 lines, maximum 100 characters. The handoff's “lines <=100” is satisfied as the repository's **line-width** rule; neither the stated approximate file sizes nor AGENTS' 1500-line file cap imposes a 100-line file cap. No forbidden tokens, instances, namespace-open changes affecting the root, or resource overrides are introduced. No new package-specific declaration short name duplicates an existing declaration; `LipStar.mono` is qualified under the new predicate and does not shadow root `mono`.

## Uncertainties, errata and deviations

No suspected new pinned-source erratum or false frozen declaration was found. This audit checks the supplied local blueprint/design, not a fresh transcription from external PDFs. The overnight unsigned-definition ruling still needs owner review, as the handoff says.

The pre-existing blueprint notation at p3b-two-scale-limit.tex:48 prints `$L_*(\check\Psi_k-\mathrm{id};\mathcal D_k\times\R^n)$`, whereas line 43 defines both checked coordinates and scaled norms. Read literally this mixes coordinates; the proof at :58 uses the ordinary max norm on the scaled image. The implementation consistently proves the equivalent unscaled-map/star-norm statement and `lipStar_iff_check` supplies the conversion. This is a notation clarification for the orchestrator, not a new source repair or a failure of the requested definition predicate.

No implementation changes or source repairs were made by this auditor. Only this report is retained; temporary probes under this worktree's `.lake/abi-scratch/` are deleted after checking. No state-changing git command, generated root regeneration, frozen/manifest edit or package-cache operation was performed.

# Independent audit: P11A-P8D (tracks I/N/P)

Verdict: **PASS WITH NOTES for the authorized parametric assembly** `KAM.Planetary.data_star_of_amount`. The signed `data_star` conclusion and the universally quantified signed `amount` premise match exactly. No mathematical or hygiene defect was found in `Datum.lean`. This is infrastructure acceptance, not a frozen-anchor seal or unconditional proof of `data_star`.

## Scope and authority

Audited on 2026-10-29, branch `inp-p11ap8d`, HEAD `dc185656e4a2f06ec77e58f56b46d540e254cc86`, against `inp` at `9ffcb3343be139ca6f003a42f0cab4ab6027fbb6`. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the handoff and its AUDIT FOCUS, track-P statement, design node/row and revision-2 reconciliation, blueprint remark, and relevant imported definitions.

The full `git diff inp...HEAD` contains exactly one addition: `KAM/Planetary/Preparation/Datum.lean` (159 lines). No provider or frozen theorem is added or sealed. The handoff was already untracked. Per the explicit user override, this report is in this package worktree, not the main inp worktree. No production source was edited.

The handoff's 03:25 orchestrator ruling explicitly permits the distinct conditional name and defers the signed `data_star` application until P8e supplies `amount`. The absence of that unconditional export is therefore not a finding.

Signed authority: `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, `amount` at 1135–1143 and `data_star` at 1282–1301. SHA256: `fd2c245ea48f1b99f36beb02bba0095e9a55b070be0eae178198fdf20011b9e9`.
Audited module SHA256: `35de1b7261e9e1ad8607081d4281a73d6987489e526638ba71d621cf2adcf734`.

## Declaration coverage

All names below are in `KAM.Planetary`.

| Node / clause | Declaration (Datum.lean line) | Verdict | Reason |
|---|---|---|---|
| data-star compact box | `p11PreparedBox_isCompact` (29) | PASS | Closed finite product of compact intervals; valid even in dimension zero. |
| data-star box measure | `p11PreparedBox_volume` (32) | PASS | Lebesgue volume of the unit-side Pi box equals one. |
| data-star diameter | `p11PreparedBox_diam` (37) | PASS | Pi max-norm upper bound and opposite constant corners attain distance one. Explicit nonempty-coordinate condition is necessary; `D.n_ge` supplies it. |
| data-star exponent gap | `p11_tau_max_gt` (58) | PASS | Each right-hand maximum entry is strictly below its corresponding left entry by one after casting `n+n`. |
| source numeric helper | `p11_one_le_L` (68) | PASS | Extracts the existing `L ≥ 1` source clause from `holo_chart`; no added premise. |
| data-star M0 normalization | `p11_one_le_M0` (73) | PASS | Uses `L ≥ 1` and `(2n+1)^(mu+1) ≥ 1`; stronger positive lower bound is harmless. |
| data-star beta normalization | `p11_beta_bounds` (84) | PASS | For positive eps below one and `eps*beta_J ≤ 1`, proves beta positive and beta ≤ 1/2, M ≥ 2, hence beta ≤ min 1 M. |
| `bpP:p11:data-star`; design row P11A-P8D | `data_star_of_amount` (111) | PASS WITH NOTES | Exact signed conclusion under exactly the authorized, universally quantified signed amount conclusion. Covers all signed conjuncts; unconditional application and downstream typed integration remain separate. |

Design table line 189 maps only `bpP:p11:data-star` to `Preparation/Datum`; row 738 specifies the same chosen Q, fixed geometry, A1–A4 and amount smallness. The same Q is preserved. No additional graph node is silently replaced by a weaker unsigned namesake.

## Signature and proof review

A scratch probe copied only the proposition text of signed `amount` and `data_star`, replacing neither with a proved implementation nor importing draft bodies. It defined `AuditSignedAmount` and `AuditSignedData`, then elaborated:

```lean
example : type_of% @data_star_of_amount :=
  (show ∀ {n : ℕ} (D : P11Physical n),
    (∀ nu : ℝ, ∀ hnu : 1 ≤ nu, AuditSignedAmount D hnu) →
      AuditSignedData D from @data_star_of_amount)
example {n : ℕ} (D : P11Physical n)
    (hamount : ∀ nu : ℝ, ∀ hnu : 1 ≤ nu, AuditSignedAmount D hnu) :
    AuditSignedData D := by
  exact data_star_of_amount D hamount
```

Both passed at default heartbeats. An independent text extraction also returned `True` for each whitespace-normalized literal comparison: signed amount conclusion against the body of `hamount`, and signed data_star conclusion against the result. Thus neither conclusion strength nor quantifier/constant dependence was weakened. There is no frozen-provider type or seal-body comparison applicable here; the fresh-name direct application above checks the authorized assembly instead.

The only non-source premise is exactly the allowed upstream amount output. In particular it includes `P11PreparedFullSpec` because signed amount itself includes that clause. The proof obtains epsA and c3 for each nu, retains c3 and Q, and shrinks only epsA to `min epsA (1/(1+beta_J))`. It reuses the amount/spec result at the smaller epsilon without assuming any new analytic conclusion. The shrink depends on fixed physical data and the old threshold, in the permitted existential order. Compactness, measure, diameter, the strict tau gap, beta normalization, and M0 normalization are proved separately.

## Definitions and consumer applicability

There are **no new definitions, abbreviations, structures, instances, or bundled hypothesis fields** in this diff. All eight additions are theorems. The imported `p11PreparedData` (PreparedData.lean:107–108) is a signed witness selector with a `default` branch outside the existence guard. This proof never infers a specification from that fallback: for each used epsilon, `hamount` explicitly supplies the full specification of that very selected Q. There is no reliance on a junk value.

The signed conjunction supplies the analytic/jet/amount data of the blueprint remark (p11-cp09-preparation.tex:243–245) through `P11PreparedFullSpec`; geometric and numeric normalizations are supplied here. The helpers use Pi max-norm geometry and retain the distinct scalar Euclidean direction gauge used in imported specifications.

**Integration limitation:** P11A-LEAN-DESIGN.md:856–861 explicitly says, “Once Part11a5 delivers its exact admissibility predicate, P8D must prove a typed bridge from these conjuncts into it.” No such bridge, K5 budget, K6 displacement statement, or wrapper application is exported here. Existing `WeakKAM/Data.lean:64–114` exposes `SelectionData`/`SelectionPerturbation`, but there is no current production consumer of `data_star_of_amount` or `Preparation.Datum`. Therefore this audit accepts the exact signed, expressly authorized conditional slice; it does not certify the full prose remark or consumer integration as completed. Before marking the broader row fully integrated, reconcile that API, prove the typed bridge, apply the original K5/K6 theorems with their constant order, and supply the unconditional amount application. This is a recorded design obligation, not a hidden added hypothesis or a defect in the proved implication.

## Hygiene and independent checks

All Lean-related commands ran serially with `LEAN_NUM_THREADS=1` and `nice -n 5`. The compile gate was used for the targeted build; no clean, update, cache fetch, root regeneration, manifest edit, or state-changing git operation occurred.

1. Full comparison: `git diff inp...HEAD` showed only the 159-line module. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output. `git diff --check inp...HEAD` exited 0 with no output.
2. Build:
   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap8d KAM.Planetary.Preparation.Datum
   [inp-gate] slot 2 acquired 03:29:14 for KAM.Planetary.Preparation.Datum
   Build completed successfully (9419 jobs).
   exit 0
   ```
   Replayed dependency warnings concerned unused variables/simp arguments and deprecated names; none was reported in Datum.lean.
3. Probe: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP8DAudit.lean`, exit 0. Only warning: the copied signed amount binder `hnu` is unused in its proposition. Every public export was checked:
   ```text
   'KAM.Planetary.p11PreparedBox_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11PreparedBox_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11PreparedBox_diam' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_tau_max_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_one_le_L' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_one_le_M0' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_beta_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.data_star_of_amount' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```
4. Kernel replay: `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.Datum`, exit 0. Complete output: `replaying KAM.Planetary.Preparation.Datum`. This single invocation covers the only new lemma module; there is no provider module.
5. Static inspection: 159 lines, maximum line length 95; copyright, module, public imports, module docstring and public section present. No forbidden proof escapes, heartbeat/recursion overrides or EuclideanSpace. All public names remain in `KAM.Planetary`; all eight short names have no other declaration in KAM. No harmful root shadow was introduced.
6. Recursive project-import inspection: no provider import, no frozen theorem import; all 64 imported frozen definition files have matching manifest entries in state SEALED. No DRAFT_SORRY anchor is imported.
7. Source lint: `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`, exit 1, complete output:
   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1227 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```
   The sole failure is the stale generated root expressly excepted by the brief; it was left untouched. No substantive lint failure occurred.

## Errata, deviations, and uncertainties

No new suspected source or blueprint defect was established by this module. The typed bridge limitation above is already expressly recorded in the design. No deviation was introduced by the auditor. The handoff's “~150 lines” is accurate (159); its later “lines ≤ 100” is understood as line width, independently measured at 95 characters maximum. All audit probes and temporary logs are removed after recording results.

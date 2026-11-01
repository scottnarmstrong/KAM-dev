# Package LP-FREEZE7R: draft 7 revision 1 (statement audit F1, F2, N2) and staging of the providers

Freeze preparation. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md`.

Two worktrees:
- **Part A:** `/root/code/KAM-inp-lp-freeze7`, branch `inp-lp-freeze7` at 309cef26 (draft 7 plus the audit report).
  The generator scripts are in its `.drafts/freeze7/`.
- **Part B:** `/root/code/KAM-inp-lp-providers`, a new branch `inp-lp-providers` that the orchestrator creates from the
  part-A result.

## Part A: the revision (gating; do it first)

Read `docs/tracks/LP/freeze/STATEMENT-AUDIT-DRAFT7-1.md` in full; F1, F2 and N2 are at lines 33–100. Apply exactly
the auditor's replacement texts, which root-b8 has confirmed as the right fix.

1. **F1.** Add two new source definitions,
   `KAM.Planetary.Spatial.spatialSourceBarycentricPositions` and `…Velocities`, each taking `(hν : ∀ i, 0 < ν i)` and
   `(hμ : 0 < μ)` and definitionally the raw map, with the auditor's exact text.
   - Add them to the implementation in a new file, for example `KAM/Planetary/Spatial/SourceBarycentric.lean`, so that
     frozen names equal implementation names.
   - In LP2 and LP2-H, replace `∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →` by `∀ μ : ℝ, ∀ hμ : 0 < μ, μ ≤ μ₀ →`, and replace the
     reconstruction expressions by the source maps.
   - The closing theorems must still close by `exact`. If they need a restated implementation theorem (because of the
     `hμ` binder), add it to `SpatialSafety/SourceCorollary.lean` or the new file; never add a premise.
   - **Characterizations under OD-11 (b).** If the implementation proves barycentric identities (zero mass-weighted
     position sum; `p_i = ν_i V_i`-type relations; see `KAM/Planetary/Spatial/Newton.lean:58–80`) on the guarded
     carrier, propose them as the characterization of the two new definitions: one semantic unit each, with new
     frozen theorem files and providers. Otherwise mark them `N/A_LITERAL` with the reason. Do the same check for
     consistency with how draft 7 treats the frozen planar barycentric maps.
2. **F2.** Use the auditor's exact role paragraph for `actionAxis`, `eccDeficit`, `spatialBarycentricPositions` and
   `spatialBarycentricVelocities`. In §4.2 change their role from `literal` to `internal`, and add them to the §4.4
   internal-helper inventory.
3. **N2.** Use the auditor's exact sentence at P:16–18.
4. **Regenerate** the approval object: the proposal, all draft files, the manifest entries and the counts. Use the
   generator in `.drafts/freeze7/`, updated as needed.
5. **Rerun checks (a), (b) and (c)** fully, and the closure computation. Record the output in
   `docs/tracks/LP/freeze/verification-draft-7r1.txt`.
6. **Diff against the audited state.** Add a hash diff of every draft file against the audited 809aa0dd: list the
   files that changed, the new files, and confirm that nothing else changed.
7. **Update the stated limitation (N1).** The simulated check (a) does not exercise the real provider/import graph;
   part B does that partly.

## Part B: stage the providers (root-b8 item 1)

On branch `inp-lp-providers`, in `/root/code/KAM-inp-lp-providers`:
- For each of the 39 draft-7 theorem anchors (5 headline and 34 characterizations), plus any new characterizations
  from F1, add one provider module at the path draft 7 §2/§5 names (`KAM/Provider/Planetary/{StrongAMD,Spatial}/<Name>.lean`).
  Follow the form of an existing provider (for example the one for `KAM.Planetary.planetaryExponentialSafety` or
  `KAM.Nekhoroshev.partialConvex_nekhoroshev`; find it under `KAM/Provider/`).
  - Each provider states the theorem as `KAM.Provider.….<name>` with **the anchor's exact type text**. It imports the
    implementation only, since the frozen files do not exist yet. Its proof is one line over the proved implementation
    theorem.
  - AGENTS rule 9: providers are quarantined. No module may import them, so do not add them to the root (check how
    `scripts/gen_root_imports.py` skips providers).
- In a transient file:
  - check that each provider's elaborated type is Expr-equal (`Expr.eqv`, or `==` after `instantiateMVars`) to the
    draft anchor's type, the anchor text elaborated in scratch as in check (c);
  - check the exact seal body `by exact KAM.Provider.….<name> <explicit binders>` against the scratch anchor;
  - record both in `docs/tracks/LP/freeze/providers-staging.txt`.
- Build the providers with `lp_build.sh`, run lint and the short-name check, and run `#print axioms` on every provider
  (the result must be standard).
- **Nothing goes under `KAM/Frozen/` or `manifest/`.**

## Owned files

Part A: draft-7 documents and draft files, `docs/tracks/LP/freeze/verification-draft-7r1.txt`, the new
implementation file(s), and `.drafts/freeze7/`.

Part B: the `KAM/Provider/Planetary/**` files on `inp-lp-providers` and `docs/tracks/LP/freeze/providers-staging.txt`.

## Handoff

Write `docs/tracks/LP/audits/LP-FREEZE7R-handoff.md` (committed) and `.drafts/handoff-LP-FREEZE7R.md`. When part A
is complete, before starting part B, `touch .drafts/READY-LP-FREEZE7R-A` in the freeze7 worktree so the re-audit can
start. At the end, `touch .drafts/READY-LP-FREEZE7R` in the freeze7 worktree.

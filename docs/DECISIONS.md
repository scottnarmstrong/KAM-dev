# Decisions

Owner rulings are marked *(Scott)*. Orchestrator decisions are revisable unless the owner has ruled on them.

- **D1 (2026-10-27) Headline.** The positive-measure KAM theorem for nearly-integrable real-analytic Hamiltonians
  H = h(I) + f(θ, I) on Tⁿ × B with general Kolmogorov-nondegenerate h. *(Scott: "Let's go for the positive-measure
  theorem for general Hamiltonians!")*
- **D2 (2026-10-27) Route and framework.** *(Scott: "go with your recommendations")*
  - A-posteriori KAM at fixed frequency in the parameterization-method form (no action-angle changes of
    variables, no generating functions, no inverses of diffeomorphisms): primary source HL19 Thm 3.1 with d = n,
    cross-checked against GJLV05.
  - One invariant torus per Diophantine frequency from the unperturbed torus; measure of the union through
    Lipschitz dependence on the frequency (source being pinned).
  - Internal norms: weighted ℓ¹ Fourier(–Taylor) coefficient norms; real-analytic hypotheses converted once.
  - Flows, not maps. Coordinates: angles in ℝⁿ with ℤⁿ-periodicity, actions in an open subset of ℝⁿ; no manifolds.
  - The mechanical-systems theorem (Chierchia's KAM Lectures, Thm 6) is not a milestone; it stays a reference.
- **D3 (2026-10-27) Independence.** Independent development; `arnold1963-kam` and PlasmaLean are references, not
  dependencies. *(Scott, by accepting the recommendation)*
- **D4 (2026-10-27) Toolchain.** `leanprover/lean4:v4.35.0` with Mathlib `v4.35.0`. Palomar's
  `PalomarSubmission/toolchains.json` requires at least `v4.35.0-rc2`.
- **D5 (2026-10-27) Workflow.** Frozen-anchor workflow (skills `lean-project-architecture`, `lean-orchestrator`):
  statements frozen before proofs, one declaration per frozen file, providers below anchors, sealing by
  `by exact`, independent audits; Lean module system everywhere.
- **D6 (2026-10-27) HQ and errata.** The README is the campaign HQ, regenerated at least every 20 minutes and
  after every commit; an errata and deviations ledger is kept for every source we formalize. *(Scott)*
- **D8 (2026-10-27) Route verdict for the measure layer** (orchestrator; revisable). Rate ε^{1/4}, with
  γ ~ ε^{1/4}. Local uniqueness for flows is proved by us, adapting GJLV05 Thm 2 (§6, §8); no source states it.
  Lipschitz dependence on the frequency comes from re-applying the a-posteriori theorem (CCdlL13, Cor. 29–30); the
  defect is O(ε/γ⁴). The measure step uses a McShane extension and a lipeomorphism (Pos01, Prop. 1–2, App. B;
  BC17, §6.5–6.6). Details in `docs/PLAN.md`, "Route verdict".
- **D7 (2026-10-27) Hosting.** GitHub repository `scottnarmstrong/KAM-dev`, created private (*Scott: "commit and push"*)
  and made public the same day (*Scott: "can you make the dev repo public?"*). Source PDFs stay out of git.
- **D9 (2026-10-27) Statement rulings Q1–Q5.** *(Scott: "go with your recommendations on Q1–Q5")*
  - Q1: the headline carries the rate meas(complement) ≤ C·ε^{1/4}; the qualitative (1 − κ) form, with no
    boundary condition, is a corollary.
  - Q2: angle period 1 (Tⁿ = ℝⁿ/ℤⁿ).
  - Q3: each torus is invariant and carries the linear flow with a Diophantine frequency; it is Lagrangian, a
    real-analytic embedding, and close to the unperturbed torus.
  - Q4: gates: the fixed-frequency a-posteriori theorem (HL19 Thm 3.1, d = n), local uniqueness for flows (ours),
    and the measure of the Diophantine set (Pos01 §1d).
  - Q5: n ≥ 2; B bounded, with a regular boundary for the rate form; ∇h bi-Lipschitz on B̄; h + f real-analytic
    on a uniform complex neighbourhood of Tⁿ × B̄.
- **D10 (2026-10-27) Public ledger.** The errata and deviations ledger stays public, CANDIDATE entries included;
  each is labelled unverified until checked against the pinned PDF. *(Scott: "keep the ledger public, it's fine")*
- **D11 (2026-10-27) Statements approved and frozen.** *(Scott: "approve all", on the review page of statement draft
  v0.2, claude.ai/artifact/WP8cHuhjvWTSSMkubhU8f2)* The approval covers the three decisions on that page: the
  inner boundary-layer reading of "regular boundary"; G1's uniform constants with margin μ and bound γ̄
  (ledger D-G1-1); and G1's explicit conclusion margins. Frozen: 5 theorem anchors (`KAM/Frozen/Theorems/`,
  `DRAFT_SORRY`) and 20 definitions (`KAM/Frozen/Defs/`, sealed whole files), byte-identical to the approved text,
  hashed in `manifest/frozen-anchors.json` (file, prefix/suffix and elaborated ABI hashes). Providers:
  `KAM/Provider/<Name>.lean`, quarantined until sealing. Draft and audit evidence, including the Lean refutation of
  draft G1 v0.1, archived at `/mnt/HC_Volume_106379410/kam-evidence/2026-10-27-statements-v0.2/`.
- **D12 (2026-10-27) Working norms** (orchestrator; refines D2). The frozen G1 hypotheses are sup-norm bounds of a
  Hamiltonian on an arbitrary open domain, so G1, G2 and the measure layer are proved in sup norms on complex
  domains, as in HL19 and GJLV05. Products and compositions are then immediate, and Cauchy estimates are
  one-variable. Weighted coefficient norms enter only through the cohomological equation and Fourier-coefficient
  arguments, joined to sup norms by the strip bridge (blueprint Part 1).
  - The cruder small-divisor exponent τ + n replaces Rüssmann's τ. This is harmless: G1's constants may depend
    on ρ, and only the γ-dependence matters downstream.
- **D13 (2026-10-27) Phase 1 and packages.** *(Scott: "start Phase 1, and coordinate Zohar's work as packages.
  Just fix his code if you don't like it")*
  - Phase 1 runs as in `docs/PHASE1.md`: blueprint parts p0–p4, then the dependency graph.
  - Collaborators pick work from `docs/campaign/PACKAGES.md`.
  - The orchestrator may change collaborators' code directly; it reviews and fixes such code as it lands.
- **D14 (2026-10-27) Parallel tracks.** *(Scott: "Let's incorporate all this planetary stuff into the plan. Let's
  formalize all of it! It's ok if it is on parallel tracks.")* Four tracks (`docs/TRACKS.md`):
  - K: positive-measure KAM;
  - I: isoenergetic KAM, two-degree-of-freedom confinement, the restricted three-body problem;
  - N: Nekhoroshev (quasi-convex, then steep);
  - P: planetary (properly degenerate KAM, planar two-planet problem, the fixed-Sun n-planet variant, the spatial
    theorem later).

  Each track runs the full pipeline, with its own owner approval of exact Lean statements before freezing.
- **D15 (2026-10-27) Authors.** The repository's authors are Scott Armstrong and Zohar Komargodski (GitHub
  zkomargo). *(Scott)*
- **D16 (2026-10-27) Author headers of the frozen files.** *(Scott: "yes change the frozen file authors too")*
  - The copyright and `Authors:` lines of the 25 frozen files (and of the provider stubs) now name Scott Armstrong
    and Zohar Komargodski.
  - This is a hash move that does not change meaning. Every byte after the header comment is unchanged (checked
    file by file), and all 25 elaborated ABI hashes are identical before and after.
  - Only `full_file_sha256`, `prefix_sha256` and `definition_closure` hashes in `manifest/frozen-anchors.json`
    changed. Log: `docs/MANIFEST-CHANGES.md`.

- **D17 (2026-10-27) Track N dimension.** N-HEAD (quasi-convex Nekhoroshev with exponents 1/(2n)) is stated for
  n ≥ 3 (track N owner question 1). *(Scott: "approve n ≥ 3 for track N")* The other track-N questions wait for the
  statement audit and the review page.
- **D18 (2026-10-27) Track N rulings Q2–Q6.** *(Scott: "approve your other recommendations for track N too")*
  - Q2: pointwise `‖f‖ ≤ ε`, with BM11's constants rescaled by a factor of two, plus a separate size-zero theorem
    (N-ZERO).
  - Q3: constants uniform in both h and f, given (n, R, s, M, m), as BM11's stable constants; no added
    frequency lower bound.
  - Q4: N-HEAD states existence on the whole interval, equality with every other solution, and the margin
    C·ε₀^{1/(2n)} ≤ R/4.
  - Q5: freeze N-QC and N-ZERO as gates; defer N-STEEP and BM11's uniform inverse-radius claim.
  - Q6: the suspected BM11 issues E-N-BM-1..3 are resolved before the proof route is signed off.

  These rulings fix the shape. The exact Lean text still needs the owner's line-by-line approval after the
  statement audit.
- **D19 (2026-10-27) Track I rulings Q1–Q5.** *(Scott: "approve your recommendations for track I too")*
  - Q1: the uniform isoenergetic gate fixes ω*, σ_ω, the endpoint distance ν, γ̄ and the margin μ before
    C₁, C₂, C₃.
  - Q2: dynamics are stated as an exhibited global solution plus agreement with every local solution; no flow is
    defined in advance.
  - Q3: the bordered determinant is nonzero on the real slice of B_{r₀}, after shrinking r₀ if needed.
  - Q4: the first physical region is the prograde interior annulus with e₊ < 1/4 and a₊(1 + e₊) < 1, open in
    phase space and independent of μ.
  - Q5: I-KEPLER is a separate joint determinant/value gate, and the documented ≤ and sign corrections to HL19
    are adopted after independent source review.

  These rulings fix the shape. The exact Lean text still needs the owner's line-by-line approval after the
  statement audit.
- **D20 (2026-10-27) Tracks I, N and P approved and frozen.** *(Scott: "approve track I; approve track N with N-HEAD-C;
  approve track P")*
  - **Track I:** 4 theorem anchors (I-G1 isoenergetic KAM, I-HEAD confinement, I-R3BP, I-KEPLER) and 15
    definitions, in `KAM/Frozen/Iso/`.
  - **Track N:** N-HEAD-C (the complex-Hessian-bound headline), N-ZERO, N-QC and 11 definitions, in
    `KAM/Frozen/Nekhoroshev/`. N-HEAD (real bounds only) is not frozen; it stays a recorded open question (source gap
    F-N1).
  - **Track P:** the exact v0.2 text, which implements the recommendations on Q-P1–Q-P7. That is 3 theorem anchors
    (P-G corrected, P-PLANAR, P-FIXED) and 33 definitions, in `KAM/Frozen/Planetary/`.
  - All 69 declarations are byte-identical to the approved drafts. The manifest now holds 94 anchors.
  - The anchor guard now also accepts `abbrev` for definition anchors, and the `EuclideanSpace` lint ignores
    comments.
  - Drafts and audit scratch are archived at `/mnt/HC_Volume_106379410/kam-evidence/2026-10-27-tracks-INP/`.
- **D21 (2026-10-27) Model policy for the proof campaign.** *(Scott: "for the proof writing campaign you should use
  Sonnet agents and use GPT 6.1 sol (in tmux, yolo mode, not fast mode) as auditors. You can also use a second
  Opus 5.5 suborchestrator in a tmux with its own sonnet if you want")*
  - Proof writers are Sonnet agents.
  - Auditors are Codex GPT-6.1-Sol sessions in tmux, in yolo mode, on the default service tier (not fast mode).
  - Optionally, a second Opus 5.5 sub-orchestrator runs in tmux with its own Sonnet workers.
- **D22 (2026-10-27) Milestones from the collaborator's research question adopted.** *(Scott: "yes, adopt the five
  milestones into tracks N and P")*
  - Track N gains N-PARTIAL-CONVEX (stopped properly-degenerate Nekhoroshev, Nekhoroshev 1977 Thm 4.4) and
    N-AVERAGING (averaging for most initial conditions, Arnold–Kozlov–Neishtadt Thm 6.11).
  - Track P gains P-EXP-SAFE (Nekhoroshev 1977 Thm 12.3 for the planar problem with a moving Sun, with the source's
    exponents), P-AMD-CONFINEMENT (the angular-momentum confinement helper) and P-SECULAR-BOX (the
    Sun–Jupiter–Saturn averaged-model box at the actual masses).
  - Each goes through Phase 0: drafting, independent audit, owner approval of the exact text, then freezing.
- **D23 (2026-10-27) Sub-orchestrator for tracks I, N, P.** *(Scott: "use the Opus suborchestrator for tracks I, N and P")*
  - A second Opus 5.5 orchestrator (account claude-8, tmux `kam-suborch`) runs tracks I, N and P end to end: the D22
    additions, blueprints, dependency graphs and proof campaigns, under the D21 model policy.
  - It works in the worktree `/root/code/KAM-inp` on branch `inp`, and lands through `scripts/land-branch.sh inp`
    (lint and build before every landing).
  - It keeps its own HQ files `docs/campaign/campaign-INP.json` and `docs/campaign/progress-INP.json`, which the README
    generator merges.
  - Owner questions and approvals go through the main orchestrator. The main orchestrator keeps track K and the HQ.
- **D24 (2026-10-27) Codex agents run GPT-6.1-Sol at medium effort.** *(Scott: "can you take down your astra subagents
  to sol-medium please")*
  - No GPT-6-Astra sessions.
  - The seven idle Astra sessions of Phase 0 and the research thread were restarted on GPT-6.1-Sol at medium
    effort, resuming their conversations.
  - Auditors launched later use medium effort. This refines D21.
- **D25 (2026-10-27) D22 additions approved: track P (all three milestones) and N-PARTIAL-CONVEX.** *(Scott: "approve P
  additions and N-PARTIAL-CONVEX")*
  - **Track P:** the exact v0.4 text of P-AMD-CONFINEMENT (`amdConfinement`), P-EXP-SAFE
    (`planetaryExponentialSafety`) and P-SECULAR-BOX (`secularBoxSafety`, `secularBoxAtCitedMasses`), with 34
    definitions. Source: `.drafts/P/Additions.lean`, sha256 `bf4b9d474e4c3fa32844af887f90851cb5bd026c101f2b5fc882b9169d5e72f0`.
    The recommendations on Q-P-A1–A5 are adopted (all yes).
  - **Track N:** the exact v0.4 text of N-PARTIAL-CONVEX (`partialConvex_nekhoroshev`), with 7 definitions, as in
    `docs/tracks/N/REVIEW-additions.md`. That is the draft sha256
    `ebef5cbca47162d83c5481726408bd4c2977375526c3579d0c791dbd1b80af4d` minus the four deferred averaging declarations.
    The recommendations on questions 1–4 are adopted:
    - the convex proof specialization on the enlarged domain G′;
    - fixed-h complex-bound inputs;
    - N-AVERAGING deferred until its primary source is pinned;
    - E-N-ADD-1 recorded as a candidate erratum, and the specialization as a deviation.
  - Review pages: claude.ai/artifact/7ENmWAuf34EGcwtLyBryPH (P), claude.ai/artifact/4RfC5jjTbqfgGksuQZvk1i (N).
  - The sub-orchestrator freezes them as for D20.
- **D26 (2026-10-27) First seal: G3. Two corrections to the frozen-anchor guard.** *(orchestrator; technical)*
  - **Seal.** `KAM.volume_not_diophantine_le` is SEALED. Its provider is `KAM.Provider.volume_not_diophantine_le`:
    the Sonnet prover for package P-G3, an independent GPT-6.1-Sol medium audit (PASS WITH NOTES), and a
    `leanchecker` kernel replay. Its axioms are `propext`, `Classical.choice` and `Quot.sound` only.
  - **Guard correction 1.** The guard's lexer treated the `'` of Lean's `∑'` as opening a character literal, which
    hid the rest of a file from the guard. It now masks only genuine character literals, matching
    `check_lean_modules.py`.
  - **Guard correction 2.** A frozen theorem whose explicit binders precede the colon cannot be sealed by a bare
    `by exact <export>`. A sealed body may now apply the export to exactly those binder names, all of them, in
    order, and to nothing else.
  - The upstream skill script `check_frozen_anchors.py` has the same two limitations (reported to the owner).
- **D27 (2026-10-27) Lean status `BYPASSED` for route substitutions.** *(orchestrator)*
  - **Meaning.** A graph step is `BYPASSED` when its proved parent's Lean proof follows another valid route, so
    the step's own conclusion is never formalized. Its `LEAN_NOTE` records the route and the audit that confirmed
    no proved consumer needs the step.
  - **Uses so far:**
    - `step:p1:li-cubes` and `step:p1:li-image`: the Mathlib Hausdorff-measure route, which the blueprint itself
      offers (I-LIP audit).
    - `step:p1:han-series`: the contour identification of the coefficients (I-STRIP-5 audits 1–2).
    - I-ZMAP's bypassed steps, to be recorded when it lands.
  - **Positive widths.** Strip widths are positive and `n ≥ 1` wherever a strip occurs. Part 1's conventions now
    state this explicitly.

- **D28 (2026-10-27) N-AVERAGING approved.** *(Scott: "approve N-AVERAGING")*
  - The exact v0.5 text is approved: `HasAveragingFrequencyRank`, `averagingError`, `averaging_mean` and
    `averaging_most`. Source: `.drafts/N/Averaging.lean`, sha256
    `6b8bf1941fd1c30f3d8ca1e81b304873d31959eae85809b52f39c9e6e132ff62`.
  - The text is re-transcribed from AKN06 §6.1.9 (Thm 6.11, Cor. 6.1, p. 243), checked against Nei76, and passed
    the independent audit v0.5.
  - The recommendations on questions 1–4 are adopted:
    - the analytic specialization with fixed-system constants;
    - both forms kept;
    - candidate erratum E-NAVG-NEI-17 (Nei76 (17)) recorded, with the integral-of-maximum repair as a declared
      deviation;
    - the audit-first condition is already satisfied by v0.5.
  - Review page: claude.ai/artifact/2QX93h35t62Fmb49UGamrm.
  - The sub-orchestrator freezes it as for D25.
- **D29 (2026-10-27, 21:00) Overnight mode.** *(Scott: "ok we go into overnight mode, defer approvals and requests and
  go with your best recommendation and i see in the morning. formalize as much of this as you can!" and "please keep
  the agents active and going and get the code written")*
  - Until the owner returns, decisions that normally need the owner are taken by the orchestrators' best
    recommendation.
  - Each such decision is logged in `docs/campaign/OVERNIGHT.md` for morning review.
  - No new statement is frozen: approvals of exact Lean text are deferred to the morning. Source requests wait too.
  - Proof work runs at full throughput.
- **D30 (2026-10-29, 10:40) Lunar spin–orbit certificate project (track SO).** *(Scott: "Let's start now! Let's aim
  for 3.3%! Let's go!")*
  - Start the project of `docs/explorations/lunar-spin-orbit-certificate-proposal.md`, as modified by its feasibility
    report: the target band is |p(t) − 1| ≤ 33/1000 with the proposal's frequencies ν± = 1 ± 1/(40 + g).
  - Deliverables: a reusable certificate checker with a soundness theorem (the "black box" turning numerical KAM
    candidates into Lean theorems through `g1_explicit`), and the lunar barrier and confinement theorems.
  - Plan, refinements and waves: `docs/campaign/design/SPIN-ORBIT-PLAN.md`. Final statements are frozen only after the
    owner approves their exact Lean text.
- **D30 (2026-10-28) Track W (PDE KAM) adopted.** *(Scott: "go with recommendation", answering the owner questions
  in §9 of [`explorations/pde-kam-and-leapfrogging.md`](explorations/pde-kam-and-leapfrogging.md))*
  - New track **W**: two-frequency quasiperiodic solutions of the cubic Dirichlet wave equation
    `u_tt = u_xx − m u − u³` on `[0,π]`, modes `J = {1,2}`, every fixed `m > 0` (Pöschel 1996, CMH 71, Main Theorem).
  - Q1: the real scalar wave equation, not the cheaper cubic NLS route.
  - Q2: density one in the action parameters is the first measure conclusion; nothing is claimed about general
    initial data.
  - Q3: the first headline is analytic existence, two independent frequencies, exact PDE reconstruction and
    smallness. Linear stability and Whitney regularity are later gates.
  - Q4: the blueprint repairs the source normalization once E-PDE-W-1/2 and E-PDE-KP-1 are independently checked.
    The printed, inconsistent formulas are never frozen.
  - Leapfrogging (Hassainia–Hmidi–Masmoudi): GO-LATER. Its first milestone is the four-point-vortex orbit.
  - Stage: source and design (blueprint-W, errata verification, then milestone W0: normalization and the
    cubic-gradient interface). Exact Lean statements follow the normal pipeline, with independent audit and owner
    approval before any freeze. Track W changes no K/I/N/P frozen surface.
  - Lean namespace `KAM.Wave` (provisional).

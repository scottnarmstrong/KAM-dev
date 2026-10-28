# P11A-W6 prover handoff (branch inp-p11aw6, ea71d2a; contains inp-p11aw5 and inp-p11aw1 (audited); offloaded package run by the main orchestrator; prover on claude-12)


**File (new):** `KAM/Planetary/WeakMeasure/Sublevel.lean` (~420 lines). No other file touched; KAM.lean not edited
(lint reports it out of date, as expected; the orchestrator regenerates it).

**Declarations (blueprint node -> Lean):**
- `bpP:p11a:sublevel` -> `KAM.Planetary.sublevel` (statement copied verbatim from P11ASignatures.lean).
- `bpP:p11a:sublevel#kappa` -> `p11_sl_kappa` (kappa >= 1, kappa >= 4M√n d/β, kappa >= √n d/v, kappa <= (M/β)(1+(4+1/v)√n d)).
- `stepP:p11a:sl-cover` -> `p11cell`, `p11cell_euclid_le`, `p11_cube_cover` (κ^n closed cells of side d/κ, d = max-norm diameter).
- `stepP:p11a:sl-lower` -> `p11_sl_lower` (with `p11_jet_mvt`, `p11_jet_cons_bound`).
- `stepP:p11a:sl-ball` -> `p11_sl_ball` (uses `ball_sublevel`, arithmetic `p11_sl_ball_arith`).
- `stepP:p11a:sl-sum` -> final part of `sublevel` with `p11_sl_sum_arith`.

**Approach:** κ = ⌈(M/β)(4+v⁻¹)√n d⌉, r = √n d/κ. K lies in a max-norm cube of side d (coordinate minimisers on the
compact K), subdivided into κ^n cells; each cell∩sublevel set lies in a Euclidean r-ball about a point b of K in it.
On that ball some jet D^ν g(b)(a^ν) has size ≥ β (finite_type, attainment lemmas of Basic), moves by ≤ M r ≤ β/4 by a
mean-value bound along the segment (size hypothesis at order ν+1), and D^ν g̃ differs from D^ν g by ≤ β/2 (close);
so |D^ν g̃(a^ν)| ≥ β/4. ν=0: set empty since |g̃| ≥ β/4 > ε. ν≥1: `ball_sublevel` with β/4, then
2ν(2r)^(n-1)(4ε/β)^(1/ν) ≤ 8μ(2r)^(n-1)(ε/β)^(1/μ) (ε/β<1/4). Sum over κ^n cells with κ ≤ (M/β)(1+(4+1/v)√n d).

**Checks:**
- `LEAN_NUM_THREADS=1 inp_lake_build.sh /root/code/KAM-inp-p11aw6 KAM.Planetary.WeakMeasure.Sublevel`: Build completed successfully; no warnings in Sublevel.lean.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK (only message: "KAM.lean is out of date").
- `#print axioms KAM.Planetary.sublevel`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / errata / deviations:** none. Signature unchanged. Note: `Metric.diam P.K` is the max-norm diameter, so
the cube of side d (and Euclidean cell diameter √n d/κ) matches the source constants exactly. No heartbeat issues.

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-W6 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements = design signatures (finite cube cover; explicit ceiling/radius inequalities); (2) proofs sound; no added premises; (3) hygiene. Audit ONLY WeakMeasure/Sublevel.lean (compare with branch inp-p11aw5).

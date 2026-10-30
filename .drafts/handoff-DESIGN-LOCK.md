# Handoff DESIGN-LOCK (SO-LOCK design writer), 2026-10-30

**Files (committed on inp-lockdesign):** `docs/tracks/SO/design/SO-LOCK-DESIGN.md` (design, §§1–8),
`docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md` (owner statements, Q1–Q6), `.drafts/design/SOLockSignatures.lean`
(tracked draft, not a KAM module). Nothing frozen; no KAM/ file touched; scratch copy deleted.

**Decisions (addendum applied: the headline names ψ*):**
- ψ* = `lunarSyncOrbit`, defined by `Classical.choose` over `IsSyncOrbit` (C², 1-periodic, odd, solves the orbit
  equation) and made canonical by `lunarSyncOrbit_unique` — GLOBAL uniqueness, no pinning ball, no Fourier data in
  the statement. Headline `lunar_sync_lock`: tube `libAction Ω ψ* x₀ < I_in` ⇒ unique global solution with
  |ψ − ψ*(φ)| ≤ Rψ, |p − 1 − ψ*′(φ)| ≤ Rp, |q − φ| < 1/4 for all t.
- LOCK-PO by Banach contraction (Mathlib `ContractingWith`) in sup norm on odd periodic functions: Lipschitz
  L = 16π²εΣ|Aₘ| ≈ 0.067, Dirichlet Green bound 1/32 ⇒ factor ≈ 0.002; gives existence, global uniqueness and
  location with c = 0 (no kernel data). Replaces the brief's Newton–Kantorovich (deviation, justified §2.2).
- Route (a′) as ruled: rational centre c (data only), exact shift (J′ = J̃ − c′(c′+Y) + Xc″), elliptic polar, v2
  `checkTorusCertificateV2 routeAV2` unchanged; invariant set transported via global uniqueness of soField.
- `HamExpr` is NOT frozen (no mention in KAM/Frozen or manifest) ⇒ add constructor `.sqrt`; semantics cpow 1/2,
  domain `0 < re`, ball rule |√w − s| ≤ r/s (outward-rounded like ballRound), derivative via existing `div`,
  composition witness à la ExpWitness.

**For owner review (reversible choices taken):** Q1 global characterisation of ψ*; Q2 orbit equation via frozen
`soField`; Q3 coarse ellipse spin bound (≈3.7 % vs true ≈2.5 %); Q4 drop trivial non-vacuity theorem; Q5 freeze
`lunarSyncOrbit_bound`; Q6 literal rules (design §1.4). All literals are placeholders (marked DATA).

**Packages:** LOCK-PO (600–900, start now), LOCK-CONF (350–550, parametric in `LockBarrier`, start now),
LOCK-COORDS (700–1000; Maps/Symplectic now, HamExpr after SQRT), LOCK-SQRT (900–1500 + cases in ~12 shared checker
files; needs owner of checker files, after BALLFIX), LOCK-GRAPH (250–400), LOCK-GEN/LOCK-DATA (data, N = 65:
K≈130 × L≈31, ≈4k half-terms, ≈11× R2 products), LOCK-ASSEMBLY (300–500). Total ≈ 3.5–4.6k lines; all files < 900.

**Risks:** checker-file contention with BALLFIX/V2 (BALLFIX not landed, clashes with BallsTrig); arg-continuity in
LOCK-CONF; √ near inner annulus inflates majorants; kernel cost ≈ 11× R2; v2 thresholds for the polar Hamiltonian
are projections (no LOCK-GEN notes existed yet in KAM-inp-lockgen).

**Suspected errata (non-pinned notes):** SO-LOCK-SCOPE §1 L3 says certifying the orbit needs Newton–Kantorovich — a
data-free contraction suffices; SO-LOCK-SCOPE §2 names `checkTorusCertificateSharp` (now `…V2 routeAV2`, D44; dated,
not wrong).

**Deviations:** Banach instead of NK; orbit pinned by global uniqueness instead of "within δ of c"; sqrt
ball/jet/witness rules specified in prose only (need the new constructor), semantic lemmas in the signatures file.

**Sig-check** (`inp_sig_check.sh /root/code/KAM-inp-lockdesign .drafts/scratch/SOLockSignatures.lean`, slot 1,
16:06 UTC): 11 warnings `declaration uses 'sorry'` (lines 43,46,49,68,78,100,107,113,123,125,129), no errors.
Earlier ball-pinned variant also elaborated clean (superseded). No lint run (no KAM/ Lean changed).
**Axioms:** n/a (no proofs).

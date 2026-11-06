# SJSU gate 2 (T2-CONF): decision log

Rulings and approvals relayed by kam-38; times in UTC from the clock.

| Date | Ruling | Source |
|---|---|---|
| 2026-11-06 | **D74** GO for gate 2 (T2-CONF): phase 1 = gates SR-1..SR-7 | owner via kam-38 |
| 2026-11-06 | **D75** model of record = the published complex form; H = Re Σ c zᵃz̄ᵇ, z = (ξ − iη)/√2 | owner via kam-38 (on main) |
| 2026-11-06 | Phase 2 GO. Statement defaults: Q radius 1e-6 (r a checker parameter), T = 5·10⁹ yr (parameter), eccentricity intervals [0.026, 0.062], [0.009, 0.085], [0.006, 0.063] | kam-38 |
| 2026-11-06 | Build plan: cp -a of KAM-inp's core build to HC, packages symlinked, targeted builds only, one heavy lane | kam-38 |
| 2026-11-06 | Plan in days (3–4); up to 4 workers; shared worktree with disjoint directories, commits by path, every lean/lake call through `.drafts/g2/g2lake` (flock + 6 GB scope); C¹-sup trig models instead of Fourier-series Banach algebras | kam-38 |
| 2026-11-06 | **Owner ruling (a):** keep two-sided eccentricity intervals; N6 proves the lower bounds with a φ-resolved grid enclosure (budget about 1 CPU-h); if it costs much more or an interval does not fit, report before widening | owner via kam-38 |
| 2026-11-06 | Statement audit 1 (refute-first) on codex-3 before owner approval of the exact text | kam-38 |
| 2026-11-06 | **D76** owner APPROVED the exact text: draft v2 of `docs/explorations/sjsu-g2-t2conf-proposal.md` (`sjsu_secular_confinement`, `sjsu18O2` and its 6 hash-pinned parts, `sjsu18O2Terms`, `sjsuTerm`). Prove it as an ordinary theorem in exactly that text, then freeze and seal in one pass (anchor and data under `KAM/Frozen/…` in the opt-in library `KAMSJSU`, byte-identical to v2; manifest SEALED; guard, ABI, Expr-equality, axioms, kernel replay; fresh seal audit in parallel; one landing request to kam-inp-63). D76 authorizes writes under `KAM/Frozen/` and `manifest/` for these entries only | owner via kam-38 (on main) |
| 2026-11-06 | Heavy lane for the G_p kernel stage (19:06 UTC): the KAMSJSU small test and production use the machine's single heavy lane — one lean process at a time, MemoryMax=10G, no swap, LEAN_NUM_THREADS=1, MemAvailable ≥ 12 GB, serial driver `prebuild_heavy.py --lib KAMSJSU` (targeted heavy builds: `.drafts/g2/g2heavy`); workers' builds stay ≤ 6 GB meanwhile; lam is the fallback; ledger ≈ 250 MB accepted (< 300 MB); no Kronecker redesign; land data and checker code as each audit passes | kam-38 |
| 2026-11-06 | Production driver (21:31 UTC): `prebuild_heavy.py --lib KAMSJSU` replaced for the KAMSJSU production build by the topological driver `scripts/sjsu/ledger/build_ledger.py` (cause: the driver's `lake build --no-build` stale round over the 4447 KAMSJSU modules costs ~120 s per built module, ≈ 150 h in total, against ~25–60 h of kernel work). Same heavy-lane settings as above (one lean process at a time, flock, MemAvailable gate, capped scope, systemd user unit); modules whose oleans are already up to date are skipped, so oleans from a lam run can be merged in mid-run. lam run requested from the owner; kam-18 builds the lam package | kam-18 |

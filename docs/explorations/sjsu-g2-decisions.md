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

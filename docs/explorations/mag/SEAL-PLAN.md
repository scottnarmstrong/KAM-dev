# Magnetic barrier: plan to seal `KAM.Magnetic.magnetic_barrier`

Owner priority since 2026-11-08. What the frozen statement says: [`docs/results/Magnetic.md`](../../results/Magnetic.md).
Progress: the Magnetic row of the README's progress table, from
[`docs/campaign/side/mag-status.json`](../../campaign/side/mag-status.json).

## Where it stands (2026-11-08)

- **Statement:** frozen 2026-11-01 (D68) as a draft anchor; not yet proved.
- **Numerical certificate:** done and passing every check in the bit-exact Python mirror of the Lean checker
  (route A refined of the v2 certifier, as for the Moon's spin band): error 7.3·10⁻²² against the threshold 10⁻¹⁹·¹⁹,
  a margin of 1.94 decades; the barrier graph lies in [0.3261, 0.3876], inside the frozen 8/25 ≤ P ≤ 39/100. Package
  on branch `mag-pilot`, `certificates/magnetic/`. Nothing is kernel-checked yet.

## Stages

1. **Re-confirm** the certificate against today's checker sources (main merged into `mag-pilot`; the mirror re-runs).
2. **Emit kernel data modules** for the opt-in library `KAMMagneticBarrier` with the SO pipeline (packed products,
   whitened literals, per-declaration splitting, segmented proofs); measure one sample module per family in the single
   10 GB heavy lane; extrapolate. Expected 10–40 kernel hours.
3. **Kernel check of the full certificate:** here as a systemd unit if it fits in about 10 hours, otherwise as a
   standalone package on the 64-core workstation (the SO-3 and SJSU pattern: verified package, per-module
   `leanchecker`, results returned and verified).
4. **Glue theorem** (in parallel with 2–3): a passing certificate implies the frozen conclusion
   (`magnetic_barrier_of_V2`): the expression form of the Hamiltonian equals the frozen `magHamC`, the clock-phase
   shift, the graph bounds, invariance under the field-line flow, global existence and uniqueness, and preservation of
   the side of the graph. About 1,000–1,500 lines; the generic layer is in core.
5. **Provider and seal:** the provider proves the exact frozen type; the seal changes only the proof body to
   `by exact KAM.Provider.Magnetic.magnetic_barrier`; an independent seal audit, kernel replay of the new modules, ABI
   hashes, frozen-anchor guard and lint.
6. **Landing** on `main`, with the built data seeded from the worktree.

## Rules

Standard axioms only (no `native_decide`, D77); one heavy lane on the 32 GB server; builds on the HC volume; the two
hard Lean rules (no heartbeat overrides; no file over 1,500 lines).

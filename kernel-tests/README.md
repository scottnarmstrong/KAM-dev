# Opt-in heavy kernel tests

These Lean files are **not** part of the library: `lakefile.lean` builds only `KAM/`, and `scripts/gen_root_imports.py`
does not import them. A plain `lake build` never compiles them. They are the lunar-size numerical kernel checks of the v2
certifier, kept as reproducible evidence.

| File | What it checks | Peak RSS | Wall |
|---|---|---:|---:|
| `CertificateSharp/V2/RefinedR1.lean` | stage 1 and 2 of the v2 route-A engine on the design package R1 (SHARP2-C6) | 10.4 GB | ≈ 2.5 min |
| `CertificateSharp/V2/RefinedRefR1.lean` | the L8′ engine on R1, prefix 5 (SHARP2-C6L8; imports `RefinedR1`) | 19.2 GB | ≈ 6 min |
| `CertificateSharp/V2/RouteBR1.lean` | route B (frozen and refined numerics) on R1 (SHARP2-C6B) | 1.8 GB (measured once, before the move) | ≈ 6 s |
| `CertificateSharp/V2/RouteBR1Sites.lean` | route B's refined core with C6's small-divisor sites (imports `RefinedR1`, `RouteBR1` by module path: place both back under `KAM/` to compile) | as `RefinedR1` | — |
| `CertificateSharp/V2/C6L1R1.lean` | the l1 entry engine on R1 (SHARP2-C6L1): numerical core without the bites about 4 GB; with the ten bites (l up to 13) above the 10 GB guard: needs sharding | 4.1 GB / > 10 GB | 6–12 s / minutes |

Run one only with the owner's approval, alone, niced, and only on a machine where a single Lean process may exceed
10 GB (lemma.farm kills any lean process above 10 GB and caps a user at 32 GB):
`nice -n 10 lake env lean kernel-tests/CertificateSharp/V2/RefinedR1.lean` (its imports must be built).
Both passed when they were written (handoffs SHARP2-C6 and SHARP2-C6L8; audits AUDIT-C6-1, AUDIT-C6L8-1).

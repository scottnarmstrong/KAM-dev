# V2-PACKED-CONS-LOOKUP: the consumers' jet-slot reads on the whole ledgers (LG00 T′)

The consumers read a jet slot through `jetSlots jd`. Each of `jetNode`, `jetRad` and `jetNb` is `(jd.led i).…`,
where `jd.led i = (jd.L.lookup (slotK i)).getD default` is a `List.lookup` on the chain's whole ledger
(AUDIT-V2-PACKED-CONS-1 L2). The gate used a ledger holding only the wanted slots. Here the reads run on
kamx-packed's real T′ ledgers.

**The ledgers.** kamx-packed's `LG00P.TP.Jet.{Low,Full}.{Book,Led*,Data}`, copied read-only from its package
(`.lake/v2-packed-prod/pkg`, worktree head `0bb4def23`) and renamed `LG00C`; sha256 of the sources in
`ledger_sha256.txt`. They are built here one module at a time under 4 GB:
- cfgLow: 31 modules, 553 CPU-s, ≤ 1.01 GB;
- cfgFull: 20 modules, 780 CPU-s, ≤ 1.42 GB.

The ledgers hold the blocks' exports only:
- **1,129 entries** (cfgLow) and **706** (cfgFull), not every live slot;
- no duplicate keys;
- the wanted slots come **last**, at positions 1,109–1,128 and 701–705, so every read walks the whole ledger;
- `ledLow` is a left-nested `++` of 29 parts, `ledFull` of 18.

**Method.** `scripts/packed/cons_lookup_gen.py` writes A/B twins as fresh modules, measured in the same session in
interleaved pairs: R reads kamx-packed's whole ledger (`LG00C.TP.jdLow`/`jdFull`), W the wanted-only ledger of the
gate.
- Consumer probes: `LKXN00` (the X_N stage entry (0, 0); it reads the 4 slots of `DX_H ∘ K`'s row 0), `LKY`
  (the averages of Y; 4 `DH` slots), `LKIV1` (invariance coordinate 1; 1 slot), `LKEN` (the energy; `v0`).
- Pure reads: `LK{Low,Full}Look` (radius and norm bound of every wanted slot) and `LK{Low,Full}Read` (the same
  plus the packed value).
- Data control: `LKData` (imports only).

Every twin decides `true` on both ledgers: the real ledger's wanted nodes are the gate's. A second pass (suffix
`2`) ran under heavier machine load (system time 4–8 s); its wall-clock kernel figures are noisy. User CPU is
stable across the passes.

| probe | reads | user CPU W → R | kernel W → R (pass 1) | peak W → R |
|---|---|---:|---:|---:|
| `LKData` | imports only | 2.66 → 4.40 s (**+1.74**) | — | 0.52 → 0.56 GB |
| `LKXN00` | 4 Low slots | 7.12 → 9.60 (+2.48; pass 2 +2.43) | 5.01 → 6.85 (**+1.84**) | 1.32 → 1.60 |
| `LKY` | 4 Low slots | 7.89 → 9.86 (+1.97; pass 2 +1.37) | 5.58 → 7.25 (**+1.67**) | 1.34 → 1.60 |
| `LKIV1` | 1 Full slot | 4.48 → 6.08 (+1.60) | 1.95 → 2.00 (**+0.05**) | 1.01 → 1.13 |
| `LKEN` | 1 Full slot | 3.50 → 5.17 (+1.67) | 0.99 → 1.35 (**+0.36**) | 0.62 → 0.73 |
| `LKLowLook` | 20 Low slots (r, nb) | 3.00 → 7.05 (+4.05) | 0.09 → 9.20 (+9.11; pass 2 +8.60) | 0.46 → 1.30 |
| `LKLowRead` | 20 Low slots (x, r, nb) | 3.42 → 7.80 (+4.38) | 0.55 → 4.99 (+4.44; pass 2 +4.85) | 0.64 → 1.42 |
| `LKFullLook` | 5 Full slots (r, nb) | 3.10 → 4.77 (+1.67) | 0.01 → 0.75 (+0.74) | 0.45 → 0.64 |
| `LKFullRead` | 5 Full slots (x, r, nb) | 4.25 → 5.48 (+1.23) | 1.55 → 2.32 (+0.77) | 0.67 → 0.90 |

**For the consumers of a torus** (T′'s gate figures; pass-1 deltas, scaled by the probes that read jet slots):

| consumer | probes reading slots | Δ kernel | of the consumer's kernel time | Δ CPU, with the import | of the consumer's CPU |
|---|---:|---:|---:|---:|---:|
| torsion | 9 (X_N ×8, Y) | ≈ 16 s | 2.5 % of 662 s | ≈ 21 s | 2.4 % of 868 s |
| invariance | 4 | ≈ 0.2 s | 1.5 % of 13.2 s | ≈ 6.4 s | 15 % of 41.4 s |
| energy | 1 | 0.36 s | 36 % of 1.0 s | 1.7 s | 17 % of 9.7 s |
| **all** | 14 | **≈ 17 s** | **2.5 %** | **≈ 29 s** | **3.2 %** |

**Reading.**
- The searches themselves (the kernel delta) are 2.5 % of the consumers' kernel time. Torsion and invariance are
  each under 3 %; energy's share is large only because its kernel time is 1 s.
- Most of the per-process CPU delta is the import of the whole ledgers' oleans (2.1 GB; +1.74 s user per process),
  not the reads.
- The pure-read probes cost a few kernel-seconds for 20 slots, and their charge rises by about 0.85 GB as the walk
  touches the ledger; within the consumer probes the rise is 0.1–0.4 GB. One unexplained point: `Look` (two reads
  per slot) is slower than `Read` (three) in both passes. The ordering is opaque from outside the kernel.

**Decision.** Under the threshold (about 10 % of the consumer cost), so there is no wanted-slot table; the consumers
are unchanged. Two options remain, for production if wanted:
- kamx-packed's generator can put the wanted slots' entries first in the ledger. No Lean change is needed: producer
  and consumer read the same total `look`. This cuts each walk from about 1,110 entries to at most 20.
- A literal wanted-slot table with a transfer lemma (one process checks the table against the ledger) would also
  remove the ledger import from the 14 consumer processes: about 24 s per torus, minus one checking process.

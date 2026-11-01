# V2-PACKED gate probes (opt-in, generated, not in the repository)

The gate of [`docs/campaign/design/V2-PACKED.md`](../../docs/campaign/design/V2-PACKED.md) §8 compares the landed
advice-checked packed product with the GMP-resident packed product (`KAM/CertificateSharp/Packed/`) on one LG00-sized
real product (`G8k`: 41 × 51 by 43 × 48 boxes, 8,134 product slots) and on LG00's largest product size (`G19k`:
19,311 slots), under a 4 GB charged cap, one Lean process at a time.

The probe files are **generated, not committed**:
- Their packed literals need one 288-bit chunk per line (lines ≤ 100 characters), so they exceed the 1,500-line cap
  of repository Lean files.
- They are deterministic (seeded): regenerate them, then run each one alone.

```
python3 -I scripts/packed/gate_gen.py G8k                      # -> $V2P_GATE_DIR (default .lake/v2-packed-gate)
python3 -I scripts/packed/gate_gen.py G19k 65 79 59 79 48
scripts/packed/run_probe.sh 4G .lake/v2-packed-gate/G8kPcore.lean LOGDIR
```

The probes import only library modules (`KAM.CertificateSharp.Packed.Bridge`). The landed advice comes from the landed
mirror `scripts/spin_orbit/sofx_packed.py`. The measured receipts (`*.cost`, `*.out`) and the data summaries
(`G8k.json`, `G19k.json`) of the 2026-11-01 run are in
[`docs/campaign/studies/V2-PACKED-GATE/`](../../docs/campaign/studies/V2-PACKED-GATE/); the handoff
`docs/campaign/handoffs/V2-PACKED.md` tabulates them.

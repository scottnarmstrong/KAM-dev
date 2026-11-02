**PASS WITH NOTES — MAG-FZ-2**, `mag-pilot@9ee1732aa8980da5352fbf82e59e789993b3d0ac`.

1. **(c′) Compatibility proof passes.** Each convolution coefficient satisfies `|T[s][i]| ≤ |Ab|·L·mA·mB`, so the original `w0` already decodes the exact coefficients. Increasing it preserves all digits, rounding and reconstruction requirements. Thus `new_final = max(old_final, E)`, where `E` is the added bound. Passing every old `shardFits` test means `E ≤ old_final`; advice is therefore byte-identical. See [generator](/mnt/HC_Volume_106379410/kam-mag/KAM-mag/scripts/spin_orbit/sofx_packed.py:440) and [Lean guard](/mnt/HC_Volume_106379410/kam-mag/KAM-mag/KAM/Certificate/Poly/Advice.lean:265).

2. **Recorded lock exception behaves correctly.** Regenerated `memos[215]`, `cfgFull/slot902`, part `ii`, using code from `61c6d5a7` and HEAD. Original advice matches the recorded advice byte-for-byte. Old width **218** fails `shardFits` at shards **3–6**; new width **220** passes the complete Python product checker. Serialized advice differs in the three layout widths; rounded windows remain identical. This was a previously failing product, so it satisfies the revised claim.

3. **Band sample passes byte comparison.** Lower-ledger memos **0, 1, 2, 32, 64, 96, 128** produced identical complete advice bytes, using the production `adv_json` serializer with identical JSON encoding. All seven passed the Python product checker under both versions.

4. **(a) and (b) remain PASS WITH NOTES.** `git diff 8aab9660 HEAD --stat` reports only `MAG-FZ-1.md` and `sofx_packed.py`: **2 files, 25 insertions, 4 deletions**. Their audited files are unchanged. Prior notes remain: missing D68 decision record and the qualified data-copy adaptations.

All regeneration stayed in memory with bytecode writes disabled and a write-rejecting audit hook. No edits, builds or Lean replay.
# SO-POLY-A prover handoff (branch inp-sopolya, a25e06e8; track SO package run by the main orchestrator)


Files: `KAM/Certificate/Arith/Mantissa.lean` (mantCheck, mantCheck_sound, ofDyadic, ofDyadic_sound,
CertFixed.toMant, CertFixed.mantCheck_m); `KAM/Certificate/Poly/Packed.lean` (418 lines: packSum,
packShift(+Aux), packShift_eq, SlotsBounded, packSum_injective, listConv, packSum_listConv,
convFits, slotsBounded_listConv, packSum_flatten_mul_shards, intSlotsBound(+Aux),
intSlotsBound_sound). All names/types verbatim from SOSignatures.lean. Layout/advice/checkShard/
checkPackedProduct/toMants/mulPacked are SO-POLY-B (not touched). No sorry.

Approach: packShift loops with Nat.shiftLeft (shift offset advances by w; no multiplication),
proved = packSum via accumulator invariant. Injectivity by induction on slots (borrow argument).
Kronecker and shards both reduce to one Cauchy-product lemma (`sum_mul_sum_range_cauchy`, proved via
Polynomial evaluation). convFits is a Nat `decide`; bound via card of the nonzero index set.
intSlotsBound peels signed slots (`slotRep`) with Int emod/ediv, kernel-reducible; sound by induction.
mantCheck_m proved from exactness of cdiv/floor on z*den/den.
Extra helpers (new public names; short-name check OK): packSum_nil/cons/append/eq_sum,
sum_map_range_eq, packShiftAux(_eq), maxAbs, natAbs_le_maxAbs, abs_getD_le, abs_conv_entry_le,
packSum_flatten, slotRep, intSlotsBoundAux(_sound), sum_mul_sum_range_cauchy.
Kernel examples in the file (`decide +kernel`): packShift 8 [3,-1,2]; intSlotsBound true/false.

Checks: `lake build` via inp_lake_build.sh for KAM.Certificate.Arith.Mantissa and
KAM.Certificate.Poly.Packed: Build completed successfully, no warnings in my files.
lint_sources.sh: only "KAM.lean is out of date" (generated; not edited), all else PASS/OK,
short-name check OK, lines ≤ 100.
#print axioms: packShift_eq [propext, Quot.sound]; packSum_injective, packSum_listConv,
slotsBounded_listConv, packSum_flatten_mul_shards, intSlotsBound_sound, mantCheck_sound,
ofDyadic_sound, CertFixed.mantCheck_m: [propext, Classical.choice, Quot.sound].

F12/F13 notes: `intSlotsBound_sound` only yields |e_i| ≤ 2^(logs i), NOT `SlotsBounded w e`
(which needs 2|e_i| < 2^w); packSum_injective's premises are unweakened, so POLY-B must check
logs i + 1 < w (for all slots, advice and decoded sides) before applying injectivity. Also
`scale - 1` in ℕ is 0 at scale = 0, giving bound 2^0 = 1, not 1/2 (F13). Note decoded e is just
some representative; injectivity is what makes it unique.
Uncertainties: none known; no errata found in the sources.

CONTEXT: track SO, the advice-checked Kronecker-packed product architecture (/root/code/KAM/docs/tracks/SO/studies/SO-REPLAY2-advice-sharded-products.md). Design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md Revision 6 (round-6 design audit running): Revision 6 repaired design audit 5's F12 (anti-carry) and F13 (scale 0) in the SO-POLY-B part and states that NO SO-POLY-A signature changed. Signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean, the SO-POLY-A part (Arith/Mantissa; Poly/Packed: packing, injectivity, Kronecker, shards, slot decoding). Check: packing is kernel-reducible with shifts; packSum_injective's premises are exactly SlotsBounded for BOTH lists (the F12 lesson: no weaker form may be exported); the Kronecker identity is exact; the decoding lemma's guarantee is stated precisely (per-slot bounds) and does not overclaim.

AUDIT FOCUS: signed declarations match verbatim; soundness with no added premise; the slice complete. Audit ONLY KAM/Certificate/Arith/Mantissa.lean and KAM/Certificate/Poly/Packed.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.

# Handoff ERRATA-R3

Files: docs/ERRATA-AND-DEVIATIONS.md; docs/errata/ledger.json (`printed` of E-GJLV05-5 and E-P-CP11-2 only); docs/errata/working-record.md (regenerated). No Lean, frozen, manifest, README or KAM.lean change. No status, verdict or count changed; reconciliation 82 + 2 + 13 + 64, 2 withdrawn, unchanged.

## R1 D-P-APPROX
Old: "...the approximation step of the maximal-torus scheme uses a smooth cutoff obtained by convolution with a tensor kernel (`WeakKAM/Cutoff.lean`, `CutoffBump`, `CutoffTensor`, `CutoffConv`), with its own constants."
New: analytic step = finite Fourier truncation + first-order action Taylor truncation; cites `p11Cut_eq_sum` (MaximalStep/FourierCutoff.lean:37), `fourier_cutoff` (:143), `p11_cutoff` (MaximalStep/Cutoff.lean:80; calls `taylor_cutoff`, `fourier_cutoff` at 90–92; remainder eps·(q²/(1−q)+2·p11Error n T d)), `cutoff_delta` (WeakKAM/IterationIncrement.lean:31). Convolution cutoff kept separately as a real frequency-extension supplement: `smooth_cutoff` (WeakKAM/Cutoff.lean:97) consumed at WeakKAM/Extension.lean:134–147 (call at 141). All names/lines opened and confirmed.

## R2a E-GJLV05-5
Old: "Printed (transcribed): a sum over j differentiated in θ_i, and the solution bounded by its own norm ‖v‖_ρ."
New: "Printed (transcribed, printed 889 / PDF 35): Σ_(j=1)^n ω_j ∂v/∂θ_i = h and ‖v‖_(ρ−δ) ≤ c δ^(−σ) γ^(−1) ‖v‖_ρ." Checked with pdftotext on gjlv.pdf (sha256 eec921dc… matches sources.json). Ledger `printed` updated to the same formulas.

## R2b E-P-CP11-2
Old: "Printed (transcribed): 37 α⁴ b_(9/2)^(4)(α)."
New: "Printed (transcribed): 37 α⁴ β₄^(9)(α), where CP11 defines β_k^(r) := b_(r/2),k (p. 61)." Checked in cp11_planetary_invent.pdf (sha256 9b525c58… matches): B.6 line "+ 37α⁴ β₄^(9)(α)" and "βk(r) := br/2,k". Ledger `printed` updated likewise.

## R3 D-P-WEAK-KAM
Added: "The physical wrapper consumes this route through `weak_kam_quantitative_full` (called at Preparation/Wrapper.lean:83; proved at Quantitative/AssemblyK6.lean:31, body from line 48), which combines `weak_kam_quantitative`, `displacement_power_flat` and `qb_beta`, the polynomial bounds being specializations of `qb_poly` in Quantitative/Budget.lean." Confirmed: Wrapper.lean:83 call; AssemblyK6 declaration at :31, body lines 48–51 use those three; Budget.lean:19/149 `qb_poly`. (Brief said body at :48; the theorem header is at :31.)

## Item 8
- Line 179 (D-N-PARTIAL-ROUTE): removed "An earlier draft of this argument used a Cauchy estimate outside its valid domain and was abandoned." Scope and Nek79 sentence kept.
- Line 359 (D-PLANAR-1): old "A factor-four restriction on the axes that appeared in an earlier proposal of this formalization was removed; it is not attributed to Fej04r." new "No factor-four restriction on the axes is imposed; none is attributed to Fej04r."

## Checks
- `python3 scripts/render_errata.py --check`: exit 0, no output.
- `git diff --check`: exit 0.
- `LEAN_NUM_THREADS=1 scripts/lint_sources.sh`: exit 1 — check_lean_modules PASS (1362 files), FROZEN-ANCHOR GUARD OK, then ABI probe `unknown module prefix 'KAM'` (no KAM oleans in this worktree; same as audit 2). Not a passing ABI receipt.
- Build/axioms: not applicable (no Lean changed).

## Uncertainties / errata / deviations
None new. Ledger JSON reserialized with indent=1, ensure_ascii=False, no trailing newline; only the two `printed` fields differ.

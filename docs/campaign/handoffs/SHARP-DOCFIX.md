# SHARP-DOCFIX handoff

Findings addressed (documents and the python mirror only; no Lean touched, no Lean build):
- **F-1**: `p2s-sharp.tex` Parseval and Rüssmann proofs now run on one scalar component `g_j` (Bessel scalar), then
  `max_j`; a-priori bound via `u·v` and the induced operator supremum; the false vector inequality is noted with the
  counterexample. Constants unchanged.
- **F-2**: design doc new §2.3 lists each export (`error_decay`, `torsion_identity`, `Scheme.iterate`,
  `perturbation_poly`, `geometry_sep`) as a deliberate projection (exported / omitted / why unneeded). No signature change.
- **F-3**: `ε ≤ 1` added to the blueprint geometry lemma.
- **F-4**: design §2.1 row and blueprint step name `KAM.Sharp.TorsionPoly.fderiv_tangentMat_eq` as the generic-ω′
  helper; `fi_dL`/`frame_identities` are standing-ω only.
- **ISO-1**: iso blueprint (energy row, average) and design §7 cite `energyRow_eq_sub_etaL`, `extended_regular`,
  `extendedTorsionAverage_eq_bordMat`; `s̄ > 1` not used.
- **F-5, ISO-2**: δ₀-dependence wording corrected in both blueprints.
- **ISO-3**: `thresholds.py` uses M = 1924/1000; comment `m ≥ max{…}`; reran. Changes: fixed Rüssmann −24.71→−24.72
  (iso stays −24.98), crude iso −49.09→−49.10, V6/V7 rows −28.32/−28.54, −26.32/−26.56, branch/sensitivity entries
  (design §6.2, 6.4, 6.5; quoted numbers in both blueprints and design §0). `lunar-band-2p8-2p9.md` quotes none.
  The old handoff `SHARP-DESIGN.md` is historical and left unchanged (it still quotes −24.71 / −49.09).

Checks: `python3 -I scripts/apost_sharp/thresholds.py` runs; `latexmk -pdf` on `blueprint/sharp.tex` and
`blueprint-I/sharp.tex`: exit 0, no undefined references in the final `sharp.log`; PDFs not committed.
Uncertainty: F-2 table names helpers (`ham_mvt`, `norm_transpose_tangentMat_sub_le`) as sources of omitted
facts; they are for the later provers to confirm. No new errata.

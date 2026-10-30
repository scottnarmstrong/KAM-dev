# SHARP2-LINT handoff

**Files:** `KAM/Sharp2/{Data,Geometry,ModConstants,ModConstantsBd,ModConstantsData,ModConstantsMono}.lean`.

**Approach:** wrapped the 26 over-100-character lines (docstrings, signature binder lists, `let`s, `exact` lines,
the `stepConsts_eq` tuple); whitespace and line breaks only, no statement/name/binder/proof change.

**Checks:**
- `awk 'length > 100 {print FILENAME":"FNR}' KAM/Sharp2/*.lean KAM/Sharp2/SmallDiv/*.lean` prints nothing.
- `scripts/lint_sources.sh | grep Sharp2` prints nothing.
- `nice -n 5 lake build KAM.Sharp2.{Data,Geometry,ModConstants,ModConstantsMono,ModConstantsBd,ModConstantsData}`: success.
- Type check before/after (`.drafts/chk.lean`: `#check` of `RefData.ofV1`, `RefHyp`, `refHyp_ofV1`,
  `norm_invarianceError_le_eta`, `fderiv_lagrangeMat_eq_etaN`, `stepConsts_eq`, and `#print stepConsts`):
  output byte-identical (`diff` empty). The B2/B3 signature probes were not re-run separately; the elaborated types are unchanged.

**Uncertainties / errata / deviations:** none.

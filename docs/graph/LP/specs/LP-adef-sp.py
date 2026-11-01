# Track LP, slice LP-adef-sp, wave 3 (streamlined extraction, D65): the 53 spatial D62 definition anchors and the
# reused KAM.Iso.IsHamiltonianSolutionOn (Q6). Mechanical binding: DEPS are the bound frozen definitions that each
# declaration file imports directly and names in its declaration (SPEC §1.3), with the EDGE at the MAIN line the definition transcribes (from the
# binding's source range); the conclusion is the declaration's docstring (frozen file), the source meaning recorded
# by the freeze's statement audit. Spatial definitions realize the d-generic MAIN definitions in d = 3 (dimension rule).
exec(open("docs/graph/LP/specs/_lp_anchor_util.py").read())

OVERRIDE_STMT = {"lpM:s1:data#spaceDot": "s1:29-29", "lpM:s1:data#spaceSq": "s1:15-15",
                 "lpM:s1:data#spaceLength": "s1:15-15", "lpM:s1:model#IsHamiltonianSolutionOn": "s1:17-17"}
OVERRIDE_DOC = {
    "lpM:L1#spatialSourceBarycentricPositions": "the barycentric positions of Lemma 1's explicit inverse (L104) on "
    "their source domain ν_i > 0, μ > 0 (literal formula, definitionally the total helper spatialBarycentricPositions)",
    "lpM:L1#spatialSourceBarycentricVelocities": "the barycentric velocities of Lemma 1's explicit inverse (L104) on "
    "their source domain ν_i > 0, μ > 0 (literal formula, definitionally the total helper spatialBarycentricVelocities)",
}
# frozen carrier definitions that no root statement and no source proof consumes (SPEC §7, D65 reachability)
UNCONSUMED = {"lpM:L16:defs#spatialSourceOscVelocity"}
NODES = {}
COV = {u: ("EXCLUDED", "outside every root closure of track LP: frozen carrier definition (V_i on the osculating "
           "carrier) that no frozen root statement and no source proof uses; checked against all wave 1-3 nodes")
       for u in UNCONSUMED}
SOURCES = {"lpM:L16:defs#spatialSourceOscVelocity": "L16:512-512"}
DELETE = {u: "unconsumed frozen carrier definition (coverage item EXCLUDED)" for u in UNCONSUMED}
for r in BIND:
    if r["node"] in UNCONSUMED:
        continue
    if r["slice"] != "LP-adef-sp" and r["node"] != "lpM:s1:model#IsHamiltonianSolutionOn":
        continue
    if r["kind"] != "definition" or int(r["wave"]) != 3:
        continue
    st = OVERRIDE_STMT.get(r["node"]) or locator(r["source_range"])
    unit, rng = st.split(":")
    line = rng.split("-")[0]
    reused = r["role"].startswith("reused")
    NODES[r["node"]] = dict(
        kind="definition", title=r["export"].split(".")[-1] + (" (reused)" if reused else " (spatial, d = 3)"),
        stmt=st, proof="-",
        H="the declaration's binders (typing data; total formula, source meaning on its carrier)",
        Q="for every value of the binders",
        C=OVERRIDE_DOC.get(r["node"], doc(r["path"])) + ("" if reused else " (MAIN, d = 3)"),
        S="none",
        deps=[(t, line, "the declaration uses " + t.split("#")[-1], unit) for t in imports(r["path"])
              if t != r["node"]],
        note=("reused frozen definition " + r["manifest_id"] + ", bound as an LP anchor node (Q6); typing data of the "
              "moving-Sun solution predicates" if reused else
              "spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read "
              "mechanically from the frozen file's direct imports (D65)"))

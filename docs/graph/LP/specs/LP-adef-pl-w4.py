# Track LP, packet LP-adef-pl-w4 (wave 4): the two reused frozen exponent definitions that the LP3 anchors import
# directly (Q6), bound as LP anchor nodes (owner: LP3-PLAN §1.1). Mechanical binding as in wave 3.
exec(open("docs/graph/LP/specs/_lp_anchor_util.py").read())
P = "docs/tracks/LP/lp3/LP3-PLAN.md"
NODES = {}
for node, what in [("lp3:s1.1#planetaryTimeExponent", "a_n = 2/(6n² - 3n + 14)"),
                   ("lp3:s1.1#planetaryDriftExponent", "b_n = 3/(6n² - 3n + 14)")]:
    r = BY_NODE[node]
    NODES[node] = dict(kind="definition", title=r["export"].split(".")[-1] + " (reused)",
                       stmt=f"{P}#s1.1@L69-L70", proof="-", H="n : ℕ (typing data)", Q="for every n",
                       C=what + " (" + doc(r["path"]) + ")", S="none",
                       deps=[(t, 69, "the declaration uses " + t.split("#")[-1]) for t in imports(r["path"])],
                       note="reused frozen definition " + r["manifest_id"] + ", bound as an LP anchor node (Q6); "
                            "equal to the track-N partial exponents (LP3-PLAN §1.1)")

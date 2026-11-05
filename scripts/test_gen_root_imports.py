#!/usr/bin/env python3
"""Unit tests for the part splitting of gen_root_imports.py.

Run from the repository root: python3 -I scripts/test_gen_root_imports.py -v
The tests call the pure functions `parts`, `split` and `top_parts` on synthetic module names; they
read and write no file.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import random
import unittest


REPO = Path(__file__).resolve().parent.parent
_spec = importlib.util.spec_from_file_location("gen_root_imports", REPO / "scripts" / "gen_root_imports.py")
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)
LIMIT = gen.LIMIT


def flat(n: int, area: str = "Area.Sub") -> list[str]:
    return [f"KAM.{area}.M{i:05d}" for i in range(n)]


class TopChunks(unittest.TestCase):
    def test_small_top_group_keeps_one_part_and_order(self):
        names = flat(LIMIT)[::-1]  # given (unsorted) order is kept when no chunking happens
        ps = gen.parts(["Lib"], names)
        self.assertEqual(list(ps), ["Lib.Area"])
        self.assertEqual(ps["Lib.Area"], names)

    def test_oversized_flat_group_is_chunked(self):
        n = 3 * LIMIT + 7
        names = flat(n)
        ps = gen.parts(["Lib"], names)
        self.assertEqual(sorted(ps), ["Lib.Area.Sub.Top0", "Lib.Area.Sub.Top1", "Lib.Area.Sub.Top2",
                                      "Lib.Area.Sub.Top3"])
        self.assertTrue(all(len(g) <= LIMIT for g in ps.values()))
        joined = [m for k in sorted(ps, key=lambda s: int(s.rsplit("Top", 1)[1])) for m in ps[k]]
        self.assertEqual(joined, sorted(names))  # a partition, in sorted name order

    def test_chunking_is_deterministic_under_input_order(self):
        names = flat(2 * LIMIT + 1)
        shuffled = names[:]
        random.Random(0).shuffle(shuffled)
        self.assertEqual(gen.parts(["Lib"], names), gen.parts(["Lib"], shuffled))

    def test_mixed_group_chunks_only_the_flat_part(self):
        names = flat(LIMIT + 5, "A") + [f"KAM.A.Deep.N{i}" for i in range(10)]
        ps = gen.parts(["Lib"], names)
        self.assertIn("Lib.A.Deep", ps)
        self.assertEqual(sorted(k for k in ps if "Top" in k), ["Lib.A.Top0", "Lib.A.Top1"])

    def test_chunk_name_clash_is_rejected(self):
        names = flat(LIMIT + 1, "A") + [f"KAM.A.Top0.X{i}" for i in range(3)]
        with self.assertRaises(SystemExit):
            gen.parts(["Lib"], names)

    def test_part_overwriting_a_module_is_rejected(self):
        # base = the module namespace, so a chunk part `KAM.A.Top0` would be the module's own path
        names = [f"KAM.A.M{i:05d}" for i in range(LIMIT)] + ["KAM.A.Top0"]
        with self.assertRaises(SystemExit):
            gen.parts(["KAM"], names)

    def test_chunk_parts_are_recorded_for_their_docstring(self):
        gen.CHUNK_PARTS.clear()
        gen.parts(["Lib"], flat(LIMIT + 1) + [f"KAM.Top3.X{i}" for i in range(2)])
        self.assertEqual(gen.CHUNK_PARTS, {"Lib.Area.Sub.Top0", "Lib.Area.Sub.Top1"})
        self.assertNotIn("Lib.Top3", gen.CHUNK_PARTS)  # a real area named Top3 is not a chunk

    def test_rendered_part_fits_line_limit(self):
        # header + LIMIT imports + doc must stay under the 1500-line hard rule
        text = gen.HEADER + "\n" + "".join(f"public import {m}\n" for m in flat(LIMIT)) \
            + gen.PART_DOC.format(name="Lib.Area.Top0", root="Lib", area="x") + gen.SECTION
        self.assertLess(text.count("\n"), 1500)


if __name__ == "__main__":
    unittest.main()

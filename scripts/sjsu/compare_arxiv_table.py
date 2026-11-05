#!/usr/bin/env python3
"""Compare the committed journal-copy table with arXiv:1010.2609v1's text layer.

Usage: python3 -I scripts/sjsu/compare_arxiv_table.py /tmp/sjsu-slg13-v1.txt
Generate that text with pdftotext -layout. This version orders both variable
indices before their exponents, independently of the journal-copy extraction.
"""
from fractions import Fraction
import json
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent
raw = Path(sys.argv[1]).read_text()
block = raw.split('A       Expansion of the secular Hamiltonian', 1)[1].split('References', 1)[0]
terms = {}
for m in re.finditer(r'([+−-])\s*(\d\.\d+)\s*×\s*10([−-]\d+)\s+([^+−\n]+)', block):
    sign, mantissa, exponent, mono = m.groups()
    c = Fraction(sign.replace('−', '-') + mantissa + 'e' + exponent.replace('−', '-'))
    e = [0]*6
    for var, index, power in re.findall(r'([ξη])(\d)(\d)', mono):
        e[int(index)-1 + (3 if var == 'η' else 0)] += int(power)
    assert tuple(e) not in terms
    terms[tuple(e)] = c
committed = {tuple(t['powers']): Fraction(t['coefficient'])
             for t in json.loads((root/'slg13_quartic.json').read_text())['terms']}
assert len(terms) == 78 and terms == committed
print('PASS: all 78 rational coefficients and exponent tuples agree with arXiv:1010.2609v1.')

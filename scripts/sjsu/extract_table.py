#!/usr/bin/env python3
"""Transcribe SLG13 Appendix A's numeric table from pdftotext -layout.

Usage: python3 -I scripts/sjsu/extract_table.py /path/to/paper.txt
The resulting decimals define a separate literal degree-four model. They are
not certified enclosures of the authors' unprinted degree-18 Hamiltonian.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re


def extract(path):
    raw = path.read_text()
    block = raw.split("Appendix A. Expansion", 1)[1].split("References", 1)[0]
    pattern = r"([+−-]\d\.\d+)\s*×\s*10([−-]\d+)\s+([^+−\n]+)"
    terms = []
    for match in re.finditer(pattern, block):
        mantissa, exponent, mono = match.groups()
        coef = mantissa.replace("−", "-") + "e" + exponent.replace("−", "-")
        powers = [0] * 6
        tokens = re.findall(r"([ξη])(\d)(\d)", mono)
        for var, a, b in tokens:
            # This PDF text layer orders xi's subscript first, eta's superscript first.
            index, power = (int(a), int(b)) if var == "ξ" else (int(b), int(a))
            assert 1 <= index <= 3 and 1 <= power <= 4, (mono, tokens)
            powers[index - 1 + (3 if var == "η" else 0)] += power
        assert sum(powers) in (2, 4), (coef, mono, powers)
        terms.append({"powers": powers, "coefficient": coef, "pdf_token": mono.strip()})
    assert len(terms) == 78 and len({tuple(t['powers']) for t in terms}) == 78
    assert Counter(sum(t['powers']) for t in terms) == {2: 12, 4: 66}
    assert all(sum(t['powers'][3:]) % 2 == 0 for t in terms)
    for t in terms:
        Fraction(t['coefficient'])
    return {
        "status": "literal decimal model; transcription, not interval coefficient provenance",
        "source": "SLG13, Mathematics and Computers in Simulation 88 (2013), Appendix A, p. 12",
        "doi": "10.1016/j.matcom.2010.11.018",
        "source_pdf_sha256": "915002b163d9efaeb7eea0a6b335bfda674a15944a7b7cf4fad0934d91e5147c",
        "text_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "variable_order": ["xi_J", "xi_S", "xi_U", "eta_J", "eta_S", "eta_U"],
        "canonical_order": "q=eta, p=xi; X=(dH/dxi,-dH/deta) in (q,p) order",
        "time_unit": "year",
        "terms": terms,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('text', type=Path)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('slg13_quartic.json'))
    args = parser.parse_args()
    args.output.write_text(json.dumps(extract(args.text), indent=2) + '\n')
    print('PASS: 78 distinct terms, 12 quadratic + 66 quartic; exact decimal strings.')

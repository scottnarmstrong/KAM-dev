#!/usr/bin/env python3
"""Checks for the numerical research artifacts, without Lean or a source PDF."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
path = root/'slg13_quartic.json'
data = json.loads(path.read_text())
H = {tuple(t['powers']): Fraction(t['coefficient']) for t in data['terms']}
assert len(H) == 78
assert sum(sum(e) == 2 for e in H) == 12
assert sum(sum(e) == 4 for e in H) == 66
assert all(sum(e[3:]) % 2 == 0 for e in H)
# Independent scalar witness in {C,H} = sum(eta*d_xi H-xi*d_eta H).
witness = (-2*H[(0, 0, 0, 0, 2, 2)] + 2*H[(0, 2, 0, 0, 0, 2)]
           + H[(0, 1, 1, 0, 1, 1)])
assert witness == Fraction(78391581085853, 250000000000000000000)
assert witness > 0
print('PASS: 78 exact decimal terms; independent nonzero AMD-bracket witness.')
for name in ['scout-k10.json', 'scout-k10-table2.json']:
    r = json.loads((root/'results'/name).read_text())
    assert r['data_sha256'] == hashlib.sha256(path.read_bytes()).hexdigest()
    assert Fraction(r['literal_table_amd_defect']['max_coefficient_exact']) == witness
    assert r['substitution_check_relative'] < 1e-12
    assert r['orthogonality_defect'] < 1e-13
    assert all(n['homological_relative_residual'] < 1e-12 for n in r['normalization'])
    assert all(max(n['relative_evaluation_errors']) < 1e-10 for n in r['bracket_checks'])
    assert len(r['curve']) == 35
    for row in r['curve']:
        if row['T_year_estimate'] > 0:
            assert all(m > 0 for m in row['boundary_margins'])
            limit = min(m/e for m, e in zip(row['boundary_margins'], row['eta_per_year']))
            assert abs(limit/row['T_year_estimate']-1) < 1e-12
        assert all(int(k) <= row['K']+2 for c in row['bracket_degree_census'] for k in c)
    nominal = max(x['T_year_estimate'] for x in r['curve'] if x['r'] == 1)
    assert 3e4 < nominal < 4e4
    assert max(x['T_year_estimate'] for x in r['curve'] if x['r'] == .3) > 1e10
    print(f'PASS: {name}: provenance, substitution, homological solve, bracket, 35 margin rows.')
print('STATUS: numerical consistency checks only; no interval proof or Lean theorem.')

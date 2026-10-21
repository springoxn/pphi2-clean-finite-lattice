#!/usr/bin/env python3
"""Check provenance of the finite lattice definitions against pinned GaussianField.
This is a source correspondence check; Lean proves the representation change
and moments separately. Proof bodies are not compared. It does not assert
identity of whole upstream Gaussian constructions. Not in global run_checks.
"""
from pathlib import Path
import argparse
import re
import subprocess

PIN = 'd63a28568a75d99f6cb27af1f888a49a69855a66'
ROOT = Path(__file__).resolve().parent.parent


def uncomment(s):
    out = []
    i = depth = 0
    while i < len(s):
        if s.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and s.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif s.startswith('--', i):
            j = s.find('\n', i)
            i = len(s) if j < 0 else j
        else:
            out.append(s[i])
            i += 1
    if depth:
        raise AssertionError('unclosed Lean comment')
    return ''.join(out)


def norm(s):
    return re.sub(r'\s+', '', s)


def decl(text, name):
    text = uncomment(text)
    m = re.search(r'(?m)^(?:noncomputable )?(?:def|abbrev) ' + name + r'\b', text)
    if not m:
        raise AssertionError('missing definition: ' + name)
    tail = text[m.end():]
    nxt = re.search(r'(?m)^(?:noncomputable )?(?:def|abbrev|theorem|lemma|instance|section|end|variable)\b', tail)
    return tail[:nxt.start()] if nxt else tail


def body(text, name):
    return decl(text, name).split(':=', 1)[1].strip()


def check_equal(label, a, b):
    if norm(a) != norm(b):
        raise AssertionError(label + ': source mismatch\nUP: ' + a + '\nCLEAN: ' + b)
    print('PASS: ' + label)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--upstream', type=Path, required=True)
    args = ap.parse_args()
    up = args.upstream
    pin = subprocess.check_output(['git', '-C', str(up), 'rev-parse', 'HEAD'], text=True).strip()
    if pin != PIN:
        raise AssertionError('upstream pin changed: ' + pin)
    files = ['Lattice/FiniteField.lean', 'Lattice/Laplacian.lean',
             'Lattice/SpectralCovariance.lean', 'Lattice/Covariance.lean']
    dirty = subprocess.check_output(['git', '-C', str(up), 'status', '--porcelain', '--', *files], text=True)
    if dirty.strip():
        raise AssertionError('uncommitted upstream source changes: ' + dirty)
    texts = {f: (up / f).read_text(encoding='utf-8') for f in files}
    clean = (ROOT / 'AImathPPhi2Clean/ConcreteLatticeOperator.lean').read_text(encoding='utf-8')
    groups = {
        'Lattice/FiniteField.lean': ['finLatticeDelta'],
        'Lattice/Laplacian.lean': ['finiteLaplacianFun', 'finiteLaplacian', 'massOperator'],
        'Lattice/SpectralCovariance.lean': ['massOperatorEntry', 'massOperatorMatrix',
            'massEigenvalues', 'massEigenvectorBasis'],
    }
    for f, names in groups.items():
        for name in names:
            a = body(texts[f], name)
            a = a.replace('finLatticeDelta d N y', 'finLatticeDelta y')
            check_equal(name, a, body(clean, name))
    a = decl(texts['Lattice/Laplacian.lean'], 'finiteLaplacianLM')
    b = decl(clean, 'finiteLaplacianLM')
    check_equal('finiteLaplacianLM.toFun', a.split('toFun :=', 1)[1].split("map_add'", 1)[0],
                b.split('toFun :=', 1)[1].split("map_add'", 1)[0])
    spectral = body(texts['Lattice/SpectralCovariance.lean'], 'spectralLatticeCovariance')
    actual = spectral.split('toFun :=', 1)[1].split("map_add'", 1)[0].strip()
    expected = '''fun f => ∑ k : FinLatticeSites d N,
        ((Real.sqrt (eigvals k))⁻¹ *
         ∑ x : FinLatticeSites d N, (eigvecs k : EuclideanSpace ℝ _) x * f x) •
        lp.single 2 (enum k).val (1 : ℝ)'''
    check_equal('spectralLatticeCovariance.toFun', actual, expected)
    for phrase in ['set eigvecs := massEigenvectorBasis d N a mass',
                   'set eigvals := massEigenvalues d N a mass',
                   'set enum := Fintype.equivFin (FinLatticeSites d N)']:
        if norm(phrase) not in norm(spectral):
            raise AssertionError('spectral input changed: ' + phrase)
    gj = body(texts['Lattice/Covariance.lean'], 'latticeCovarianceGJ')
    check_equal('latticeCovarianceGJ scalar', gj,
                '(Real.sqrt (a^d))⁻¹ • latticeCovariance d N a mass ha hmass')
    check_equal('latticeCovariance delegates to spectral construction',
                body(texts['Lattice/Covariance.lean'], 'latticeCovariance'),
                'spectralLatticeCovariance d N a mass ha hmass')
    for corrupted in [expected.replace('⁻¹', '', 1), expected.replace('lp.single 2', 'lp.single 1')]:
        if norm(actual) == norm(corrupted):
            raise AssertionError('negative control accepted corrupted formula')
    print('PASS: coefficient corruption negative controls')
    print('Pinned upstream finite lattice definitions correspond: ' + pin)

if __name__ == '__main__':
    main()

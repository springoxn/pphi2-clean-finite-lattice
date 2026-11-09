#!/usr/bin/env python3
"""Article audit: core scale identities, source coverage, PDF structure and layout.

Finite CAS checks complement the written proofs; they do not verify infinite
sums, weak convergence or Lean statements. Failures have nonzero exit codes.
Requires sympy and PyMuPDF. Not registered in the parent project's run_checks.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def source_checks():
    files = [ROOT / "main.tex", ROOT / "bibliography.tex", *sorted((ROOT / "sections").glob("*.tex"))]
    require(len(files) == 9, "unexpected source coverage")
    text = "\n".join(p.read_text(encoding="utf-8") for p in files)
    for anchor in ("\\begin{theorem}[Common paper theorem]", "eq:dispersion", "eq:variance-error",
                   "periodicHMinusThree_fixedVolume_weak_limit_exists_with_expected_cylinders",
                   "fs4PeriodicFixedVolume\\_weak\\_tendsto\\_free", "arbitrary-dimensional formalization",
                   "UNVERIFIED", "QUALIFIED", "s>d/2", "C-iS", "C+iS", "L^{-4}"):
        require(anchor in text, "missing source anchor: " + anchor)
    for env in ("equation", "align", "table", "theorem", "proof", "lemma", "proposition"):
        require(text.count("\\begin{" + env + "}") == text.count("\\end{" + env + "}"),
                "unbalanced environment: " + env)
    labels = re.findall(r"\\label\{([^}]+)\}", text)
    require(len(labels) == len(set(labels)), "duplicate labels")
    for key in re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", text):
        require(key in labels, "undefined reference: " + key)
    bibliography = set(re.findall(r"\\bibitem\{([^}]+)\}", text))
    for group in re.findall(r"\\cite\{([^}]+)\}", text):
        require(set(group.split(',')) <= bibliography, "undefined citation: " + group)
    return files


def scale_checks():
    a, N, L, m, t = sp.symbols('a N L m t', positive=True)
    for d in (1, 2, 4):
        prefactor = a**(2*d) * a**(-d) * N**(-d) * N**(2*d)
        require(sp.simplify(prefactor.subs(a, L/N) - L**d) == 0, "volume prefactor")
        require(sp.simplify(L**d * (4*sp.pi**4*a**2/(3*L**4)) / m**4
                            - 4*sp.pi**4*a**2*L**(d-4)/(3*m**4)) == 0,
                "dispersion to variance scale")
    series = sp.series(t**2 - sp.sin(t)**2, t, 0, 6).removeO()
    require(sp.expand(series - t**4/3) == 0, "sine leading error coefficient")
    # Independent finite matrix check: inverse nearest-neighbour precision vs
    # Fourier diagonalization, including the N=2 doubled-neighbour case.
    for n in (1, 2, 3, 4):
        for side in (sp.Rational(1, 10), sp.Rational(3, 2)):
            spacing = side/n
            precision = sp.eye(n) * sp.Rational(9, 4)
            for x in range(n):
                precision[x, x] += 2/spacing**2
                precision[x, (x+1) % n] -= 1/spacing**2
                precision[x, (x-1) % n] -= 1/spacing**2
            covariance = precision.inv()/spacing
            for k in range(n):
                vec = sp.Matrix([sp.exp(-2*sp.pi*sp.I*k*x/n) for x in range(n)])
                actual = (spacing**2 * (vec.T * covariance * sp.conjugate(vec))[0]).expand(complex=True)
                target = side/(sp.Rational(9, 4)+4/spacing**2*sp.sin(sp.pi*k/n)**2)
                require(sp.simplify(actual-target) == 0, "independent matrix Fourier variance")
    # Published old guide's missing L^-4 is falsified at small volume.
    side = sp.Rational(1, 10)
    n = 100
    spacing = side/n
    gap = (2*sp.pi/side)**2 - 4/spacing**2*sp.sin(sp.pi/n)**2
    old = 4*sp.pi**4*spacing**2/3
    correct = old/side**4
    require(bool(sp.N(gap-old, 40) > 0), "negative control did not expose old guide bound")
    require(bool(sp.N(correct-gap, 40) > 0), "corrected bound failed")
    return {"old_guide_counterexample": {"L": str(side), "N": n,
            "gap": str(sp.N(gap, 20)), "incorrect_upper_bound": str(sp.N(old, 20)),
            "correct_upper_bound": str(sp.N(correct, 20))}}


def contract_checks(repo=None):
    import importlib.util
    record = json.loads((ROOT / 'audit/bridge_contract.json').read_text(encoding='utf-8'))
    query = ROOT / 'audit/bridge_contract.lean'
    log = ROOT / 'audit/bridge_contract.log'
    require(hashlib.sha256(query.read_bytes()).hexdigest() == record['query_sha256'], 'joint query hash')
    require(hashlib.sha256(log.read_bytes()).hexdigest() == record['output_sha256'], 'joint transcript hash')
    require(record['returncode'] == 0, 'joint Lean contract exit status')
    text = log.read_text(encoding='utf-8')
    require(not re.search(r'error:|sorryAx', text), 'bad joint contract output')
    names = ('periodicHMinusThree_fixedVolume_weak_limit_exists_with_expected_cylinders',
             'fs4PeriodicFixedVolume_weak_tendsto_free')
    for name in names:
        full = 'Pphi2Clean.Continuum.' + name
        require(re.search(re.escape(full) + r'\s*:', text), 'missing signature ' + name)
        match = re.search("'" + re.escape(full) + r"' depends on axioms:\s*\[([^]]*)\]", text)
        require(match is not None, 'missing axiom record ' + name)
        require(set(x.strip() for x in match[1].split(',')) ==
                {'propext', 'Classical.choice', 'Quot.sound'}, 'nonfoundational axiom ' + name)
    require(record['toolchain'] == 'leanprover/lean4:v4.34.0-rc2', 'toolchain mismatch')
    require(record['mathlib_rev'] == '852d20a84581aeba8527bd01d0be361d8c0e71c0', 'Mathlib mismatch')
    if repo is not None:
        repo = repo.resolve()
        for rel, expected in record['source_sha256'].items():
            require(hashlib.sha256((repo / rel).read_bytes()).hexdigest() == expected,
                    'bound release source mismatch: ' + rel)
        spec = importlib.util.spec_from_file_location('bridge_release_verify', repo / 'verify.py')
        verifier = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(verifier)
        modules = sorted((repo / 'AImathPPhi2Clean').glob('*.lean'))
        lines, declarations, sorry = verifier._census(modules)
        census = {'modules': len(modules), 'module_lines': lines, 'declarations': declarations, 'sorry': sorry}
        require(census == record['census'], 'source census mismatch')
        counts = [verifier.DECL.match(line) for p in modules
                  for line in verifier.strip_comments(p.read_text(encoding='utf-8')).splitlines()]
        require(sum(bool(m and m[1] in ('theorem', 'lemma')) for m in counts) == 780,
                'article theorem/lemma count')
    return {'two_native_theorems': list(names), 'only_foundational_axioms': True,
            'actual_release_hashes_checked': repo is not None, 'census': record['census']}


def pdf_checks(path):
    import fitz
    with fitz.open(path) as doc:
        require(len(doc) >= 8, "unexpectedly short PDF")
        text = " ".join(" ".join(page.get_text().split()) for page in doc)
        for phrase in ("PERIODIC GAUSSIAN LATTICE LIMITS", "Common paper theorem",
                       "Evidence ledger", "Evidence boundary", "References"):
            require(phrase.lower() in text.lower(), "PDF missing: " + phrase)
        require('�' not in text, "PDF replacement character")
        require(not re.search(r'\?\?|undefined', text, re.I), "unresolved PDF content")
        captions = sorted(set(re.findall(r'Table\s+([1-3])\.', text)))
        require(captions == ['1', '2', '3'], "PDF lost a table caption")
        for page in doc:
            require(len(page.get_text().strip()) > 30, "blank or missing-text page")
            for block in page.get_text('dict')['blocks']:
                for line in block.get('lines', []):
                    for span in line['spans']:
                        x0, y0, x1, y1 = span['bbox']
                        require(x0 >= 35 and x1 <= page.rect.width-35,
                                f"text crosses page margin on page {page.number+1}: {span['text']}")
                        require(y0 >= 20 and y1 <= page.rect.height-20, "text outside page")
        return {"pages": len(doc), "table_captions": captions,
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pdf', type=Path)
    parser.add_argument('--source-only', action='store_true')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--repo', type=Path, help='release repository root for actual source-hash verification')
    args = parser.parse_args()
    try:
        files = source_checks()
        result = {"source_sha256": {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
                  "finite_symbolic_checks": scale_checks(),
                  "joint_Lean_contract": contract_checks(args.repo)}
        if not args.source_only:
            pdf = args.pdf or ROOT / 'periodic_gaussian_dimension_bridge.pdf'
            result['artifact'] = pdf_checks(pdf)
            log = ROOT / 'build/main.log'
            if log.exists():
                text = log.read_text(encoding='utf-8')
                require(not re.search(r'Overfull|undefined|Missing character', text, re.I), "TeX log has layout/reference/font defects")
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
        print(json.dumps(result, indent=2))
        print('PASS source anchors, exact scale checks, independent finite matrix tests and requested artifact checks')
        return 0
    except (ValueError, OSError, KeyError) as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        return 1

if __name__ == '__main__':
    raise SystemExit(main())

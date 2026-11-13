"""Exact finite Fourier checks for the 4-D periodic Gaussian normalization.

This probe checks finite character orthogonality, alias invariance, the raw atomic lift's coefficient identity, lattice and target Gaussian normalizations, both complex cross-mode covariance identities, the fixed-mode O(a^2) dispersion/variance bound on finite rational parameter grids, and finite instances of the frequency-shell inequalities. The assertions are finite checks, not proofs of the corresponding all-N estimates.
"""
from __future__ import annotations

from functools import lru_cache
import itertools
import sys

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

import sympy as sp

_I = sp.I
_PI = sp.pi
_Z = sp.Symbol("z")


def _exact_zero(expression):
    return sp.simplify(sp.expand_complex(expression)) == 0


def _character_sum_remainder(n: int, r: int):
    polynomial = sp.Poly(
        sum(_Z ** ((r * x) % n) for x in range(n)), _Z, domain=sp.QQ
    )
    cyclotomic = sp.Poly(sp.cyclotomic_poly(n, _Z), _Z, domain=sp.QQ)
    return polynomial.rem(cyclotomic).as_expr()


def _sampled_mode_coefficient(n: int, side, mode: int, residue: int, sine: bool):
    one_dimensional = sum(
        (sp.sin if sine else sp.cos)(2 * _PI * mode * x / n)
        * sp.exp(-2 * _PI * _I * residue * x / n)
        for x in range(n)
    )
    # The other three coordinates contribute n^3 by character orthogonality.
    return sp.simplify(sp.expand_complex((side / n) ** 4 * n**3 * one_dimensional))


def _lambda(n: int, side, mass, residue: int):
    return sp.simplify(
        mass**2 + 4 * (sp.Rational(n, 1) / side) ** 2
        * sp.sin(_PI * residue / n) ** 2
    )


@lru_cache(maxsize=None)
def _orthogonality_value(n: int, residue: int):
    expected = sp.Integer(n if residue % n == 0 else 0)
    remainder = _character_sum_remainder(n, residue)
    assert sp.simplify(remainder - expected) == 0
    return expected


def _lambda_4d(n: int, side, mass, residue):
    return sp.simplify(
        mass**2 + 4 * (sp.Rational(n, 1) / side) ** 2
        * sum(sp.sin(_PI * int(p) / n) ** 2 for p in residue)
    )


def _fourier_cross_covariance(n: int, side, mass, k, ell, conjugate_second: bool):
    """Evaluate the finite Fourier-kernel covariance by exact character sums."""
    mesh = sp.Rational(side, n)
    prefactor = mesh**8 * mesh**-4 * sp.Rational(1, n**4)
    total = sp.Integer(0)
    for p in itertools.product(range(n), repeat=4):
        left = sp.prod(
            _orthogonality_value(n, p[j] - k[j]) for j in range(4)
        )
        if conjugate_second:
            right = sp.prod(
                _orthogonality_value(n, ell[j] - p[j]) for j in range(4)
            )
        else:
            right = sp.prod(
                _orthogonality_value(n, -ell[j] - p[j]) for j in range(4)
            )
        if left != 0 and right != 0:
            total += left * right / _lambda_4d(n, side, mass, p)
    return sp.simplify(prefactor * total)


def check_character_orthogonality():
    for n in range(2, 9):
        for r in range(-2 * n, 2 * n + 1):
            expected = sp.Integer(n if r % n == 0 else 0)
            assert sp.simplify(_character_sum_remainder(n, r) - expected) == 0
    return "exact roots-of-unity sums for N=2..8 and residues across multiple periods"


def check_alias_invariance():
    for n in range(2, 8):
        for k in range(-5, 6):
            for q in range(-3, 4):
                for x in range(n):
                    aliased = sp.exp(2 * _PI * _I * (k + n * q) * x / n)
                    reduced = sp.exp(2 * _PI * _I * k * x / n)
                    assert _exact_zero(aliased - reduced)
    return "exact character invariance under k -> k+Nq for N=2..7"


def check_four_dimensional_mode_moment():
    side = sp.Integer(2)
    mass = sp.Integer(1)
    volume = side**4
    for n in range(2, 7):
        for mode in range(n):
            cos_coefficients = [
                _sampled_mode_coefficient(n, side, mode, p, sine=False)
                for p in range(n)
            ]
            sin_coefficients = [
                _sampled_mode_coefficient(n, side, mode, p, sine=True)
                for p in range(n)
            ]
            cov_cos = sp.simplify(sum(
                sp.conjugate(c) * c / _lambda(n, side, mass, p)
                for p, c in enumerate(cos_coefficients)
            ) / volume)
            cov_sin = sp.simplify(sum(
                sp.conjugate(c) * c / _lambda(n, side, mass, p)
                for p, c in enumerate(sin_coefficients)
            ) / volume)
            expected = sp.simplify(volume / _lambda(n, side, mass, mode))
            assert _exact_zero(cov_cos + cov_sin - expected)
    return "E|Xhat_N(k)|^2 = L^4/lambda_N(k mod N), including zero and self-negative modes"


def check_raw_atomic_lift_fourier_coordinates():
    for n in range(2, 5):
        side = sp.Integer(1)
        mesh = side / n
        modes = [(0, 0, 0, 0), (1, -1, 0, 1), (-2, 1, 0, 0), (n, 0, -n, 1)]
        sites = list(itertools.product(range(n), repeat=4))
        for k in modes:
            raw = sp.Integer(0)
            cosine = sp.Integer(0)
            sine = sp.Integer(0)
            for x in sites:
                field_value = 1 + sum((j + 1) * x[j] for j in range(4))
                phase = 2 * _PI * sum(k[j] * x[j] for j in range(4)) / n
                raw += mesh**4 * field_value * sp.exp(-_I * phase)
                cosine += mesh**4 * field_value * sp.cos(phase)
                sine += mesh**4 * field_value * sp.sin(phase)
            assert _exact_zero(raw - (cosine - _I * sine))
    return "raw atomic Fourier coefficient equals cosine minus i times sine evaluation"


def check_four_dimensional_cross_mode_covariances():
    side = sp.Integer(2)
    mass = sp.Integer(1)
    for n in range(2, 6):
        modes = [
            (0, 0, 0, 0),
            (1, 0, 0, 0),
            (-1, 0, 0, 0),
            (n, 1, -n, 0),
            (0, -1, 1, 0),
            (n // 2, 0, 0, 0),
        ]
        for k, ell in itertools.product(modes, repeat=2):
            residue_k = tuple(value % n for value in k)
            for conjugate_second in (True, False):
                actual = _fourier_cross_covariance(
                    n, side, mass, k, ell, conjugate_second
                )
                if conjugate_second:
                    matches = residue_k == tuple(value % n for value in ell)
                else:
                    matches = residue_k == tuple((-value) % n for value in ell)
                expected = (
                    side**4 / _lambda_4d(n, side, mass, residue_k)
                    if matches else sp.Integer(0)
                )
                assert _exact_zero(actual - expected)
    return (
        "both conjugated and unconjugated cross covariances, including aliases "
        "and Nyquist self-opposition, equal the exact modulo-N formulas"
    )


def check_real_coordinate_conversion():
    c_k, s_k, c_l, s_l = sp.symbols("c_k s_k c_l s_l", real=True)
    z_k = c_k - _I * s_k
    z_l = c_l - _I * s_l
    A = sp.expand(z_k * sp.conjugate(z_l))
    B = sp.expand(z_k * z_l)
    expected = {
        "cc": c_k * c_l,
        "ss": s_k * s_l,
        "cs": c_k * s_l,
    }
    actual = {
        "cc": (sp.re(A) + sp.re(B)) / 2,
        "ss": (sp.re(A) - sp.re(B)) / 2,
        "cs": (sp.im(A) - sp.im(B)) / 2,
    }
    for name in expected:
        assert sp.simplify(actual[name] - expected[name]) == 0, name
    return "real cosine/sine covariance conversion from A=E[Z conjugate W], B=E[Z W]"


def check_target_gaussian_mode_normalization():
    side, mass, lam = sp.symbols("L m lam", positive=True, real=True)
    xi0, xi, eta = sp.symbols("xi0 xi eta", real=True)
    zero_coeff = side**2 * xi0 / mass
    nonzero_coeff = side**2 * (xi + _I * eta) / sp.sqrt(2 * lam)
    zero_second = sp.expand(zero_coeff**2).subs(xi0**2, 1)
    nonzero_second = sp.expand_complex(
        nonzero_coeff * sp.conjugate(nonzero_coeff)
    ).subs({xi**2: 1, eta**2: 1, xi * eta: 0})
    assert sp.simplify(zero_second - side**4 / mass**2) == 0
    assert sp.simplify(nonzero_second - side**4 / lam) == 0
    return "target zero and paired Gaussian modes have E|Xhat(k)|^2=L^4/lambda(k)"


def check_target_covariance_pairing_factor():
    side, lam = sp.symbols("L lam", positive=True, real=True)
    f_minus, g_plus = sp.symbols("Ff_minus Fg_plus")
    mode_covariance = side**4 / lam
    pairing = sp.simplify(side**-8 * mode_covariance * f_minus * g_plus)
    expected = side**-4 * f_minus * g_plus / lam
    assert sp.simplify(pairing - expected) == 0
    return "target mode covariance plus L^-4 pairing gives the stated Q normalization"


def check_fixed_mode_dispersion_error_bound():
    worst_ratio = 0.0
    for side in (1, 2, 5):
        for mass in (0.5, 1, 3):
            for n in range(2, 24):
                a = side / n
                for k in ((1, 0, 0, 0), (1, -2, 1, 0), (2, 1, -1, 3)):
                    if max(abs(component) for component in k) >= n:
                        continue
                    norm4 = sum(component**4 for component in k)
                    discrete = mass**2 + (4 / a**2) * sum(
                        sp.sin(_PI * component / n) ** 2 for component in k
                    )
                    continuum = mass**2 + (2 * _PI / side) ** 2 * sum(
                        component**2 for component in k
                    )
                    gap = float(sp.N(continuum - discrete, 40))
                    bound = (4 * float(_PI**4) * a**2 * norm4) / (3 * side**4)
                    assert -1e-35 <= gap <= bound + 1e-30
                    variance_gap = float(sp.N(
                        side**4 / discrete - side**4 / continuum, 40
                    ))
                    variance_bound = (
                        4 * float(_PI**4) * a**2 * norm4 / (3 * mass**4)
                    )
                    assert -1e-30 <= variance_gap <= variance_bound + 1e-28
                    if norm4:
                        worst_ratio = max(worst_ratio, gap / bound)
    assert 0 <= worst_ratio <= 1
    return "fixed-mode dispersion and variance errors obey the derived O(a^2) bounds on rational parameter grids"


def check_shell_and_alias_inequalities():
    for radius in range(1, 65):
        shell_count = (2 * radius + 1) ** 4 - (2 * radius - 1) ** 4
        assert shell_count == 64 * radius**3 + 16 * radius
        assert shell_count <= 80 * radius**3

    for n in range(2, 9):
        box = range(-(n // 2), -(n // 2) + n)
        for p in itertools.product(box, repeat=4):
            for q in itertools.product(range(-2, 3), repeat=4):
                if not any(q):
                    continue
                lhs = sum((p[j] + n * q[j]) ** 2 for j in range(4))
                q_sq = sum(qj**2 for qj in q)
                assert 4 * lhs >= n**2 * q_sq

    # Sharpness control: even-N boundary residues attain equality.
    n = 4
    p = (-2, 0, 0, 0)
    q = (1, 0, 0, 0)
    lhs = sum((p[j] + n * q[j]) ** 2 for j in range(4))
    q_sq = sum(qj**2 for qj in q)
    assert 2 * lhs < n**2 * q_sq
    return "shell count = 64r^3+16r <= 80r^3; exhaustive centered-box alias bound |p+Nq|^2 >= N^2|q|^2/4 for N=2..8, with sharpness negative control"


def check_mass_gap_trace_majorant():
    """Exact algebra for the all-frequency bound; measure theory is paper-level."""
    r = sp.Symbol("r", integer=True, positive=True)
    x = sp.Symbol("x", positive=True)
    shell = sp.expand((2 * r + 1) ** 4 - (2 * r - 1) ** 4)
    assert sp.expand(shell - (64 * r**3 + 16 * r)) == 0
    assert sp.factor(80 * r**3 - shell) == 16 * r * (r - 1) * (r + 1)
    # For integer r>=1 the last factorization is nonnegative.
    assert sp.integrate(x**-3, (x, 1, sp.oo)) == sp.Rational(1, 2)
    assert 1 + 80 * (1 + sp.Rational(1, 2)) == 121
    # Exact mode identity also holds for the one-site lattice (all modes alias zero).
    side, mass = sp.Integer(2), sp.Integer(3)
    c = _sampled_mode_coefficient(1, side, 0, 0, sine=False)
    assert _exact_zero(c**2 / (side**4 * mass**2) - side**4 / mass**2)
    # A critical H^-2 weight would leave a harmonic shell majorant: it does not
    # justify summability by this mass-gap-only argument in four dimensions.
    assert sp.expand(80 * r**3 * r**-4 - 80 / r) == 0
    return "exact shell algebra and integral-test constant 121; N=1 normalization; H^-2 critical-exponent control (all-N measure bound remains paper-level)"


def check_all_n_raw_mode_prefactor():
    """Symbolically reduce the kernel/character normalization in dimension four."""
    a, n, side, lam = sp.symbols("a N L lambda", positive=True, real=True)
    # a^8 comes from the two raw atomic coefficients; a^-4 N^-4 is the
    # covariance kernel prefactor; each character sum contributes N^4.
    raw_prefactor = sp.simplify(a**8 * a**-4 * n**-4 * n**4 * n**4 / lam)
    assert sp.simplify(raw_prefactor - a**4 * n**4 / lam) == 0
    assert sp.simplify(raw_prefactor.subs(a, side / n) - side**4 / lam) == 0
    return "symbolic kernel prefactor a^8*a^-4*N^-4*N^4*N^4 = (aN)^4; set a=L/N to get L^4"


def check_wrong_volume_normalization_fails():
    n, side, mass, mode = 3, sp.Integer(2), sp.Integer(1), 1
    coeffs = [
        _sampled_mode_coefficient(n, side, mode, p, sine=False)
        for p in range(n)
    ]
    sum_sq = sp.simplify(sum(
        sp.conjugate(c) * c / _lambda(n, side, mass, p)
        for p, c in enumerate(coeffs)
    ))
    correct = sp.simplify(sum_sq / side**4)
    wrong = sp.simplify(sum_sq / side**2)
    target = sp.simplify(side**4 / _lambda(n, side, mass, mode))
    assert _exact_zero(correct + (
        sum(sp.conjugate(_sampled_mode_coefficient(
            n, side, mode, p, sine=True
        )) * _sampled_mode_coefficient(n, side, mode, p, sine=True)
            / _lambda(n, side, mass, p) for p in range(n)) / side**4
    ) - target)
    assert not _exact_zero(wrong - correct)
    return "negative control: substituting L^-2 for L^-4 changes the covariance"


def run_all():
    checks = (
        ("finite character orthogonality", check_character_orthogonality),
        ("integer-mode alias invariance", check_alias_invariance),
        ("4-D Fourier probe moment normalization", check_four_dimensional_mode_moment),
        ("all-N raw mode prefactor algebra", check_all_n_raw_mode_prefactor),
        ("raw atomic lift complex coefficient and real evaluations", check_raw_atomic_lift_fourier_coordinates),
        ("4-D cross-mode covariance and alias cases", check_four_dimensional_cross_mode_covariances),
        ("real cosine/sine covariance conversion", check_real_coordinate_conversion),
        ("target Gaussian mode normalization", check_target_gaussian_mode_normalization),
        ("target covariance pairing normalization", check_target_covariance_pairing_factor),
        ("fixed-mode dispersion error bound", check_fixed_mode_dispersion_error_bound),
        ("shell counts and centered alias inequality", check_shell_and_alias_inequalities),
        ("mass-gap trace majorant algebra", check_mass_gap_trace_majorant),
        ("volume-factor negative control", check_wrong_volume_normalization_fails),
    )
    for name, check in checks:
        try:
            yield name, True, check()
        except Exception as exc:  # noqa: BLE001
            yield name, False, repr(exc)


if __name__ == "__main__":
    failed = False
    for name, ok, message in run_all():
        print(f"[{'OK' if ok else 'FAIL'}] {name}: {message}")
        failed = failed or not ok
    raise SystemExit(1 if failed else 0)

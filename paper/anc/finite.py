"""Exact finite adjacent-row checks for ordered set partitions, threshold two."""
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent


def original_rows(last):
    rows = [[1]]
    for n in range(1, last + 1):
        row = [0] * (n // 2 + 1)
        for s in range(1, n + 1):
            for h, c in enumerate(rows[n - s]):
                row[h + int(s >= 2)] += comb(n, s) * c
        rows.append(row)
    return rows


def associated_rows(last):
    a = {(0, 0): 1}
    for m in range(1, last + 1):
        for h in range(m // 2 + 1):
            a[m, h] = (h * a.get((m - 1, h), 0)
                        + (m - 1) * a.get((m - 2, h - 1), 0))
    return [[sum(comb(n, s) * a.get((n - s, h), 0) * factorial(h + s)
                 for s in range(n + 1)) for h in range(n // 2 + 1)]
            for n in range(last + 1)]


def val(poly, i, den):
    """(den-i)^degree O(-i/(den-i)); includes the limit at i=den."""
    x, y = -i, den - i
    res, yp = poly[-1], 1
    for c in reversed(poly[:-1]):
        yp *= y
        res = res * x + c * yp
    return res


def generate(pols):
    total = sum(len(p) - 1 for p in pols)
    for power in range(3, 24):
        den = 1 << power
        signs = []
        prev = [val(p, 0, den) for p in pols]
        for i in range(1, den + 1):
            curr = [val(p, i, den) for p in pols]
            for h in (0, 1):
                if prev[h] * curr[h] < 0:
                    signs.append([h, i-1, i])
                if i >= 2 and prev[h] == 0 and curr[h] * val(pols[h], i-2, den) < 0:
                    signs.append([h, i-2, i])
            prev = curr
        signs.sort(key=lambda triple: triple[1:])
        if len(signs) == total and all(u[2] <= v[1] for u,v in zip(signs,signs[1:])):
            return [den, signs]
    raise RuntimeError("grid did not isolate both rows")


def check(n, pols, cert):
    den, signs = cert
    assert type(den) is int and den > 0
    assert len(signs) == sum(len(p)-1 for p in pols)
    # Increasing q is decreasing original t. The new row has its root first.
    for j, (h, left, right) in enumerate(signs):
        assert h == 1 - j % 2 and 0 <= left < right <= den
        assert not j or signs[j-1][2] <= left
        assert val(pols[h], left, den) * val(pols[h], right, den) < 0
    for h, p in enumerate(pols):
        assert sum(t[0] == h for t in signs) == (n + h) // 2 == len(p)-1
        assert p[0] > 0 and p[-1] > 0


if __name__ == "__main__":
    rows = original_rows(22)
    assert rows == associated_rows(22)
    assert 4*42*7**21 < 9**21
    assert 2*sum(Fraction(5,7)**(2*i+1)/(2*i+1) for i in range(3)) > Fraction(5,3)
    assert sum(Fraction(3**i,factorial(i)) for i in range(9)) > 20
    assert Fraction(25,9)+Fraction(121,49)<Fraction(49,9)
    assert Fraction(12+4*Fraction(22,7),6)*4 < 18
    path = HERE / "brackets.json"
    if sys.argv[1:] == ["--generate"]:
        path.write_text(json.dumps({str(n): generate(rows[n:n+2]) for n in range(2,22)},
                                   separators=(",",":"))+"\n")
    certs = json.loads(path.read_text())
    assert set(certs) == {str(n) for n in range(2,22)}
    for n in range(2,22):
        check(n, rows[n:n+2], certs[str(n)])
    print("PASS: independent ordered last-block and unordered associated Stirling rows n=0..22")
    print("PASS: all old indices 2..21 and exact negative-root isolation for each adjacent pair")
    print("PASS:", sum(len(c[1]) for c in certs.values()), "disjoint sign brackets; analytic cutoff old n=20")
    print("PASS: five rational inequalities used in the contour estimates")

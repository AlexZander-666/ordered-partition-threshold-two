"""Replay the exact two-step signs, independent of contour estimates."""
from finite import HERE, original_rows, associated_rows, generate, val
from fractions import Fraction
import json
import sys

rows = original_rows(29)
assert rows == associated_rows(29)
assert 4 * 162 * 7**26 < 9**26
assert Fraction(1,6) - Fraction(121,49*120) > Fraction(1,7)
path = HERE / "two-step-brackets.json"
if sys.argv[1:] == ["--generate"]:
    data = {str(n): generate((rows[n], rows[n+2])) for n in range(2,28)}
    path.write_text(json.dumps(data,separators=(",",":"))+"\n")
data = json.loads(path.read_text())
assert set(data) == {str(n) for n in range(2,28)}
for n in range(2,28):
    den, brackets = data[str(n)]
    assert type(den) is int and den > 0
    pols = (rows[n],rows[n+2])
    assert len(brackets) == sum(len(p)-1 for p in pols)
    for i,(owner,left,right) in enumerate(brackets):
        assert owner == 1-i%2
        assert 0 <= left < right <= den and (not i or brackets[i-1][2] <= left)
        assert val(pols[owner],left,den)*val(pols[owner],right,den) < 0
    assert all(sum(t[0]==h for t in brackets)==len(p)-1 for h,p in enumerate(pols))
print("PASS: two exact coefficient constructions through 29")
print("PASS: O_n and O_(n+2) for 2<=n<=27,",sum(len(x[1]) for x in data.values()),"strict brackets")
print("PASS: two rational analytic bounds, valid for all old n>=25")

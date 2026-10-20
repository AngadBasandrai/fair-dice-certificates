import itertools
import json
import math
import sys
from fractions import Fraction as Q
from pathlib import Path
import sympy as sp
import z3
HERE = Path(__file__).resolve().parent
PLAYERS = 4
ROOT_SYMBOL = sp.Symbol('s')
TABLES = {}
TABLE_CACHE = {}

def vertices(M):
    mu = Q(M + 1, 2)
    out = []
    for i in range(1, M + 1):
        for j in range(i + 1, M + 1):
            if i < mu < j:
                p = (j - mu) / (j - i)
                out.append((f'D{i}_{j}', {i: p, j: 1 - p}))
    if M % 2 == 1:
        out.append((f'D{(M + 1) // 2}', {(M + 1) // 2: Q(1)}))
    return out

def payoff_by_enumeration(dists):
    total = Q(0)
    for combo in itertools.product(*[sorted(d.items()) for d in dists]):
        prob = Q(1)
        for _, q in combo:
            prob *= q
        top = max((r for r, _ in combo))
        if combo[0][0] == top:
            total += prob / sum((1 for r, _ in combo if r == top))
    return total

def payoff_by_cdf(own, opponents, M):
    total = Q(0)
    k = len(opponents)
    for r in range(1, M + 1):
        mass = own.get(r, Q(0))
        if mass == 0:
            continue
        at = [d.get(r, Q(0)) for d in opponents]
        below = [sum((q for s, q in d.items() if s < r), Q(0)) for d in opponents]
        conditional = Q(0)
        for tied in range(1 << k):
            term = Q(1, 1 + bin(tied).count('1'))
            for j in range(k):
                term *= at[j] if tied >> j & 1 else below[j]
            conditional += term
        total += mass * conditional
    return total

def payoff_table(V, method='enumeration', M=None):
    n = len(V)
    table = {}
    for a in range(n):
        for others in itertools.combinations_with_replacement(range(n), PLAYERS - 1):
            if method == 'enumeration':
                table[(a,) + others] = payoff_by_enumeration([V[a][1]] + [V[o][1] for o in others])
            else:
                table[(a,) + others] = payoff_by_cdf(V[a][1], [V[o][1] for o in others], M)
    return table

def pay(table, a, others):
    return table[(a,) + tuple(sorted(others))]

def expected_profiles(M):
    A, B = ((f'D1_{M}',), (f'D2_{M}',))
    AB = A + B
    if M < 8:
        return [(A, A, A, B), (A, A, AB, AB), (A, AB, AB, AB), (AB,) * 4]
    C = ('D3_8',)
    AC, ABC = (A + C, AB + C)
    return [(A, AB, ABC, AC), (A, AC, AC, B), (AB, AB, ABC, ABC), (AB, AB, ABC, AC), (AB, AB, AC, AC), (AB, ABC, ABC, ABC), (AB, ABC, AC, AC), (ABC,) * 4, (AC, AC, AC, B)]

def canonical(profile):
    return tuple(sorted((tuple(sorted(support)) for support in profile)))

def check_census(M):
    data = json.loads((HERE / f'M{M}.json').read_text(encoding='utf-8'))
    V = vertices(M)
    table = payoff_table(V)
    assert table == payoff_table(V, method='cdf', M=M)
    TABLES[M] = table
    index = {name: i for i, (name, _) in enumerate(V)}
    alive = list(range(len(V)))
    for record in data['dominance']:
        vertex = index[record['vertex']]
        mixture = {index[name]: Q(value) for name, value in record['mixture'].items()}
        assert vertex in alive and vertex not in mixture
        assert set(mixture) <= set(alive) and all((value >= 0 for value in mixture.values()))
        assert sum(mixture.values()) == 1
        domain = alive if M == 8 else range(len(V))
        assert all((sum((value * pay(table, a, others) for a, value in mixture.items())) > pay(table, vertex, others) for others in itertools.combinations_with_replacement(domain, 3)))
        alive.remove(vertex)
    supports = [support for n in range(1, len(alive) + 1) for support in itertools.combinations(alive, n)]
    pairs = {tuple(sorted(pair)) for pair in itertools.combinations_with_replacement(supports, 2)}

    def exclusions(records, players):
        excluded = set()
        for record in records:
            profile = [tuple((index[name] for name in support)) for support in record['supports']]
            assert len(profile) == players
            key = canonical(profile)
            assert key not in excluded
            exact_minimum(V, table, 4, index, record['supports'], record['multipliers'], alive)
            excluded.add(key)
        return excluded
    excluded_pairs = exclusions(data['pairs'], 2)
    assert excluded_pairs <= pairs
    compatible = pairs - excluded_pairs
    candidates = sorted({support for pair in compatible for support in pair})
    profiles = {profile for profile in itertools.combinations_with_replacement(candidates, 4) if all((tuple(sorted(pair)) in compatible for pair in itertools.combinations(profile, 2)))}
    excluded_profiles = exclusions(data['profiles'], 4)
    assert excluded_profiles <= profiles
    residual = profiles - excluded_profiles
    expected = {canonical([[index[name] for name in support] for support in profile]) for profile in expected_profiles(M)}
    assert residual == expected
    counts = [len(alive), len(pairs), len(excluded_pairs), len(profiles), len(excluded_profiles), len(residual)]
    assert counts == {6: [5, 496, 492, 6, 2, 4], 7: [6, 2016, 2006, 21, 17, 4], 8: [8, 32640, 32613, 123, 114, 9]}[M]
    return {'surviving_vertices': counts[0], 'support_pairs': counts[1], 'excluded_pairs': counts[2], 'compatible_profiles': counts[3], 'excluded_profiles': counts[4], 'remaining_profiles': counts[5], 'certificates': len(data['dominance']) + len(data['pairs']) + len(data['profiles'])}

def integer_table(table):
    key = id(table)
    if key not in TABLE_CACHE:
        denominator = math.lcm(*(t.denominator for t in table.values()))
        TABLE_CACHE[key] = (denominator, {k: int(v * denominator) for k, v in table.items()})
    return TABLE_CACHE[key]

def exact_minimum(V, table, players, index, supports, cert, survivors):
    focal = [tuple((index[name] for name in part)) for part in supports]
    F = len(focal)
    assert len(cert) == F
    assert all((part and len(set(part)) == len(part) and (set(part) <= set(survivors)) for part in focal))
    coefficients, multipliers = ([], [])
    for i, record in enumerate(cert):
        y = {index[k]: Q(v) for k, v in record['y'].items()}
        z = {index[k]: Q(v) for k, v in record['z'].items()}
        lam = {index[k]: Q(v) for k, v in record['lambda'].items()}
        assert set(y) <= set(focal[i])
        assert set(z) <= set(range(len(V))) - set(focal[i])
        assert set(lam) <= set(focal[i])
        assert all((t >= 0 for t in z.values())) and all((t >= 0 for t in lam.values()))
        assert sum(y.values()) + sum(z.values()) == 0
        coefficients.append(y | z)
        multipliers.append(lam)
    assert sum((sum(t.values()) for t in multipliers)) == 1
    scale = math.lcm(*(v.denominator for row in coefficients + multipliers for v in row.values()))
    coeff = [{a: int(t * scale) for a, t in row.items() if t} for row in coefficients]
    lam = [{a: int(t * scale) for a, t in row.items() if t} for row in multipliers]
    D, pay = integer_table(table)
    cache = {}

    def value(i, opponents):
        rest = tuple(sorted(opponents))
        key = (i, rest)
        if key not in cache:
            cache[key] = sum((c * pay[(a,) + rest] for a, c in coeff[i].items()))
        return cache[key]
    worst = None
    for tail in itertools.combinations_with_replacement(survivors, players - F):
        if F == 2:
            lower = min((value(0, (b,) + tail) - lam[1].get(b, 0) * D for b in focal[1]))
            lower += min((value(1, (a,) + tail) - lam[0].get(a, 0) * D for a in focal[0]))
            worst = lower if worst is None else min(worst, lower)
        else:
            for head in itertools.product(*focal):
                profile = head + tail
                lower = sum((value(i, profile[:i] + profile[i + 1:]) - lam[i].get(profile[i], 0) * D for i in range(F)))
                worst = lower if worst is None else min(worst, lower)
    assert worst is not None and worst >= 0
    return Q(worst, D * scale)

def mixed_payoff(table, a, params, A, B):
    total = sp.Integer(0)
    for picks in itertools.product((A, B), repeat=len(params)):
        weight = sp.Integer(1)
        for p, pick in zip(params, picks):
            weight *= p if pick == A else 1 - p
        value = pay(table, a, picks)
        total += weight * sp.Rational(value.numerator, value.denominator)
    return sp.expand(total)

def exact_sign(expr):
    expr = sp.nsimplify(sp.expand(expr))
    if expr == 0:
        return 0
    radicals = sorted({r for r in expr.atoms(sp.Pow) if r.exp == sp.Rational(1, 2)}, key=str)
    if not radicals:
        return int(sp.sign(expr))
    assert len(radicals) == 1
    d = radicals[0].base
    poly = sp.Poly(sp.expand(expr.subs(radicals[0], ROOT_SYMBOL)), ROOT_SYMBOL)
    reduced = sp.Poly(sp.rem(poly.as_expr(), ROOT_SYMBOL ** 2 - d, ROOT_SYMBOL), ROOT_SYMBOL)
    coeffs = dict(zip([m[0] for m in reduced.monoms()], reduced.coeffs()))
    a0 = sp.Rational(coeffs.get(0, 0))
    a1 = sp.Rational(coeffs.get(1, 0))
    if a1 == 0:
        return int(sp.sign(a0))
    if a0 == 0:
        return int(sp.sign(a1))
    if sp.sign(a0) == sp.sign(a1):
        return int(sp.sign(a0))
    if a0 ** 2 == a1 ** 2 * d:
        return 0
    return int(sp.sign(a0)) if a0 ** 2 > a1 ** 2 * d else int(sp.sign(a1))

def classify(M):
    V = vertices(M)
    table = payoff_table(V)
    index = {name: k for k, (name, _) in enumerate(V)}
    A = index[f'D1_{M}']
    B = index[f'D2_{M}']
    r, s, t = sp.symbols('r s t')
    D = sp.factor(mixed_payoff(table, A, (r, s, t), A, B) - mixed_payoff(table, B, (r, s, t), A, B))
    equilibria = []
    for k in range(PLAYERS + 1):
        for l in range(PLAYERS + 1 - k):
            q = PLAYERS - k - l
            ps = sp.symbols(f'p1:{q + 1}') if q else ()
            params = [sp.Integer(1)] * k + [sp.Integer(0)] * l + list(ps)
            equations = []
            for i in range(k + l, PLAYERS):
                others = params[:i] + params[i + 1:]
                equations.append(sp.expand(D.subs(dict(zip((r, s, t), others)), simultaneous=True)))
            if q:
                basis = sp.groebner(equations, *ps, order='lex')
                solutions = sp.solve(list(basis), ps, dict=True)
                if any((len(sol) < q for sol in solutions)):
                    raise RuntimeError(f'positive-dimensional component at k={k}, l={l}')
                interior = []
                for sol in solutions:
                    vals = [sp.nsimplify(sp.radsimp(sol[p])) for p in ps]
                    if all((v.is_real and exact_sign(v) > 0 and (exact_sign(1 - v) > 0) for v in vals)):
                        interior.append(vals)
            else:
                interior = [[]]
            for vals in interior:
                full = [sp.Integer(1)] * k + [sp.Integer(0)] * l + list(vals)
                ok = True
                for i in range(k):
                    others = full[:i] + full[i + 1:]
                    if exact_sign(D.subs(dict(zip((r, s, t), others)), simultaneous=True)) < 0:
                        ok = False
                for i in range(k, k + l):
                    others = full[:i] + full[i + 1:]
                    if exact_sign(D.subs(dict(zip((r, s, t), others)), simultaneous=True)) > 0:
                        ok = False
                if ok:
                    equilibria.append((k, l, full))
    certified = []
    for k, l, full in equilibria:
        roles = []
        for i in range(PLAYERS):
            others = full[:i] + full[i + 1:]
            values = [mixed_payoff(table, a, others, A, B) for a in range(len(V))]
            own = full[i] * values[A] + (1 - full[i]) * values[B]
            slacks = {V[a][0]: exact_sign(own - values[a]) for a in range(len(V))}
            assert all((v >= 0 for v in slacks.values()))
            best = sorted((name for name, v in slacks.items() if v == 0))
            expected = [V[A][0]] if full[i] == 1 else [V[B][0]] if full[i] == 0 else sorted([V[A][0], V[B][0]])
            assert best == expected
            roles.append({'parameter': str(full[i]), 'payoff': str(sp.nsimplify(sp.expand(own)))})
        certified.append({'parameters': [role['parameter'] for role in roles], 'payoffs': [role['payoff'] for role in roles]})
    return certified
V = dict(vertices(8))
V_INDEX = {name: i for i, name in enumerate(V)}

def payoff(own, opponents):
    return pay(TABLES[8], V_INDEX[own], tuple((V_INDEX[name] for name in opponents)))

class Interval:

    def __init__(self, lo, hi=None):
        self.lo = Q(lo)
        self.hi = Q(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = other if isinstance(other, Interval) else Interval(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)
    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other if isinstance(other, Interval) else -Q(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = other if isinstance(other, Interval) else Interval(other)
        ends = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(min(ends), max(ends))
    __rmul__ = __mul__

    def __pow__(self, exponent):
        assert exponent >= 0
        out = Interval(1)
        for _ in range(exponent):
            out = out * self
        return out

    def magnitude(self):
        return max(abs(self.lo), abs(self.hi))

def evaluate(poly, point):
    ans = Interval(0) if any((isinstance(x, Interval) for x in point)) else Q(0)
    for powers, coefficient in poly.terms():
        value = Q(int(coefficient.p), int(coefficient.q))
        for x, power in zip(point, powers):
            if power:
                value = value * x ** power
        ans = ans + value
    return ans

def zexpr(poly, variables):
    terms = []
    for powers, coefficient in poly.terms():
        val = z3.RealVal(str(coefficient))
        for var, power in zip(variables, powers):
            for _ in range(power):
                val = val * var
        terms.append(val)
    return z3.Sum(terms)

class System:

    def __init__(self, pattern):
        self.pattern = pattern
        self.n = sum((len(s) - 1 for s in pattern))
        self.x = sp.symbols(f'x0:{self.n}')
        self.weights = []
        at = 0
        for support in pattern:
            first = list(self.x[at:at + len(support) - 1])
            self.weights.append(first + [1 - sum(first)])
            at += len(support) - 1
        self.f = []
        self.margins = []
        for i, support in enumerate(pattern):
            others = [j for j in range(4) if j != i]
            values = {}
            for own in V:
                expression = 0
                for picks in itertools.product(*(range(len(pattern[j])) for j in others)):
                    probability = sp.prod((self.weights[j][k] for j, k in zip(others, picks)))
                    opponent_names = tuple(sorted((pattern[j][k] for j, k in zip(others, picks))))
                    u = payoff(own, opponent_names)
                    expression += probability * sp.Rational(u.numerator, u.denominator)
                values[own] = sp.Poly(sp.expand(expression), *self.x)
            base = values[support[0]]
            self.f.extend((values[a] - base for a in support[1:]))
            self.margins.extend(((i, a, base - values[a]) for a in V if a not in support))
        assert len(self.f) == self.n
        self.jacobian = [[p.diff(v) for v in self.x] for p in self.f]

    def certify(self, center, C, radius):
        box = [Interval(t - radius, t + radius) for t in center]
        Fx = [evaluate(p, center) for p in self.f]
        JX = [[evaluate(p, box) for p in row] for row in self.jacobian]
        B = [[Interval(int(i == j)) - sum((C[i][k] * JX[k][j] for k in range(self.n))) for j in range(self.n)] for i in range(self.n)]
        K = []
        for i in range(self.n):
            value = Interval(center[i] - sum((C[i][k] * Fx[k] for k in range(self.n))))
            for j in range(self.n):
                value += B[i][j] * Interval(-radius, radius)
            K.append(value)
        inclusion = all((X.lo < Y.lo <= Y.hi < X.hi for X, Y in zip(box, K)))
        contraction = max((sum((t.magnitude() for t in row)) for row in B))
        weights = [[evaluate(sp.Poly(w, *self.x), box) for w in part] for part in self.weights]
        margins = [(i, a, evaluate(p, box)) for i, a, p in self.margins]
        minimum = min((t.lo for _, _, t in margins))
        assert inclusion and contraction < 1
        assert all((w.lo > 0 for part in weights for w in part))
        assert minimum > 0
        return minimum

def check_equal_roles(system, center):
    weights = [[evaluate(sp.Poly(w, *system.x), center) for w in part] for part in system.weights]
    for i in range(4):
        for j in range(i + 1, 4):
            if system.pattern[i] == system.pattern[j]:
                assert weights[i] == weights[j]
    return weights

def check_global(system, center, radius):
    variables = [z3.Real(f'x{i}') for i in range(system.n)]
    solver = z3.SolverFor('QF_NRA')
    solver.set(timeout=20000)
    for part in system.weights:
        for weight in part:
            solver.add(zexpr(sp.Poly(weight, *system.x), variables) > 0)
    for polynomial in system.f:
        solver.add(zexpr(polynomial, variables) == 0)
    for _, _, polynomial in system.margins:
        solver.add(zexpr(polynomial, variables) >= 0)
    solver.add(z3.Or(*[z3.Or(variable < z3.RealVal(str(value - radius)), variable > z3.RealVal(str(value + radius))) for variable, value in zip(variables, center)]))
    verdict = solver.check()
    assert verdict == z3.unsat, str(verdict)

def check_roots():
    records = json.loads((HERE / 'roots.json').read_text(encoding='utf-8'))
    assert len(records) == 9
    assert [canonical(record['pattern']) for record in records] == [canonical(pattern) for pattern in expected_profiles(8)]
    results = []
    for row, record in enumerate(records, 1):
        system = System(record['pattern'])
        center = [Q(value) for value in record['center']]
        matrix = [[Q(value) for value in part] for part in record['preconditioner']]
        assert len(center) == system.n and len(matrix) == system.n
        assert all((len(part) == system.n for part in matrix))
        assert sp.Matrix([[sp.Rational(value.numerator, value.denominator) for value in part] for part in matrix]).det() != 0
        margin = system.certify(center, matrix, Q(1, 10 ** 30))
        assert margin > Q(24, 10000)
        weights = check_equal_roles(system, center)
        parameters = [[f'{float(weight):.6f}' for weight in part[:-1]] for part in weights]
        result = {'row': row, 'supports': record['pattern'], 'parameters': parameters}
        if row in (1, 2, 9):
            radius = Q(2, 10 ** 6)
            system.certify(center, matrix, radius)
            check_global(system, center, radius)
            result['global'] = 'unsat'
        results.append(result)
    assert payoff('D3_8', ('D1_8', 'D1_8', 'D2_8')) - payoff('D1_8', ('D1_8', 'D1_8', 'D2_8')) == Q(13, 2880)
    return results

def main():
    if sys.flags.optimize:
        raise RuntimeError('Run Python without -O or -OO.')
    census = {}
    for M in (6, 7, 8):
        census[str(M)] = check_census(M)
        print(f"M={M}: {census[str(M)]['certificates']} certificates verified", flush=True)
    assert sum((result['certificates'] for result in census.values())) == 35260
    segment = {}
    for M in (6, 7):
        result = classify(M)
        assert len(result) == 4
        segment[str(M)] = result
    print('M=6,7: exact equilibria verified', flush=True)
    roots = check_roots()
    result = {'census': census, 'segment_equilibria': segment, 'M8_equilibria': roots, 'globally_unique_rows': [1, 2, 9], 'unresolved_rows': [3, 4, 5, 6, 7, 8], 'M8_minimum_outside_gap_lower_bound': '0.0024', 'M8_AAAB_deviation_gain': '13/2880'}
    (HERE / 'results.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print('M=8: nine equilibria verified; global uniqueness verified in rows 1,2,9', flush=True)
if __name__ == '__main__':
    main()

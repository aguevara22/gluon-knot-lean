from itertools import combinations

def check():
    cases = 0
    by_size = {}
    unary = full_cuts = first_position = last_possible_attachment = 0
    for n in range(3, 10):
        size_count = 0
        for s in range(n - 1):
            A, B = s, s + 1
            old = lambda k: k if k <= s else k + 1
            tail = lambda k: k if k < s else k + 1
            collapse = lambda p: p if p <= s else p - 1
            for Y in range(B + 1, n + 1):
                interior = list(range(s + 1, Y - 1))
                for count in range(len(interior) + 1):
                    for chosen in combinations(interior, count):
                        core = {s, Y - 1, *chosen}
                        c = sorted(core)
                        core_children = list(zip(c, c[1:]))
                        assert core_children and core_children[0][0] == s
                        image0 = {old(k) for k in core}
                        image1 = {A} | {tail(k) for k in core}
                        nonduplicate = {p for p in range(A, Y + 1)
                                        if collapse(p) in core and collapse(p) != s}
                        row0 = nonduplicate | {A}
                        row1 = nonduplicate | {A, B}
                        assert row0 == image0
                        assert row1 == row0 | {B} == image1
                        assert B not in row0
                        assert min({tail(k) for k in core}) == B
                        c0, c1 = sorted(row0), sorted(row1)
                        child0, child1 = list(zip(c0, c0[1:])), list(zip(c1, c1[1:]))
                        mapped0 = [(old(l), old(r)) for l,r in core_children]
                        mapped1 = [(tail(l), tail(r)) for l,r in core_children]
                        assert child0 == mapped0
                        assert child1 == [(A, B)] + mapped1
                        assert (A, B) not in mapped1
                        assert len(set(mapped1)) == len(core_children)
                        X = core_children[0][1]
                        assert child0[0] == (A, old(X)) and B < old(X)
                        assert child1[1] == (B, old(X))
                        for K, oldK, tailK in zip(core_children[1:], mapped0[1:], mapped1[1:]):
                            assert s < K[0] and oldK == tailK
                        assert {collapse(p) for p in row0} == core
                        assert {collapse(p) for p in row1} == core
                        cases += 1
                        size_count += 1
                        unary += (len(core_children) == 1)
                        full_cuts += (count == len(interior))
                        first_position += (s == 0)
                        last_possible_attachment += (s == n - 2)
        by_size[n] = size_count
    return dict(cases=cases, by_core_size=by_size, unary_cases=unary,
                all_interior_cuts_cases=full_cuts, first_position_cases=first_position,
                last_possible_starting_attachment_cases=last_possible_attachment)

if __name__ == '__main__':
    import json
    print(json.dumps(check(), sort_keys=True))

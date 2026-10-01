"""Literal K3 join I3: a nontrivial edge partition and its candidate pool."""

from itertools import combinations

from certo import CoverSpec


def spec():
    core = (0, 1, 2)
    hosts = (3, 4, 5)
    edges = list(combinations(core, 2)) + [(u, v) for u in core for v in hosts]
    triangles = [(0, 1, 3), (0, 2, 4), (1, 2, 5)]
    used = {tuple(sorted(e)) for t in triangles for e in combinations(t, 2)}
    parts = triangles + [e for e in edges if tuple(sorted(e)) not in used]
    candidates = [e for e in edges]
    for size in (3, 4):
        for piece in combinations(range(6), size):
            if all(tuple(sorted(e)) in {tuple(sorted(x)) for x in edges}
                   for e in combinations(piece, 2)):
                candidates.append(piece)
    return CoverSpec(universe=edges, parts=parts, candidates=candidates,
                     cliques=True, title="Literal K3 join I3 partition")

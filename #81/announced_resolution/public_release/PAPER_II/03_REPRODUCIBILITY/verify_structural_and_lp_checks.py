#!/usr/bin/env python3
"""Unified audit for Paper II v0.5."""

from itertools import combinations
from math import comb, floor

import networkx as nx
import numpy as np
from scipy.optimize import linprog

TOL = 1e-8


def is_clique(graph, vertices):
    return all(graph.has_edge(u, v) for u, v in combinations(vertices, 2))


def complete_split(p, q):
    graph = nx.complete_graph(p)
    graph.add_nodes_from(range(p, p + q))
    graph.add_edges_from(
        (u, v)
        for u in range(p)
        for v in range(p, p + q)
    )
    return graph


def is_complete_split(graph):
    universal = {
        v for v in graph
        if graph.degree(v) == graph.number_of_nodes() - 1
    }
    remainder = set(graph) - universal
    return is_clique(graph, universal) and all(
        not graph.has_edge(u, v)
        for u, v in combinations(remainder, 2)
    )


def clone_classes(graph):
    groups = {}
    for vertex in graph:
        groups.setdefault(frozenset(graph.neighbors(vertex)), set()).add(vertex)
    return [frozenset(group) for group in groups.values()]


def simplicial(graph, vertex):
    return is_clique(graph, graph.neighbors(vertex))


def symmetrize(graph, target, source):
    result = graph.copy()
    source_vertex = next(iter(source))
    neighborhood = set(graph.neighbors(source_vertex))

    for vertex in target:
        result.remove_edges_from(
            [(vertex, neighbor) for neighbor in list(result.neighbors(vertex))]
        )
    for vertex in target:
        result.add_edges_from(
            (vertex, neighbor)
            for neighbor in neighborhood
            if neighbor not in target
        )
    return result


def nu_star(graph, r):
    edges = [tuple(sorted(edge)) for edge in graph.edges()]
    cliques = [
        subset
        for subset in combinations(graph.nodes(), r)
        if is_clique(graph, subset)
    ]
    if not cliques:
        return 0.0

    edge_index = {edge: i for i, edge in enumerate(edges)}
    matrix = np.zeros((len(edges), len(cliques)))
    for j, clique in enumerate(cliques):
        for edge in combinations(clique, 2):
            matrix[edge_index[tuple(sorted(edge))], j] = 1.0

    result = linprog(
        -np.ones(len(cliques)),
        A_ub=matrix,
        b_ub=np.ones(len(edges)),
        bounds=(0, None),
        method="highs",
    )
    assert result.success
    return float(-result.fun)


def phi(graph, r):
    return graph.number_of_edges() - (comb(r, 2) - 1) * nu_star(graph, r)


def formula_nu(p, q, r):
    if p < r - 1:
        return 0.0
    if p == r - 1:
        return 1.0 if q >= 1 else 0.0

    P = comb(p, 2)
    m = comb(r, 2)
    c = comb(r - 1, 2)
    return P / m + (P / c - P / m) * min(
        1.0, (r - 2) * q / (p - 1)
    )


def formula_phi(p, q, r):
    return (
        comb(p, 2) + p * q
        - (comb(r, 2) - 1) * formula_nu(p, q, r)
    )


def construct_to_complete_split(graph, r):
    current = graph.copy()
    initial = phi(current, r)
    steps = 0

    while not is_complete_split(current):
        classes = clone_classes(current)
        pair = None
        for first, second in combinations(classes, 2):
            u = next(iter(first))
            v = next(iter(second))
            if (
                not current.has_edge(u, v)
                and simplicial(current, u)
                and simplicial(current, v)
                and set(current.neighbors(u)) != set(current.neighbors(v))
            ):
                pair = first, second
                break

        assert pair is not None
        first, second = pair

        forward = symmetrize(current, first, second)
        reverse = symmetrize(current, second, first)

        assert nx.is_chordal(forward)
        assert nx.is_chordal(reverse)
        assert len(clone_classes(forward)) < len(classes)
        assert len(clone_classes(reverse)) < len(classes)

        current = max((forward, reverse), key=lambda h: phi(h, r))
        steps += 1
        assert steps <= graph.number_of_nodes() - 1

    assert phi(current, r) >= initial - TOL
    return current, steps


def main():
    atlas = [
        graph
        for graph in nx.graph_atlas_g()
        if 1 <= graph.number_of_nodes() <= 7 and nx.is_chordal(graph)
    ]
    assert len(atlas) == 531

    # Complete-split reduction and equality of maxima.
    for r in (3, 4):
        chordal_max = {}
        complete_split_max = {}
        max_steps = 0

        for graph in atlas:
            n = graph.number_of_nodes()
            value = phi(graph, r)
            chordal_max[n] = max(chordal_max.get(n, float("-inf")), value)

            final_graph, steps = construct_to_complete_split(graph, r)
            assert is_complete_split(final_graph)
            max_steps = max(max_steps, steps)

        for n in chordal_max:
            complete_split_max[n] = max(
                formula_phi(p, n - p, r)
                for p in range(n + 1)
            )
            assert abs(chordal_max[n] - complete_split_max[n]) <= TOL

        print(
            f"PASS r={r}: 531 chordal graphs reduce to complete split; "
            f"maximum {max_steps} steps"
        )
        print(
            f"PASS r={r}: chordal and complete-split maxima agree through n=7"
        )

    # Orbit formula against the full LP.
    instances = 0
    for r in range(3, 7):
        for p in range(0, 9):
            for q in range(0, 9):
                graph = complete_split(p, q)
                assert abs(nu_star(graph, r) - formula_nu(p, q, r)) <= TOL
                instances += 1

    print(f"PASS: complete-split packing formula on {instances} LP instances")

    # Exact triangle formula.
    for n in range(1, 501):
        maximum = max(
            formula_phi(p, n - p, 3)
            for p in range(n + 1)
        )
        expected = floor((2 * n + 1) ** 2 / 24)
        assert abs(maximum - expected) <= TOL

    print("PASS: exact triangle maximum through n=500")

    # Fixed-r leading coefficient.
    for r in range(3, 9):
        for n in (200, 500, 1000):
            maximum = max(
                formula_phi(p, n - p, r)
                for p in range(n + 1)
            )
            leading = (r - 1) * n * n / (4 * r)
            assert abs(maximum - leading) <= 3 * n

    print("PASS: fixed-r coefficient for r=3,...,8")


if __name__ == "__main__":
    main()

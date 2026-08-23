from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path

import networkx as nx
import numpy as np
from scipy.optimize import linprog


TOL = 1e-8


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tau_star(graph: nx.Graph) -> float:
    edges = [tuple(sorted(edge)) for edge in graph.edges()]
    triangles = [tuple(sorted(nodes)) for nodes in nx.enumerate_all_cliques(graph) if len(nodes) == 3]
    if not triangles:
        return 0.0
    edge_index = {edge: index for index, edge in enumerate(edges)}
    matrix = np.zeros((len(triangles), len(edges)))
    for row, (a, b, c) in enumerate(triangles):
        for edge in ((a, b), (a, c), (b, c)):
            matrix[row, edge_index[tuple(sorted(edge))]] = -1.0
    result = linprog(
        np.ones(len(edges)),
        A_ub=matrix,
        b_ub=-np.ones(len(triangles)),
        bounds=[(0, None)] * len(edges),
        method="highs",
    )
    if not result.success:
        raise AssertionError(result.message)
    return float(result.fun)


def phi(graph: nx.Graph, cache: dict[tuple[int, tuple[tuple[int, int], ...]], float]) -> float:
    key = (graph.number_of_nodes(), tuple(sorted(tuple(sorted(edge)) for edge in graph.edges())))
    if key not in cache:
        cache[key] = graph.number_of_edges() - 2 * tau_star(graph)
    return cache[key]


def copy_vertex(graph: nx.Graph, source: int, target: int) -> nx.Graph:
    copied = graph.copy()
    copied.remove_edges_from(list(copied.edges(source)))
    copied.add_edges_from((source, neighbor) for neighbor in graph.neighbors(target))
    return copied


def complete_split(p: int, q: int) -> nx.Graph:
    graph = nx.Graph()
    graph.add_nodes_from(range(p + q))
    graph.add_edges_from(itertools.combinations(range(p), 2))
    graph.add_edges_from((x, y) for x in range(p) for y in range(p, p + q))
    return graph


def closed_tau(p: int, q: int) -> Fraction:
    P = p * (p - 1) // 2
    if p <= 1 or (p == 2 and q == 0):
        return Fraction(0)
    if p >= 3 and q <= p - 1:
        return Fraction(P + p * q, 3)
    return Fraction(P)


def closed_phi(p: int, q: int) -> Fraction:
    return Fraction(p * (p - 1), 2) + p * q - 2 * closed_tau(p, q)


def simplicial(graph: nx.Graph, vertex: int) -> bool:
    neighborhood = list(graph.neighbors(vertex))
    return all(graph.has_edge(x, y) for x, y in itertools.combinations(neighborhood, 2))


def terminal_property(graph: nx.Graph) -> bool:
    vertices = [vertex for vertex in graph if simplicial(graph, vertex)]
    for u, v in itertools.combinations(vertices, 2):
        if not graph.has_edge(u, v) and set(graph.neighbors(u)) != set(graph.neighbors(v)):
            return False
    return True


def is_complete_split(graph: nx.Graph) -> bool:
    universal = {vertex for vertex in graph if graph.degree(vertex) == graph.number_of_nodes() - 1}
    remainder = set(graph) - universal
    return all(not graph.has_edge(x, y) for x, y in itertools.combinations(remainder, 2))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manuscript", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    args = parser.parse_args()
    cache: dict[tuple[int, tuple[tuple[int, int], ...]], float] = {}

    complete_split_count = 0
    for p in range(0, 13):
        for q in range(0, 15):
            graph = complete_split(p, q)
            actual = tau_star(graph)
            expected = float(closed_tau(p, q))
            if abs(actual - expected) > TOL:
                raise AssertionError((p, q, actual, expected))
            complete_split_count += 1

    integer_count = 0
    level_count = 0
    for n in range(1, 5001):
        values = [closed_phi(p, n - p) for p in range(n + 1)]
        maximum = max(values)
        expected = (2 * n + 1) ** 2 // 24
        if maximum != expected:
            raise AssertionError((n, maximum, expected))
        maximizers = [p for p, value in enumerate(values) if value == maximum]
        center = Fraction(2 * n + 1, 6)
        saturated = [p for p in range(n + 1) if n - p >= p - 1]
        nearest_distance = min(abs(Fraction(p) - center) for p in saturated)
        nearest = [p for p in saturated if abs(Fraction(p) - center) == nearest_distance]
        saturated_maximizers = [p for p in saturated if values[p] == maximum]
        if saturated_maximizers != nearest or not set(nearest) <= set(maximizers):
            raise AssertionError((n, maximizers, saturated_maximizers, nearest))
        residue_expected = ((2 * n + 1) ** 2 - (9 if n % 3 == 1 else 1)) // 24
        if expected != residue_expected:
            raise AssertionError((n, expected, residue_expected))
        integer_count += 1
        for p in saturated_maximizers:
            delta = Fraction((2 * n + 1) ** 2, 24) - closed_phi(p, n - p)
            lhs = abs(Fraction(p) - center)
            if lhs * lhs != Fraction(2, 3) * delta:
                raise AssertionError((n, p, lhs, delta))
            level_count += 1

    copy_pairs = 0
    terminal_graphs = 0
    chordal_graphs = 0
    for graph in nx.graph_atlas_g():
        if graph.number_of_nodes() > 6 or not nx.is_chordal(graph):
            continue
        graph = nx.convert_node_labels_to_integers(graph)
        chordal_graphs += 1
        original = phi(graph, cache)
        for u, v in itertools.combinations(graph.nodes(), 2):
            if graph.has_edge(u, v):
                continue
            left = phi(copy_vertex(graph, v, u), cache)
            right = phi(copy_vertex(graph, u, v), cache)
            if left + right + TOL < 2 * original:
                raise AssertionError((graph.number_of_nodes(), graph.edges(), u, v, left, right, original))
            copy_pairs += 1
        if terminal_property(graph):
            terminal_graphs += 1
            if not is_complete_split(graph):
                raise AssertionError(("terminal", graph.number_of_nodes(), graph.edges()))

    summary = {
        "paper": "PAPER_II",
        "claim_gate": "G2_MATHEMATICS",
        "target_sha256": sha256(args.manuscript),
        "status": "PASS",
        "complete_split_lp_instances": complete_split_count,
        "exact_integer_maximization_instances": integer_count,
        "argmax_level_checks": level_count,
        "chordal_atlas_graphs_n_le_6": chordal_graphs,
        "vertex_copy_nonedge_pairs": copy_pairs,
        "terminal_property_graphs": terminal_graphs,
        "scope": "Exact arithmetic through n=5000; exhaustive non-isomorphic graph atlas checks through n=6; bounded computation is corroborating evidence.",
    }
    rendered = json.dumps(summary, indent=2) + "\n"
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(rendered, encoding="utf-8")
    args.log.write_text(rendered + "EXIT_CODE=0\n", encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

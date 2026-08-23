#!/usr/bin/env python3
"""Paper III v1.3, gate E4 -- transitive import closure of the canonical roots.

The author's ESCAPE_HATCH_ASSESSMENT.md asserts:

    "No source file imports either legacy module, and neither declaration appears in any
     recorded theorem footprint. They are therefore outside the canonical release proof
     closure."

A single grep cannot decide that: `PaperIII/Theorem_1_1_Final.lean` does import an `Ax2`
module. The question is whether the two axiom-bearing modules

    Ax2/PartB/Axioms.lean      (axiom bklo_kthree_transfer)
    Ax2/PartA/Wlog.lean        (axiom dross_fractional_flow_noHDT)

are reachable through the TRANSITIVE import graph from any canonical root. That is decided
here by building the graph from the frozen sources and walking it.
"""
import json
import os
import re
from collections import deque

ROOT = "C:/p3a"
OUT = "C:/erdos_audit/v14/E4"

CANONICAL_ROOTS = [
    "PaperIII.Theorem_1_1_Final",
    "PaperIII.PublicAPI",
    "PaperIII.CanonicalTrianglePacking",
    "PaperIII.Obstructions",
    "PaperIII.PaperImprovementsGate",
    "Nibble.AX1Closed",
    "BKLO.MainDenseUnconditional",
    "PaperIII",                      # the aggregate library root
]

AXIOM_MODULES = {"Ax2.PartB.Axioms": "bklo_kthree_transfer",
                 "Ax2.PartA.Wlog": "dross_fractional_flow_noHDT"}


def mod_to_path(m):
    return os.path.join(ROOT, *m.split(".")) + ".lean"


def strip_comments(t):
    """Blank out nested /- -/ blocks and -- line comments. An `import` inside a docstring
    is prose, not an import: PublicAPI.lean contains the phrase "import tree stays lean"."""
    out = list(t)
    i = depth = 0
    while i < len(t):
        if t.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if t.startswith("-/", i) and depth:
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth:
            if t[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if t.startswith("--", i):
            j = t.find("\n", i)
            j = len(t) if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        i += 1
    return "".join(out)


def imports_of(m):
    p = mod_to_path(m)
    if not os.path.isfile(p):
        return None
    t = strip_comments(open(p, encoding="utf-8", errors="replace").read())
    return re.findall(r"^\s*import\s+([A-Za-z0-9_.]+)", t, re.M)


def closure(root):
    """Transitive closure over PROJECT modules; Mathlib and friends are not expanded."""
    seen, missing, order = set(), set(), []
    q = deque([root])
    parents = {}
    while q:
        m = q.popleft()
        if m in seen:
            continue
        seen.add(m)
        order.append(m)
        imps = imports_of(m)
        if imps is None:
            missing.add(m)
            continue
        for i in imps:
            if i.split(".")[0] in ("Mathlib", "Lean", "Std", "Batteries", "Aesop",
                                   "Qq", "ImportGraph", "LeanSearchClient",
                                   "Plausible", "ProofWidgets", "Cli"):
                continue
            if i not in parents:
                parents[i] = m
            q.append(i)
    return seen, missing, parents


def path_to(parents, root, target):
    """Reconstruct the import chain root -> ... -> target, if any."""
    if target not in parents:
        return None
    chain = [target]
    while chain[-1] != root and chain[-1] in parents:
        chain.append(parents[chain[-1]])
    chain.reverse()
    return chain


def main():
    os.makedirs(OUT, exist_ok=True)
    res = {"gate": "E4", "check": "transitive import closure of the canonical roots",
           "author_claim": ("No source file imports either legacy module, and neither "
                            "declaration appears in any recorded theorem footprint."),
           "axiom_modules": AXIOM_MODULES, "roots": {}}

    # which Ax2 modules does each root import directly
    res["direct_Ax2_imports"] = {}
    for r in CANONICAL_ROOTS:
        imps = imports_of(r) or []
        res["direct_Ax2_imports"][r] = [i for i in imps if i.startswith("Ax2")]

    for r in CANONICAL_ROOTS:
        seen, missing, parents = closure(r)
        hits = {}
        for am in AXIOM_MODULES:
            if am in seen:
                hits[am] = path_to(parents, r, am)
        res["roots"][r] = {
            "project_modules_in_closure": len(seen),
            "unresolved_modules": sorted(missing),
            "Ax2_modules_in_closure": sorted(m for m in seen if m.startswith("Ax2")),
            "axiom_modules_reachable": hits,
            "clean": not hits}

    # who, anywhere in the frozen tree, imports the two axiom modules
    importers = {am: [] for am in AXIOM_MODULES}
    all_mods = []
    for dp, dn, fn in os.walk(ROOT):
        if ".lake" in dp.replace("\\", "/"):
            continue
        for f in fn:
            if not f.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(dp, f), ROOT).replace("\\", "/")
            m = rel[:-5].replace("/", ".")
            all_mods.append(m)
            tt = strip_comments(open(os.path.join(dp, f), encoding="utf-8",
                                     errors="replace").read())
            for im in re.findall(r"^\s*import\s+([A-Za-z0-9_.]+)", tt, re.M):
                if im in importers:
                    importers[im].append(m)
    res["direct_importers_of_axiom_modules"] = importers
    res["total_project_modules"] = len(all_mods)

    json.dump(res, open(f"{OUT}/import_closure.json", "w"), indent=1)

    print(f"modulos de proyecto en el arbol congelado: {len(all_mods)}\n")
    print("=== imports DIRECTOS de Ax2 por cada raiz canonica")
    for r, v in res["direct_Ax2_imports"].items():
        print(f"  {r:38} {v if v else '(ninguno)'}")
    print("\n=== clausura transitiva de imports por raiz")
    for r, v in res["roots"].items():
        flag = "LIMPIA" if v["clean"] else "ALCANZA UN MODULO CON AXIOMA"
        print(f"  {r:38} {v['project_modules_in_closure']:4} modulos  {flag}")
        if v["Ax2_modules_in_closure"]:
            print(f"        modulos Ax2 alcanzados: {v['Ax2_modules_in_closure']}")
        for am, chain in v["axiom_modules_reachable"].items():
            print(f"        !! {am} via {' -> '.join(chain)}")
        if v["unresolved_modules"]:
            print(f"        modulos no resueltos: {v['unresolved_modules'][:4]}")
    print("\n=== quien importa directamente los modulos con axioma")
    for am, who in importers.items():
        print(f"  {am:22} <- {who if who else '(NADIE)'}")


if __name__ == "__main__":
    main()

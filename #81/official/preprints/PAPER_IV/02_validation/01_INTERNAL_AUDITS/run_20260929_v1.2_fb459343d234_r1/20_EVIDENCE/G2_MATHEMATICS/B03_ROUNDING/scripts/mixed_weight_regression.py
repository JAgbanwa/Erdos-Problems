"""Small literal regression against replacing mixed gain by copy count."""

from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path


HERE = Path(__file__).resolve().parents[1]


def edges(piece):
    return set(combinations(piece, 2))


def packing(parts):
    used = set()
    for part in parts:
        es = edges(part)
        if used & es:
            return False
        used |= es
    return True


def gain(parts):
    return sum(2 if len(part) == 3 else 5 if len(part) == 4 else 0 for part in parts)


def main():
    # Same graph K5, two physically valid choices with reversed rankings.
    more_copies = ((0, 1, 2), (0, 3, 4))
    more_gain = ((0, 1, 2, 3),)
    if not packing(more_copies) or not packing(more_gain):
        raise AssertionError("overlapping copies")
    if not (len(more_copies) > len(more_gain) and gain(more_copies) < gain(more_gain)):
        raise AssertionError("count-versus-gain example changed")
    if packing(((0, 1, 2), (0, 1, 3))):
        raise AssertionError("negative control: shared edge accepted")
    result = {"graph": "K5", "two_triangles": {"count": 2, "gain": 4},
              "one_K4": {"count": 1, "gain": 5},
              "negative": "two triangles sharing an edge rejected",
              "limit": "This demonstrates why cardinality alone is insufficient; it does not prove the nibble."}
    path = HERE / "results" / "mixed_weight_regression.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

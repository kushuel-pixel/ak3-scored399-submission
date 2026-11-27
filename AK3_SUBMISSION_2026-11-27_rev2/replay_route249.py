#!/usr/bin/env python3
"""Read the included exact Lean fixtures and replay the two fixed route segments."""
import json
from pathlib import Path
from replay_bridge44 import INVERSE, trace, reduce_word

def reverse_ids(ids):
    return [INVERSE[i] for i in reversed(ids)]

def main():
    path = Path(__file__).resolve().parent / "evidence/route_and_C/route249.json"
    data = json.loads(path.read_text())
    states = {k: tuple(v) for k, v in data["states"].items()}
    q, e, ab = (states[k] for k in ("Q", "E3", "AB"))
    q_e, q_ab, ab_q = (data[k] for k in ("Q_to_E3", "Q_to_AB", "AB_to_Q"))
    checks = [(len(q_e) == 187, "187"), (len(q_ab) == len(ab_q) == 62, "62"),
              (ab_q == reverse_ids(q_ab), "inverse of 62")]
    onward = trace(e, reverse_ids(q_e) + q_ab)
    reverse = trace(ab, ab_q + q_e)
    lengths = [len(r) + len(s) for r, s in onward]
    checks += [(onward[187] == q, "Q"), (onward[-1] == ab, "AB"),
               (reverse == onward[::-1], "exact reverse replay"),
               (len(onward) == 250, "states"), (max(lengths) == 682, "peak"),
               (tuple(map(len,ab)) == (283,399), "literal endpoint lengths"),
               (all(reduce_word(w) == w for v in states.values() for w in v), "reduced")]
    for passed, name in checks:
        if not passed:
            raise SystemExit(f"FAIL: {name}")
    print("PASS: E3 <-> Q <-> (a,b), 187 + 62 = 249 moves, exact reverse replay.")
    print("PASS: endpoint lengths 283 + 399; observed peak 682 (Python).")

if __name__ == "__main__":
    main()

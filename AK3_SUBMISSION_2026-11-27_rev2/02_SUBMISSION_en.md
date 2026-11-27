# The minimum peak from the official AK(3) start to S, and nonconjugacy in a common quotient

Author: Hiromu Yasuno  
Partial result

Work with ordered pairs of words in the free group F(x,y), with uppercase letters denoting inverses. Each of the 14 allowed moves costs one, and both words are freely reduced after each move. The peak of a path is the maximum sum of the two reduced word lengths across all states, including both endpoints. [The `ac-r2-v1` move specification](https://github.com/SAIRcompetition/Andrews-Curtis/blob/a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e/competition/tools/verifier/README.md#ac-moves)

## 1. The minimum peak from the official start to S is 22

The previous report studied paths from the conventionally written start A = `(xyxYXY, xxxYYYY)` to the fixed pair S. The following 44-move sequence runs from the ordered start `(YXYxyx, YYYYxxx)` as written in the official scoring row `ac-00399` to S = `(XyyyxYYYY, xxYYYYYXyyyyy)`. [Previous report ACC-P000029](https://github.com/kushuel-pixel/ak3-connection-013/blob/906baa95d8a76691b0f2b828e49aedd6b5fbb621/README.md) · [Official scoring row](https://github.com/SAIRcompetition/Andrews-Curtis/blob/a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e/competition/problems/ac.jsonl#L399)

```text
7 10 5 6 5 6 8 12 0 2 6 1 4 1 9 7 5 12 12 11 5 12
4 10 12 11 5 12 11 5 12 4 10 12 12 12 6 4 13 13 8 8 8 7
```

The Lean kernel checks that the ordered endpoint after 44 moves is S and that the total freely reduced length is at most 22 in all 45 states. Every path to S contains its endpoint, whose total freely reduced length is 9 + 13 = 22. The minimum peak is therefore exactly 22. [Lean declarations and replay records (R1)](03_CLAIMS_AND_REPLAY_ja.md#r1-en)

Moving from the official start to A in six moves and appending the earlier 42-move witness also gives a path with peak 22. The resulting path takes 48 moves. After move 12, the 44-move witness is in the same state as the earlier 42-move witness after move 10. Their remaining 32 moves coincide. Lean checks both the common state and the common suffix. The comparison is between two witnesses at the same peak, with no claim that 44 moves is optimal. [Earlier 42-move witness](https://github.com/kushuel-pixel/ak3-connection-013/blob/906baa95d8a76691b0f2b828e49aedd6b5fbb621/submission018/evidence/012/stages/006/bridge42.json) · [Checks for the comparison (R1)](03_CLAIMS_AND_REPLAY_ja.md#r1-en)

## 2. Reducing unrestricted reachability to the fixed endpoint (a,b)

Write f = `XyyyxYYYY`, r = `xxYYYYYXyyyyy`, and e = `xxYXy`. Set S = (f,r), Q = (f,e), and E₃ = (f,`xxYYYYXyyyy`). The fixed ordered pair (a,b) has freely reduced word lengths 283 and 399, respectively. [Full words a and b (`states.AB`)](evidence/route_and_C/route249.json)

Lean verifies the 187-move connection E₃ ↔ Q and the 62-move connection Q ↔ (a,b) in both directions. Together these give a path of 249 moves each way between E₃ and (a,b). [Lean declarations for both directions (R2)](03_CLAIMS_AND_REPLAY_ja.md#r2-en)

**Corollary. With no length cap, S can reach E₃ if and only if S can reach (a,b).** Given a path from S to E₃, append E₃ → Q → (a,b). Conversely, given a path from S to (a,b), append (a,b) → Q → E₃. Whether a path from S to either endpoint exists remains unresolved. [Move sequences for both implications (R3)](03_CLAIMS_AND_REPLAY_ja.md#r3-en)

Python replay confirms a peak of 682 for the 249-move sequence. A length cap below 682 prevents using this particular sequence for concatenation. The stated reachability equivalence is for paths with no length cap. [Python replay record (R5)](03_CLAIMS_AND_REPLAY_ja.md#r5-en)

## 3. The obstruction idea and nonconjugacy in the original common quotient C

Let **C = F(x,y) / ⟨⟨r,b⟩⟩** be the original common quotient by the normal closure of r and b, the second words of S and (a,b). Write ā for the image of a and f̄ for the image of f. Lean proves **c ā c⁻¹ ≠ f̄ for every c ∈ C**. A curvature argument proves the intermediate statement `yQ ≠ 1`, so the final theorem has no such hypothesis. Its transitive axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`. [Quotient definition, final theorem, and axiom audit (R4)](03_CLAIMS_AND_REPLAY_ja.md#r4-en)

In the free group, a and f have cyclically reduced lengths 281 and 9, respectively. Conjugate words have the same cyclically reduced length, so these words already lie in distinct conjugacy classes. Passing to a quotient can merge such classes. The theorem shows that ā and f̄ remain in distinct classes after both second words r and b become trivial. [Words used for cyclic reduction (first entries of `states.AB` and `states.S`)](evidence/route_and_C/route249.json)

The obstruction identifies a change that any path from S to (a,b) must make. A move on the second word alone leaves the first word unchanged. Conjugating the first word preserves its conjugacy class in C. Right multiplication of the first word by the current second word or its inverse also preserves its image whenever the current second word maps to the identity in C. A path consisting entirely of these moves cannot connect S to (a,b). The condition on the second word applies at each such multiplication. Its image may be nontrivial at intermediate states.

Q and S share the first word f. The declaration `literal_route_and_obstruction` gives both the 62-move connection Q ↔ (a,b) and nonconjugacy of the images of its first words. The full move set also permits inversion of the first word and right multiplication by a second word with nontrivial image in C, so the 62-move connection is consistent with nonconjugacy. **Reachability from S to E₃ with all allowed moves remains unresolved.** [Lean declaration combining the 62-move replay and nonconjugacy](evidence/route_and_C/EndpointReplay.lean) · [Appendix on the restricted diagram exclusion for 68 allocations](04_DIAGRAM_APPENDIX_ja.md#english)

AI assistance was used in search, implementation, proof and verification work, and drafting. This English text is an AI-assisted translation of the Japanese original.

Checks to date include Lean verification of the formal proofs, AI-assisted replay of the move sequences, and human review of theorem statements, replay results, and axiom reports, with independent expert assessment of the mathematics still unconfirmed.

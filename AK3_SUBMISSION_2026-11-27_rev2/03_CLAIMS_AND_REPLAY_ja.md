# 主張・Lean 定理・再生記録

[日本語原本](01_SUBMISSION_ja.md) · [英訳](02_SUBMISSION_en.md) · [English evidence index](#english)

## R1

**本文第1節。公式始点 `ac-00399` → S の44手と最小ピーク22。** 名前空間 `Verify.Submission.Scored399Peak22` の `bridge44_length`、`bridge44_reaches`、`bridge44_cap22` が手数・順序付き終点・全45状態の上界を確認する。`literalS_length` と `reachesAtCap_iff` が、長さ上限 h の下で到達できることと 22 ≤ h が同値であることを示す。 [Lean ソース](evidence/bridge44/Scored399Bridge44.lean) · [Lean 公理監査](evidence/bridge44/LeanBridge44.log) · [検証環境の記録](evidence/bridge44/BRIDGE44_CHECKPOINT_ja.md)

A への6手は `6 8 6 10 10 10`。これを既報の42手列に前置した48手列もピーク22。Lean の `joins_bridge42_after_10` と `same_last32` は、新しい44手列の12手後と既報の42手列の10手後の状態が等しく、末尾32手が一致することを示す。手数は実例の比較であり、44手の最短性は主張しない。 [既報の42手列](https://github.com/kushuel-pixel/ak3-connection-013/blob/906baa95d8a76691b0f2b828e49aedd6b5fbb621/submission018/evidence/012/stages/006/bridge42.json) · [44手の Python ログ](replay_bridge44.log) · [全45状態](bridge44_trace.tsv)

## R2

**本文第2節。E₃ ↔ Q ↔ (a,b) の固定経路は各方向187＋62手。**

| 区間 | Lean 定理と向き | 証拠 |
|---|---|---|
| E₃ ↔ Q | `AK3.Class31Route.route_length` が187手。 `forward` が Q → E₃、`backward` が E₃ → Q。 | [経路と公理検査を含むソース](evidence/route_and_C/AK3Class31Route.lean) |
| Q ↔ (a,b) | `AK3.SSeven.literal_route_and_obstruction` の最初の4項が両方向の62手と順序付き終点。 `backwardMoves` が Q → (a,b)、`forwardMoves` が (a,b) → Q。 | [Lean ソース](evidence/route_and_C/EndpointReplay.lean) · [公理監査](evidence/route_and_C/EndpointReplay.stdout) |

`AK3.SSeven.exact_seed` は経路で使う Q と62手定理の `targetPair` の一致を示す。Q = (f,e) と S = (f,r) は第一語 f を共有し、第二語 e = `xxYXy` と r = `xxYYYYYXyyyyy` が異なる。249手列の端点は E₃ と (a,b)。 [Q・S・a・b の Lean 定義](evidence/route_and_C/AK3SSevenWords.lean) · [再生データ](evidence/route_and_C/route249.json)

## R3

**本文第2節の系。長さ上限なしで S → E₃ ⇔ S → (a,b)。** 同梱の R2 で、既存の経路の末尾につなぐ手列を向きごとに照合できる。

| 与えられた経路 | 末尾に加える手列 | 得られる到達先 |
|---|---|---|
| S → E₃ | E₃ → Q（`undo route`, 187手）、Q → (a,b)（`backwardMoves`, 62手） | (a,b) |
| S → (a,b) | (a,b) → Q（`forwardMoves`, 62手）、Q → E₃（`route`, 187手） | E₃ |

二つの区間の接点が同じ Q であることは `exact_seed` による。 [187手の定理](evidence/route_and_C/AK3Class31Route.lean) · [62手の定理](evidence/route_and_C/EndpointReplay.lean) · [接点 Q の一致](evidence/route_and_C/AK3SSevenWords.lean)

補足の検証履歴として、進捗表に `from_s_iff` の記載がある。この定理のソース・実行ログは収録外であり、本文の系の根拠は上表の両方向の連結で完結する。 [進捗表の抜粋](evidence/route_and_C/SUB_STATUS_EXCERPT.md)

## R4

**本文第3節。元の共通商 C で ā と f̄ が非共役。** `AK3.SSeven.RBNorm` は元の自由群での `rWord` と `bWord` の正規閉包。`Common` はその商で、`commonMap` は商写像である。 [商と商写像の定義](evidence/route_and_C/AK3SSevenCommonKernel.lean)

最終宣言は `AK3.SSeven.FreeCap.RawChart.common_nonconjugate_by_curvature`。任意の `c : Common` について `c * commonMap (FreeGroup.mk aWord) * c⁻¹ ≠ commonMap (FreeGroup.mk fWord)` を述べる。`yQ = 1` から印付きの相対図式を取り、選んだ成分の面・頂点・辺の座標を圧縮後のオイラー式に合わせて曲率矛盾を得る。圧縮で省いた2価頂点では係数が相殺する。最終定理は `yQ_ne_one_by_curvature` を `common_nonconjugate_of_yQ` に適用する。推移的な公理依存は `propext`、`Classical.choice`、`Quot.sound`。 [最終 Lean ソース](evidence/route_and_C/TerminalAssembly.lean) · [定理型・公理監査](evidence/route_and_C/FinalKernelAudit.stdout) · [検証記録](evidence/route_and_C/RESULT.txt)

第二語だけを変える手、第一語の共役、その時点の第二語の像が C で単位元のときに限った第一語の右乗算（第二語またはその逆元による）は、いずれも第一語の像の共役類を保つ。これらだけからなる S → (a,b) の経路は排除される。62手の両端は Q と (a,b) で、C の定義で殺す第二語は S の r と (a,b) の b。第一語の反転・右乗算も許される経路では、この共役類は一般には保存されない。上限なしの S → E₃ の到達可否は未決。 [62手と非共役を同時に述べる定理](evidence/route_and_C/EndpointReplay.lean) · [68配分の限定排除](04_DIAGRAM_APPENDIX_ja.md)

## R5

**本文第2節。249手列の実測ピークは682。** Python が片道249手の全250状態と逆順の一致、E₃・Q・(a,b) の順序付き語対、(a,b) の長さ 283 + 399、ピーク682を検査する。682は Python の再生結果で、R2 の Lean 定理が扱うのは手数と終点である。 [Python ログ](replay_route249.log) · [再生スクリプト](replay_route249.py) · [再生データ](evidence/route_and_C/route249.json)

## Replay

展開先で実行する。Python 3 の標準ライブラリで再生できる。最初のコマンドは収録ファイルのハッシュを照合する。最後のコマンドは44手の全状態を同梱の表と比較する。

```sh
sha256sum -c SHA256SUMS
python3 -B replay_bridge44.py
python3 -B replay_route249.py
python3 -B replay_bridge44.py --tsv | diff - bridge44_trace.tsv
```

Lean については関連ソース・既存の実行票・公理監査を収録した。完全な依存関係とビルド環境は別に必要。R3 の導出、R4 の定理型と公理監査はいずれも同梱資料で確認できる。

## English

[English paper](02_SUBMISSION_en.md) · [Replay commands](#replay) · [Diagram appendix](04_DIAGRAM_APPENDIX_ja.md#english)

### R1 EN

**Section 1. A 44-move path from the official start `ac-00399` to S attains the minimum peak of 22.** In `Verify.Submission.Scored399Peak22`, `bridge44_length`, `bridge44_reaches`, and `bridge44_cap22` check the move count, ordered endpoint, and bound for all 45 states. `literalS_length` and `reachesAtCap_iff` certify that S can be reached under cap h exactly when 22 ≤ h. `joins_bridge42_after_10` and `same_last32` check the common state after 12 and 10 moves, respectively, and the shared final 32 moves. The six moves `6 8 6 10 10 10` followed by the earlier 42 moves give the 48-move comparison at the same peak. Optimality in move count is not claimed. [Lean source](evidence/bridge44/Scored399Bridge44.lean) · [Axiom audit](evidence/bridge44/LeanBridge44.log) · [Official starting row](https://github.com/SAIRcompetition/Andrews-Curtis/blob/a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e/competition/problems/ac.jsonl#L399) · [Official move IDs and inverses](https://github.com/SAIRcompetition/Andrews-Curtis/blob/a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e/competition/tools/verifier/README.md#ac-moves) · [Earlier 42-move witness](https://github.com/kushuel-pixel/ak3-connection-013/blob/906baa95d8a76691b0f2b828e49aedd6b5fbb621/submission018/evidence/012/stages/006/bridge42.json) · [Python log](replay_bridge44.log) · [All 45 states](bridge44_trace.tsv)

### R2 EN

**Section 2. E₃ ↔ Q ↔ (a,b) takes 187 + 62 moves each way.** In `AK3.Class31Route`, `route_length` gives 187 moves, `forward` gives Q → E₃, and `backward` gives E₃ → Q. In `AK3.SSeven`, the first four conjuncts of `literal_route_and_obstruction` give the 62-move counts and endpoints in both directions. Here `backwardMoves` runs Q → (a,b) and `forwardMoves` runs (a,b) → Q. `exact_seed` identifies the Q of the 187-move route with `targetPair` in the 62-move theorem. S and Q share f and have distinct second words r and e. The 249-move connection runs between E₃ and (a,b). [187-move Lean source](evidence/route_and_C/AK3Class31Route.lean) · [Endpoint definitions and `exact_seed`](evidence/route_and_C/AK3SSevenWords.lean) · [62-move Lean theorem](evidence/route_and_C/EndpointReplay.lean) · [Axiom audit](evidence/route_and_C/EndpointReplay.stdout) · [Replay data](evidence/route_and_C/route249.json)

### R3 EN

**Section 2, corollary. With no length cap, S can reach E₃ if and only if S can reach (a,b).** R2 supplies the suffix in each direction.

| Given path | Append these moves | New endpoint |
|---|---|---|
| S → E₃ | E₃ → Q (`undo route`, 187 moves), then Q → (a,b) (`backwardMoves`, 62 moves) | (a,b) |
| S → (a,b) | (a,b) → Q (`forwardMoves`, 62 moves), then Q → E₃ (`route`, 187 moves) | E₃ |

The declaration `exact_seed` identifies the two occurrences of Q. [187-move declarations](evidence/route_and_C/AK3Class31Route.lean) · [62-move declaration](evidence/route_and_C/EndpointReplay.lean) · [Identification of Q](evidence/route_and_C/AK3SSevenWords.lean)

As supplementary history, the SUB status report mentions a declaration named `from_s_iff`. Its source and execution log are outside this package. The two concatenations in the table establish the corollary in the paper. [Excerpt from the status report](evidence/route_and_C/SUB_STATUS_EXCERPT.md)

### R4 EN

**Section 3. The images of a and f are nonconjugate in the original common quotient C.** `AK3.SSeven.RBNorm` is the normal closure of `rWord` and `bWord` in the original free group. `Common` is the quotient and `commonMap` is the quotient map. The theorem `AK3.SSeven.FreeCap.RawChart.common_nonconjugate_by_curvature` gives `c * commonMap (FreeGroup.mk aWord) * c⁻¹ ≠ commonMap (FreeGroup.mk fWord)` for every `c : Common`. The curvature argument establishes `yQ_ne_one_by_curvature` by contradiction from `yQ = 1`, and `common_nonconjugate_of_yQ` then yields the result. The final axiom audit lists `propext`, `Classical.choice`, and `Quot.sound`. The quotient rules out paths from S to (a,b) built entirely from moves on the second word alone, conjugations of the first word, and right multiplications of the first word by the current second word or its inverse when that second word maps to the identity in C. The 62-move route starts at Q = (f,e), while C kills r from S = (f,r) and b from (a,b). General reachability from S to E₃ remains unresolved. [Lean quotient definition](evidence/route_and_C/AK3SSevenCommonKernel.lean) · [Final Lean source](evidence/route_and_C/TerminalAssembly.lean) · [Exact theorem type and axiom audit](evidence/route_and_C/FinalKernelAudit.stdout) · [Verification record](evidence/route_and_C/RESULT.txt)

### R5 EN

**Section 2. The observed peak of the 249-move path is 682.** Python checks all 250 states of the one-way replay against the reverse path, the ordered pairs at E₃, Q and (a,b), the endpoint lengths 283 and 399, and the peak 682. The Lean results in R2 concern move counts and endpoints. [Python log](replay_route249.log) · [Replay script](replay_route249.py) · [Replay data](evidence/route_and_C/route249.json)

Run the commands under **Replay** from the extracted directory with Python 3 and its standard library. The first command checks the bundled file hashes. The last compares the 44-move trace to the supplied table. The Lean material consists of source excerpts and existing verification and axiom audit records. A complete Lean build requires the original dependencies. The derivation in R3 and the theorem type and axiom audit in R4 can be inspected in the included files. [Replay commands](#replay)

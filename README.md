# AK(3) · ac-00399

Hiromu Yasuno · 2026-11-27 · rev2

[日本語本文](AK3_SUBMISSION_2026-11-27_rev2/01_SUBMISSION_ja.md) · [English paper](AK3_SUBMISSION_2026-11-27_rev2/02_SUBMISSION_en.md) · [確定版 ZIP / Download rev2](AK3_SUBMISSION_2026-11-27_rev2.zip)

## 日本語

既報 ACC-P000029 は慣用表記の始点 A から固定語対 S への経路を調べた。今回の始点は公式採点行 `ac-00399` に書かれた順序付き語対 `(YXYxyx, YYYYxxx)` である。 [既報 ACC-P000029](https://github.com/kushuel-pixel/ak3-connection-013/blob/906baa95d8a76691b0f2b828e49aedd6b5fbb621/README.md) → [今回の日本語本文](AK3_SUBMISSION_2026-11-27_rev2/01_SUBMISSION_ja.md)

| 結果 | 確認先 |
| --- | --- |
| 公式始点から44手で S に到達する。全45状態で自由簡約後の2語の長さの和は22以下であり、S 自身の長さの和が22なので最小ピークは22。44手の最短性は主張しない。 | [Lean 定理・全状態表（R1）](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md#r1) |
| E₃ ↔ Q ↔ (a,b) は片道187＋62手。この経路を末尾につなぐと、長さ上限なしで S → E₃ と S → (a,b) の到達可否が同値になる。249手列のピーク682は Python の再生値。 | [両方向の Lean 定理（R2）](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md#r2) · [系（R3）](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md#r3) · [再生（R5）](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md#r5) |
| S = (f,r) と (a,b) の第二語 r, b をともに単位元にする共通商 C でも、第一語 f, a の像は非共役。第一語の像の共役類を保つ手だけで両端を結ぶ経路を排除できる。全操作を許した S → E₃ の到達可否は未解決。 | [Lean 定理・公理監査・排除できる手（R4）](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md#r4) |

## English

ACC-P000029 studied paths from the conventional start A to the fixed pair S. The present paper starts at the ordered pair printed in the official scoring row `ac-00399`. [Earlier paper](https://github.com/kushuel-pixel/ak3-connection-013/blob/906baa95d8a76691b0f2b828e49aedd6b5fbb621/README.md) → [English translation](AK3_SUBMISSION_2026-11-27_rev2/02_SUBMISSION_en.md)

1. A 44-move path reaches S. The minimum peak of the total freely reduced length is exactly 22, since S itself has length 22. The paper makes no claim that 44 moves is shortest. [Lean theorems and replay](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md#r1-en)
2. The paths E₃ ↔ Q ↔ (a,b) take 187 + 62 moves each way. Appending them shows that, without a length cap, S reaches E₃ if and only if S reaches (a,b). Python gives a peak of 682 for the path from E₃ to (a,b). [Lean theorems](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md#r2-en) · [Corollary](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md#r3-en) · [Replay](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md#r5-en)
3. In the common quotient C that kills the second words of S = (f,r) and (a,b), the images of f and a are nonconjugate. This excludes paths between those pairs that preserve the conjugacy class of the first image at every step. Whether S reaches E₃ using all allowed moves remains open. [Lean theorem, axiom audit and scope](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md#r4-en)

## 再生 / Replay

リポジトリのルートから次の2本を実行する。どちらも Python 3 の標準ライブラリだけを使う。

From the repository root, run both scripts with Python 3. They use only the standard library.

```sh
cd AK3_SUBMISSION_2026-11-27_rev2
python3 -B replay_bridge44.py
python3 -B replay_route249.py
```

成功時は両方が `PASS` を表示する。最初のスクリプトは44手とその逆順、次のスクリプトは249手とその逆順を照合する。ファイルのハッシュと44手の全状態表も照合できる。 [照合コマンド](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md#replay)

Both scripts print `PASS` on success. They check the 44-move and 249-move paths in both directions. The evidence index also gives commands to verify the file hashes and compare all 45 states of the first path with the archived table. [Verification commands](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md#replay)

Lean については、関連ソース、既存の実行記録、公理監査を収録した。Lean の再ビルドには別途依存関係が必要。 [証拠索引](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md)

The kit includes Lean source excerpts, recorded runs and axiom audits. Rebuilding the Lean proofs requires additional dependencies. [English evidence index](AK3_SUBMISSION_2026-11-27_rev2/03_CLAIMS_AND_REPLAY_ja.md#english)

**rev2 ZIP SHA-256** `94efab03489a1d935b1719fd328b72bfa7eaded90d90a86e27d65802f9991402`

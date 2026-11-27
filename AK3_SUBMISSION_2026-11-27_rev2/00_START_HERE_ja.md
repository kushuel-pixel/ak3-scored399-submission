# AK(3) 提出資料

読む順番は **ACC-P000029 → 今回の提出稿**。既報の始点 A と、今回使う公式採点行 `ac-00399` の始点を区別して読む。 [ACC-P000029](https://github.com/kushuel-pixel/ak3-connection-013/blob/906baa95d8a76691b0f2b828e49aedd6b5fbb621/README.md) → [日本語原本](01_SUBMISSION_ja.md)・[英訳](02_SUBMISSION_en.md)

| 本文 | 確認する主張 | 対応する証拠 |
|---|---|---|
| 第1節 | 公式始点から S へ44手。最小ピーク22。 | [Lean 定理・44手再生（R1）](03_CLAIMS_AND_REPLAY_ja.md#r1) |
| 第2節 | E₃ ↔ Q ↔ (a,b) は片道187＋62手。長さ上限なしで S からの到達先を移せる。 | [両方向の Lean 定理（R2）](03_CLAIMS_AND_REPLAY_ja.md#r2) · [往復経路から従う系（R3）](03_CLAIMS_AND_REPLAY_ja.md#r3) · [ピーク682の Python 再生（R5）](03_CLAIMS_AND_REPLAY_ja.md#r5) |
| 第3節 | 第二語 r と b を殺す元の共通商 C で、第一語 a と f の像は非共役。 | [商の定義・Lean の最終定理と公理監査（R4）](03_CLAIMS_AND_REPLAY_ja.md#r4) |

S の第二語は `xxYYYYYXyyyyy`、Q の第二語は `xxYXy`。62手の接続は Q と (a,b) の間にあり、C での非共役と両立する。全操作を許した S → E₃ の到達可否は未決。68配分の限定排除は別付録を参照。 [図式の付録](04_DIAGRAM_APPENDIX_ja.md)

提出用の短い要旨を日英で収録した。 [日本語要旨](FORM_DESCRIPTION_ja.txt) · [English summary](FORM_DESCRIPTION_en.txt)

本資料は証拠抜粋である。Python の再生に必要なファイルと、Lean の関連ソース・既存の検証記録を収録した。依存関係込みの Lean ビルド一式は別。 [再生手順](03_CLAIMS_AND_REPLAY_ja.md#replay)

## English

Read **ACC-P000029 → the present paper**. The paper links the three results to the relevant evidence and states the remaining open question. The evidence index also gives the Python replay commands in English. [ACC-P000029](https://github.com/kushuel-pixel/ak3-connection-013/blob/906baa95d8a76691b0f2b828e49aedd6b5fbb621/README.md) → [English paper](02_SUBMISSION_en.md) · [English summary](FORM_DESCRIPTION_en.txt) · [Evidence index](03_CLAIMS_AND_REPLAY_ja.md#english) · [Diagram appendix](04_DIAGRAM_APPENDIX_ja.md#english)

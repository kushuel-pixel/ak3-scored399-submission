# 補足資料　到達同値についての検証履歴 / Supplementary verification history

2026年11月27日付の進捗表 `PROOF_STATUS_ja.md`（版 `4906d8b07c99`、12行目）は、SUB での検証を次のように記録している。

> 往復249手の端点・手数・操作IDと、**上限なし**での S→E₃ ⇔ S→(a,b) を SUB の Lean 4.35.0 で検証済み（`AK3SubExactRoute`、`from_s_iff`、標準3公理の範囲）。

この引用は進捗表の記述である。`from_s_iff` 自体のソースと実行ログはこの資料集に含まれない。本文第2節の系は、同梱した両方向の経路から確認できる。 [経路をつなぐ順序（R3）](../../03_CLAIMS_AND_REPLAY_ja.md#r3)

The quotation records an earlier report of verification in the SUB environment. The source and execution log for `from_s_iff` are outside this package. Section 2 derives the corollary directly from the two paths available here in both directions. [Concatenation in each direction (R3)](../../03_CLAIMS_AND_REPLAY_ja.md#r3-en)

# 公式始点から S への44手列の検証記録

公式採点行 `ac-00399` の始点は `(YXYxyx, YYYYxxx)`。同梱の Python 再生で使う14個の操作番号・左右の語への作用・逆操作番号を固定版 `ac-r2-v1` の表と照合した。 [公式採点行](https://github.com/SAIRcompetition/Andrews-Curtis/blob/a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e/competition/problems/ac.jsonl#L399) · [14操作の表](https://github.com/SAIRcompetition/Andrews-Curtis/blob/a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e/competition/tools/verifier/README.md#ac-moves) · [Python 実装](../../replay_bridge44.py)

既存の Lean 4.35.0 の検査は、順序付き終点 S、手数44、始点と終点を含む全45状態の総自由簡約長の上界22を確認している。S 自身の総自由簡約長は22であり、`reachesAtCap_iff` は上限 h での到達可能性と 22 ≤ h の同値を与える。 [定理のソース](Scored399Bridge44.lean) · [9宣言の公理監査](LeanBridge44.log)

既報の A 始点の42手列との合流は `joins_bridge42_after_10`、共通の末尾32手は `same_last32` で確認できる。Python 再生では44手列とその逆順を検査する。 [45状態の表](../../bridge44_trace.tsv) · [再生ログ](../../replay_bridge44.log)

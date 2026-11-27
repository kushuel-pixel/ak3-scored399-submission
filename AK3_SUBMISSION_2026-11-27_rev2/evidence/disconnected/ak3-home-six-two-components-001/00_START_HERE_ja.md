# AK3 固定12型：非連結のうちちょうど2成分

対象は `FaceTriple ∈ coefficientTriples` の正アンカー2行、負アンカー1行、関係式3行の実図式 `PlanarCore`。成分は補助円板を数えず、ギャップ上の回転と辺の相手から作る `SixGapComponent`。今回はその個数がちょうど2の場合。

- **VFiveSixTwoMixed**: `six_mixed_region_subsingleton` は、両成分にまたがる結合係数領域が高々1つであることを示す。両因子にまたがりが生じることはなく、`two_components_have_closed_factor` が、すべての成分を同時に分離する一つの因子の存在を示す。
- **VFiveSixTwoContact**: `two_components_crossing_has_two_orbits` は、またぐ領域があれば、その逆像を異なる成分からの各1つ、計2つのギャップ頂点軌道に固定する。`two_components_crossing_spends_budget` は、それ以外に共有ギャップ頂点軌道がないことも示す。
- **VFiveSixTwoCensus**: 二因子の少なくとも片方で係数和がゼロになる負アンカー側の行配分を、全12型について検査。`two_component_negative_mask_in_census` が、実図式の配分が表から漏れないことを示す。前回排除済みのマスク5・6は含まない。`two_component_candidate_count` は因子間の重複を各型の中で除いた合計が **100** と示す（各型 12,8,6,9,9,6,16,7,5,8,6,8）。これは必要条件を通過した (型, 行配分) の組数であり、実在する図式数ではない。
- **VFiveSixTwoReduction**: `two_component_neutral_or_one_contact` は、実図式が前回の3つの両因子中立候補に入るか、またはただ1つのまたぎ領域に両成分から各1つのギャップ頂点軌道が接することを示す。選言は排他的ではない。

次は、1つのまたぎで生じる局所係数と各成分の辺数・面の並びを照合する。両因子中立3型も未排除。3成分以上と連結枝は別。S からの一般不達は主張しない。

## 再検証

HOME で、既存の `ak3-home-six-disconnected-001` とその固定作業キャッシュを使い、`./verify.sh` を実行する（Lean 4.35.0、1ジョブ）。最終ログは `verified.log`。依存キャッシュ込みのクリーン再構築や独立機での再検証ではない。Git 未更新。

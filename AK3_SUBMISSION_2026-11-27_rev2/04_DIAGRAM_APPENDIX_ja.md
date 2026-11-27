# 付録　固定12型の2成分図式での限定排除

対象は固定12の符号付き係数型に対応する6行図式のうち、ちょうど2成分があり、両成分にまたがる係数領域がある、非中立の2行対4行の68配分である。各配分について **2行側の全頂点の次数が2** である場合を排除する。

1. 2行側の全頂点の次数が2なら、辺の対応は2行の角を逆巡回順に一対一に結ぶ。角数が一致しない66配分は排除される。 [角数と行配分の検査](evidence/disconnected/ak3-home-six-digon-pair-001/VFiveSixDigonLengthTable.lean)
2. 等長の2配分では、因子が一致する逆巡回照合の全位相で、係数が相殺しない角対がそれぞれ少なくとも10組と22組ある。実図式の照合が検査した位相のいずれかに一致し、異なる角対が異なる頂点を与えることも証明した。 [角対の数値検査](evidence/disconnected/ak3-home-six-digon-pair-001/VFiveSixDigonMismatch.lean) · [実図式との対応](evidence/disconnected/ak3-home-six-digon-close-001/VFiveSixDigonReverseActual.lean)
3. 両成分にまたがる領域の係数を担える非零頂点は各成分で高々1つであり、2と矛盾する。 [最終定理](evidence/disconnected/ak3-home-six-digon-close-001/VFiveSixDigonAll.lean)

最終宣言は `AK3.SubVPicture.RingGeneralSix.charged_two_row_all_degree_two_excluded`。既存の Lean 実行票は推移的な公理依存 `propext`、`Classical.choice`、`Quot.sound` を記録している。 [検証ログ](evidence/disconnected/ak3-home-six-digon-close-001/verified.log)

この付録は本文の非共役定理とは独立した限定結果である。2行側に次数1と3が各1つある枝、3行対3行の非中立配分、両因子中立の3型、3成分以上、連結枝はこの排除の範囲外にある。全操作を許した S → E₃ の到達可否は未決。 [付録の範囲を記録した案内](evidence/disconnected/ak3-home-six-digon-close-001/00_START_HERE_ja.md)

## English

### Appendix. A restricted exclusion for two-component diagrams in 12 fixed types

Consider six-row diagrams from the 12 fixed signed coefficient types. The result applies to 68 non-neutral two-row versus four-row allocations with exactly two components and a coefficient region spanning both. In each allocation it excludes the case in which **every vertex of the two-row component has degree two**.

1. With all degrees two on that side, the edges pair corners of the two rows bijectively in reverse cyclic order. The 66 allocations with unequal corner counts are excluded. [Corner-count and allocation check](evidence/disconnected/ak3-home-six-digon-pair-001/VFiveSixDigonLengthTable.lean)
2. For the two equal-length allocations, every factor-compatible reverse cyclic alignment has at least 10 and 22 corner pairs with nonzero coefficient sum, respectively. The proof connects each actual diagram to one of the checked alignments and shows that distinct pairs give distinct vertices. [Numerical check](evidence/disconnected/ak3-home-six-digon-pair-001/VFiveSixDigonMismatch.lean) · [Application to actual diagrams](evidence/disconnected/ak3-home-six-digon-close-001/VFiveSixDigonReverseActual.lean)
3. At most one nonzero vertex per component can carry a coefficient for the region spanning both components. This contradicts the previous step. [Final theorem](evidence/disconnected/ak3-home-six-digon-close-001/VFiveSixDigonAll.lean)

The final declaration is `AK3.SubVPicture.RingGeneralSix.charged_two_row_all_degree_two_excluded`. Its recorded transitive axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`. [Lean verification log](evidence/disconnected/ak3-home-six-digon-close-001/verified.log)

The appendix is independent of the nonconjugacy theorem in Section 3. This exclusion leaves out the case with one degree-one and one degree-three vertex on the two-row side, the non-neutral three-row versus three-row allocations, the three types neutral in both factors, diagrams with three or more components, and connected diagrams. Reachability from S to E₃ with all allowed moves remains unresolved. [Scope of the diagram result](evidence/disconnected/ak3-home-six-digon-close-001/00_START_HERE_ja.md)

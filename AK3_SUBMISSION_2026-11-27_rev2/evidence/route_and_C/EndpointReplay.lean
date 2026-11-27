import TerminalAssembly
import AK3SSevenTerminalAudit

namespace AK3.SSeven
open Verify.AtomicSemantics FreeGroup

/-- The replay starts at the actual entrance pair (f,e), whereas the
arbitrary-route bound uses (f,r). The second words are not identified. -/
theorem literal_route_and_obstruction :
    backwardMoves.length = 62 ∧ forwardMoves.length = 62 ∧
    wordRun backwardMoves targetPair = inputPair ∧
    wordRun forwardMoves inputPair = targetPair ∧
    (∀ c : Common,
      c * commonMap (mk (wordRun backwardMoves targetPair).1) * c⁻¹ ≠
        commonMap (mk targetPair.1)) :=
  ⟨fixed_route_size.1, fixed_route_size.2, backward_exact, forward_exact,
    raw_replayed_nonconjugate_of_yQ FreeCap.RawChart.yQ_ne_one_by_curvature⟩

#print axioms literal_route_and_obstruction
end AK3.SSeven

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20110

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [8, 11]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [10, 13]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [9, 15]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [8, 17]⟩,
    ⟨.or, [18, 14]⟩,
    ⟨.or, [10, 22]⟩,
    ⟨.or, [16, 19]⟩,
    ⟨.or, [11, 23]⟩,
    ⟨.or, [19, 23]⟩,
    ⟨.or, [16, 20]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.or, [16, 21]⟩,
    ⟨.or, [17, 21]⟩,
    ⟨.and, [0, 28]⟩,
    ⟨.and, [1, 30]⟩,
    ⟨.and, [2, 29]⟩,
    ⟨.and, [3, 25]⟩,
    ⟨.and, [4, 27]⟩,
    ⟨.and, [5, 31]⟩,
    ⟨.and, [6, 24]⟩,
    ⟨.and, [7, 26]⟩,
    ⟨.or, [32, 33]⟩,
    ⟨.or, [40, 34]⟩,
    ⟨.or, [41, 35]⟩,
    ⟨.or, [42, 36]⟩,
    ⟨.or, [43, 37]⟩,
    ⟨.or, [44, 38]⟩,
    ⟨.or, [45, 39]⟩], 46⟩

end PEqualNP.Outside.L_meta_20110

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_20110 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7788925477185833355 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  refine ⟨PEqualNP.Outside.L_meta_20110.witness, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_20110.witness]
  · decide
  · decide +kernel

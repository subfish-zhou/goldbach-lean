import Wu04BypassData

namespace Wu04Bypass
open scoped BigOperators

theorem round2 (i : Fin 9) : v3 i ≤ v0 i + ∑ k : Fin 9, M i k * v2 k := by
  fin_cases i <;> norm_num [v0, v2, v3, M, Fin.sum_univ_succ]

end Wu04Bypass

import Wu04BypassData

namespace Wu04Bypass
open scoped BigOperators

theorem round4 (i : Fin 9) : v5 i ≤ v0 i + ∑ k : Fin 9, M i k * v4 k := by
  fin_cases i <;> norm_num [v0, v4, v5, M, Fin.sum_univ_succ]

end Wu04Bypass

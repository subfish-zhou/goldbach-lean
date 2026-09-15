import Wu04BypassData

namespace Wu04Bypass
open scoped BigOperators

theorem round6 (i : Fin 9) : v7 i ≤ v0 i + ∑ k : Fin 9, M i k * v6 k := by
  fin_cases i <;> norm_num [v0, v6, v7, M, Fin.sum_univ_succ]

end Wu04Bypass

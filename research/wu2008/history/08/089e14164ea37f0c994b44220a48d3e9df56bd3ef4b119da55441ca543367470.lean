import Wu04BypassData

namespace Wu04Bypass
open scoped BigOperators

theorem round3 (i : Fin 9) : v4 i ≤ v0 i + ∑ k : Fin 9, M i k * v3 k := by
  fin_cases i <;> norm_num [v0, v3, v4, M, Fin.sum_univ_succ]

end Wu04Bypass

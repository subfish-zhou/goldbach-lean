import Wu04BypassData

namespace Wu04Bypass
open scoped BigOperators

theorem round0 (i : Fin 9) : v1 i ≤ v0 i + ∑ k : Fin 9, M i k * v0 k := by
  fin_cases i <;> norm_num [v0, v0, v1, M, Fin.sum_univ_succ]

end Wu04Bypass

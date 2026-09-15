import Wu04BypassData

namespace Wu04Bypass
open scoped BigOperators

theorem round5 (i : Fin 9) : v6 i ≤ v0 i + ∑ k : Fin 9, M i k * v5 k := by
  fin_cases i <;> norm_num [v0, v5, v6, M, Fin.sum_univ_succ]

end Wu04Bypass

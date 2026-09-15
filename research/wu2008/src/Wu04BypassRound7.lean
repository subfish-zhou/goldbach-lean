import Wu04BypassData

namespace Wu04Bypass
open scoped BigOperators

theorem round7 (i : Fin 9) : v8 i ≤ v0 i + ∑ k : Fin 9, M i k * v7 k := by
  fin_cases i <;> norm_num [v0, v7, v8, M, Fin.sum_univ_succ]

end Wu04Bypass

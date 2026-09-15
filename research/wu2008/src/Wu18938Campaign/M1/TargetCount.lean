import Wu18938Campaign.M1.TargetPrimeGains

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical

theorem target_count_nonunit_remainder {N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (hz : 2 ≤ (N : ℝ) ^ (100 / 1327 : ℝ)) :
    let z := (N : ℝ) ^ (100 / 1327 : ℝ)
    let w := (N : ℝ) ^ (25 / 206 : ℝ)
    let u := (N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ))
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ))
    (eleven N z w u v V : ℝ) + quotientAssemblyGains N z w u v ≤
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
      (∑ t ∈ targetExcessTuples N,
        ((targetPrimeCofactorCarrier N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2)).card : ℝ)) +
      ((∑ t ∈ targetExcessTuples N, ∑ q ∈ primeWindow N (t.2.1 : ℝ) v,
        sieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2 * q) N (q : ℝ) : ℤ) : ℝ) +
      (18 + 2 * (1 / (100 / 1327 : ℝ)) ^ 3 +
        2 * (1 / (25 / 206 : ℝ)) ^ 2 + 2 * (1327 / 100 : ℝ) ^ 4) *
          (N : ℝ) ^ (1 - (100 / 1327 : ℝ)) := by
  have h := eleven_count_signed (κ₁ := (100 / 1327 : ℝ)) (κ₂ := (25 / 206 : ℝ))
    hN he (by norm_num) (by norm_num) (by norm_num) (by norm_num) hz
  have hpaid := target_excess_nonunit_paid hN he
  dsimp only at h ⊢
  linarith

end Wu18938Campaign.M1

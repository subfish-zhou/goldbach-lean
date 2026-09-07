import MathlibNt.SieveTheory.LiLiuGoldbachB10RosserFactor

open scoped BigOperators
open Finset MathlibNt.SieveTheory

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableB10UpperError (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The actual Rosser remainder needs only the unweighted coprime modulus sum.
The natural Rosser level is `Q+1`, so its strict support is exactly `d≤Q`. -/
theorem goldbachB10_upperErrSum_le_commonModulusSum
    (N : ℕ) (hEven : Even N) (ε b c Z X : ℝ) (Q : ℕ) :
    let S := goldbachB10BoundingSieve N hEven ε b c Z X
    LinearSieve.upperErrSum S (Q + 1)
      (LinearSieve.upperRosserWeight S.prodPrimes (Q + 1)) ≤
    ∑ d ∈ (Icc 1 Q).filter (fun d => Nat.Coprime d N),
      |((goldbachB10DivisorAtoms N d ε b c).card : ℝ) - X / d.totient| := by
  let S := goldbachB10BoundingSieve N hEven ε b c Z X
  let I := S.prodPrimes.divisors.filter (fun d => d < Q + 1)
  have hdiv {d : ℕ} (hd : d ∈ I) : d ∣ goldbachB10ProdPrimes N Z :=
    (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
  have hsub : I ⊆ (Icc 1 Q).filter (fun d => Nat.Coprime d N) := by
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors (mem_filter.mp hd).1
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hdpos, by
      have := (mem_filter.mp hd).2
      omega⟩, goldbachB10_dvd_prodPrimes_coprime_N (hdiv hd)⟩
  change (∑ d ∈ I, |LinearSieve.upperRosserWeight S.prodPrimes (Q + 1) d| * |S.rem d|) ≤ _
  calc
    _ ≤ ∑ d ∈ I, |S.rem d| := by
      apply sum_le_sum
      intro d _
      exact (mul_le_mul_of_nonneg_right
        (LinearSieve.abs_upperRosserWeight_le_one S.prodPrimes (Q + 1) d)
        (abs_nonneg _)).trans_eq (one_mul _)
    _ = ∑ d ∈ I, |((goldbachB10DivisorAtoms N d ε b c).card : ℝ) - X / d.totient| := by
      apply sum_congr rfl
      intro d hd
      exact congrArg abs (goldbachB10BoundingSieve_rem_eq_card_sub hEven (hdiv hd))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
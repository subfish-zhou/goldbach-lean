import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryLargeSupportDensity
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighDeltaWeights

/-!
# Reciprocal mass of the large-square-divisor support

Exact finite reindexing of multiples, followed by the inverse-square tail,
retains the square-root saving in harmonic rather than counting measure.
-/

noncomputable section

open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The harmonic mass of the positive multiples of `d` up to a real endpoint. -/
theorem sum_one_div_multiples_le_log {L : ℝ} (hL : 1 ≤ L)
    {d : ℕ} (hd : 0 < d) :
    (∑ n ∈ (Ioc 0 ⌊L⌋₊).filter (fun n => d ∣ n), (1 : ℝ) / n) ≤
      (1 + Real.log L) / d := by
  let S := (Ioc 0 ⌊L⌋₊).filter (fun n => d ∣ n)
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hi : Set.InjOn (fun n => n / d) (↑S : Set ℕ) := by
    intro n hn m hm he
    change n / d = m / d at he
    calc
      n = d * (n / d) := (Nat.mul_div_cancel' (mem_filter.mp hn).2).symm
      _ = d * (m / d) := by rw [he]
      _ = m := Nat.mul_div_cancel' (mem_filter.mp hm).2
  have hsub : S.image (fun n => n / d) ⊆ Ioc 0 ⌊L⌋₊ := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    obtain ⟨hn, hdn⟩ := mem_filter.mp hn
    obtain ⟨hn0, hnL⟩ := mem_Ioc.mp hn
    exact mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn0 hdn) hd,
      (Nat.div_le_self _ _).trans hnL⟩
  have hh : (∑ m ∈ Ioc 0 ⌊L⌋₊, (1 : ℝ) / m) ≤ 1 + Real.log L := by
    calc
      _ = ∑ m ∈ Ioc 0 ⌊L⌋₊, (fouvryTau 1 m : ℝ) / m := by
        apply sum_congr rfl
        intro m hm
        rw [fouvryTau_order_one (mem_Ioc.mp hm).1.ne', Nat.cast_one]
      _ ≤ _ := by simpa using sum_fouvryTau_div_le_real 1 hL
  calc
    _ = (∑ m ∈ S.image (fun n => n / d), (1 : ℝ) / m) / d := by
      rw [sum_image hi, sum_div]
      apply sum_congr rfl
      intro n hn
      rw [Nat.cast_div (mem_filter.mp hn).2 hd0]
      field_simp
    _ ≤ (∑ m ∈ Ioc 0 ⌊L⌋₊, (1 : ℝ) / m) / d :=
      div_le_div_of_nonneg_right
        (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
        (Nat.cast_nonneg d)
    _ ≤ _ := div_le_div_of_nonneg_right hh (Nat.cast_nonneg d)

/-- Uniform harmonic saving for large square divisors, with constant `2`. -/
theorem sum_one_div_largeSquareDivisorSet_le {L Z : ℝ}
    (hL : 1 ≤ L) (hZ : 0 < Z) :
    (∑ n ∈ largeSquareDivisorSet ⌊L⌋₊ Z, (1 : ℝ) / n) ≤
      (2 / Z) * (1 + Real.log L) := by
  let B := Ioc ⌊Z⌋₊ (Nat.sqrt ⌊L⌋₊)
  have hsub : largeSquareDivisorSet ⌊L⌋₊ Z ⊆ Ioc 0 ⌊L⌋₊ :=
    filter_subset _ _
  have htail : (∑ b ∈ B, ((b : ℝ) ^ 2)⁻¹) ≤ 2 / Z := by
    calc
      _ = ∑ b ∈ Ioo ⌊Z⌋₊ (Nat.sqrt ⌊L⌋₊ + 1), ((b : ℝ) ^ 2)⁻¹ := by
        congr 1
        ext b
        simp only [B, mem_Ioc, mem_Ioo]
        omega
      _ ≤ 2 / ((⌊Z⌋₊ : ℝ) + 1) := sum_Ioo_inv_sq_le _ _
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hZ
        (Nat.lt_floor_add_one Z).le
  calc
    _ ≤ ∑ n ∈ largeSquareDivisorSet ⌊L⌋₊ Z,
        ∑ b ∈ B, if b ^ 2 ∣ n then (1 : ℝ) / n else 0 := by
      apply sum_le_sum
      intro n hn
      rw [largeSquareDivisorSet_eq_biUnion _ hZ.le] at hn
      obtain ⟨b, hb, hn⟩ := mem_biUnion.mp hn
      calc
        _ = (if b ^ 2 ∣ n then (1 : ℝ) / n else 0) := by
          rw [if_pos (mem_filter.mp hn).2]
        _ ≤ _ := single_le_sum
          (f := fun b => if b ^ 2 ∣ n then (1 : ℝ) / n else 0)
          (fun _ _ => by split_ifs <;> positivity) hb
    _ ≤ ∑ n ∈ Ioc 0 ⌊L⌋₊,
        ∑ b ∈ B, if b ^ 2 ∣ n then (1 : ℝ) / n else 0 :=
      sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => sum_nonneg (fun _ _ => by split_ifs <;> positivity))
    _ = ∑ b ∈ B, ∑ n ∈ (Ioc 0 ⌊L⌋₊).filter (fun n => b ^ 2 ∣ n),
        (1 : ℝ) / n := by rw [sum_comm]; simp only [sum_filter]
    _ ≤ ∑ b ∈ B, (1 + Real.log L) / (b : ℝ) ^ 2 := by
      apply sum_le_sum
      intro b hb
      have hb0 : 0 < b := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hb).1
      simpa only [Nat.cast_pow] using sum_one_div_multiples_le_log hL (pow_pos hb0 2)
    _ = (∑ b ∈ B, ((b : ℝ) ^ 2)⁻¹) * (1 + Real.log L) := by
      simp only [sum_mul, div_eq_mul_inv]
      apply sum_congr rfl
      intro _ _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right htail (by linarith [Real.log_nonneg hL])

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

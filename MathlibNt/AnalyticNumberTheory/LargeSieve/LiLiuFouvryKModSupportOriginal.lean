import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWModulusSupportOriginal

/-! Fixed-scale divisor growth on the actual nonzero progression difference.
Only its arithmetic bound uses the auxiliary scale; physical M, T, x, Y and
the actual tuple mask are unchanged. -/

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wMaskedOriginal_abs_le_modulus_support_kscale
    (Cscale : ℝ) (hCscale : 1 ≤ Cscale) (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T L x Y : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → M * T ≤ x → L ≤ x → 0 < Y →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
        (∀ t ∈ wOriginalTuples N Q a, P t →
          Y < ((wGCDTuple t).δ₁ : ℝ) ∨ Y < ((wGCDTuple t).δ₂ : ℝ)) →
      |wMaskedOriginal M N Q β c a P| ≤
        C * x ^ ε * (M * (1 + Real.log L) + L) *
          (∑ n ∈ N, |β n|) ^ 2 / Real.sqrt Y := by
  obtain ⟨D, hD, hdiv⟩ := fouvryTau_le_const_rpow (k := j + 1) (by omega)
    (show 0 < ε / 2 by linarith)
  refine ⟨16 * D ^ 2 * (4 * Cscale) ^ ε, by positivity, ?_⟩
  intro M T L x Y hM hT hL hMT hLx hY N Q hN hQ β c hc a ha hs P hP
  have hx : 1 ≤ x := hL.trans hLx
  have hK0 : 0 < Cscale := by linarith
  have hxK : x ≤ Cscale * x := le_mul_of_one_le_left (by linarith) hCscale
  let A := D * (4 * Cscale * x) ^ (ε / 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc' (q : ℕ) (hq : q ∈ Q) : |c q| ≤ A := by
    have hqx : (q : ℝ) ≤ x :=
      (by exact_mod_cast (mem_Ioc.mp (hQ hq)).2 : (q : ℝ) ≤ ⌊L⌋₊).trans
        ((Nat.floor_le (by linarith)).trans hLx)
    calc
      _ ≤ (fouvryTau j q : ℝ) := hc q hq
      _ ≤ (fouvryTau (j + 1) q : ℝ) := by exact_mod_cast fouvryTau_le_succ j q
      _ ≤ D * (q : ℝ) ^ (ε / 2) := hdiv q (mem_Ioc.mp (hQ hq)).1
      _ ≤ A := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by linarith)) hD.le
  have hrow (n : ℕ) (hn : n ∈ N) (hβn : β n ≠ 0)
      (m : ℕ) (hm : scaledDyadicCutoff M m ≠ 0) :
      (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) ≤ A := by
    have hne := mul_sub_ne_zero_of_not_dvd m n a (hs n hn hβn)
    have hnT : (n : ℝ) ≤ T :=
      (by exact_mod_cast (mem_Ioc.mp (hN hn)).2 : (n : ℝ) ≤ ⌊T⌋₊).trans
        (Nat.floor_le (by linarith))
    calc
      _ ≤ (fouvryTau (j + 1) ((m : ℤ) * n - a).natAbs : ℝ) :=
        sum_modEq_abs_le_fouvryTau j Q c hc m n a hne
      _ ≤ D * (((m : ℤ) * n - a).natAbs : ℝ) ^ (ε / 2) :=
        hdiv _ (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hne))
      _ ≤ A := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity)
          (by
            have hb := natAbs_mul_sub_le_of_cutoff (by linarith) (hMT.trans hxK) hnT hm a ha
            nlinarith [hb])
          (by linarith)) hD.le
  have hAsq : A ^ 2 = D ^ 2 * (4 * Cscale) ^ ε * x ^ ε := by
    dsimp [A]
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 4 * Cscale * x)]
    norm_num
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * Cscale) (by linarith : 0 ≤ x)]
    ring
  let S := largeSquareDivisorSet ⌊L⌋₊ (Real.sqrt Y)
  have hPS : ∀ t ∈ wOriginalTuples N Q a, P t → t.1.1 ∈ S ∨ t.1.2 ∈ S := by
    intro t ht hp
    obtain ⟨hqr, _⟩ := mem_product.mp (mem_filter.mp ht).1
    obtain ⟨hq, hr⟩ := mem_product.mp hqr
    rcases hP t ht hp with hδ | hδ
    · exact Or.inl (deltaOne_mem_largeSquareDivisorSet _ _ _
        (hQ (mem_filter.mp hq).1) hY.le hδ)
    · exact Or.inr (deltaTwo_mem_largeSquareDivisorSet _ _ _
        (hQ (mem_filter.mp hr).1) hY.le hδ)
  calc
    _ ≤ 2 * A * A * (8 * M * (1 + Real.log L) + 2 * L) *
        (∑ n ∈ N, |β n|) ^ 2 / Real.sqrt Y :=
      wMaskedOriginal_abs_le_sparse_row_cap hM hL (Real.sqrt_pos.mpr hY)
        hA hA N Q S (fun _ h => h) β c hc' a hrow P hPS
    _ ≤ 2 * A * A * (8 * (M * (1 + Real.log L) + L)) *
        (∑ n ∈ N, |β n|) ^ 2 / Real.sqrt Y := by
      gcongr
      linarith
    _ = 16 * A ^ 2 * (M * (1 + Real.log L) + L) *
        (∑ n ∈ N, |β n|) ^ 2 / Real.sqrt Y := by ring
    _ = _ := by rw [hAsq]; ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

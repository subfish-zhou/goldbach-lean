import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeGCDOriginal
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeGCDZero

/-!
# Original and same-mask zero-mode bounds from finite beta-pair support

A mask may depend on both moduli as well as both beta indices. Its only
required support information is that the beta pair belongs to a specified
finite set. Both bounds retain arbitrary coefficient signs and do not
restrict an unmasked cancellation estimate to a signed submask.
-/

noncomputable section

open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- A finite enclosure of the masked beta pairs gives a nonnegative
majorant with the two modulus sums separated. No enclosure of `F` in
`N ×ˢ N` is needed until the individual rows are estimated. -/
theorem wMaskedOriginal_abs_le_pair_modulus_sums
    (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) (F : Finset (ℕ × ℕ))
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → t.2 ∈ F) :
    |wMaskedOriginal M N Q β c a P| ≤
      ∑ p ∈ F, ∑ m ∈ dyadicCutoffNatSupport M,
        |β p.1 * β p.2| * scaledDyadicCutoff M m *
          (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * p.1) a then |c q| else 0) *
          (∑ r ∈ Q, if Int.ModEq r ((m : ℤ) * p.2) a then |c r| else 0) := by
  let G : WOriginalTuple → ℝ := fun t ↦ |wTupleCoefficient β c t| *
    productProgressionWeight (dyadicCutoffNatSupport M)
      (fun m ↦ scaledDyadicCutoff M m) a t.1.1 t.1.2 t.2.1 t.2.2
  have hw (q r n₁ n₂ : ℕ) : 0 ≤
      productProgressionWeight (dyadicCutoffNatSupport M)
        (fun m ↦ scaledDyadicCutoff M m) a q r n₁ n₂ := by
    apply sum_nonneg
    intro m _
    split_ifs
    · exact scaledDyadicCutoff_nonneg M m
    · rfl
  have hG (t : WOriginalTuple) : 0 ≤ G t :=
    mul_nonneg (abs_nonneg _) (hw _ _ _ _)
  calc
    _ ≤ ∑ t ∈ wMaskedTuples N Q a P, G t := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro t _
      dsimp [G]
      rw [abs_mul, abs_of_nonneg (hw _ _ _ _)]
    _ ≤ ∑ t ∈ (Q ×ˢ Q) ×ˢ F, G t := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨ho, hp⟩ := mem_filter.mp ht
        obtain ⟨hs, _⟩ := mem_filter.mp ho
        obtain ⟨hqr, _⟩ := mem_product.mp hs
        obtain ⟨hq, hr⟩ := mem_product.mp hqr
        exact mem_product.mpr ⟨mem_product.mpr
          ⟨(mem_filter.mp hq).1, (mem_filter.mp hr).1⟩, hP t ho hp⟩
      · intro t _ _
        exact hG t
    _ = _ := by
      rw [sum_product, sum_comm]
      apply sum_congr rfl
      intro p _
      simp only [sum_product, G, productProgressionWeight, mul_sum]
      rw [sum_comm]
      conv_lhs => arg 2; ext r; rw [sum_comm]
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      simp only [sum_mul]
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro q _
      dsimp [wTupleCoefficient]
      simp only [abs_mul]
      split_ifs <;> simp_all
      ring

/-- The original progression sum is bounded by the absolute mass of any
finite beta-pair support enclosure. The constant depends only on `j` and
`ε`, and is chosen before the scales, coefficients, residue, pair set, and
mask. The nondivisibility hypothesis removes the equality progression. -/
theorem wMaskedOriginal_abs_le_pair_mass (j : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T x : ℝ, 1 ≤ M → 1 ≤ T → 1 ≤ x → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ F : Finset (ℕ × ℕ), F ⊆ N ×ˢ N →
      ∀ P : WOriginalTuple → Prop,
        (∀ t ∈ wOriginalTuples N Q a, P t → t.2 ∈ F) →
      |wMaskedOriginal M N Q β c a P| ≤
        C * M * x ^ ε * ∑ p ∈ F, |β p.1 * β p.2| := by
  obtain ⟨D, hD, hdiv⟩ := fouvryTau_le_const_rpow (k := j + 1) (by omega)
    (show 0 < ε / 2 by linarith)
  refine ⟨5 * D ^ 2 * (4 : ℝ) ^ ε, by positivity, ?_⟩
  intro M T x hM hT hx hMT N Q hN β c hc a ha hsupport F hF P hP
  let A : ℝ := D * (4 * x) ^ (ε / 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hrow (n m : ℕ) (hn : n ∈ N) (hβn : β n ≠ 0)
      (hm : scaledDyadicCutoff M m ≠ 0) :
      (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) ≤ A := by
    have hne := mul_sub_ne_zero_of_not_dvd m n a (hsupport n hn hβn)
    have hnT : (n : ℝ) ≤ T :=
      (by exact_mod_cast (mem_Ioc.mp (hN hn)).2 : (n : ℝ) ≤ ⌊T⌋₊).trans
        (Nat.floor_le (by linarith))
    calc
      _ ≤ (fouvryTau (j + 1) ((m : ℤ) * n - a).natAbs : ℝ) :=
        sum_modEq_abs_le_fouvryTau j Q c hc m n a hne
      _ ≤ D * (((m : ℤ) * n - a).natAbs : ℝ) ^ (ε / 2) :=
        hdiv _ (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hne))
      _ ≤ A := by
        apply mul_le_mul_of_nonneg_left _ hD.le
        exact Real.rpow_le_rpow (by positivity)
          (natAbs_mul_sub_le_of_cutoff (by linarith) hMT hnT hm a ha)
          (by linarith)
  have hrow0 (m n : ℕ) : 0 ≤
      ∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0 := by
    apply sum_nonneg
    intro q _
    split_ifs <;> positivity
  have hAsq : A ^ 2 = D ^ 2 * (4 : ℝ) ^ ε * x ^ ε := by
    dsimp [A]
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 4 * x)]
    norm_num
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by linarith : 0 ≤ x)]
    ring
  calc
    _ ≤ ∑ p ∈ F, ∑ m ∈ dyadicCutoffNatSupport M,
        |β p.1 * β p.2| * scaledDyadicCutoff M m *
          (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * p.1) a then |c q| else 0) *
          (∑ r ∈ Q, if Int.ModEq r ((m : ℤ) * p.2) a then |c r| else 0) :=
      wMaskedOriginal_abs_le_pair_modulus_sums M N Q β c a P F hP
    _ ≤ ∑ p ∈ F,
        |β p.1 * β p.2| * (∑ m ∈ dyadicCutoffNatSupport M,
          scaledDyadicCutoff M m) * A ^ 2 := by
      apply sum_le_sum
      intro p hp
      rw [mul_sum, sum_mul]
      apply sum_le_sum
      intro m _
      by_cases hb₁ : β p.1 = 0
      · simp [hb₁]
      by_cases hb₂ : β p.2 = 0
      · simp [hb₂]
      by_cases hm : scaledDyadicCutoff M m = 0
      · simp [hm]
      obtain ⟨hn₁, hn₂⟩ := mem_product.mp (hF hp)
      calc
        _ = (|β p.1 * β p.2| * scaledDyadicCutoff M m) *
            ((∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * p.1) a then |c q| else 0) *
              (∑ r ∈ Q, if Int.ModEq r ((m : ℤ) * p.2) a then |c r| else 0)) := by ring
        _ ≤ (|β p.1 * β p.2| * scaledDyadicCutoff M m) * (A * A) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hrow _ _ hn₁ hb₁ hm) (hrow _ _ hn₂ hb₂ hm) (hrow0 _ _) hA)
            (mul_nonneg (abs_nonneg _) (scaledDyadicCutoff_nonneg M m))
        _ = _ := by ring
    _ ≤ ∑ p ∈ F, |β p.1 * β p.2| * (5 * M) * A ^ 2 := by
      apply sum_le_sum
      intro p _
      gcongr
      exact sum_scaledDyadicCutoff_le hM
    _ = _ := by
      rw [hAsq]
      simp only [mul_sum]
      apply sum_congr rfl
      intro p _
      ring

/-- An arbitrary modulus-dependent beta-pair mask is paid by the absolute
mass of its finite pair enclosure, without positivity or symmetry of beta. -/
theorem masked_beta_pair_abs_le_pair_mass
    (N Q : Finset ℕ) (β : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) (F : Finset (ℕ × ℕ))
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → t.2 ∈ F)
    {q r : ℕ} (hq : q ∈ reducedModuli Q a) (hr : r ∈ reducedModuli Q a) :
    |∑ p ∈ N ×ˢ N, if WCompatible q r p.1 p.2 ∧ P ((q, r), p)
      then β p.1 * β p.2 else 0| ≤
      ∑ p ∈ F, |β p.1 * β p.2| := by
  rw [← sum_filter]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp, hc, hm⟩ := mem_filter.mp hp
    exact hP ((q, r), p)
      (mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨hq, hr⟩, hp⟩, hc⟩) hm
  · intro p _ _
    exact abs_nonneg _

/-- The actual zero mode with the same mask is paid by its absolute
beta-pair mass and a logarithmic modulus sum. There is no beta divisor
bound, nondivisibility condition, symmetry, or restriction on `M` or `a`.
Unlike the original-sum row estimate, this also permits extraneous pairs
in `F`. -/
theorem wMaskedZeroMode_abs_le_pair_mass
    (j : ℕ) {L : ℝ} (hL : 1 ≤ L) (M : ℝ) (N Q : Finset ℕ)
    (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) (β c : ℕ → ℝ)
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ)
    (P : WOriginalTuple → Prop) (F : Finset (ℕ × ℕ))
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → t.2 ∈ F) :
    |wMaskedZeroMode M N Q β c a P| ≤
      |M * dyadicCutoffMass| * (∑ p ∈ F, |β p.1 * β p.2|) *
        (1 + Real.log L) ^ (2 * j ^ 2 + 1) := by
  let B : ℝ := ∑ p ∈ F, |β p.1 * β p.2|
  have hB : 0 ≤ B := sum_nonneg (fun _ _ ↦ abs_nonneg _)
  rw [wMaskedZeroMode_eq_modulus_sum, abs_mul]
  calc
    _ ≤ |M * dyadicCutoffMass| *
        ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          |c q * c r / (q.lcm r : ℝ)| * B := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro q hq
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro r hr
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (masked_beta_pair_abs_le_pair_mass N Q β a P F hP hq hr) (abs_nonneg _)
    _ = |M * dyadicCutoffMass| *
        ((∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          |c q * c r / (q.lcm r : ℝ)|) * B) := by simp only [sum_mul]
    _ ≤ |M * dyadicCutoffMass| * ((1 + Real.log L) ^ (2 * j ^ 2 + 1) * B) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply mul_le_mul_of_nonneg_right _ hB
      exact sum_abs_lcm_weight_le_log j hL (reducedModuli Q a)
        ((filter_subset _ _).trans hQ) c (fun q hq ↦ hc q (mem_filter.mp hq).1)
    _ = _ := by dsimp [B]; ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

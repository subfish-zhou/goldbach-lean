import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMaskedW
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryLargeGCDBetaMass
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryTauPointwise

/-!
# The original progression sum with a large beta gcd

An elementary substitute for Fouvry (1984), p. 235, (8.2). Modulus sums
are bounded by divisors of the nonzero differences `m*n-a`. The hypothesis
that nonzero beta coefficients have `n ∤ a` is essential: it removes the
equality term, and its preprocessing is not proved here.
-/

noncomputable section

open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The equality progression is impossible under the beta support hypothesis. -/
theorem mul_sub_ne_zero_of_not_dvd (m n : ℕ) (a : ℤ)
    (hn : ¬(n : ℤ) ∣ a) : (m : ℤ) * n - a ≠ 0 := by
  intro h
  apply hn
  exact ⟨m, by nlinarith⟩

/-- Summing arbitrary signed divisor-bounded modulus weights costs one
additional divisor order, independently of the size of the modulus set. -/
theorem sum_modEq_abs_le_fouvryTau (j : ℕ) (Q : Finset ℕ)
    (c : ℕ → ℝ)
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ))
    (m n : ℕ) (a : ℤ) (hne : (m : ℤ) * n - a ≠ 0) :
    (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) ≤
      (fouvryTau (j + 1) ((m : ℤ) * n - a).natAbs : ℝ) := by
  rw [← sum_filter, fouvryTau_succ, Nat.cast_sum]
  calc
    _ ≤ ∑ q ∈ Q.filter (fun q : ℕ ↦ Int.ModEq q ((m : ℤ) * n) a),
        (fouvryTau j q : ℝ) :=
      sum_le_sum (fun q hq ↦ hc q (mem_filter.mp hq).1)
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        obtain ⟨hq, he⟩ := mem_filter.mp hq
        apply Nat.mem_divisors.mpr
        refine ⟨?_, Int.natAbs_ne_zero.mpr hne⟩
        have hd : (q : ℤ) ∣ (m : ℤ) * n - a := Int.modEq_iff_dvd.mp he.symm
        exact_mod_cast (Int.natAbs_dvd_natAbs.mpr hd)
      · intro q _ _
        positivity

/-- Discarding compatibility and any additional mask gives a nonnegative
majorant whose two modulus sums can be paid separately. -/
theorem wMaskedOriginal_abs_le_modulus_sums
    (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) (Y : ℝ)
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.2.1.gcd t.2.2 : ℝ)) :
    |wMaskedOriginal M N Q β c a P| ≤
      ∑ p ∈ largeGCDPairs N Y, ∑ m ∈ dyadicCutoffNatSupport M,
        |β p.1 * β p.2| * scaledDyadicCutoff M m *
          (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * p.1) a then |c q| else 0) *
          (∑ r ∈ Q, if Int.ModEq r ((m : ℤ) * p.2) a then |c r| else 0) := by
  let F : WOriginalTuple → ℝ := fun t ↦ |wTupleCoefficient β c t| *
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
  have hF (t : WOriginalTuple) : 0 ≤ F t := mul_nonneg (abs_nonneg _) (hw _ _ _ _)
  calc
    _ ≤ ∑ t ∈ wMaskedTuples N Q a P, F t := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro t _
      dsimp [F]
      rw [abs_mul, abs_of_nonneg (hw _ _ _ _)]
    _ ≤ ∑ t ∈ (Q ×ˢ Q) ×ˢ largeGCDPairs N Y, F t := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨ho, hp⟩ := mem_filter.mp ht
        obtain ⟨hs, _⟩ := mem_filter.mp ho
        obtain ⟨hqr, hn⟩ := mem_product.mp hs
        obtain ⟨hq, hr⟩ := mem_product.mp hqr
        exact mem_product.mpr ⟨mem_product.mpr
          ⟨(mem_filter.mp hq).1, (mem_filter.mp hr).1⟩,
          mem_filter.mpr ⟨hn, hP t ho hp⟩⟩
      · intro t _ _
        exact hF t
    _ = _ := by
      rw [sum_product, sum_comm]
      apply sum_congr rfl
      intro p _
      simp only [sum_product, F, productProgressionWeight, mul_sum]
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

/-- The finite support enclosure costs at most five times the scale. -/
theorem sum_scaledDyadicCutoff_le {M : ℝ} (hM : 1 ≤ M) :
    (∑ m ∈ dyadicCutoffNatSupport M, scaledDyadicCutoff M m) ≤ 5 * M := by
  calc
    _ ≤ ∑ _m ∈ dyadicCutoffNatSupport M, (1 : ℝ) :=
      sum_le_sum (fun m _ ↦ scaledDyadicCutoff_le_one M m)
    _ = (⌈3 * M⌉₊ : ℝ) + 1 := by simp [dyadicCutoffNatSupport]
    _ ≤ _ := by
      have := Nat.ceil_lt_add_one (by linarith : 0 ≤ 3 * M)
      linarith

/-- The differences occurring on the actual nonzero bump support remain
uniformly bounded for all changing residues with `|a| ≤ x`. -/
theorem natAbs_mul_sub_le_of_cutoff {M T x : ℝ} (hM : 0 < M)
    (hMT : M * T ≤ x) {m n : ℕ} (hn : (n : ℝ) ≤ T)
    (hm : scaledDyadicCutoff M m ≠ 0) (a : ℤ) (ha : |(a : ℝ)| ≤ x) :
    (((m : ℤ) * n - a).natAbs : ℝ) ≤ 4 * x := by
  have hm3 := (scaledDyadicCutoff_mem_Icc_of_ne_zero hM hm).2
  have hmn : (m : ℝ) * n ≤ 3 * x := by
    calc
      _ ≤ (3 * M) * T := mul_le_mul hm3 hn (by positivity) (by positivity)
      _ ≤ 3 * x := by linarith
  calc
    _ = |(m : ℝ) * n - a| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      push_cast
      rfl
    _ ≤ |(m : ℝ) * n| + |(a : ℝ)| := abs_sub _ _
    _ ≤ 4 * x := by rw [abs_of_nonneg (by positivity)]; linarith

/-- The original progression sum is paid before invoking any beta mean.
The modulus set can even contain zero, since a nonzero difference has no
zero divisor. The fixed-order constant precedes every changing datum. -/
theorem wMaskedOriginal_abs_le_largeGCD_pair_mass (j : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T x : ℝ, 1 ≤ M → 1 ≤ T → 1 ≤ x → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ (Y : ℝ) (P : WOriginalTuple → Prop),
        (∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.2.1.gcd t.2.2 : ℝ)) →
      |wMaskedOriginal M N Q β c a P| ≤
        C * M * x ^ ε * ∑ p ∈ largeGCDPairs N Y, |β p.1 * β p.2| := by
  obtain ⟨D, hD, hdiv⟩ := fouvryTau_le_const_rpow (k := j + 1) (by omega)
    (show 0 < ε / 2 by linarith)
  refine ⟨5 * D ^ 2 * (4 : ℝ) ^ ε, by positivity, ?_⟩
  intro M T x hM hT hx hMT N Q hN β c hc a ha hsupport Y P hP
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
    _ ≤ ∑ p ∈ largeGCDPairs N Y, ∑ m ∈ dyadicCutoffNatSupport M,
        |β p.1 * β p.2| * scaledDyadicCutoff M m *
          (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * p.1) a then |c q| else 0) *
          (∑ r ∈ Q, if Int.ModEq r ((m : ℤ) * p.2) a then |c r| else 0) :=
      wMaskedOriginal_abs_le_modulus_sums M N Q β c a P Y hP
    _ ≤ ∑ p ∈ largeGCDPairs N Y,
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
      obtain ⟨hn₁, hn₂⟩ := mem_product.mp (mem_filter.mp hp).1
      calc
        _ = (|β p.1 * β p.2| * scaledDyadicCutoff M m) *
            ((∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * p.1) a then |c q| else 0) *
              (∑ r ∈ Q, if Int.ModEq r ((m : ℤ) * p.2) a then |c r| else 0)) := by ring
        _ ≤ (|β p.1 * β p.2| * scaledDyadicCutoff M m) * (A * A) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hrow _ _ hn₁ hb₁ hm) (hrow _ _ hn₂ hb₂ hm) (hrow0 _ _) hA)
            (mul_nonneg (abs_nonneg _) (scaledDyadicCutoff_nonneg M m))
        _ = _ := by ring
    _ ≤ ∑ p ∈ largeGCDPairs N Y, |β p.1 * β p.2| * (5 * M) * A ^ 2 := by
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

/-- Uniform large-beta-gcd exclusion for the ORIGINAL smoothed progression
sum. This uses the elementary inverse-square-root pair-mass saving, not
an estimate for its zero mode or a presumed distribution theorem. -/
theorem wMaskedOriginal_abs_le_largeGCD
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T Y x : ℝ,
      1 ≤ M → 1 ≤ T → 0 < Y → 1 ≤ x → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
        (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
        (∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.2.1.gcd t.2.2 : ℝ)) →
      |wMaskedOriginal M N Q β c a P| ≤ C * M * x ^ ε *
        (T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
          Real.sqrt ((1 + Real.log T) / Y)) := by
  obtain ⟨C, hC, hb⟩ := wMaskedOriginal_abs_le_largeGCD_pair_mass j hε
  refine ⟨C, hC, ?_⟩
  intro M T Y x hM hT hY hx hMT N Q hN β c hβ hc a ha hs P hP
  exact (hb M T x hM hT hx hMT N Q hN β c hc a ha hs Y P hP).trans
    (mul_le_mul_of_nonneg_left (sum_abs_largeGCDPairs_le hk hT hY N hN β hβ)
      (by positivity))

/-- Direct specialization to the first large-gcd exclusion. -/
theorem wLargeBetaGCDOriginal_abs_le
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T Y x : ℝ,
      1 ≤ M → 1 ≤ T → 0 < Y → 1 ≤ x → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
        (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      |wMaskedOriginal M N Q β c a (fun t ↦ Y < (t.2.1.gcd t.2.2 : ℝ))| ≤
        C * M * x ^ ε *
          (T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
            Real.sqrt ((1 + Real.log T) / Y)) := by
  obtain ⟨C, hC, hb⟩ := wMaskedOriginal_abs_le_largeGCD hk j hε
  refine ⟨C, hC, ?_⟩
  intro M T Y x hM hT hY hx hMT N Q hN β c hβ hc a ha hs
  exact hb M T Y x hM hT hY hx hMT N Q hN β c hβ hc a ha hs _
    (fun _ _ h ↦ h)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

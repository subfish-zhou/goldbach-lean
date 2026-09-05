

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIActualDyadic

/-!
 # Exact Vaughan Type-I decomposition into actual dyadic long rows
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

private lemma first_row_prefix_square
    (d y q : ℕ) (χ : PrimitiveCharacter q) :
    ‖∑ m ∈ Finset.Icc 1 (y / d),
        (Real.log (m : ℝ) : ℂ) * χ.1 (m : ZMod q)‖ ^ 2 =
      primitiveCharacterPrefixSquare
        (vaughanTypeIFirstRowCoeff (fun _ => 1) d) 0 (y / d) q χ := by
  unfold primitiveCharacterPrefixSquare vaughanTypeIFirstRowCoeff
  simp only [zero_add]
  have hsum := sum_Ioc_nat_eq_sum_Icc_int 0 0 (y / d)
    (fun z => ((Real.log (z.toNat : ℝ) : ℂ) * χ.1 (z : ZMod q)))
  have hset : Finset.Ioc 0 (y / d) = Finset.Icc 1 (y / d) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset] at hsum
  simpa using congrArg norm hsum

private lemma middle_row_prefix_square
    (d e y q : ℕ) (χ : PrimitiveCharacter q) :
    ‖∑ m ∈ Finset.Icc 1 (y / (d * e)), χ.1 (m : ZMod q)‖ ^ 2 =
      primitiveCharacterPrefixSquare
        (vaughanTypeIMiddlePairRowCoeff (fun _ => 1) (d, e)) 0
          (y / (d * e)) q χ := by
  unfold primitiveCharacterPrefixSquare vaughanTypeIMiddlePairRowCoeff
  simp only [zero_add]
  have hsum := sum_Ioc_nat_eq_sum_Icc_int 0 0 (y / (d * e))
    (fun z => χ.1 (z : ZMod q))
  have hset : Finset.Ioc 0 (y / (d * e)) = Finset.Icc 1 (y / (d * e)) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset] at hsum
  simpa using congrArg norm hsum

private lemma first_row_prefix_norm_le
    {N y d q : ℕ} (hy : y ≤ N) (χ : PrimitiveCharacter q) :
    ‖∑ m ∈ Finset.Icc 1 (y / d),
        (Real.log (m : ℝ) : ℂ) * χ.1 (m : ZMod q)‖ ≤
      Real.sqrt (primitiveCharacterPrefixMaxSquare
        (vaughanTypeIFirstRowCoeff (fun _ => 1) d) 0 (N / d) q χ) := by
  rw [← Real.sqrt_sq (norm_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [first_row_prefix_square]
  exact primitiveCharacterPrefixSquare_le_max _ _ (Nat.div_le_div_right hy) χ

private lemma middle_row_prefix_norm_le
    {N y d e q : ℕ} (hy : y ≤ N) (χ : PrimitiveCharacter q) :
    ‖∑ m ∈ Finset.Icc 1 (y / (d * e)), χ.1 (m : ZMod q)‖ ≤
      Real.sqrt (primitiveCharacterPrefixMaxSquare
        (vaughanTypeIMiddlePairRowCoeff (fun _ => 1) (d, e)) 0
          (N / (d * e)) q χ) := by
  rw [← Real.sqrt_sq (norm_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [middle_row_prefix_square]
  exact primitiveCharacterPrefixSquare_le_max _ _ (Nat.div_le_div_right hy) χ

theorem norm_vaughanTypeIFirstLong_le
    {N y u q : ℕ} (hy : y ≤ N) (χ : PrimitiveCharacter q) :
    ‖vaughanTypeIFirstLong (fun _ => 1) y u q χ‖ ≤
      ∑ d ∈ Finset.Icc 1 u,
        ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ *
          Real.sqrt (primitiveCharacterPrefixMaxSquare
            (vaughanTypeIFirstRowCoeff (fun _ => 1) d) 0 (N / d) q χ) := by
  unfold vaughanTypeIFirstLong
  simp only [one_mul]
  calc
    _ ≤ ∑ d ∈ vaughanTypeIShortRange y u,
        ‖((((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ.1 (d : ZMod q)) *
          ∑ m ∈ Finset.Icc 1 (y / d),
            ((Real.log (m : ℝ) : ℂ) * χ.1 (m : ZMod q)))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ vaughanTypeIShortRange y u,
        ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ *
          Real.sqrt (primitiveCharacterPrefixMaxSquare
            (vaughanTypeIFirstRowCoeff (fun _ => 1) d) 0 (N / d) q χ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, norm_mul]
      calc
        _ ≤ ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ * 1 *
            ‖∑ m ∈ Finset.Icc 1 (y / d),
              ((Real.log (m : ℝ) : ℂ) * χ.1 (m : ZMod q))‖ := by
          gcongr
          exact χ.1.norm_le_one _
        _ = ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ *
            ‖∑ m ∈ Finset.Icc 1 (y / d),
              ((Real.log (m : ℝ) : ℂ) * χ.1 (m : ZMod q))‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (first_row_prefix_norm_le hy χ) (norm_nonneg _)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr
          ⟨(mem_vaughanTypeIShortRange.mp hd).1,
            (mem_vaughanTypeIShortRange.mp hd).2.2⟩
      · intro d hd hnot
        positivity

/-- The complete middle row is bounded by its fully summed `(d,e)` prefix
amplitude.  This is public because the whole-first-row Type-I decomposition
must split before applying triangle only to the middle lane. -/
theorem norm_vaughanTypeIMiddleLong_le
    {N y u v q : ℕ} (hy : y ≤ N) (χ : PrimitiveCharacter q) :
    ‖vaughanTypeIMiddleLong (fun _ => 1) y u v q χ‖ ≤
      ∑ de ∈ Finset.Icc 1 u ×ˢ Finset.Icc 1 v,
        ‖(((ArithmeticFunction.moebius de.1 : ℤ) : ℂ))‖ *
          ‖(ArithmeticFunction.vonMangoldt de.2 : ℂ)‖ *
          Real.sqrt (primitiveCharacterPrefixMaxSquare
            (vaughanTypeIMiddlePairRowCoeff (fun _ => 1) de) 0
              (N / (de.1 * de.2)) q χ) := by
  unfold vaughanTypeIMiddleLong
  simp only [one_mul]
  calc
    _ ≤ ∑ d ∈ vaughanTypeIShortRange y u,
        ‖∑ e ∈ vaughanTypeIShortRange y v,
          (((((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              (ArithmeticFunction.vonMangoldt e : ℂ)) *
              χ.1 (d : ZMod q) * χ.1 (e : ZMod q)) *
            ∑ m ∈ Finset.Icc 1 (y / (d * e)), χ.1 (m : ZMod q))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ vaughanTypeIShortRange y u,
        ∑ e ∈ vaughanTypeIShortRange y v,
          ‖(((((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              (ArithmeticFunction.vonMangoldt e : ℂ)) *
              χ.1 (d : ZMod q) * χ.1 (e : ZMod q)) *
            ∑ m ∈ Finset.Icc 1 (y / (d * e)), χ.1 (m : ZMod q))‖ := by
      apply Finset.sum_le_sum
      intro d hd
      exact norm_sum_le _ _
    _ ≤ ∑ d ∈ vaughanTypeIShortRange y u,
        ∑ e ∈ vaughanTypeIShortRange y v,
          ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ *
            ‖(ArithmeticFunction.vonMangoldt e : ℂ)‖ *
            Real.sqrt (primitiveCharacterPrefixMaxSquare
              (vaughanTypeIMiddlePairRowCoeff (fun _ => 1) (d, e)) 0
                (N / (d * e)) q χ) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      simp only [norm_mul]
      calc
        _ ≤ ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ *
              ‖(ArithmeticFunction.vonMangoldt e : ℂ)‖ * 1 * 1 *
            ‖∑ m ∈ Finset.Icc 1 (y / (d * e)), χ.1 (m : ZMod q)‖ := by
          gcongr
          · exact χ.1.norm_le_one _
          · exact χ.1.norm_le_one _
        _ = ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ *
              ‖(ArithmeticFunction.vonMangoldt e : ℂ)‖ *
            ‖∑ m ∈ Finset.Icc 1 (y / (d * e)), χ.1 (m : ZMod q)‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (middle_row_prefix_norm_le hy χ)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ∑ de ∈ vaughanTypeIShortRange y u ×ˢ vaughanTypeIShortRange y v,
          ‖(((ArithmeticFunction.moebius de.1 : ℤ) : ℂ))‖ *
            ‖(ArithmeticFunction.vonMangoldt de.2 : ℂ)‖ *
            Real.sqrt (primitiveCharacterPrefixMaxSquare
              (vaughanTypeIMiddlePairRowCoeff (fun _ => 1) de) 0
                (N / (de.1 * de.2)) q χ) := by rw [Finset.sum_product]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro de hde
        rw [Finset.mem_product] at hde ⊢
        exact ⟨Finset.mem_Icc.mpr
            ⟨(mem_vaughanTypeIShortRange.mp hde.1).1,
              (mem_vaughanTypeIShortRange.mp hde.1).2.2⟩,
          Finset.mem_Icc.mpr
            ⟨(mem_vaughanTypeIShortRange.mp hde.2).1,
              (mem_vaughanTypeIShortRange.mp hde.2).2.2⟩⟩
      · intro de hde hnot
        positivity

/-- For each primitive character, the maximum over all Vaughan Type-I prefixes
is bounded by the sum of the complete first and middle long-row maxima. -/
theorem primitivePrefixAmplitude_vaughanTypeI_le_rows
    (N u v q : ℕ) (χ : PrimitiveCharacter q) :
    primitivePrefixAmplitude
        (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N q χ ≤
      (∑ d ∈ Finset.Icc 1 u,
        ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ *
          Real.sqrt (primitiveCharacterPrefixMaxSquare
            (vaughanTypeIFirstRowCoeff (fun _ => 1) d) 0 (N / d) q χ)) +
      ∑ de ∈ Finset.Icc 1 u ×ˢ Finset.Icc 1 v,
        ‖(((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
          (ArithmeticFunction.vonMangoldt de.2 : ℂ))‖ *
          Real.sqrt (primitiveCharacterPrefixMaxSquare
            (vaughanTypeIMiddlePairRowCoeff (fun _ => 1) de) 0
              (N / (de.1 * de.2)) q χ) := by
  let R1 : ℝ := ∑ d ∈ Finset.Icc 1 u,
    ‖(((ArithmeticFunction.moebius d : ℤ) : ℂ))‖ *
      Real.sqrt (primitiveCharacterPrefixMaxSquare
        (vaughanTypeIFirstRowCoeff (fun _ => 1) d) 0 (N / d) q χ)
  let R2 : ℝ := ∑ de ∈ Finset.Icc 1 u ×ˢ Finset.Icc 1 v,
    ‖(((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
      (ArithmeticFunction.vonMangoldt de.2 : ℂ))‖ *
      Real.sqrt (primitiveCharacterPrefixMaxSquare
        (vaughanTypeIMiddlePairRowCoeff (fun _ => 1) de) 0
          (N / (de.1 * de.2)) q χ)
  have hR1 : 0 ≤ R1 := by dsimp [R1]; positivity
  have hR2 : 0 ≤ R2 := by dsimp [R2]; positivity
  change Real.sqrt (primitiveCharacterPrefixMaxSquare
    (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) 0 N q χ) ≤ R1 + R2
  rw [← Real.sqrt_sq (add_nonneg hR1 hR2)]
  apply Real.sqrt_le_sqrt
  unfold primitiveCharacterPrefixMaxSquare
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := by simpa [Finset.mem_range] using hy
  have hcoeff : vaughanTypeICoeff vaughanUnitIntegerCoeff u v =
      vaughanTypeILongCoeff vaughanUnitIntegerCoeff u v := rfl
  rw [hcoeff]
  have hsq := primitiveCharacterPrefixSquare_typeI_eq_long
    vaughanUnitIntegerCoeff y u v q χ
  rw [hsq]
  simp only [vaughanUnitIntegerCoeff]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  calc
    ‖vaughanTypeILongPrefix (fun _ => 1) y u v q χ‖ ≤
        ‖vaughanTypeIFirstLong (fun _ => 1) y u q χ‖ +
          ‖vaughanTypeIMiddleLong (fun _ => 1) y u v q χ‖ := by
      exact norm_sub_le _ _
    _ ≤ R1 + R2 := add_le_add
      (norm_vaughanTypeIFirstLong_le hyN χ)
      (by
        simpa only [R2, norm_mul] using
          norm_vaughanTypeIMiddleLong_le hyN χ)

/-- The first dyadic shells partition the complete positive short range exactly. -/
theorem sum_vaughanTypeIFirstDyadicShell
    {M : Type*} [AddCommMonoid M] (u : ℕ) (f : ℕ → M) :
    (∑ k ∈ Finset.range (Nat.log2 u + 1),
      ∑ d ∈ vaughanTypeIFirstDyadicShell u k, f d) =
      ∑ d ∈ Finset.Icc 1 u, f d := by
  let K := Nat.log2 u + 1
  let g : ℕ → Fin K := fun d =>
    ⟨Nat.log2 d % K, Nat.mod_lt _ (by dsimp [K]; omega)⟩
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => ∑ d ∈ vaughanTypeIFirstDyadicShell u k, f d) K]
  calc
    (∑ k : Fin K, ∑ d ∈ vaughanTypeIFirstDyadicShell u k, f d) =
        ∑ k : Fin K, ∑ d ∈ (Finset.Icc 1 u).filter (fun d => g d = k), f d := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr
      · ext d
        by_cases hd : d ∈ Finset.Icc 1 u
        · have hd' := Finset.mem_Icc.mp hd
          have hidx : Nat.log2 d < K := by
            dsimp [K]
            exact firstDyadicShell_index_lt
              (mem_own_vaughanTypeIFirstDyadicShell (by omega) hd'.2)
          have hmod : Nat.log2 d % K = Nat.log2 d := Nat.mod_eq_of_lt hidx
          simp [vaughanTypeIFirstDyadicShell, g, hd, hmod]
          constructor
          · intro h
            apply Fin.ext
            exact h
          · intro h
            exact congrArg Fin.val h
        · simp [vaughanTypeIFirstDyadicShell, hd]
      · intro d hd
        rfl
    _ = _ := Finset.sum_fiberwise (Finset.Icc 1 u) g f

/-- Product-dyadic shells partition the complete positive `(d,e)` rectangle
exactly, with the shell selected by the actual product `d*e`. -/
theorem sum_vaughanTypeIMiddleProductDyadicShell
    {M : Type*} [AddCommMonoid M] (u v : ℕ) (f : ℕ × ℕ → M) :
    (∑ k ∈ Finset.range (Nat.log2 (u * v) + 1),
      ∑ de ∈ vaughanTypeIMiddleProductDyadicShell u v k, f de) =
      ∑ de ∈ Finset.Icc 1 u ×ˢ Finset.Icc 1 v, f de := by
  let K := Nat.log2 (u * v) + 1
  let g : ℕ × ℕ → Fin K := fun de =>
    ⟨Nat.log2 (de.1 * de.2) % K, Nat.mod_lt _ (by dsimp [K]; omega)⟩
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => ∑ de ∈ vaughanTypeIMiddleProductDyadicShell u v k, f de) K]
  calc
    (∑ k : Fin K, ∑ de ∈ vaughanTypeIMiddleProductDyadicShell u v k, f de) =
        ∑ k : Fin K,
          ∑ de ∈ (Finset.Icc 1 u ×ˢ Finset.Icc 1 v).filter (fun de => g de = k),
            f de := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr
      · ext de
        by_cases hde : de ∈ Finset.Icc 1 u ×ˢ Finset.Icc 1 v
        · have hde' := Finset.mem_product.mp hde
          have hd := Finset.mem_Icc.mp hde'.1
          have he := Finset.mem_Icc.mp hde'.2
          have hidx : Nat.log2 (de.1 * de.2) < K := by
            dsimp [K]
            exact middleProductDyadicShell_index_lt
              (mem_own_vaughanTypeIMiddleProductDyadicShell
                (by omega) hd.2 (by omega) he.2)
          have hmod : Nat.log2 (de.1 * de.2) % K =
              Nat.log2 (de.1 * de.2) := Nat.mod_eq_of_lt hidx
          simp [vaughanTypeIMiddleProductDyadicShell, g, hde, hmod]
          constructor
          · intro h
            apply Fin.ext
            exact h
          · intro h
            exact congrArg Fin.val h
        · simp [vaughanTypeIMiddleProductDyadicShell, hde]
      · intro de hde
        rfl
    _ = _ := Finset.sum_fiberwise (Finset.Icc 1 u ×ˢ Finset.Icc 1 v) g f

end

end AnalyticNumberTheory.LargeSieve

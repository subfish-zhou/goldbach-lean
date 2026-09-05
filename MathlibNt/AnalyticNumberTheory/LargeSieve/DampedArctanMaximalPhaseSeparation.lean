

import MathlibNt.AnalyticNumberTheory.LargeSieve.DampedArctanRankOneSeparation

/-!
 # Y-uniform phase separation for the damped arctangent kernel

This leaf separates the half-step parameter `y` from both coefficient
sequences.  The four coefficient twists below are independent of `y`, so the
selector `Y q χ` may be chosen separately for every primitive character before
one applies the rectangular rank-one mean theorem.  No maximal-mean estimate is
claimed here.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- The `y`-independent cosine coefficient twist. -/
def phaseCosTwist (a : ℤ → ℂ) (t : ℝ) (m : ℤ) : ℂ :=
  a m * (Real.cos (t * Real.log (m : ℝ)) : ℂ)

/-- The `y`-independent sine coefficient twist. -/
def phaseSinTwist (a : ℤ → ℂ) (t : ℝ) (m : ℤ) : ℂ :=
  a m * (Real.sin (t * Real.log (m : ℝ)) : ℂ)

/-- One rectangular rank-one character product. -/
def phaseRankOneCharacterProduct
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), a m * χ.1 (m : ZMod q)) *
    (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), b n * χ.1 (n : ZMod q))

/-- The direct positive-frequency logarithmic kernel on a rectangle. -/
def dampedLogRectangularCharacterSum
    (a b : ℤ → ℂ) (y t : ℝ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
    ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
      a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
        (Real.sin (t * Real.log (y / ((m * n : ℤ) : ℝ))) / t : ℂ)

/-- Exact `sin (A-B-C)` expansion into four rank-one products. -/
theorem damped_log_term_eq_four_rankOne
    (a b : ℤ → ℂ) {y t : ℝ} {m n : ℤ} {q : ℕ}
    (χ : PrimitiveCharacter q) (hy : 0 < y) (hm : 0 < m) (hn : 0 < n)
    (_ht : 0 < t) :
    a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
        (Real.sin (t * Real.log (y / ((m * n : ℤ) : ℝ))) / t : ℂ) =
      (1 / (t : ℂ)) *
        (((Real.sin (t * Real.log y) : ℂ) *
              (phaseCosTwist a t m * χ.1 (m : ZMod q)) *
              (phaseCosTwist b t n * χ.1 (n : ZMod q))) -
          ((Real.cos (t * Real.log y) : ℂ) *
              (phaseSinTwist a t m * χ.1 (m : ZMod q)) *
              (phaseCosTwist b t n * χ.1 (n : ZMod q))) -
          ((Real.cos (t * Real.log y) : ℂ) *
              (phaseCosTwist a t m * χ.1 (m : ZMod q)) *
              (phaseSinTwist b t n * χ.1 (n : ZMod q))) -
          ((Real.sin (t * Real.log y) : ℂ) *
              (phaseSinTwist a t m * χ.1 (m : ZMod q)) *
              (phaseSinTwist b t n * χ.1 (n : ZMod q)))) := by
  rw [log_div_int_mul_eq_sub_log_sub_log hy hm hn]
  rw [show t * ((Real.log y - Real.log (m : ℝ)) - Real.log (n : ℝ)) =
      t * Real.log y - t * Real.log (m : ℝ) - t * Real.log (n : ℝ) by ring]
  rw [Real.sin_sub, Real.sin_sub, Real.cos_sub]
  simp only [phaseCosTwist, phaseSinTwist]
  rw [Int.cast_mul, map_mul]
  push_cast
  field_simp
  ring

/-- Exact four-product separation of the whole rectangle. -/
theorem dampedLogRectangularCharacterSum_eq_four_rankOne
    (a b : ℤ → ℂ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t)
    (Ma Mb : ℤ) (Na Nb q : ℕ) (χ : PrimitiveCharacter q)
    (hm : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 0 < m)
    (hn : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < n) :
    dampedLogRectangularCharacterSum a b y t Ma Mb Na Nb q χ =
      (1 / (t : ℂ)) *
        (((Real.sin (t * Real.log y) : ℂ) *
            phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
              Ma Mb Na Nb q χ) -
          ((Real.cos (t * Real.log y) : ℂ) *
            phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
              Ma Mb Na Nb q χ) -
          ((Real.cos (t * Real.log y) : ℂ) *
            phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
              Ma Mb Na Nb q χ) -
          ((Real.sin (t * Real.log y) : ℂ) *
            phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
              Ma Mb Na Nb q χ)) := by
  have hprod (c d : ℤ → ℂ) :
      phaseRankOneCharacterProduct c d Ma Mb Na Nb q χ =
        ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
          ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
            (c m * χ.1 (m : ZMod q)) * (d n * χ.1 (n : ZMod q)) := by
    unfold phaseRankOneCharacterProduct
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hmm
    rw [Finset.mul_sum]
  unfold dampedLogRectangularCharacterSum
  calc
    (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
          a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
            (Real.sin (t * Real.log (y / ((m * n : ℤ) : ℝ))) / t : ℂ)) =
      ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
          (1 / (t : ℂ)) *
            (((Real.sin (t * Real.log y) : ℂ) *
                (phaseCosTwist a t m * χ.1 (m : ZMod q)) *
                (phaseCosTwist b t n * χ.1 (n : ZMod q))) -
              ((Real.cos (t * Real.log y) : ℂ) *
                (phaseSinTwist a t m * χ.1 (m : ZMod q)) *
                (phaseCosTwist b t n * χ.1 (n : ZMod q))) -
              ((Real.cos (t * Real.log y) : ℂ) *
                (phaseCosTwist a t m * χ.1 (m : ZMod q)) *
                (phaseSinTwist b t n * χ.1 (n : ZMod q))) -
              ((Real.sin (t * Real.log y) : ℂ) *
                (phaseSinTwist a t m * χ.1 (m : ZMod q)) *
                (phaseSinTwist b t n * χ.1 (n : ZMod q)))) := by
        apply Finset.sum_congr rfl
        intro m hmm
        apply Finset.sum_congr rfl
        intro n hnn
        exact damped_log_term_eq_four_rankOne a b χ hy (hm m hmm) (hn n hnn) ht
    _ = _ := by
      rw [hprod, hprod, hprod, hprod]
      simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      ring

/-- Pointwise absolute-value control by the four rank-one character products.
The `y`-dependent factors occur only through their absolute values. -/
theorem norm_dampedLogRectangularCharacterSum_le_four_rankOne
    (a b : ℤ → ℂ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t)
    (Ma Mb : ℤ) (Na Nb q : ℕ) (χ : PrimitiveCharacter q)
    (hm : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 0 < m)
    (hn : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < n) :
    ‖dampedLogRectangularCharacterSum a b y t Ma Mb Na Nb q χ‖ ≤
      (1 / t) *
        (|Real.sin (t * Real.log y)| *
            ‖phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
              Ma Mb Na Nb q χ‖ +
          |Real.cos (t * Real.log y)| *
            ‖phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
              Ma Mb Na Nb q χ‖ +
          |Real.cos (t * Real.log y)| *
            ‖phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
              Ma Mb Na Nb q χ‖ +
          |Real.sin (t * Real.log y)| *
            ‖phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
              Ma Mb Na Nb q χ‖) := by
  rw [dampedLogRectangularCharacterSum_eq_four_rankOne a b hy ht Ma Mb Na Nb q χ hm hn]
  rw [norm_mul]
  simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖(Real.sin (t * Real.log y) : ℂ) *
          phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
            Ma Mb Na Nb q χ -
        (Real.cos (t * Real.log y) : ℂ) *
          phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
            Ma Mb Na Nb q χ -
        (Real.cos (t * Real.log y) : ℂ) *
          phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
            Ma Mb Na Nb q χ -
        (Real.sin (t * Real.log y) : ℂ) *
          phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
            Ma Mb Na Nb q χ‖ ≤
      ‖(Real.sin (t * Real.log y) : ℂ) *
          phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
            Ma Mb Na Nb q χ‖ +
      ‖(Real.cos (t * Real.log y) : ℂ) *
          phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
            Ma Mb Na Nb q χ‖ +
      ‖(Real.cos (t * Real.log y) : ℂ) *
          phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
            Ma Mb Na Nb q χ‖ +
      ‖(Real.sin (t * Real.log y) : ℂ) *
          phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
            Ma Mb Na Nb q χ‖ := by
        calc
          ‖_ - _‖ ≤ ‖(Real.sin (t * Real.log y) : ℂ) *
              phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
                Ma Mb Na Nb q χ -
            (Real.cos (t * Real.log y) : ℂ) *
              phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
                Ma Mb Na Nb q χ -
            (Real.cos (t * Real.log y) : ℂ) *
              phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
                Ma Mb Na Nb q χ‖ +
            ‖(Real.sin (t * Real.log y) : ℂ) *
              phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
                Ma Mb Na Nb q χ‖ := norm_sub_le _ _
          _ ≤ (‖(Real.sin (t * Real.log y) : ℂ) *
              phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
                Ma Mb Na Nb q χ -
            (Real.cos (t * Real.log y) : ℂ) *
              phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
                Ma Mb Na Nb q χ‖ +
            ‖(Real.cos (t * Real.log y) : ℂ) *
              phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
                Ma Mb Na Nb q χ‖) +
            ‖(Real.sin (t * Real.log y) : ℂ) *
              phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
                Ma Mb Na Nb q χ‖ := by gcongr; exact norm_sub_le _ _
          _ ≤ _ := by gcongr; exact norm_sub_le _ _
    _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Uniform half-step sine bound for the separately chosen phase. -/
theorem abs_sin_log_halfstep_le
    {M : ℕ} (hM : 3 ≤ M) {y t : ℝ}
    (hy0 : 1 / 2 ≤ y) (hyM : y ≤ (M : ℝ) + 1 / 2) (ht : 0 < t) :
    |Real.sin (t * Real.log y)| ≤ min 1 (2 * Real.log (M : ℝ) * t) := by
  have hlog : |Real.log y| ≤ 2 * Real.log (M : ℝ) := by
    have h := abs_log_div_int_le_two_log hM hy0 hyM (m := (1 : ℤ)) (by norm_num)
      (by exact_mod_cast (le_trans (by norm_num) hM))
    simpa using h
  apply le_min (Real.abs_sin_le_one _)
  calc
    |Real.sin (t * Real.log y)| ≤ |t * Real.log y| := Real.abs_sin_le_abs
    _ = t * |Real.log y| := by rw [abs_mul, abs_of_pos ht]
    _ ≤ t * (2 * Real.log (M : ℝ)) := mul_le_mul_of_nonneg_left hlog ht.le
    _ = 2 * Real.log (M : ℝ) * t := by ring

/-- Uniform positive-integer sine bound for either coefficient coordinate. -/
theorem abs_sin_log_int_le
    {M : ℕ} (hM : 1 ≤ M) {m : ℤ} (hm1 : 1 ≤ m) (hmM : m ≤ (M : ℤ))
    {t : ℝ} (ht : 0 < t) :
    |Real.sin (t * Real.log (m : ℝ))| ≤ min 1 (Real.log (M : ℝ) * t) := by
  have hlog := abs_log_int_le_log hM hm1 hmM
  apply le_min (Real.abs_sin_le_one _)
  calc
    |Real.sin (t * Real.log (m : ℝ))| ≤ |t * Real.log (m : ℝ)| := Real.abs_sin_le_abs
    _ = t * |Real.log (m : ℝ)| := by rw [abs_mul, abs_of_pos ht]
    _ ≤ t * Real.log (M : ℝ) := mul_le_mul_of_nonneg_left hlog ht.le
    _ = Real.log (M : ℝ) * t := by ring

/-- Uniform cosine bound, used for `y`, `m`, and `n`. -/
theorem abs_cos_phase_le_one (x : ℝ) : |Real.cos x| ≤ 1 :=
  Real.abs_cos_le_one x

/-- `Y` may select a different half-step for every primitive character.  The
result is the pointwise interface needed before summing and invoking
`rankOneRectangularWeightedPrimitiveMean_le` separately on the four fixed
coefficient pairs. -/
theorem norm_dampedLogRectangularCharacterSum_le_four_rankOne_of_selector
    (a b : ℤ → ℂ) {M : ℕ} (hM : 3 ≤ M)
    (Y : (q : ℕ) → PrimitiveCharacter q → ℝ) {t : ℝ} (ht : 0 < t)
    (Ma Mb : ℤ) (Na Nb q : ℕ) (χ : PrimitiveCharacter q)
    (hY0 : ∀ q χ, 1 / 2 ≤ Y q χ)
    (hYM : ∀ q χ, Y q χ ≤ (M : ℝ) + 1 / 2)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (_hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ))
    (hn1 : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 1 ≤ n)
    (_hnM : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), n ≤ (M : ℤ)) :
    ‖dampedLogRectangularCharacterSum a b (Y q χ) t Ma Mb Na Nb q χ‖ ≤
      (1 / t) *
        (min 1 (2 * Real.log (M : ℝ) * t) *
            ‖phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
              Ma Mb Na Nb q χ‖ +
          ‖phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
              Ma Mb Na Nb q χ‖ +
          ‖phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
              Ma Mb Na Nb q χ‖ +
          min 1 (2 * Real.log (M : ℝ) * t) *
            ‖phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
              Ma Mb Na Nb q χ‖) := by
  have hbase := norm_dampedLogRectangularCharacterSum_le_four_rankOne
    a b (lt_of_lt_of_le (by norm_num) (hY0 q χ)) ht Ma Mb Na Nb q χ
    (fun m hm => lt_of_lt_of_le (by norm_num) (hm1 m hm))
    (fun n hn => lt_of_lt_of_le (by norm_num) (hn1 n hn))
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hs := abs_sin_log_halfstep_le hM (hY0 q χ) (hYM q χ) ht
  have hc := Real.abs_cos_le_one (t * Real.log (Y q χ))
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_right hs (norm_nonneg
          (phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
            Ma Mb Na Nb q χ))
      · simpa using mul_le_mul_of_nonneg_right hc (norm_nonneg
          (phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
            Ma Mb Na Nb q χ))
    · simpa using mul_le_mul_of_nonneg_right hc (norm_nonneg
        (phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
          Ma Mb Na Nb q χ))
  · exact mul_le_mul_of_nonneg_right hs (norm_nonneg
      (phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
        Ma Mb Na Nb q χ))

/-- Coefficient sine twists have the uniform `log M` energy loss needed by
the rank-one mean theorem. -/
theorem sum_norm_sq_phaseSinTwist_Icc_le
    (a : ℤ → ℂ) (t : ℝ) (Ma : ℤ) (Na M : ℕ)
    (hM : 1 ≤ M)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ)) :
    ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖phaseSinTwist a t m‖ ^ 2 ≤
      (min 1 (Real.log (M : ℝ) * |t|)) ^ 2 *
        ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2 := by
  simpa only [phaseSinTwist, rightSinTwist] using
    sum_norm_sq_rightSinTwist_Icc_le a t Ma Na M hM hm1 hmM

/-- Coefficient cosine twists do not enlarge energy. -/
theorem sum_norm_sq_phaseCosTwist_le
    (a : ℤ → ℂ) (t : ℝ) (s : Finset ℤ) :
    ∑ m ∈ s, ‖phaseCosTwist a t m‖ ^ 2 ≤ ∑ m ∈ s, ‖a m‖ ^ 2 := by
  simpa only [phaseCosTwist, rightCosTwist] using sum_norm_sq_rightCosTwist_le a t s

/-- Weighted selector mean.  This is not a prefix maximum; it is only the
phase-separated finite rectangular quantity to be connected to one later. -/
def selectorDampedLogRectangularWeightedMean
    (a b : ℤ → ℂ) (Y : (q : ℕ) → PrimitiveCharacter q → ℝ) (t : ℝ)
    (Ma Mb : ℤ) (Na Nb : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q,
      ‖dampedLogRectangularCharacterSum a b (Y q χ) t Ma Mb Na Nb q χ‖

/-- Even when every character chooses its own `y`, the uniform phase bounds
reduce the weighted selector mean to the same four `y`-independent rank-one
means.  Each term on the right is directly consumable by
`rankOneRectangularWeightedPrimitiveMean_le`. -/
theorem selectorDampedLogRectangularWeightedMean_le_four_rankOne
    (a b : ℤ → ℂ) {M : ℕ} (hM : 3 ≤ M)
    (Y : (q : ℕ) → PrimitiveCharacter q → ℝ) {t : ℝ} (ht : 0 < t)
    (Ma Mb : ℤ) (Na Nb : ℕ) (S : Finset ℕ)
    (hY0 : ∀ q χ, 1 / 2 ≤ Y q χ)
    (hYM : ∀ q χ, Y q χ ≤ (M : ℝ) + 1 / 2)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ))
    (hn1 : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 1 ≤ n)
    (hnM : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), n ≤ (M : ℤ)) :
    selectorDampedLogRectangularWeightedMean a b Y t Ma Mb Na Nb S ≤
      (1 / t) *
        (min 1 (2 * Real.log (M : ℝ) * t) *
            rankOneRectangularWeightedPrimitiveMean
              (phaseCosTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S +
          rankOneRectangularWeightedPrimitiveMean
              (phaseSinTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S +
          rankOneRectangularWeightedPrimitiveMean
              (phaseCosTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S +
          min 1 (2 * Real.log (M : ℝ) * t) *
            rankOneRectangularWeightedPrimitiveMean
              (phaseSinTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S) := by
  let d : ℝ := min 1 (2 * Real.log (M : ℝ) * t)
  have hmean (c e : ℤ → ℂ) :
      (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖phaseRankOneCharacterProduct c e Ma Mb Na Nb q χ‖) =
        rankOneRectangularWeightedPrimitiveMean c e Ma Mb Na Nb S := by
    unfold phaseRankOneCharacterProduct rankOneRectangularWeightedPrimitiveMean
    simp only [norm_mul]
  unfold selectorDampedLogRectangularWeightedMean
  calc
    (∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : PrimitiveCharacter q,
          ‖dampedLogRectangularCharacterSum a b (Y q χ) t Ma Mb Na Nb q χ‖) ≤
      ∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : PrimitiveCharacter q, (1 / t) *
          (d * ‖phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseCosTwist b t)
                Ma Mb Na Nb q χ‖ +
            ‖phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseCosTwist b t)
                Ma Mb Na Nb q χ‖ +
            ‖phaseRankOneCharacterProduct (phaseCosTwist a t) (phaseSinTwist b t)
                Ma Mb Na Nb q χ‖ +
            d * ‖phaseRankOneCharacterProduct (phaseSinTwist a t) (phaseSinTwist b t)
                Ma Mb Na Nb q χ‖) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum
          intro χ hχ
          simpa only [d] using
            norm_dampedLogRectangularCharacterSum_le_four_rankOne_of_selector
              a b hM Y ht Ma Mb Na Nb q χ hY0 hYM hm1 hmM hn1 hnM
        · positivity
    _ = _ := by
      rw [← hmean (phaseCosTwist a t) (phaseCosTwist b t),
        ← hmean (phaseSinTwist a t) (phaseCosTwist b t),
        ← hmean (phaseCosTwist a t) (phaseSinTwist b t),
        ← hmean (phaseSinTwist a t) (phaseSinTwist b t)]
      simp only [Finset.mul_sum]
      dsimp only [d]
      ring_nf
      simp_rw [Finset.sum_add_distrib]
      simp_rw [Finset.mul_sum]
      ring

end

end AnalyticNumberTheory.LargeSieve

import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWTailBound

/-!
# Replacing the retained ceiling cutoff by the floor cutoff

The ceiling cutoff is adequate for a tail estimate, but does not bound the
dimensionless frequencies retained inside the Fourier integral. We replace the
actual signed masked finite sum, and estimate its change before any supremum.
The sharper tail estimate uses the first omitted integer, not the last retained
integer. All constants are independent of the arithmetic mask and residue.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology FourierTransform

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wFloorCutoff (M Z : ℝ) (q r : ℕ) : ℕ :=
  ⌊(q.lcm r : ℝ) / M * Z⌋₊

theorem wFloorCutoff_le_uniformCutoff (M Z : ℝ) (q r : ℕ) :
    wFloorCutoff M Z q r ≤ wUniformCutoff M Z q r :=
  Nat.floor_le_ceil _

theorem wFloorCutoff_scale {M Z : ℝ} (hM : 0 < M) (hZ : 0 ≤ Z)
    {q r : ℕ} (hl : 0 < q.lcm r) :
    (M / (q.lcm r : ℝ)) * wFloorCutoff M Z q r ≤ Z := by
  have hl' : (0 : ℝ) < q.lcm r := by exact_mod_cast hl
  calc
    _ ≤ (M / (q.lcm r : ℝ)) * ((q.lcm r : ℝ) / M * Z) :=
      mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (div_pos hM hl').le
    _ = Z := by field_simp

theorem wFloorCutoff_retained_scale {M Z : ℝ} (hM : 0 < M) (hZ : 0 ≤ Z)
    {q r : ℕ} (hl : 0 < q.lcm r) {h : ℤ}
    (hh : h.natAbs ≤ wFloorCutoff M Z q r) :
    M * |(h : ℝ)| / (q.lcm r : ℝ) ≤ Z := by
  have hh' : |(h : ℝ)| ≤ (wFloorCutoff M Z q r : ℝ) := by
    have hi : |h| ≤ (wFloorCutoff M Z q r : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hh
    exact_mod_cast hi
  have hl' : (0 : ℝ) < q.lcm r := by exact_mod_cast hl
  calc
    _ = (M / (q.lcm r : ℝ)) * |(h : ℝ)| := by ring
    _ ≤ (M / (q.lcm r : ℝ)) * wFloorCutoff M Z q r :=
      mul_le_mul_of_nonneg_left hh' (div_pos hM hl').le
    _ ≤ Z := wFloorCutoff_scale hM hZ hl

theorem wFloorCutoff_mem_Icc_scale {M Z : ℝ} (hM : 0 < M) (hZ : 0 ≤ Z)
    {q r : ℕ} (hl : 0 < q.lcm r) {h : ℤ}
    (hh : h ∈ Icc (-(wFloorCutoff M Z q r : ℤ)) (wFloorCutoff M Z q r)) :
    M * |(h : ℝ)| / (q.lcm r : ℝ) ≤ Z := by
  apply wFloorCutoff_retained_scale hM hZ hl
  have hi := abs_le.mpr (mem_Icc.mp hh)
  rw [← Int.natCast_natAbs] at hi
  exact_mod_cast hi

theorem wFloorCutoff_first_omitted_scale {M : ℝ} (hM : 0 < M) (Z : ℝ)
    {q r : ℕ} (hl : 0 < q.lcm r) :
    Z < (M / (q.lcm r : ℝ)) * (wFloorCutoff M Z q r + 1) := by
  have hl' : (0 : ℝ) < q.lcm r := by exact_mod_cast hl
  calc
    Z = (M / (q.lcm r : ℝ)) * ((q.lcm r : ℝ) / M * Z) := by field_simp
    _ < _ := mul_lt_mul_of_pos_left (Nat.lt_floor_add_one _) (div_pos hM hl')

/-- The first omitted integer gives an extra mesh width in the denominator. -/
theorem dyadicPoissonTail_first_omitted_uniform (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ x : ℝ, ∀ H : ℕ,
      Summable (fun h : ℤ ↦ ‖dyadicPoissonTail t x H h‖) ∧
        ‖∑' h : ℤ, dyadicPoissonTail t x H h‖ ≤
          C / (1 + t * ((H : ℝ) + 1)) ^ k := by
  obtain ⟨C, hC, hdecay⟩ :=
    schwartz_norm_le_rapidDecay (𝓕 dyadicCutoffSchwartz) (k + 2)
  refine ⟨2 * C, by positivity, fun t ht x H ↦ ?_⟩
  obtain ⟨hs, hb⟩ := poissonNonzeroDecay_summable_tsum_le ht
  have hp (h : ℤ) :
      ‖dyadicPoissonTail t x H h‖ ≤
        (C / (1 + t * ((H : ℝ) + 1)) ^ k) * poissonNonzeroDecay t h := by
    by_cases hh : h.natAbs ≤ H
    · simp only [dyadicPoissonTail, if_pos hh, norm_zero]
      unfold poissonNonzeroDecay
      split_ifs <;> positivity
    · have hne : h ≠ 0 := by intro hz; subst h; simp at hh
      have hH : (H : ℝ) + 1 ≤ |(h : ℝ)| := by
        have hi : (H : ℤ) + 1 ≤ |h| := by
          rw [← Int.natCast_natAbs]
          exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_of_not_ge hh))
        exact_mod_cast hi
      have hbase : 1 + t * ((H : ℝ) + 1) ≤ 1 + |t * (h : ℝ)| := by
        rw [abs_mul, abs_of_pos ht]
        exact add_le_add_right (mul_le_mul_of_nonneg_left hH ht.le) 1
      have hpow : (1 + t * ((H : ℝ) + 1)) ^ k ≤ (1 + |t * (h : ℝ)|) ^ k :=
        pow_le_pow_left₀ (by positivity) hbase k
      simp only [dyadicPoissonTail, if_neg hh, dyadicCutoffPoissonRemainder,
        if_neg hne, norm_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        fourier_apply, Circle.norm_coe, mul_one, poissonNonzeroDecay]
      calc
        _ ≤ t * (C / (1 + |t * (h : ℝ)|) ^ (k + 2)) :=
          mul_le_mul_of_nonneg_left (hdecay (t * h)) ht.le
        _ = (C * t / (1 + |t * (h : ℝ)|) ^ 2) /
            (1 + |t * (h : ℝ)|) ^ k := by
          simp only [pow_add, div_eq_mul_inv, mul_inv_rev]
          ring
        _ ≤ (C * t / (1 + |t * (h : ℝ)|) ^ 2) /
            (1 + t * ((H : ℝ) + 1)) ^ k :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
        _ = _ := by ring
  have hn : Summable (fun h : ℤ ↦ ‖dyadicPoissonTail t x H h‖) :=
    (hs.mul_left (C / (1 + t * ((H : ℝ) + 1)) ^ k)).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) hp
  refine ⟨hn, (norm_tsum_le_tsum_norm hn).trans ?_⟩
  calc
    _ ≤ ∑' h : ℤ, (C / (1 + t * ((H : ℝ) + 1)) ^ k) * poissonNonzeroDecay t h :=
      hn.tsum_le_tsum hp (hs.mul_left _)
    _ = (C / (1 + t * ((H : ℝ) + 1)) ^ k) * ∑' h : ℤ, poissonNonzeroDecay t h :=
      tsum_mul_left
    _ ≤ (C / (1 + t * ((H : ℝ) + 1)) ^ k) * 2 :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Uniform truncation at any cutoff at least the floor, including zero moduli
where the frequency summands vanish by definition. -/
theorem wPoissonFrequency_floorCutoff_error (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M Z : ℝ, 0 < M → 0 ≤ Z →
      ∀ q r : ℕ, ∀ a : ℤ, ∀ n₁ n₂ H : ℕ, wFloorCutoff M Z q r ≤ H →
      ‖(∑' h : ℤ, wPoissonFrequency M a q r n₁ n₂ h) -
          ∑ h ∈ Icc (-(H : ℤ)) H, wPoissonFrequency M a q r n₁ n₂ h‖ ≤
        C / (1 + Z) ^ k := by
  obtain ⟨C, hC, hb⟩ := dyadicPoissonTail_first_omitted_uniform k
  refine ⟨C, hC, fun M Z hM hZ q r a n₁ n₂ H hH ↦ ?_⟩
  by_cases hl : q.lcm r = 0
  · simp only [wPoissonFrequency, hl, Nat.cast_zero, div_zero,
      dyadicCutoffPoissonRemainder, zero_smul, zero_mul, ite_self,
      tsum_zero, sum_const_zero, sub_self, norm_zero]
    positivity
  · have hl' : (0 : ℝ) < q.lcm r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hl)
    have ht : 0 < M / (q.lcm r : ℝ) := div_pos hM hl'
    have hs : Z ≤ (M / (q.lcm r : ℝ)) * ((H : ℝ) + 1) := by
      apply (wFloorCutoff_first_omitted_scale hM Z (Nat.pos_of_ne_zero hl)).le.trans
      apply mul_le_mul_of_nonneg_left _ ht.le
      have hH' : (wFloorCutoff M Z q r : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
      linarith
    unfold wPoissonFrequency
    rw [dyadicPoissonRemainder_eq_truncation ht, add_sub_cancel_left]
    exact (hb _ ht _ H).2.trans
      (div_le_div_of_nonneg_left hC.le (by positivity)
        (pow_le_pow_left₀ (by positivity) (by linarith) k))

/-- The actual retained sums are compared with identical signed coefficients
and the identical arbitrary mask. No well-factorability input is used. -/
theorem wMaskedTruncated_ceil_sub_floor_uniform (l : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M Z : ℝ, 0 < M → 0 ≤ Z →
      ∀ N Q : Finset ℕ, ∀ β c : ℕ → ℝ, ∀ a : ℤ,
      ∀ P : WOriginalTuple → Prop,
      |wMaskedTruncated M (wUniformCutoff M Z) N Q β c a P -
          wMaskedTruncated M (wFloorCutoff M Z) N Q β c a P| ≤
        C * ((∑ q ∈ Q, |c q|) ^ 2 * (∑ n ∈ N, |β n|) ^ 2) / (1 + Z) ^ l := by
  obtain ⟨C, hC, hb⟩ := wPoissonFrequency_floorCutoff_error l
  refine ⟨2 * C, by positivity, fun M Z hM hZ N Q β c a P ↦ ?_⟩
  have hterm (t : WOriginalTuple) :
      |wOriginalTerm M (wUniformCutoff M Z) β c a t -
          wOriginalTerm M (wFloorCutoff M Z) β c a t| ≤
        |wTupleCoefficient β c t| * (2 * C / (1 + Z) ^ l) := by
    let f : ℤ → ℂ := wPoissonFrequency M a t.1.1 t.1.2 t.2.1 t.2.2
    have hc := hb M Z hM hZ t.1.1 t.1.2 a t.2.1 t.2.2
      (wUniformCutoff M Z t.1.1 t.1.2) (wFloorCutoff_le_uniformCutoff M Z _ _)
    have hf := hb M Z hM hZ t.1.1 t.1.2 a t.2.1 t.2.2
      (wFloorCutoff M Z t.1.1 t.1.2) le_rfl
    have hfreq :
        ‖(∑ h ∈ Icc (-(wUniformCutoff M Z t.1.1 t.1.2 : ℤ))
            (wUniformCutoff M Z t.1.1 t.1.2), f h) -
          ∑ h ∈ Icc (-(wFloorCutoff M Z t.1.1 t.1.2 : ℤ))
            (wFloorCutoff M Z t.1.1 t.1.2), f h‖ ≤ 2 * C / (1 + Z) ^ l := by
      have he : (∑ h ∈ Icc (-(wUniformCutoff M Z t.1.1 t.1.2 : ℤ))
            (wUniformCutoff M Z t.1.1 t.1.2), f h) -
          ∑ h ∈ Icc (-(wFloorCutoff M Z t.1.1 t.1.2 : ℤ))
            (wFloorCutoff M Z t.1.1 t.1.2), f h =
          ((∑' h : ℤ, f h) -
            ∑ h ∈ Icc (-(wFloorCutoff M Z t.1.1 t.1.2 : ℤ))
              (wFloorCutoff M Z t.1.1 t.1.2), f h) -
          ((∑' h : ℤ, f h) -
            ∑ h ∈ Icc (-(wUniformCutoff M Z t.1.1 t.1.2 : ℤ))
              (wUniformCutoff M Z t.1.1 t.1.2), f h) := by ring
      rw [he]
      exact (norm_sub_le _ _).trans ((add_le_add hf hc).trans (by ring_nf; rfl))
    simp only [wOriginalTerm, wTupleCoefficient, ← mul_sub, ← Complex.sub_re]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      ((Complex.abs_re_le_norm _).trans hfreq) (abs_nonneg _)
  calc
    _ = |∑ t ∈ wMaskedTuples N Q a P,
        (wOriginalTerm M (wUniformCutoff M Z) β c a t -
          wOriginalTerm M (wFloorCutoff M Z) β c a t)| := by
      rw [wMaskedTruncated, wMaskedTruncated, sum_sub_distrib]
    _ ≤ ∑ t ∈ wMaskedTuples N Q a P,
        |wTupleCoefficient β c t| * (2 * C / (1 + Z) ^ l) :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun t _ ↦ hterm t))
    _ = (∑ t ∈ wMaskedTuples N Q a P, |wTupleCoefficient β c t|) *
        (2 * C / (1 + Z) ^ l) := (sum_mul _ _ _).symm
    _ ≤ ((∑ q ∈ Q, |c q|) ^ 2 * (∑ n ∈ N, |β n|) ^ 2) *
        (2 * C / (1 + Z) ^ l) :=
      mul_le_mul_of_nonneg_right
        (sum_wMaskedTuples_abs_coefficient_le N Q β c a P) (by positivity)
    _ = _ := by ring

/-- Fixed-order divisor means evaluate the actual ceiling-to-floor difference. -/
theorem wMaskedTruncated_ceil_sub_floor_fouvryTau (l : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M Z : ℝ, 0 < M → 0 < Z →
      ∀ k j : ℕ, 1 ≤ k → 1 ≤ j → ∀ T L : ℝ, 1 ≤ T → 1 ≤ L →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) → ∀ a : ℤ,
      ∀ P : WOriginalTuple → Prop,
      |wMaskedTruncated M (wUniformCutoff M Z) N Q β c a P -
          wMaskedTruncated M (wFloorCutoff M Z) N Q β c a P| ≤
        C * ((L * (1 + Real.log L) ^ (j - 1)) ^ 2 *
          (T * (1 + Real.log T) ^ (k - 1)) ^ 2) / Z ^ l := by
  obtain ⟨C, hC, hb⟩ := wMaskedTruncated_ceil_sub_floor_uniform l
  refine ⟨C, hC, fun M Z hM hZ k j hk hj T L hT hL N Q hN hQ β c hβ hc a P ↦ ?_⟩
  calc
    _ ≤ C * ((∑ q ∈ Q, |c q|) ^ 2 * (∑ n ∈ N, |β n|) ^ 2) / (1 + Z) ^ l :=
      hb M Z hM hZ.le N Q β c a P
    _ ≤ C * ((∑ q ∈ Q, |c q|) ^ 2 * (∑ n ∈ N, |β n|) ^ 2) / Z ^ l :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hZ l)
        (pow_le_pow_left₀ hZ.le (by linarith) l)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (pow_pos hZ l).le
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact mul_le_mul
        (pow_le_pow_left₀ (sum_nonneg (fun _ _ ↦ abs_nonneg _))
          (sum_abs_le_fouvryTau_mean hj hL Q hQ c hc) 2)
        (pow_le_pow_left₀ (sum_nonneg (fun _ _ ↦ abs_nonneg _))
          (sum_abs_le_fouvryTau_mean hk hT N hN β hβ) 2)
        (sq_nonneg _) (sq_nonneg _)

/-- The cutoff replacement is paid before choosing `M`, the signed data,
the residue or the mask. The three fixed divisor orders may all be zero. -/
theorem wMaskedTruncated_ceil_sub_floor_alpha_log_payment
    (i k j A : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ M : ℝ, 0 < M →
      ∀ S N Q : Finset ℕ,
      S ⊆ Ioc 0 ⌊x⌋₊ → N ⊆ Ioc 0 ⌊x⌋₊ → Q ⊆ Ioc 0 ⌊x⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, ∀ P : WOriginalTuple → Prop,
      (∑ m ∈ S, α m ^ 2) *
        |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q β c a P -
          wMaskedTruncated M (wFloorCutoff M (x ^ η)) N Q β c a P| ≤
          x ^ 2 / Real.log x ^ A := by
  obtain ⟨l, hl⟩ := exists_nat_gt (6 / η)
  have hlη : 6 < η * (l : ℝ) := by
    have := (div_lt_iff₀ hη).mp hl
    nlinarith
  obtain ⟨C, hC, hdiff⟩ := wMaskedTruncated_ceil_sub_floor_fouvryTau l
  let D : ℕ := (i + 1) ^ 2 - 1 + 2 * j + 2 * k
  have hlogpay := betaPayment_eventually_log_mul_rpow_le C hC.le (D + A)
    (b := 0) (d := 1) (by norm_num)
  filter_upwards [hlogpay, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hpay hx hlog
  intro M hM S N Q hS hN hQ α β c hα hβ hc a P
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 < Real.log x := by linarith
  have hbase : 0 ≤ 1 + Real.log x := by linarith
  have hZ : 0 < x ^ η := Real.rpow_pos_of_pos hx0 _
  have hα' : ∀ m ∈ S, |α m| ≤ (fouvryTau (i + 1) m : ℝ) := by
    intro m hm
    exact (hα m hm).trans (by exact_mod_cast fouvryTau_le_succ i m)
  have hβ' : ∀ n ∈ N, |β n| ≤ (fouvryTau (k + 1) n : ℝ) := by
    intro n hn
    exact (hβ n hn).trans (by exact_mod_cast fouvryTau_le_succ k n)
  have hc' : ∀ q ∈ Q, |c q| ≤ (fouvryTau (j + 1) q : ℝ) := by
    intro q hq
    exact (hc q hq).trans (by exact_mod_cast fouvryTau_le_succ j q)
  have hαsq := sum_alpha_sq_le_fouvryTau (by omega : 1 ≤ i + 1) hx S hS α hα'
  have ht := hdiff M (x ^ η) hM hZ (k + 1) (j + 1) (by omega) (by omega)
    x x hx hx N Q hN hQ β c hβ' hc' a P
  simp only [Nat.add_sub_cancel] at ht
  have hbound :
      (∑ m ∈ S, α m ^ 2) *
          |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q β c a P -
            wMaskedTruncated M (wFloorCutoff M (x ^ η)) N Q β c a P| ≤
        C * x ^ 5 * (1 + Real.log x) ^ D / (x ^ η) ^ l := by
    calc
      _ ≤ (x * (1 + Real.log x) ^ ((i + 1) ^ 2 - 1)) *
          (C * ((x * (1 + Real.log x) ^ j) ^ 2 *
            (x * (1 + Real.log x) ^ k) ^ 2) / (x ^ η) ^ l) :=
        mul_le_mul hαsq ht (abs_nonneg _) (by positivity)
      _ = _ := by
        simp only [D, pow_add, mul_pow, ← pow_mul, Nat.mul_comm]
        ring
  apply hbound.trans
  apply (div_le_div_iff₀ (pow_pos hZ l) (pow_pos hlog0 A)).mpr
  have hpay' : C * (1 + Real.log x) ^ (D + A) ≤ x := by
    simpa only [Real.rpow_zero, Real.rpow_one, mul_one] using hpay
  have hnum :
      C * x ^ 5 * (1 + Real.log x) ^ D * Real.log x ^ A ≤ x ^ 6 := by
    calc
      _ ≤ C * x ^ 5 * (1 + Real.log x) ^ D * (1 + Real.log x) ^ A := by
        gcongr
        linarith
      _ = x ^ 5 * (C * (1 + Real.log x) ^ (D + A)) := by rw [pow_add]; ring
      _ ≤ x ^ 5 * x := mul_le_mul_of_nonneg_left hpay' (by positivity)
      _ = x ^ 6 := by ring
  have hdenom : x ^ 6 ≤ (x ^ η) ^ l := by
    rw [← Real.rpow_natCast x 6, ← Real.rpow_natCast (x ^ η) l,
      ← Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx hlη.le
  exact hnum.trans (hdenom.trans (by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (one_le_pow₀ hx : 1 ≤ x ^ 2) (pow_nonneg hZ.le l)))

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

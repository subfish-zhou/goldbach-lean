import MathlibNt.SieveTheory.LiLiuGoldbachB10PanGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachB10PanPrefixes

open scoped BigOperators
open MeasureTheory
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual floor-endpoint Li interval weight, before the divisor coprimality gate. -/
noncomputable def goldbachB10MainWeight (N : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  liuLogarithmicIntegral goldbachB10PanKappa0 ((N : ℝ) / m) -
    liuLogarithmicIntegral goldbachB10PanKappa0 ((⌊ε * (N : ℝ)⌋₊ : ℝ) / m)

/-- Common main mass on the actual product support, with labels already accounted for
by the proved injectivity of the ordered prime-pair product. -/
noncomputable def goldbachB10MainMass (N : ℕ) (ε b c : ℝ) : ℝ :=
  ∑ m ∈ goldbachC10ProductSupport N b c, goldbachB10MainWeight N ε m

theorem b10_li_difference_nonneg_le (κ a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    0 ≤ liuLogarithmicIntegral κ b - liuLogarithmicIntegral κ a ∧
    liuLogarithmicIntegral κ b - liuLogarithmicIntegral κ a ≤ (b - a) / Real.log 2 := by
  have hi := liuLogarithmicIntegrand_intervalIntegrable_of_two_le ha hab
  have he := intervalIntegral.integral_add_adjacent_intervals
    (liuLogarithmicIntegrand_intervalIntegrable ha) hi
  have hid : liuLogarithmicIntegral κ b - liuLogarithmicIntegral κ a =
      ∫ t in a..b, 1 / Real.log t := by
    unfold liuLogarithmicIntegral
    linarith
  rw [hid]
  constructor
  · exact intervalIntegral.integral_nonneg hab (fun t ht =>
      liuLogarithmicIntegrand_nonneg (ha.trans ht.1))
  · have hupper := intervalIntegral.integral_mono_on hab hi
      (intervalIntegrable_const (c := (1 : ℝ) / Real.log 2))
      (fun t ht => one_div_le_one_div_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2))
        (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (ha.trans ht.1)))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv, one_mul] using hupper

private theorem b10_two_mul_le_of_rpow {Y m : ℕ} (hY : 8 ≤ Y)
    (hm : (m : ℝ) ≤ (Y : ℝ) ^ ((2 : ℝ) / 3)) : 2 * (m : ℝ) ≤ Y := by
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have h8 : (8 : ℝ) ^ ((1 : ℝ) / 3) = 2 := by
    calc
      (8 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by norm_num
      _ = (2 : ℝ) ^ ((3 : ℝ) * (1 / 3)) := (Real.rpow_mul (by norm_num) _ _).symm
      _ = 2 := by norm_num
  have hr : (2 : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [← h8]
    exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hY) (by norm_num)
  calc
    2 * (m : ℝ) ≤ 2 * (Y : ℝ) ^ ((2 : ℝ) / 3) := by gcongr
    _ ≤ (Y : ℝ) ^ ((1 : ℝ) / 3) * (Y : ℝ) ^ ((2 : ℝ) / 3) := by gcongr
    _ = Y := by rw [← Real.rpow_add hYpos]; norm_num

theorem goldbachB10MainWeight_bounds_eventually
    (ε γ : ℝ) (hε : 0 < ε) (hεlt : ε < 1) (hγ : γ < (1 : ℝ) / 3) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ,
      (1 : ℝ) / 18 < β → ∀ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ β) ((N : ℝ) ^ γ),
      0 ≤ goldbachB10MainWeight N ε m ∧
      |goldbachB10MainWeight N ε m| ≤ ((N : ℝ) / Real.log 2) / m := by
  obtain ⟨N₀, hN₀, hgeo⟩ := B10PanGeometry_consumer_threshold ε γ 0 0 8
    hε hεlt hγ (by norm_num) (by norm_num)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN β hβ m hm
  rcases hgeo N hN with ⟨_, hY8, _, _, _, hA2Y, _, _, _, _, hsupp⟩
  have hmi := hsupp β hβ m hm
  have hm1 := goldbachC10CoeffReal_ne_zero_imp_one_lt
    (goldbachC10CoeffReal_ne_zero_iff.mpr hm)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmA2 : (m : ℝ) ≤ B10PanGeometryUpperWindow N γ := by
    exact_mod_cast (Finset.mem_Ioc.mp hmi).2
  have hmY : 2 * (m : ℝ) ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) :=
    b10_two_mul_le_of_rpow hY8 (hmA2.trans hA2Y)
  have hYle : (⌊ε * (N : ℝ)⌋₊ : ℝ) ≤ N :=
    (Nat.floor_le (by positivity : 0 ≤ ε * (N : ℝ))).trans (by nlinarith)
  have hi := b10_li_difference_nonneg_le goldbachB10PanKappa0
    ((⌊ε * (N : ℝ)⌋₊ : ℝ) / m) ((N : ℝ) / m)
    ((le_div_iff₀ hmpos).mpr hmY) (div_le_div_of_nonneg_right hYle hmpos.le)
  have hnonneg : 0 ≤ goldbachB10MainWeight N ε m := hi.1
  refine ⟨hnonneg, ?_⟩
  rw [abs_of_nonneg hnonneg]
  change liuLogarithmicIntegral _ _ - liuLogarithmicIntegral _ _ ≤ _
  calc
    _ ≤ ((N : ℝ) / m - (⌊ε * (N : ℝ)⌋₊ : ℝ) / m) / Real.log 2 := hi.2
    _ ≤ ((N : ℝ) / m) / Real.log 2 := by
      apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
      exact sub_le_self _ (by positivity)
    _ = ((N : ℝ) / Real.log 2) / m := by ring

theorem goldbachB10MainMass_nonneg_eventually
    (ε γ : ℝ) (hε : 0 < ε) (hεlt : ε < 1) (hγ : γ < (1 : ℝ) / 3) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ,
      (1 : ℝ) / 18 < β → 0 ≤ goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) := by
  obtain ⟨N₀, hN₀, hw⟩ := goldbachB10MainWeight_bounds_eventually ε γ hε hεlt hγ
  exact ⟨N₀, hN₀, fun N hN β hβ => Finset.sum_nonneg
    (fun m hm => (hw N hN β hβ m hm).1)⟩

/-- Exact support restriction of the already-defined Pan main prefix. -/
theorem goldbachB10PanMainPrefix_eq_support_sum
    {N Y A₁ A₂ d : ℕ} {b c : ℝ}
    (hsupp : ∀ ⦃m : ℕ⦄, m ∈ goldbachC10ProductSupport N b c → m ∈ Finset.Ioc A₁ A₂) :
    goldbachB10PanMainPrefix N Y A₁ A₂ d b c =
      ∑ m ∈ goldbachC10ProductSupport N b c,
        if Nat.Coprime m d then
          liuLogarithmicIntegral goldbachB10PanKappa0 ((Y : ℝ) / m) / d.totient else 0 := by
  classical
  unfold goldbachB10PanMainPrefix
  have hsub : goldbachC10ProductSupport N b c ⊆ Finset.Ioc A₁ A₂ := fun _ hm => hsupp hm
  calc
    _ = ∑ m ∈ goldbachC10ProductSupport N b c,
        if Nat.Coprime m d then goldbachC10CoeffReal N b c m *
          (liuLogarithmicIntegral goldbachB10PanKappa0 ((Y : ℝ) / m) / d.totient) else 0 := by
      symm
      apply Finset.sum_subset hsub
      intro m _ hm
      have hzero : goldbachC10CoeffReal N b c m = 0 := by
        by_contra h
        exact hm (goldbachC10CoeffReal_ne_zero_iff.mp h)
      simp [hzero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [goldbachC10CoeffReal_eq_one_of_mem_productSupport hm, one_mul]

/-- Same-source main-prefix subtraction, still retaining the divisor coprimality gate. -/
theorem goldbachB10PanMainPrefix_sub_eq_gatedMainWeight
    {N A₁ A₂ d : ℕ} {ε b c : ℝ}
    (hsupp : ∀ ⦃m : ℕ⦄, m ∈ goldbachC10ProductSupport N b c → m ∈ Finset.Ioc A₁ A₂) :
    goldbachB10PanMainPrefix N N A₁ A₂ d b c -
      goldbachB10PanMainPrefix N ⌊ε * (N : ℝ)⌋₊ A₁ A₂ d b c =
      (∑ m ∈ goldbachC10ProductSupport N b c,
        if Nat.Coprime m d then goldbachB10MainWeight N ε m else 0) / d.totient := by
  classical
  rw [goldbachB10PanMainPrefix_eq_support_sum hsupp,
    goldbachB10PanMainPrefix_eq_support_sum hsupp, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  split_ifs <;> simp_all only [goldbachB10MainWeight, zero_div, sub_self]
  ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
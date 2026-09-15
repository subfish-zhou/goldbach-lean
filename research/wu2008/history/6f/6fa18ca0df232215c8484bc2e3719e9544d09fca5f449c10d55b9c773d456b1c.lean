import MathlibNt.Wu2008DoubleSieve.BoxMassUniform

/-!
# The matching upper bound in Wu (2004), (3.9)

The same true-li prefix PNT supplies a matching uniform upper bound.
The only finite endpoint loss is the possible prime at the lower ceiling.
-/

namespace Wu2008DoubleSieve

open Finset Filter
open scoped Classical Topology

theorem box_trueLi_sub_upper {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral b -
      AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral a ≤
        (b - a) / Real.log a := by
  have hia := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegrand_intervalIntegrable ha
  have hib := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegrand_intervalIntegrable
    (ha.trans hab)
  have hi := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegrand_intervalIntegrable_of_two_le
    ha hab
  have heq :
      AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral b -
        AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral a =
          ∫ t in a..b, 1 / Real.log t := by
    simp only [AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral,
      MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral, zero_add]
    exact intervalIntegral.integral_interval_sub_left hib hia
  rw [heq]
  calc
    _ ≤ ∫ _t in a..b, 1 / Real.log a := by
      apply intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
      intro t ht
      exact one_div_le_one_div_of_le (Real.log_pos (by linarith))
        (Real.log_le_log (by linarith) ht.1)
    _ = _ := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul, div_eq_mul_inv, one_mul]

/-- The intersection with the lower closed prefix contains at most its
endpoint. Coprimality can only decrease the upper bound. -/
theorem box_window_card_le_prefix_difference (N : ℕ) {Y V : ℝ} (hYV : Y ≤ V) :
    ((primeWindow N Y V).card : ℝ) ≤
      (boxPrimePrefix ⌈V⌉₊).card - (boxPrimePrefix ⌈Y⌉₊).card + 1 := by
  have hu : primeWindow N Y V ∪ boxPrimePrefix ⌈Y⌉₊ ⊆ boxPrimePrefix ⌈V⌉₊ := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · obtain ⟨hp, _, _, hpV⟩ := mem_primeWindow.mp hp
      exact mem_boxPrimePrefix.mpr ⟨hp, (Nat.lt_ceil.mpr hpV).le⟩
    · obtain ⟨hp, hpY⟩ := mem_boxPrimePrefix.mp hp
      exact mem_boxPrimePrefix.mpr ⟨hp, hpY.trans (Nat.ceil_mono hYV)⟩
  have hi : primeWindow N Y V ∩ boxPrimePrefix ⌈Y⌉₊ ⊆ {⌈Y⌉₊} := by
    intro p hp
    obtain ⟨hp, hpY⟩ := mem_inter.mp hp
    have hlo : ⌈Y⌉₊ ≤ p := Nat.ceil_le.mpr (mem_primeWindow.mp hp).2.2.1
    exact mem_singleton.mpr (le_antisymm (mem_boxPrimePrefix.mp hpY).2 hlo)
  have hc := card_union_add_card_inter (primeWindow N Y V) (boxPrimePrefix ⌈Y⌉₊)
  have huc := card_le_card hu
  have hic : (primeWindow N Y V ∩ boxPrimePrefix ⌈Y⌉₊).card ≤ 1 := by
    simpa only [card_singleton] using card_le_card hi
  have hn : (primeWindow N Y V).card + (boxPrimePrefix ⌈Y⌉₊).card ≤
      (boxPrimePrefix ⌈V⌉₊).card + 1 := by omega
  have hr : ((primeWindow N Y V).card : ℝ) + (boxPrimePrefix ⌈Y⌉₊).card ≤
      (boxPrimePrefix ⌈V⌉₊).card + 1 := by exact_mod_cast hn
  linarith

theorem box_mul_reciprocal_mass_le_card (N : ℕ) (Y V : ℝ) :
    Y * (∑ p ∈ primeWindow N Y V, (1 : ℝ) / p) ≤
      ((primeWindow N Y V).card : ℝ) := by
  calc
    _ = ∑ p ∈ primeWindow N Y V, Y / (p : ℝ) := by rw [mul_sum]; simp [div_eq_mul_inv]
    _ ≤ ∑ _p ∈ primeWindow N Y V, (1 : ℝ) := by
      apply sum_le_sum
      intro p hp
      exact (div_le_one (by exact_mod_cast (mem_primeWindow.mp hp).1.pos)).mpr
        (mem_primeWindow.mp hp).2.2.1
    _ = _ := by simp

/-- Unconditional finite upper estimate with true-li PNT error and exact
ceiling payments; no prime-window nonemptiness hypothesis is needed. -/
theorem box_reciprocal_mass_trueLi_upper (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ N : ℕ, ∀ Y V : ℝ,
      2 ≤ Y → Y ≤ V → X₀ ≤ ⌈V⌉₊ →
      Y * (∑ p ∈ primeWindow N Y V, (1 : ℝ) / p) ≤
        (V - Y + 1) / Real.log (⌈Y⌉₊ : ℝ) +
          2 * (C * (⌈V⌉₊ : ℝ) / Real.log (⌈V⌉₊ : ℝ) ^ A) + 1 := by
  obtain ⟨C, hC, X₀, hPNT⟩ := boxPrimePrefix_trueLi A hA
  refine ⟨C, hC, X₀, ?_⟩
  intro N Y V hY hYV hX
  have hcY : (2 : ℝ) ≤ ⌈Y⌉₊ := hY.trans (Nat.le_ceil Y)
  have hcYV : (⌈Y⌉₊ : ℝ) ≤ ⌈V⌉₊ := by exact_mod_cast Nat.ceil_mono hYV
  have hcV : (2 : ℝ) ≤ ⌈V⌉₊ := hcY.trans hcYV
  have hP := hPNT ⌈V⌉₊ hX ⌈V⌉₊ (by exact_mod_cast hcV) le_rfl
  have hQ := hPNT ⌈V⌉₊ hX ⌈Y⌉₊ (by exact_mod_cast hcY) (Nat.ceil_mono hYV)
  have hcard := box_window_card_le_prefix_difference N hYV
  have hmass := box_mul_reciprocal_mass_le_card N Y V
  have hli := box_trueLi_sub_upper hcY hcYV
  have hlen : (⌈V⌉₊ : ℝ) - ⌈Y⌉₊ ≤ V - Y + 1 := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ V)
    have := Nat.le_ceil Y
    linarith
  have hlen' := div_le_div_of_nonneg_right hlen
    (Real.log_nonneg (show (1 : ℝ) ≤ ⌈Y⌉₊ by linarith))
  have hP' := (abs_le.mp hP).2
  have hQ' := (abs_le.mp hQ).1
  linarith

/-- The matching upper half of (3.9): for fixed `α > 0`, the constant
`4/α + 2` and one threshold work for all source `Δ` and all `N^α ≤ V ≤ N`.
In fact the upper estimate does not require `V ≤ N`. -/
theorem wu_primeWindow_reciprocal_mass_upper {α : ℝ} (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Δ V : ℝ,
      1 + Real.log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
      Δ < 1 + 2 * Real.log (N : ℝ) ^ (-4 : ℝ) →
      (N : ℝ) ^ α ≤ V →
      (∑ p ∈ primeWindow N (V / Δ) V, (1 : ℝ) / p) ≤
        (4 / α + 2) / Real.log (N : ℝ) ^ 5 := by
  obtain ⟨C, hC, X₀, hfinite⟩ := box_reciprocal_mass_trueLi_upper 8 (by norm_num)
  have hlogt : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgrowth : ∀ᶠ N : ℕ in atTop, 12 * C ≤ α ^ 8 * Real.log (N : ℝ) ^ 3 :=
    (Tendsto.const_mul_atTop (pow_pos hα 8)
      ((tendsto_pow_atTop (by decide : 3 ≠ 0)).comp hlogt)).eventually
        (eventually_ge_atTop (12 * C))
  have hαlog : ∀ᶠ N : ℕ in atTop, 1 ≤ (α / 2) * Real.log (N : ℝ) :=
    (Tendsto.const_mul_atTop (show 0 < α / 2 by positivity) hlogt).eventually
      (eventually_ge_atTop 1)
  have hX : ∀ᶠ N : ℕ in atTop, (X₀ : ℝ) ≤ (N : ℝ) ^ α :=
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (X₀ : ℝ))
  have htwo : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (α / 2) :=
    ((tendsto_rpow_atTop (show 0 < α / 2 by positivity)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  apply eventually_atTop.mp
  filter_upwards [hgrowth, hαlog, hX, htwo,
    box_eventually_log_power_budget 5 (show (0 : ℝ) < 6 by norm_num) hα,
    convolutionWuWindows_eventually_lower_cutoff hα,
    hlogt.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop (2 : ℕ)] with N hg hαL hNX hNtwo hbud hcut hL hN
  intro Δ V hΔlo hΔhi hVlo
  let L := Real.log (N : ℝ)
  let X := (⌈V⌉₊ : ℝ)
  let Y := V / Δ
  let Z := (⌈Y⌉₊ : ℝ)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hYlow := hcut Δ hΔlo hΔhi V hVlo
  have hY2 : 2 ≤ Y := hNtwo.trans hYlow
  have hY0 : 0 < Y := by linarith
  have hΔ1 : 1 ≤ Δ := by
    have := Real.rpow_nonneg hL0.le (-4)
    dsimp [L] at this
    linarith
  have hΔ0 : 0 < Δ := by linarith
  have hΔ3 : Δ ≤ 3 := by
    have := Real.rpow_le_one_of_one_le_of_nonpos hL (show (-4 : ℝ) ≤ 0 by norm_num)
    linarith
  have hV0 : 0 < V := (Real.rpow_pos_of_pos hN0 α).trans_le hVlo
  have hYV : Y ≤ V := (div_le_iff₀ hΔ0).mpr (by nlinarith)
  have hV2 : 2 ≤ V := hY2.trans hYV
  have hVX : V ≤ X := Nat.le_ceil V
  have hYZ : Y ≤ Z := Nat.le_ceil Y
  have hX2V : X ≤ 2 * V := by
    have := Nat.ceil_lt_add_one hV0.le
    dsimp [X]
    linarith
  have hlogX : α * L ≤ Real.log X := by
    rw [← Real.log_rpow hN0]
    exact Real.log_le_log (Real.rpow_pos_of_pos hN0 α) (hVlo.trans hVX)
  have hlogZ : (α / 2) * L ≤ Real.log Z := by
    rw [← Real.log_rpow hN0]
    exact Real.log_le_log (Real.rpow_pos_of_pos hN0 _) (hYlow.trans hYZ)
  have hlogZ1 : 1 ≤ Real.log Z := hαL.trans hlogZ
  have hlogZ0 : 0 < Real.log Z := by linarith
  have hlogX0 : 0 < Real.log X := (mul_pos hα hL0).trans_le hlogX
  have hcX : X₀ ≤ ⌈V⌉₊ := by
    have ht : (X₀ : ℝ) ≤ (⌈V⌉₊ : ℝ) := hNX.trans (hVlo.trans hVX)
    exact_mod_cast ht
  have hf := hfinite N Y V hY2 hYV hcX
  change Y * (∑ p ∈ primeWindow N Y V, (1 : ℝ) / p) ≤
    (V - Y + 1) / Real.log Z + 2 * (C * X / Real.log X ^ (8 : ℝ)) + 1 at hf
  rw [show (8 : ℝ) = (8 : ℕ) by norm_num, Real.rpow_natCast] at hf
  have hΔL : Δ - 1 ≤ 2 / L ^ 4 := by
    have he : Real.log (N : ℝ) ^ (-4 : ℝ) = 1 / L ^ 4 := by
      rw [Real.rpow_neg hL0.le, show (4 : ℝ) = (4 : ℕ) by norm_num,
        Real.rpow_natCast]
      simp only [one_div]
    rw [he] at hΔhi
    have he2 : 2 * (1 / L ^ 4) = 2 / L ^ 4 := by ring
    rw [he2] at hΔhi
    linarith
  have hmain : (V - Y) / Real.log Z ≤ Y * (4 / α) / L ^ 5 := by
    calc
      _ = Y * (Δ - 1) / Real.log Z := by dsimp [Y]; field_simp
      _ ≤ Y * (2 / L ^ 4) / ((α / 2) * L) := by gcongr
      _ = _ := by ring
  have hVY : V ≤ 3 * Y := by
    have heq : Y * Δ = V := by dsimp [Y]; exact div_mul_cancel₀ V hΔ0.ne'
    nlinarith
  have hE : 2 * (C * X / Real.log X ^ 8) ≤ Y / L ^ 5 := by
    calc
      _ = (2 * C) * X / Real.log X ^ 8 := by ring
      _ ≤ (2 * C) * (2 * V) / (α * L) ^ 8 := by gcongr
      _ = 4 * C * V / (α ^ 8 * L ^ 8) := by ring
      _ ≤ V / (3 * L ^ 5) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have ht := mul_le_mul_of_nonneg_right hg (show 0 ≤ V * L ^ 5 by positivity)
        dsimp [L] at *
        nlinarith
      _ ≤ Y / L ^ 5 := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hVY (show 0 ≤ L ^ 5 by positivity)]
  have hround : 2 ≤ Y / L ^ 5 := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hb : 6 * L ^ 5 ≤ V := hbud.trans hVlo
    linarith
  have hone : 1 / Real.log Z ≤ 1 := (div_le_one hlogZ0).mpr hlogZ1
  have heq : (V - Y + 1) / Real.log Z =
      (V - Y) / Real.log Z + 1 / Real.log Z := by ring
  have hm : Y * (∑ p ∈ primeWindow N Y V, (1 : ℝ) / p) ≤
      Y * ((4 / α + 2) / L ^ 5) := by
    have heq' : Y * ((4 / α + 2) / L ^ 5) = Y * (4 / α) / L ^ 5 + 2 * (Y / L ^ 5) := by ring
    linarith
  exact (mul_le_mul_iff_right₀ hY0).mp hm

/-- The literal two-sided order statement (3.9), with one threshold before
both real parameters and with no empty-box premise. -/
theorem wu_primeWindow_reciprocal_mass_bounds {α : ℝ} (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Δ V : ℝ,
      1 + Real.log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
      Δ < 1 + 2 * Real.log (N : ℝ) ^ (-4 : ℝ) →
      (N : ℝ) ^ α ≤ V → V ≤ N →
      1 / (12 * Real.log (N : ℝ) ^ 5) ≤
        (∑ p ∈ primeWindow N (V / Δ) V, (1 : ℝ) / p) ∧
      (∑ p ∈ primeWindow N (V / Δ) V, (1 : ℝ) / p) ≤
        (4 / α + 2) / Real.log (N : ℝ) ^ 5 := by
  obtain ⟨N₁, hlo⟩ := wu_primeWindow_reciprocal_mass_lower hα
  obtain ⟨N₂, hhi⟩ := wu_primeWindow_reciprocal_mass_upper hα
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN Δ V hΔlo hΔhi hVlo hVhi
  exact ⟨hlo N ((le_max_left _ _).trans hN) Δ V hΔlo hΔhi hVlo hVhi,
    hhi N ((le_max_right _ _).trans hN) Δ V hΔlo hΔhi hVlo⟩

end Wu2008DoubleSieve

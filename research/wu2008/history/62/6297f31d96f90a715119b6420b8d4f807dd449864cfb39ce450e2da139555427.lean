import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientHalfOpen

/-!
# Uniform geometry for all source prime-sum endpoints

One lower bound for q controls every pair 2 ≤ s ≤ t ≤ 10.
In particular the whole first continuous cell, not just its right sample,
has transformed argument at most 10.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real
open scoped Classical Topology

theorem primeCoefficient_source_geometry (X0 : ℕ) :
    ∃ Q0 : ℝ, 1 < Q0 ∧ ∀ q : ℝ, Q0 ≤ q → ∀ s t : ℝ,
      2 ≤ s → s ≤ t → t ≤ 10 →
      let Y := q ^ (1 / t)
      let Z := q ^ (1 / s)
      let a := ⌈Y⌉₊ - 1
      0 < Y ∧ Y ≤ Z ∧ X0 ≤ a ∧ 4 ≤ a ∧ 1 ≤ log (a : ℝ) ∧
        2 ≤ log q ∧ Z ≤ q ^ (1 / 2 : ℝ) ∧
        log q / 11 ≤ log (a : ℝ) ∧ log q / log (a : ℝ) - 1 ≤ 10 := by
  have hgrow : Tendsto (fun q : ℝ => q ^ (1 / 10 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hevent : ∀ᶠ q : ℝ in atTop,
      2 ≤ q ∧ 2 * ((X0 : ℝ) + 4 + exp 1) ≤ q ^ (1 / 10 : ℝ) ∧
        max 2 (110 * log 2) ≤ log q := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      hgrow.eventually (eventually_ge_atTop (2 * ((X0 : ℝ) + 4 + exp 1))),
      tendsto_log_atTop.eventually (eventually_ge_atTop (max 2 (110 * log 2)))]
      with q hq hp hl
    exact ⟨hq, hp, hl⟩
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp hevent
  refine ⟨max 2 Q, by linarith [le_max_left (2 : ℝ) Q], ?_⟩
  intro q hq s t hs hst ht
  obtain ⟨hq2, hp, hl⟩ := hQ q ((le_max_right _ _).trans hq)
  have hq1 : 1 < q := by linarith
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < s := by linarith
  let Y := q ^ (1 / t)
  let Z := q ^ (1 / s)
  let a := ⌈Y⌉₊ - 1
  have hY0 : 0 < Y := rpow_pos_of_pos (by linarith) _
  have hYZ : Y ≤ Z := rpow_le_rpow_of_exponent_le hq1.le
    (one_div_le_one_div_of_le hs0 hst)
  have hlow : q ^ (1 / 10 : ℝ) ≤ Y := rpow_le_rpow_of_exponent_le hq1.le
    (one_div_le_one_div_of_le ht0 ht)
  have hCY : 0 < ⌈Y⌉₊ := Nat.ceil_pos.mpr hY0
  have hYa : Y ≤ (a : ℝ) + 1 := by
    have h := Nat.le_ceil Y
    rw [← Nat.sub_add_cancel hCY] at h
    push_cast at h
    exact h
  have hexp : 0 < exp (1 : ℝ) := exp_pos _
  have hX : (0 : ℝ) ≤ X0 := Nat.cast_nonneg _
  have hY2 : 2 ≤ Y := by linarith
  have haY : Y / 2 ≤ (a : ℝ) := by linarith
  have haX : (X0 : ℝ) ≤ a := by linarith
  have ha4 : (4 : ℝ) ≤ a := by linarith
  have hae : exp (1 : ℝ) ≤ a := by linarith
  have hla : 1 ≤ log (a : ℝ) := by
    have h := log_le_log hexp hae
    simpa only [log_exp] using h
  have hZ : Z ≤ q ^ (1 / 2 : ℝ) := rpow_le_rpow_of_exponent_le hq1.le
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs)
  have hlogY : log Y = log q / t := by
    dsimp [Y]
    rw [log_rpow (by linarith : 0 < q)]
    ring
  have hloglower : log q / 10 - log 2 ≤ log (a : ℝ) := by
    have h1 := log_le_log (div_pos hY0 (by norm_num)) haY
    rw [log_div hY0.ne' (by norm_num : (2 : ℝ) ≠ 0), hlogY] at h1
    have h2 : log q / 10 ≤ log q / t :=
      div_le_div_of_nonneg_left (log_pos hq1).le ht0 ht
    linarith
  have hl110 : 110 * log 2 ≤ log q := (le_max_right _ _).trans hl
  have hl11 : log q / 11 ≤ log (a : ℝ) := by linarith
  refine ⟨hY0, hYZ, by exact_mod_cast haX, by exact_mod_cast ha4,
    hla, (le_max_left _ _).trans hl, hZ, hl11, ?_⟩
  have hdiv : log q / log (a : ℝ) ≤ 11 :=
    (div_le_iff₀ (by linarith : 0 < log (a : ℝ))).2 (by linarith)
  linarith

/-- Source half-open prime summation to a continuous integral, uniform
over both parameters and every bounded monotone signed coefficient. -/
theorem primeCoefficient_source_continuous_uniform {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Q0 : ℝ, 1 < Q0 ∧ ∀ q : ℝ, Q0 ≤ q → ∀ f : ℝ → ℝ,
      MonotoneOn f (Set.Icc 1 10) →
      (∀ u ∈ Set.Icc (1 : ℝ) 10, |f u| ≤ B) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      |(∑ p ∈ primeWindow 1 (q ^ (1 / t)) (q ^ (1 / s)),
          wuPrimeCoefficientWeight f q p) -
        ∫ x in (q ^ (1 / t))..(q ^ (1 / s)), wuPrimeRealWeight f q x / log x| ≤ ε := by
  obtain ⟨C, _, X0, hquad⟩ := primeCoefficient_halfopen_continuous
  obtain ⟨Q, hQ1, hgeom⟩ := primeCoefficient_source_geometry X0
  have hevent : ∀ᶠ q : ℝ in atTop, 11 * C * B / ε ≤ log q :=
    tendsto_log_atTop.eventually (eventually_ge_atTop _)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hevent
  refine ⟨max Q R, hQ1.trans_le (le_max_left _ _), ?_⟩
  intro q hq f hf hfb s t hs hst ht
  have hQq := (le_max_left Q R).trans hq
  have hRq := (le_max_right Q R).trans hq
  obtain ⟨hY, hYZ, hXa, ha, hla, hlq, hZ, hl11, haq⟩ := hgeom q hQq s t hs hst ht
  have h := hquad f B q _ _ hf hB hfb hY hYZ hXa ha hla
    (hQ1.trans_le hQq) hlq hZ haq
  apply h.trans
  apply (div_le_iff₀ (by linarith : 0 < log (⌈q ^ (1 / t)⌉₊ - 1 : ℕ))).2
  have hp := (div_le_iff₀ hε).1 (hR q hRq)
  nlinarith [mul_le_mul_of_nonneg_left hl11 hε.le]

end Wu2008DoubleSieve

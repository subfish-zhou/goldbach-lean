import Wu18938Campaign.M1.PaperAssembly

namespace Wu18938Campaign.M1

open WuPaper.R2Mother

theorem eventually_original_count_all_gains {κ₁ κ₂ : ℝ}
    (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ < κ₂)
    (hupper : 3 * κ₁ + κ₂ < 1 / 2) (hparam : 3 * κ₁ - κ₂ < 1 / 6) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N →
      let z := (N : ℝ) ^ κ₁
      let w := (N : ℝ) ^ κ₂
      let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
      let v := (N : ℝ) ^ (1 / 3 : ℝ)
      let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
      ((eleven N z w u v V : ℝ) + (paperRetained N z w u v : ℝ) +
          paperAssemblyGains N z w u v - (quotientExcess N z w u V : ℝ)) / 4 ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
          ((16 + 2 * (1 / κ₁) ^ 3 + 2 * (1 / κ₂) ^ 2) / 4) *
            (N : ℝ) ^ (1 - κ₁) := by
  have hz : ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ (N : ℝ) ^ κ₁ :=
    ((tendsto_rpow_atTop (by linarith : 0 < κ₁)).comp
      tendsto_natCast_atTop_atTop).eventually (Filter.eventually_ge_atTop 2)
  apply Filter.eventually_atTop.mp
  filter_upwards [hz, Filter.eventually_ge_atTop (4 : ℕ)] with N hzN hN
  intro he
  have h := original_count_all_gains hN he hκ₁ hκ.le hupper.le hparam.le hzN
  dsimp only at h ⊢
  nlinarith

end Wu18938Campaign.M1

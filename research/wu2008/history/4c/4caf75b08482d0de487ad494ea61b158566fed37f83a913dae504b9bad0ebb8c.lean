import R2MotherDelta2
import R2MotherNinthEndpoint

namespace WuPaper.R2Mother

theorem eventually_original_count_frontier {κ₁ κ₂ : ℝ}
    (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ < κ₂)
    (hupper : 3 * κ₁ + κ₂ < 1 / 2) (hparam : 3 * κ₁ - κ₂ < 1 / 6) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N →
      let z := (N : ℝ) ^ κ₁
      let w := (N : ℝ) ^ κ₂
      let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
      let v := (N : ℝ) ^ (1 / 3 : ℝ)
      let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
      ((eleven N z w u v V : ℝ) + (paperRetained N z w u v : ℝ) -
        (quotientExcess N z w u V : ℝ)) / 4 ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
          ((16 + 2 * (1 / κ₁) ^ 3 + 2 * (1 / κ₂) ^ 2) / 4) *
            (N : ℝ) ^ (1 - κ₁) := by
  have hz : ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ (N : ℝ) ^ κ₁ :=
    ((tendsto_rpow_atTop (by linarith : 0 < κ₁)).comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 2)
  apply Filter.eventually_atTop.mp
  filter_upwards [hz, Filter.eventually_ge_atTop (4 : ℕ)] with N hzN hN
  intro he
  have h := original_eleven_count_frontier hN he hκ₁ hκ.le hupper.le hparam.le hzN
  dsimp only at h ⊢
  nlinarith

end WuPaper.R2Mother

#check @WuPaper.R2Mother.upsilon1
#check @WuPaper.R2Mother.upsilon2
#check @WuPaper.R2Mother.upsilon3
#check @WuPaper.R2Mother.upsilon4
#check @WuPaper.R2Mother.upsilon5
#check @WuPaper.R2Mother.upsilon6
#check @WuPaper.R2Mother.upsilon7
#check @WuPaper.R2Mother.upsilon8
#check @WuPaper.R2Mother.upsilon9
#check @WuPaper.R2Mother.upsilon10
#check @WuPaper.R2Mother.upsilon11
#check @WuPaper.R2Mother.eq23_count
#check @WuPaper.R2Mother.eq24_count
#check @WuPaper.R2Mother.eq25_count
#check @WuPaper.R2Mother.paper_eq26_count
#check @WuPaper.R2Mother.source_missingMass_zero
#check @WuPaper.R2Mother.signed_aggregate_transport
#check @WuPaper.R2Mother.eleven_count_signed
#check @WuPaper.R2Mother.quotient_to_unscaled_signed
#check @WuPaper.R2Mother.ninth_strict_eq_closed
#check @WuPaper.R2Mother.modulus_loss_le_repeated
#check @WuPaper.R2Mother.original_delta2_signed_paid
#check @WuPaper.R2Mother.original_eleven_count_frontier
#check @WuPaper.R2Mother.eventually_original_count_frontier
#print axioms WuPaper.R2Mother.upsilon1
#print axioms WuPaper.R2Mother.upsilon2
#print axioms WuPaper.R2Mother.upsilon3
#print axioms WuPaper.R2Mother.upsilon4
#print axioms WuPaper.R2Mother.upsilon5
#print axioms WuPaper.R2Mother.upsilon6
#print axioms WuPaper.R2Mother.upsilon7
#print axioms WuPaper.R2Mother.upsilon8
#print axioms WuPaper.R2Mother.upsilon9
#print axioms WuPaper.R2Mother.upsilon10
#print axioms WuPaper.R2Mother.upsilon11
#print axioms WuPaper.R2Mother.eq23_count
#print axioms WuPaper.R2Mother.eq24_count
#print axioms WuPaper.R2Mother.eq25_count
#print axioms WuPaper.R2Mother.paper_eq26_count
#print axioms WuPaper.R2Mother.source_missingMass_zero
#print axioms WuPaper.R2Mother.signed_aggregate_transport
#print axioms WuPaper.R2Mother.eleven_count_signed
#print axioms WuPaper.R2Mother.quotient_to_unscaled_signed
#print axioms WuPaper.R2Mother.ninth_strict_eq_closed
#print axioms WuPaper.R2Mother.modulus_loss_le_repeated
#print axioms WuPaper.R2Mother.original_delta2_signed_paid
#print axioms WuPaper.R2Mother.original_eleven_count_frontier
#print axioms WuPaper.R2Mother.eventually_original_count_frontier

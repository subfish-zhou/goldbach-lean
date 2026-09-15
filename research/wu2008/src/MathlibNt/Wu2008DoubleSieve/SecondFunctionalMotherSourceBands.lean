import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPrefixMass

/-! # Four-band window identities and the two generic pair masses -/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

theorem secondFunctionalMother_colour_zero (b c e : ℝ) (p : ℕ) :
    secondFunctionalMotherColour b c e p = 0 ↔ (p : ℝ) < b := by
  unfold secondFunctionalMotherColour
  split_ifs <;> simp_all

theorem secondFunctionalMother_colour_low {b c : ℝ} (hbc : b ≤ c) (e : ℝ) (p : ℕ) :
    secondFunctionalMotherColour b c e p ≤ 1 ↔ (p : ℝ) < c := by
  unfold secondFunctionalMotherColour
  split_ifs <;> simp_all
  linarith

theorem secondFunctionalMother_colour_mid {b c e : ℝ} (hbc : b ≤ c) (hce : c ≤ e) (p : ℕ) :
    secondFunctionalMotherColour b c e p ≤ 2 ↔ (p : ℝ) < e := by
  unfold secondFunctionalMotherColour
  split_ifs <;> simp_all <;> linarith

theorem secondFunctionalMother_colour_two {b c e : ℝ} (hbc : b ≤ c) (p : ℕ) :
    secondFunctionalMotherColour b c e p = 2 ↔ c ≤ (p : ℝ) ∧ (p : ℝ) < e := by
  constructor
  · intro h
    unfold secondFunctionalMotherColour at h
    split_ifs at h with hb hc he <;> norm_num at h
    exact ⟨le_of_not_gt hc, he⟩
  · rintro ⟨hc, he⟩
    have hb : ¬(p : ℝ) < b := by linarith
    simp [secondFunctionalMotherColour, hb, not_lt.mpr hc, he]

theorem secondFunctionalMother_window_filter (M n : ℕ) {a u f : ℝ} (huf : u ≤ f) :
    (divisorsIn (primeWindow M a f) n).filter (fun p : ℕ => (p : ℝ) < u) =
      divisorsIn (primeWindow M a u) n := by
  ext p
  simp only [divisorsIn, mem_filter, mem_primeWindow]
  constructor
  · rintro ⟨⟨⟨hp, hM, ha, _⟩, hd⟩, hu⟩
    exact ⟨⟨hp, hM, ha, hu⟩, hd⟩
  · rintro ⟨⟨hp, hM, ha, hu⟩, hd⟩
    exact ⟨⟨⟨hp, hM, ha, hu.trans_le huf⟩, hd⟩, hu⟩

theorem secondFunctionalMother_band_zero (M n : ℕ) {a b c e f : ℝ} (hbf : b ≤ f) :
    (divisorsIn (primeWindow M a f) n).filter
      (fun p => secondFunctionalMotherColour b c e p = 0) =
      divisorsIn (primeWindow M a b) n := by
  simp only [secondFunctionalMother_colour_zero]
  exact secondFunctionalMother_window_filter M n hbf

theorem secondFunctionalMother_band_low (M n : ℕ) {a b c e f : ℝ}
    (hbc : b ≤ c) (hcf : c ≤ f) :
    (divisorsIn (primeWindow M a f) n).filter
      (fun p => secondFunctionalMotherColour b c e p ≤ 1) =
      divisorsIn (primeWindow M a c) n := by
  simp only [secondFunctionalMother_colour_low hbc]
  exact secondFunctionalMother_window_filter M n hcf

theorem secondFunctionalMother_band_mid (M n : ℕ) {a b c e f : ℝ}
    (hbc : b ≤ c) (hce : c ≤ e) (hef : e ≤ f) :
    (divisorsIn (primeWindow M a f) n).filter
      (fun p => secondFunctionalMotherColour b c e p ≤ 2) =
      divisorsIn (primeWindow M a e) n := by
  simp only [secondFunctionalMother_colour_mid hbc hce]
  exact secondFunctionalMother_window_filter M n hef

theorem secondFunctionalMother_band_two (M n : ℕ) {a b c e f : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hef : e ≤ f) :
    (divisorsIn (primeWindow M a f) n).filter
      (fun p => secondFunctionalMotherColour b c e p = 2) =
      divisorsIn (primeWindow M c e) n := by
  ext p
  simp only [divisorsIn, mem_filter, mem_primeWindow, secondFunctionalMother_colour_two hbc]
  constructor
  · rintro ⟨⟨⟨hp, hM, _, _⟩, hd⟩, hc, he⟩
    exact ⟨⟨hp, hM, hc, he⟩, hd⟩
  · rintro ⟨⟨hp, hM, hc, he⟩, hd⟩
    exact ⟨⟨⟨hp, hM, hab.trans (hbc.trans hc), he.trans_le hef⟩, hd⟩, hc, he⟩

theorem secondFunctionalMother_gamma5_mass (N d : ℕ) {a b c e f : ℝ}
    (hbc : b ≤ c) (hcf : c ≤ f) :
    fourthRowMotherPair N d (d*N) a c a c =
      ∑ ell ∈ sieveCarrier N d (d*N) a,
        ((fourthRowMotherLowPairs (divisorsIn (primeWindow (d*N) a f) ((N-ell)/d))
          (secondFunctionalMotherColour b c e)).card : ℝ) := by
  rw [fourthRowMother_pair_mass]
  simp only [fourthRowMotherLowPairs, secondFunctionalMother_band_low _ _ hbc hcf]

theorem secondFunctionalMother_gamma6_mass (N d : ℕ) {a b c e f : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (hef : e ≤ f) :
    fourthRowMotherPair N d (d*N) a b c e =
      ∑ ell ∈ sieveCarrier N d (d*N) a,
        ((fourthRowMotherCrossPairs (divisorsIn (primeWindow (d*N) a f) ((N-ell)/d))
          (secondFunctionalMotherColour b c e)).card : ℝ) := by
  rw [fourthRowMother_pair_mass]
  apply sum_congr rfl
  intro ell _
  simp only [fourthRowMotherCrossPairs,
    secondFunctionalMother_band_zero _ _ (hbc.trans (hce.trans hef)),
    secondFunctionalMother_band_two _ _ hab hbc hef]
  congr 1
  apply congrArg Finset.card
  apply filter_eq_self.mpr
  rintro ⟨p,q⟩ hpq
  obtain ⟨hp,hq⟩ := mem_product.mp hpq
  have hp' := (mem_primeWindow.mp (mem_filter.mp hp).1).2.2.2
  have hq' := (mem_primeWindow.mp (mem_filter.mp hq).1).2.2.1
  exact_mod_cast hp'.trans_le (hbc.trans hq')

end Wu2008DoubleSieve

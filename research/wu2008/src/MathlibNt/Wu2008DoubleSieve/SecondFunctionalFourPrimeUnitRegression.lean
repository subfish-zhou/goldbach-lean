import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeUnitPayment

namespace Wu2008DoubleSieve.FourPrimeUnit
open Finset Real
open scoped Classical

theorem cut_order {i k N d : ℕ} {δ Δ r t : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hr : 0 < r) (hrt : r ≤ t) :
    wuLocalCutoff N δ d t ≤ wuLocalCutoff N δ d r := by
  obtain ⟨hdpos,hdQ⟩ := omega3_source_support_le_Q hN hδ hδhi hb hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hdpos
  unfold wuLocalCutoff
  apply rpow_le_rpow_of_exponent_le
  · exact (le_div_iff₀ hd0).mpr (by simpa using hdQ)
  · exact one_div_le_one_div_of_le hr hrt

/-- Regression is only an inclusion: the accepted old profiles remain strengthened. -/
theorem old_profiles_subset {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) :
    (gamma16Profiles N δ (convolutionWuWindows N Δ V)).filter (fun x => x.2.2.2.2 = 1) ⊆
      actualProfiles N δ SecondFunctionalParameters.row4 (convolutionWuWindows N Δ V) 0 := by
  rintro ⟨d,p3,p2,p1,n⟩ hx
  obtain ⟨hx,hn⟩ := mem_filter.mp hx
  change n = 1 at hn
  subst n
  obtain ⟨hd,h3,h2,h1,_,_,hcap,_⟩ := mem_gamma16Profiles.mp hx
  have ha := cut_order hN hδ hδhi hb hd (r := (291/100 : ℝ)) (t := (412/100 : ℝ))
    (by norm_num) (by norm_num)
  have hbcut := cut_order hN hδ hδhi hb hd (r := (291/100 : ℝ)) (t := (356/100 : ℝ))
    (by norm_num) (by norm_num)
  obtain ⟨hp3,hm3,hl3,hu3⟩ := mem_primeWindow.mp h3
  obtain ⟨hp2,hm2,hl2,hu2⟩ := mem_primeWindow.mp h2
  obtain ⟨hp1,hm1,hl1,hu1⟩ := mem_primeWindow.mp h1
  have hi2 := hu2.trans hu3
  have hi1 := hu1.trans hi2
  have colour : ∀ q : ℕ, wuLocalCutoff N δ d (291/100) ≤ (q : ℝ) →
      (q : ℝ) < wuLocalCutoff N δ d (5/2) →
      secondFunctionalMotherColour (wuLocalCutoff N δ d (356/100))
        (wuLocalCutoff N δ d (291/100)) (wuLocalCutoff N δ d (5/2)) q = 2 := by
    intro q hlo hhi
    simp [secondFunctionalMotherColour, not_lt.mpr (hbcut.trans hlo), not_lt.mpr hlo, hhi]
  unfold actualProfiles
  simp only [SecondFunctionalParameters.row4, show (250/100 : ℝ) = 5/2 by norm_num]
  apply mem_profiles.mpr
  refine ⟨hd, mem_primeWindow.mpr ⟨hp3,hm3,ha.trans hl3,hu3⟩,
    mem_primeWindow.mpr ⟨hp2,hm2,ha.trans hl2,hi2⟩,
    mem_primeWindow.mpr ⟨hp1,hm1,ha.trans hl1,hi1⟩, rfl,
    by exact_mod_cast hu1, by exact_mod_cast hu2, ?_, hcap⟩
  simp [word, colour p1 hl1 hi1, colour p2 hl2 hi2, colour p3 hl3 hu3]

/-- In particular, the old last-cap atom is not discarded. -/
theorem old_fibre_subset {i N : ℕ} {δ : ℝ} {W : Fin i → Finset ℕ}
    {x : Gamma16Profile} (hx : x ∈ gamma16Profiles N δ W) :
    gamma16PrimeFibre N δ x ⊆ actualFibre N δ SecondFunctionalParameters.row4 0 x := by
  rcases x with ⟨d,p3,p2,p1,n⟩
  have hl3 := (mem_primeWindow.mp (mem_gamma16Profiles.mp hx).2.1).2.2.1
  intro q hq
  obtain ⟨hrange,hprime,horder,hupper,hcap⟩ := mem_filter.mp hq
  unfold actualFibre fibre
  apply mem_filter.mpr
  refine ⟨hrange,hprime,horder,?_,?_,?_⟩
  · change wuLocalCutoff N δ d (291/100) ≤ (q : ℝ)
    exact hl3.trans (by exact_mod_cast horder.le)
  · convert hupper using 1; norm_num [word, SecondFunctionalParameters.row4, gamma16Encode]
  · simpa only [gamma16_encode_value] using hcap

theorem old_unit_le_envelope {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) :
    secondFunctionalUnitGamma16 N δ (convolutionWuWindows N Δ V) ≤
      actualEnvelope N δ SecondFunctionalParameters.row4 (convolutionWuWindows N Δ V) 0 := by
  unfold secondFunctionalUnitGamma16 actualEnvelope envelope
  calc
    _ ≤ ∑ x ∈ (gamma16Profiles N δ (convolutionWuWindows N Δ V)).filter
        (fun x => x.2.2.2.2 = 1),
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
          (actualFibre N δ SecondFunctionalParameters.row4 0 x).card := by
      apply sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (card_le_card (old_fibre_subset (mem_filter.mp hx).1))) (Nat.cast_nonneg _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (old_profiles_subset hN hδ hδhi hb)
      (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end Wu2008DoubleSieve.FourPrimeUnit

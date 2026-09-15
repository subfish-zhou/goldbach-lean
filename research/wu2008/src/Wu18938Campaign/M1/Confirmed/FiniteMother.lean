import Wu18938Campaign.M1.Confirmed.RoughBox
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherSource

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve Finset Real
open scoped Classical

theorem roughBox_mother_cutoffs {m i N d : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    wuLocalCutoff N δ d p.S ≤ wuLocalCutoff N δ d p.kappa1 ∧
    wuLocalCutoff N δ d p.kappa1 ≤ wuLocalCutoff N δ d p.kappa2 ∧
    wuLocalCutoff N δ d p.kappa2 ≤ wuLocalCutoff N δ d p.kappa3 ∧
    wuLocalCutoff N δ d p.kappa3 ≤ wuLocalCutoff N δ d p.s := by
  have hs : 0 < p.s := zero_lt_one.trans_le hp.one_le_s
  have h3 := hs.trans_le hp.s_le_kappa3
  have h2 := h3.trans hp.kappa3_lt_kappa2
  have h1 := h2.trans hp.kappa2_lt_kappa1
  exact ⟨hb.cutoff_antitone hN hη hδ hd h1 hp.kappa1_le_S,
    hb.cutoff_antitone hN hη hδ hd h2 hp.kappa2_lt_kappa1.le,
    hb.cutoff_antitone hN hη hδ hd h3 hp.kappa3_lt_kappa2.le,
    hb.cutoff_antitone hN hη hδ hd hs hp.s_le_kappa3⟩

theorem roughBox_mother_finite {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) :
    5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
      secondFunctionalMotherRHS p N δ (convolutionWuWindows N Δ V) +
        secondFunctionalMotherError p N δ (convolutionWuWindows N Δ V) := by
  rw [← secondFunctionalMother_weighted_identity]
  unfold secondFunctionalMotherError wuBoxPhi convolutionSieveCount
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  obtain ⟨hab, hbc, hce, hef⟩ := roughBox_mother_cutoffs hb hN hη hδ p hp hd
  have h := mul_le_mul_of_nonneg_left
    (secondFunctionalMother_original_windows N d hab hbc hce hef)
    (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _)
  convert h using 1 <;> ring

theorem roughBox_mother_error (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
        secondFunctionalMotherError p N δ (convolutionWuWindows N Δ V) ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, hT⟩ := roughBox_power_mass_relative m hη hδ hε
    (show 0 < 3 / η by positivity) hη
  refine ⟨T, hT4, ?_⟩
  intro N hN he i Δ V hb p hp
  have hN4 : 4 ≤ N := hT4.trans hN
  have hfinite :
      secondFunctionalMotherError p N δ (convolutionWuWindows N Δ V) ≤
        ((3 / η) * ((N : ℝ) / (N : ℝ) ^ η)) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
    unfold secondFunctionalMotherError boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hg := hb.support_geometry (by omega) hη hδ hd
    have ho := roughBox_mother_cutoffs hb (by omega) hη hδ p hp hd
    have hlarge : ∀ q ∈ d.primeFactors, (N : ℝ) ^ η ≤ (q : ℝ) := by
      intro q hq
      obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
      exact omega3_support_prime_lower _ hb.window_large hd hqp hqd
    have h := mul_le_mul_of_nonneg_left
      (secondFunctionalMother_three_error_power (a := wuLocalCutoff N δ d p.S)
        hN4 he hg.1 hg.2.1 ho.2.2.1 ho.2.2.2 hη hlarge)
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _)
    convert h using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  exact hfinite.trans (hT N hN i Δ V hb)

theorem roughBox_mother_source (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          secondFunctionalMotherRHS p N δ (convolutionWuWindows N Δ V) +
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, hT⟩ := roughBox_mother_error m hη hδ hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he i Δ V hb p hp
  exact (roughBox_mother_finite hb (by omega) hη hδ p hp).trans
    (add_le_add le_rfl (hT N hN he i Δ V hb p hp))

end Wu18938Campaign.M1.Confirmed

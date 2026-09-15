import Wu18938Campaign.M1.Confirmed.FourIntegral
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeUnit

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Four

open Wu2008DoubleSieve Finset Real
open scoped Classical

theorem unit_mass {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (j : Fin 4) :
    FourPrimeUnit.actualSource N δ p (convolutionWuWindows N Δ V) j ≤
      ((N : ℝ) ^ (1 / 2 - δ)) ^ (4 / p.s) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  have hsource : FourPrimeUnit.actualSource N δ p (convolutionWuWindows N Δ V) j ≤
      FourPrimeUnit.actualEnvelope N δ p (convolutionWuWindows N Δ V) j :=
    FourPrimeUnit.source_le_envelope (fun _ hd => hb.support_pos hd) j
  apply hsource.trans
  rw [FourPrimeUnit.actual_envelope_eq]
  apply secondFunctionalUnit_mass_le _ _ _ (rpow_nonneg (Nat.cast_nonneg N) _) hs hs3
    (fun _ hd => hb.support_pos hd)
    (fun _ hx _ => FourPrimeUnit.actual_profiles_geometry hx)
  intro x hx _ q hq
  exact FourPrimeUnit.fibre_geometry
    (hb.cutoff_antitone hN hη hδ (FourPrimeUnit.actual_profiles_geometry hx).1
      (by linarith [hp.one_le_s]) hp.s_le_kappa3) hq

theorem unit_relative (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ j : Fin 4, FourPrimeUnit.actualSource N δ p (convolutionWuWindows N Δ V) j ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let ξ := 1 - (1 / 2 - δ) * (4 / p.s)
  have hξ : 0 < ξ := by
    have hh : (1 / 2 - δ) * 4 / p.s < 1 :=
      (div_lt_iff₀ (by linarith : 0 < p.s)).mpr (by linarith)
    dsimp only [ξ]
    rw [mul_div_assoc] at hh
    linarith
  obtain ⟨T, hT4, ht⟩ := roughBox_power_mass_relative m hη hδ he
    (by norm_num : (0 : ℝ) < 1) hξ
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb j
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hscale : ((N : ℝ) ^ (1 / 2 - δ)) ^ (4 / p.s) = (N : ℝ) / (N : ℝ) ^ ξ := by
    calc
      _ = (N : ℝ) ^ ((1 / 2 - δ) * (4 / p.s)) := (rpow_mul hNr.le _ _).symm
      _ = (N : ℝ) ^ (1 - ξ) := by congr 1; dsimp only [ξ]; ring
      _ = _ := by rw [rpow_sub hNr, rpow_one]
  have hunit := unit_mass hb (by omega) hη hδ p hp hs hs3 j
  rw [hscale] at hunit
  exact hunit.trans (by simpa only [one_mul] using ht N hN i Δ V hb)

theorem gamma_theta (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ j : Fin 4, secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) (16 + j.val) ≤
        (2 / (1 - 2 * δ)) * FourPrimeNonunit.sourceKTheta N δ Δ V p j +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0, hT04, hunit⟩ := unit_relative p hp hs hs3 m hη hδ (half_pos he)
  obtain ⟨T1, _, hnon⟩ := source_theta m hη hδ hδhi (half_pos he)
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb j
  have hu := hunit N (by omega) i Δ V hb j
  have hd := hnon N (by omega) heven i Δ V hb p hp hs.le j
  have ha := FourPrimeNonunit.actual_source_le (N := N) (δ := δ) p
    (convolutionWuWindows N Δ V) (fun _ hd => hb.support_pos hd) (by omega) heven j
  rw [← (FourPrimeNonunit.sourceFamily_dictionary N δ Δ V p j).1] at ha
  change FourPrimeNonunit.actualSource N δ p (convolutionWuWindows N Δ V) j ≤ _ at ha
  have hpart := FourPrimeUnit.actual_gamma_partition N δ p (convolutionWuWindows N Δ V) j
  change FourPrimeUnit.actualSource N δ p (convolutionWuWindows N Δ V) j +
      FourPrimeNonunit.actualSource N δ p (convolutionWuWindows N Δ V) j =
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) (16 + j.val) at hpart
  linarith only [hu, hd, ha, hpart]

theorem mother_six_high_paid (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
        4 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.S +
        wuBoxPhi N δ (convolutionWuWindows N Δ V) p.kappa1 -
        wuOmega2Sum N δ p.s p.S (convolutionWuWindows N Δ V) -
        wuOmega2Sum N δ p.kappa2 p.S (convolutionWuWindows N Δ V) -
        wuOmega2Sum N δ p.kappa3 p.S (convolutionWuWindows N Δ V) +
        (∑ j ∈ Icc 5 15, secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j) +
        (2 / (1 - 2 * δ)) * (HighSourcePayload.pairedTheta N δ Δ V p +
          ∑ j : Fin 4, FourPrimeNonunit.sourceKTheta N δ Δ V p j) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0, hT04, hmother⟩ := roughBox_mother_high_paid m hη hδ hδhi (half_pos he)
  obtain ⟨T1, _, hfour⟩ := gamma_theta p hp hs hs3 m hη hδ hδhi (show 0 < ε / 8 by positivity)
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb
  have hm := hmother N (by omega) heven i Δ V hb p hp hs.le
  have hf := sum_le_sum (s := (univ : Finset (Fin 4)))
    (fun j _ => hfour N (by omega) heven i Δ V hb j)
  have hsplit : (∑ j ∈ Icc 5 19,
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j) =
      (∑ j ∈ Icc 5 15, secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j) +
      ∑ j : Fin 4, secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) (16 + j.val) := by
    rw [show Icc 5 19 = Icc 5 15 ∪ Icc 16 19 by decide, sum_union (by decide)]
    congr 1
  rw [hsplit] at hm
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hf
  nlinarith only [hm, hf]

end Wu18938Campaign.M1.Confirmed.Four

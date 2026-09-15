import R2GammaHighUpper

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle HighTheta HighBoxRecovery HighO2Terminal
open Real Finset Filter
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical Topology Interval

theorem inserted_geometry {N d p : ℕ} {δ s t : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hm : d ∈ psiPrimes (j.castAdd 4) N)
    (hs : 2 ≤ s) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hp : p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)) :
    (N : ℝ)^highEta ≤ p ∧ (p : ℝ) ≤ N ∧
      ((d*p : ℕ) : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta) := by
  have hg := prime_geometry j hN hd hh hm
  have hsize := hg.2.2.2.2.2.1
  have hlevel := hg.2.2.2.2.2.2.1
  have hq := hg.2.2.2.2.2.2.2
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hg.2.2.2.1
  have hq0 : 0 < (N : ℝ)^(1/2-δ)/d := by linarith
  have hp' := mem_primeWindow.mp hp
  have hhalf : (p : ℝ) ≤ ((N : ℝ)^(1/2-δ)/d)^(1/2 : ℝ) :=
    hp'.2.2.2.le.trans (rpow_le_rpow_of_exponent_le hq.le
      (one_div_le_one_div_of_le (by norm_num) hs))
  have hdp : ((d*p : ℕ) : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta) := by
    have hpow : (N : ℝ)^(1/2-δ)*d ≤ ((N : ℝ)^(1/2-δ-10*highEta))^2 := by
      calc
        _ ≤ (N : ℝ)^(1/2-δ)*(N : ℝ)^(1/2-100*highEta) :=
          mul_le_mul_of_nonneg_left hsize (by positivity)
        _ = (N : ℝ)^((1/2-δ)+(1/2-100*highEta)) := (rpow_add hN0 _ _).symm
        _ ≤ (N : ℝ)^((1/2-δ-10*highEta)*2) :=
          rpow_le_rpow_of_exponent_le hN1.le (by norm_num [highEta] at *; linarith)
        _ = _ := by rw [rpow_mul (Nat.cast_nonneg N), rpow_two]
    have hsquare : (p : ℝ)^2 ≤ (N : ℝ)^(1/2-δ)/d := by
      have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) p) hhalf 2
      have heq : (((N : ℝ)^(1/2-δ)/d)^(1/2 : ℝ))^2 = (N : ℝ)^(1/2-δ)/d := by
        rw [← rpow_two, ← rpow_mul hq0.le]
        norm_num
      rwa [heq] at hsq
    have hmul := mul_le_mul_of_nonneg_right ((le_div_iff₀ hd0).mp hsquare) hd0.le
    rw [Nat.cast_mul]
    nlinarith [rpow_nonneg (Nat.cast_nonneg N) (1/2-δ-10*highEta)]
  refine ⟨?_, ?_, hdp⟩
  · apply le_trans _ hp'.2.2.1
    change (N : ℝ)^highEta ≤ ((N : ℝ)^(1/2-δ)/d)^(1/t)
    calc
      _ ≤ (N : ℝ)^((10*highEta)*(1/t)) := rpow_le_rpow_of_exponent_le hN1.le (by
        rw [mul_one_div]
        apply (le_div_iff₀ (show 0 < t by linarith)).mpr
        have hη : 0 < highEta := by norm_num [highEta]
        nlinarith)
      _ = ((N : ℝ)^(10*highEta))^(1/t) := rpow_mul (Nat.cast_nonneg N) _ _
      _ ≤ _ := rpow_le_rpow (by positivity) hlevel (by positivity)
  · have hpdp : (p : ℝ) ≤ d*p := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hg.2.2.2.1
      nlinarith [Nat.cast_nonneg (α := ℝ) p]
    rw [Nat.cast_mul] at hdp
    apply hpdp.trans (hdp.trans ?_)
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hN1.le
      (show 1/2-δ-10*highEta ≤ (1 : ℝ) by norm_num [highEta] at *; linarith)

theorem atom_lower {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) (heps1 : ε ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      ∀ s t : ℝ, 2 ≤ s → 3 ≤ t → t ≤ 5 → 2 ≤ t-t/s →
      ∀ d ∈ psiPrimes (j.castAdd 4) N,
      ∀ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        (4*logarithmicIntegral N)*(wuSingularSeries (d*N)/((Nat.totient d : ℝ)*
          log ((N : ℝ)^(1/2-δ)/d))) *
          (logCoefficient ε (ratio N d p δ t)/(((p : ℝ)-2)*
            (1-log (p : ℝ)/log ((N : ℝ)^(1/2-δ)/d)))) -
          apAtom N (convolutionModulusCutoff N δ) (d*p) ≤
        (sourceSieveCount N (d*p) (d*N) (wuLocalCutoff N δ d t) : ℝ) := by
  obtain ⟨T0, hT04, hlocal⟩ := local_count_lower hd.le heps heps1
  obtain ⟨T1, hlarge⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < highEta by norm_num [highEta])).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN he j s t hs ht ht5 hc d hm p hp
  have hN4 : 4 ≤ N := hT04.trans (by omega)
  have hp' := mem_primeWindow.mp hp
  have hpN := selected_subset_original N d _ _ hp
  have hg := inserted_geometry j (by omega) hd hh hm hs ht ht5 hpN
  have hsp := prime_geometry j (by omega) hd hh hm
  have hq := hsp.2.2.2.2.2.2.2
  have hu := ratio_domain hq hs ht ht5 hc hpN
  have hl := hlocal N (by omega) he (d*p) (Nat.mul_pos hsp.2.2.2.1 hp'.1.pos)
    hg.2.2 (ratio N d p δ t) hu.1 hu.2
  rw [ratio_cutoff hq hp'.1.pos (by linarith) (by linarith [hu.1]),
    omega2_source_count_prime_modulus_eq N d hp'.1 hp'.2.2.1] at hl
  have hp4 : (4 : ℝ) ≤ p := (hlarge N (by omega)).trans hg.1
  have hpd : ¬p ∣ d := hp'.1.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_right.mp hp'.2.1).1
  have hw := wu_inserted_theta_weight (show 0 < N by omega) hsp.2.2.2.1 hp'.1
    (show 2 < p by exact_mod_cast (show (2 : ℝ) < p by linarith))
    (Nat.coprime_mul_iff_right.mp hp'.2.1).2 hq
  simp only [if_neg hpd] at hw
  rw [Nat.cast_mul] at hl
  rw [hw] at hl
  convert hl using 1
  dsimp [logCoefficient]
  rw [max_eq_right hu.1]
  simp only [div_mul_eq_div_div]
  ring

theorem selected_integral {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      ∀ f : ℝ → ℝ, MonotoneOn f (Set.Icc 1 10) →
      (∀ u ∈ Set.Icc (1 : ℝ) 10, |f u| ≤ 11) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      |reboxingPrimeSum true N δ s t (windows j N) (fun d p => f (ratio N d p δ t)) -
        (∫ u in (1-1/s)..(1-1/t), f (t*u)/(u*(1-u))) * theta j N δ| ≤
        ε * theta j N δ := by
  obtain ⟨T, hT4, hquad⟩ := selected_fibre_integral heps
  refine ⟨T, hT4, ?_⟩
  intro N hN j f hf hfb s t hs hst ht ht5
  have hN4 := hT4.trans hN
  let W := windows j N
  let Q := (N : ℝ)^(1/2-δ)
  let I := ∫ u in (1-1/s)..(1-1/t), f (t*u)/(u*(1-u))
  let w := fun d : ℕ => (convolutionCoeff W d : ℝ)*wuSingularSeries (d*N)/
    ((Nat.totient d : ℝ)*log (Q/d))
  have hg : ∀ d ∈ boxConvolutionSupport W,
      d.Prime ∧ d.Coprime N ∧ (N : ℝ)^highEta ≤ d ∧
      0 < d ∧ d ≤ N ∧ (d : ℝ) ≤ (N : ℝ)^(1/2-100*highEta) ∧
      (N : ℝ)^(10*highEta) ≤ Q/d ∧ 1 < Q/d := by
    intro d hm
    rw [support_eq] at hm
    exact prime_geometry j (by omega) hd hh hm
  have hpoint : ∀ d ∈ boxConvolutionSupport W,
      |(∑ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        f (ratio N d p δ t)/(((p : ℝ)-2)*(1-log (p : ℝ)/log (Q/d)))) - I| ≤ ε := by
    intro d hm
    have hg' := hg d hm
    exact hquad N hN d hg'.2.2.2.1 hg'.2.2.2.2.1
      (Q/d) hg'.2.2.2.2.2.2.1 f hf hfb s t hs hst ht ht5
  have hw : ∀ d ∈ boxConvolutionSupport W, 0 ≤ w d := by
    intro d hm
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (wuSingularSeries_pos _ (Nat.mul_pos (hg d hm).2.2.2.1 (by omega))).le)
      (mul_nonneg (Nat.cast_nonneg _) (log_pos (hg d hm).2.2.2.2.2.2.2).le)
  have hli : 0 ≤ 4*logarithmicIntegral N := mul_nonneg (by norm_num)
    ((by positivity : (0 : ℝ) ≤ N/(2*log N)).trans (box_trueLi_lower hN4))
  change |4*logarithmicIntegral N*(∑ d ∈ boxConvolutionSupport W, w d *
      ∑ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        f (ratio N d p δ t)/(((p : ℝ)-2)*(1-log (p : ℝ)/log (Q/d)))) -
      I*(4*logarithmicIntegral N*∑ d ∈ boxConvolutionSupport W, w d)| ≤
    ε*(4*logarithmicIntegral N*∑ d ∈ boxConvolutionSupport W, w d)
  rw [mul_left_comm I, ← mul_sub, abs_mul, abs_of_nonneg hli, mul_left_comm ε]
  apply mul_le_mul_of_nonneg_left _ hli
  rw [mul_comm I, sum_mul, ← sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, |w d*((∑ p ∈ primeWindow (d*N)
        (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        f (ratio N d p δ t)/(((p : ℝ)-2)*(1-log (p : ℝ)/log (Q/d))))-I)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ boxConvolutionSupport W, w d*ε := by
      apply sum_le_sum
      intro d hm
      rw [abs_mul, abs_of_nonneg (hw d hm)]
      exact mul_le_mul_of_nonneg_left (hpoint d hm) (hw d hm)
    _ = _ := by rw [← sum_mul, mul_comm]

#check @inserted_geometry
#check @atom_lower
#check @selected_integral
#print axioms inserted_geometry
#print axioms atom_lower
#print axioms selected_integral
end WuPaper.R2GammaHigh

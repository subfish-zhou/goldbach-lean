import U8MotherInsertion

/-! Classical payment of exactly the remaining large-first-prime carrier. -/
noncomputable section
open Finset Set Real Filter MeasureTheory
open Wu2008DoubleSieve Wu2008DoubleSieve.SeventhEighth
open scoped Classical Topology Interval
namespace U8MotherInsertion

def oldSmallIntegral : ℝ :=
  ∫ t in alpha..(1/10), log (2-3*t)/(t*(1-t))
def largeIntegral : ℝ :=
  ∫ t in (1/10 : ℝ)..(1/3), log (2-3*t)/(t*(1-t))

theorem J8_split : J8 = oldSmallIntegral + largeIntegral := by
  have hsmall : IntervalIntegrable (fun t => log (2-3*t)/(t*(1-t))) volume alpha (1/10) :=
    (eighth_integrand_continuous.mono (by
      intro t ht
      exact ⟨ht.1,ht.2.trans (by norm_num)⟩)).intervalIntegrable_of_Icc (by norm_num [alpha])
  have hlarge : IntervalIntegrable (fun t => log (2-3*t)/(t*(1-t))) volume (1/10) (1/3) :=
    (eighth_integrand_continuous.mono (by
      intro t ht
      exact ⟨(by norm_num [alpha] : alpha ≤ 1/10).trans ht.1,ht.2⟩)).intervalIntegrable_of_Icc (by norm_num)
  exact (intervalIntegral.integral_add_adjacent_intervals hsmall hlarge).symm

theorem largeIntegral_nonneg : 0 ≤ largeIntegral := by
  apply intervalIntegral.integral_nonneg (by norm_num : (1/10 : ℝ) ≤ 1/3)
  intro t ht
  exact div_nonneg (log_nonneg (by linarith [ht.2]))
    (mul_nonneg (by linarith [ht.1]) (by linarith [ht.2]))

theorem largeIntegral_eq_pairInner :
    largeIntegral = ∫ t in (1/10 : ℝ)..(1/3), pairInner pairLower8 t/t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (1/10 : ℝ) ≤ 1/3)] at ht
  dsimp only
  rw [pairInner8_eq_log ⟨(by norm_num [alpha] : alpha ≤ 1/10).trans ht.1,ht.2⟩]
  rw [div_div, mul_comm (1-t) t]

theorem large_pairSum_le_nested {N : ℕ} (hN : 512 ≤ N) :
    classicalPairSum N (largePairs N) ≤ pairNested N (1/10) pairLower8 := by
  apply classicalPairSum_le_pairNested (by omega) _ _ _ (by norm_num)
  intro p hp
  obtain ⟨hold,hcut⟩ := mem_filter.mp hp
  obtain ⟨ha,hb,_,_,_,hvb,hab,hsize⟩ := lowerPairs_data (mem_filter.mp hold).1
  obtain ⟨hl,_,_,_⟩ := classical_pair_log_geometry (by omega) ha hb hab hcut hvb hsize
  obtain ⟨_,hu,hv,htop⟩ := eighth_pair_log_domain (by omega) hold
  exact ⟨ha,hb,⟨hl,hu.le⟩,hv,htop.le⟩

theorem large_pairSum_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      classicalPairSum N (largePairs N) ≤ largeIntegral+ε := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (pairNested_eventually_le hε)
  refine ⟨max T 512,le_max_right _ _,?_⟩
  intro N hN
  have h512 := (le_max_right T 512).trans hN
  have h := hT N ((le_max_left T 512).trans hN) (1/10) pairLower8
    (by norm_num) (by norm_num) (fun t ht => pairLower8_bounds ht)
    (fun x _ y _ => pairLower8_lipschitz x y)
  rw [← largeIntegral_eq_pairInner] at h
  exact (large_pairSum_le_nested h512).trans h

theorem large_mass_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      classicalMass N (largePairs N) ≤ (largeIntegral+ε)*N/log N := by
  let η := min 1 (ε/(largeIntegral+2))
  have hJ := largeIntegral_nonneg
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηE : η*(largeIntegral+2) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < largeIntegral+2)).mp (min_le_right _ _)
  have hc : (1+η)*(largeIntegral+η) ≤ largeIntegral+ε := by
    nlinarith [mul_le_mul_of_nonneg_left hη1 hη.le]
  obtain ⟨Tp,hTp⟩ := eventually_atTop.mp (classicalMass_sharp_pair_bound hη)
  obtain ⟨Tq,hTq,hq⟩ := large_pairSum_upper hη
  refine ⟨max Tp Tq,hTq.trans (le_max_right _ _),?_⟩
  intro N hN
  have h512 := hTq.trans ((le_max_right Tp Tq).trans hN)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp := hTp N ((le_max_left Tp Tq).trans hN) (largePairs N)
    (fun p hp => eighth_classicalPairGeometry h512 p (mem_filter.mp hp).1)
  have hpair := hq N ((le_max_right Tp Tq).trans hN)
  calc
    _ ≤ (1+η)*((N : ℝ)/log N)*(largeIntegral+η) :=
      hp.trans (mul_le_mul_of_nonneg_left hpair (by positivity))
    _ = ((1+η)*(largeIntegral+η))*((N : ℝ)/log N) := by ring
    _ ≤ (largeIntegral+ε)*((N : ℝ)/log N) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

/-- Unconditional classical high-region endpoint with the original closed cutoff.
No small-region bound is imported or assumed. -/
theorem large_integral_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((large N).card : ℝ) ≤
        (8*largeIntegral+ε)*wuSingularSeries N*N/log N^(2 : ℕ) := by
  let η := min 1 (ε/(largeIntegral+10))
  have hJ := largeIntegral_nonneg
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηE : η*(largeIntegral+10) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < largeIntegral+10)).mp (min_le_right _ _)
  have hc : (8+η)*(largeIntegral+η)+η ≤ 8*largeIntegral+ε := by
    nlinarith [mul_le_mul_of_nonneg_left hη1 hη.le]
  obtain ⟨Ts,hTs,hs⟩ := large_classical_mass_upper hη
  obtain ⟨Tm,_,hm⟩ := large_mass_upper hη
  refine ⟨max Ts Tm,hTs.trans (le_max_left _ _),?_⟩
  intro N hN he
  have h512 := hTs.trans ((le_max_left Ts Tm).trans hN)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := wuSingularSeries_pos N (by omega)
  have hsN := hs N ((le_max_left Ts Tm).trans hN) he
  have hmN := hm N ((le_max_right Ts Tm).trans hN)
  have hmul := mul_le_mul_of_nonneg_left hmN
    (show 0 ≤ (8+η)*wuSingularSeries N/log N by positivity)
  have hscale : 0 ≤ wuSingularSeries N*N/log N^(2 : ℕ) := by positivity
  calc
    _ ≤ ((8+η)*wuSingularSeries N/log N)*((largeIntegral+η)*N/log N) +
          η*wuSingularSeries N*N/log N^(2 : ℕ) := hsN.trans (add_le_add hmul le_rfl)
    _ = ((8+η)*(largeIntegral+η)+η)*(wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
    _ ≤ (8*largeIntegral+ε)*(wuSingularSeries N*N/log N^(2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hc hscale
    _ = _ := by ring

end U8MotherInsertion

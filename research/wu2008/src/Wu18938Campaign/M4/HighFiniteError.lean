import Wu18938Campaign.M4.HighTupleCube

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh HighNonunit Finset Real
open scoped Classical

theorem original_finite_error_bound {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 4 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) (high : Bool)
    (hmass : ∀ d ∈ boxConvolutionSupport (windows j N),
      (∑ q ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d), 1 / (q : ℝ)) ≤ 5) :
    originalFiniteError j N δ high ≤
      (40 * 5 ^ (if high then 6 else 5) : ℝ) * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass (windows j N) := by
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hinner (d : ℕ) (hdm : d ∈ boxConvolutionSupport (windows j N)) :
      (∑ t ∈ legalPrimeTuples N δ (Wu04RemainingCore.row j) high d,
        ((N : ℝ) / tupleProduct d t) / log t.2.1) ≤
      ((N : ℝ) / d) / ((1 / 40) * log N) * 5 ^ (if high then 6 else 5) := by
    have hrec := tuple_reciprocal_le (legalPrimeTuples N δ (Wu04RemainingCore.row j) high d)
      (fun t ht => high_tuple_length high (mem_filter.mp ht).1)
      (fun t ht => original_tuple_cube j (by omega) hd hh hdm (mem_filter.mp ht).1)
      (hmass d hdm)
    calc
      _ ≤ ∑ t ∈ legalPrimeTuples N δ (Wu04RemainingCore.row j) high d,
          (((N : ℝ) / d) / ((1 / 40) * log N)) * (1 / ((tupleList t).prod : ℝ)) := by
        apply sum_le_sum
        intro t ht
        have hdm' : d ∈ WuSource.SrcSingle.psiPrimes (j.castAdd 4) N := by
          simpa only [support_eq] using hdm
        have hp := (original_label_bounds j (by omega) hd hh hdm'
          (mem_primeTuples.mp (mem_filter.mp ht).1).2.1).2.1
        have hy := log_le_log (rpow_pos_of_pos (by positivity : (0 : ℝ) < N) _) hp
        rw [log_rpow (by positivity : (0 : ℝ) < N)] at hy
        calc
          _ ≤ ((N : ℝ) / tupleProduct d t) / ((1 / 40) * log N) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hy
          _ = _ := by simp only [tupleProduct, Nat.cast_mul]; ring
      _ = (((N : ℝ) / d) / ((1 / 40) * log N)) *
          (∑ t ∈ legalPrimeTuples N δ (Wu04RemainingCore.row j) high d,
            1 / ((tupleList t).prod : ℝ)) := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by positivity)
  unfold originalFiniteError boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hdm
  calc
    _ ≤ (convolutionCoeff (windows j N) d : ℝ) *
        (((N : ℝ) / d) / ((1 / 40) * log N) * 5 ^ (if high then 6 else 5)) :=
      mul_le_mul_of_nonneg_left (hinner d hdm) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem original_rough_finite_paid {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3, ∀ high : Bool,
      originalRoughMass j N δ high ≤ originalFiniteMain j N δ high +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (windows j N) := by
  let C : ℝ := 40 * 5 ^ 6
  have hC : 0 < C := by positivity
  obtain ⟨T0, hT04, hscalar⟩ := original_rough_finite_buchstab (div_pos heps hC)
  obtain ⟨T1, _, hmass⟩ := original_cube_mass
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro δ hd hh N hN j high
  have hs := hscalar δ hd hh N (by omega) j high
  have he := original_finite_error_bound j (by omega) hd hh high
    (hmass δ hd hh N (by omega) j)
  have hcap : (40 * 5 ^ (if high then 6 else 5) : ℝ) ≤ C := by
    cases high <;> norm_num [C]
  have hn : 0 ≤ ((N : ℝ) / log N) * boxConvolutionReciprocalMass (windows j N) := by
    have hlog := log_natCast_nonneg N
    have hm : 0 ≤ boxConvolutionReciprocalMass (windows j N) :=
      sum_nonneg (fun _ _ => by positivity)
    positivity
  have hb : originalFiniteError j N δ high ≤
      C * (((N : ℝ) / log N) * boxConvolutionReciprocalMass (windows j N)) :=
    he.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcap hn)
  have hp := mul_le_mul_of_nonneg_left hb (div_pos heps hC).le
  have hcancel : (ε / C) * (C * (((N : ℝ) / log N) *
      boxConvolutionReciprocalMass (windows j N))) =
      ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (windows j N) := by
    field_simp
  rw [hcancel] at hp
  exact hs.trans (add_le_add le_rfl hp)

end Wu18938Campaign.M4

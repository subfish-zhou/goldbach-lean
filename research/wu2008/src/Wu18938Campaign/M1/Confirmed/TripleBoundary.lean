import Wu18938Campaign.M1.Confirmed.TripleUnit
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleShiftedBoundary

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Triple

open Wu2008DoubleSieve LowerTripleGroupedFinite LowerTripleGroupedBoundary
  LowerTripleGroupedUnit Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem pairs_slab {m i N d : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) (j : Fin 6) :
    actualPairs N δ p j d ⊆ (primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)).product
      (primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)) := by
  let R := (N : ℝ) ^ (1 / 2 - δ) / d
  have hR := (hb.support_geometry hN hη hδ hd).2.2.1
  have hS : 0 < p.S := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (hp.one_le_s.trans (hp.s_le_kappa3.trans (hp.kappa3_lt_kappa2.le.trans
      (hp.kappa2_lt_kappa1.le.trans hp.kappa1_le_S))))
  have hlo : R ^ (1 / 10 : ℝ) ≤ wuLocalCutoff N δ d p.S :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le hS hp.S_le_ten)
  have hhi : wuLocalCutoff N δ d p.s ≤ R ^ (1 / 2 : ℝ) :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le (by norm_num) hs)
  have hw (r : ℕ) (hr : r ∈ primeWindow N (wuLocalCutoff N δ d p.S)
      (wuLocalCutoff N δ d p.s)) : r ∈ primeSlabPrimes R := by
    have hh := mem_primeWindow.mp hr
    exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
      ⟨hh.1,hlo.trans hh.2.2.1,hh.2.2.2.le.trans hhi⟩
  intro x hx
  have hpq := mem_pairs.mp hx
  exact mem_product.mpr ⟨hw x.1 hpq.1,hw x.2 hpq.2.1⟩

theorem boundary_weight {m i N d : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {j : Fin 6} {t : PrimeTriple} (ht : t ∈ badTriples N δ p j d) :
    mainWeight N d t ≤ (((N : ℝ) / d) / ((η / 10) * log N)) *
      (N : ℝ) ^ (-(η / 10)) * (1 / ((t.1 : ℝ) * t.2.1)) := by
  have hη' : 0 < η / 10 := by positivity
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hNpos : (0 : ℝ) < N := by positivity
  have hlegal := (mem_filter.mp ht).1
  have hactual := (mem_filter.mp hlegal).1
  have hq := (hb.mother_window_large (by omega) hη hδ p hp hd (mem_primeTriples.mp hactual).2.1).2
  have hlog := log_le_log (rpow_pos_of_pos hNpos (η / 10)) hq
  rw [log_rpow hNpos] at hlog
  have hrq : (t.2.1 : ℝ) < t.2.2 :=
    (le_max_left _ _).trans_lt (mem_primeTriples.mp hactual).2.2.2.2.2.2.1
  have hr : 1 / (t.2.2 : ℝ) ≤ (N : ℝ) ^ (-(η / 10)) := by
    rw [rpow_neg hNpos.le,← one_div]
    exact one_div_le_one_div_of_le (rpow_pos_of_pos hNpos _) (hq.trans hrq.le)
  calc
    _ ≤ ((N : ℝ) / tupleProduct d t) / log t.2.1 := legal_weight_le (hb.support_pos hd) hlegal
    _ ≤ ((N : ℝ) / tupleProduct d t) / ((η / 10) * log N) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hη' hlogN) hlog
    _ = ((((N : ℝ) / d) / ((η / 10) * log N)) * (1 / ((t.1 : ℝ) * t.2.1))) *
        (1 / (t.2.2 : ℝ)) := by simp only [tupleProduct,Nat.cast_mul]; ring
    _ ≤ ((((N : ℝ) / d) / ((η / 10) * log N)) * (1 / ((t.1 : ℝ) * t.2.1))) *
        (N : ℝ) ^ (-(η / 10)) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

theorem boundary_mass {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 6)
    (hmass : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (∑ q ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d), 1 / (q : ℝ)) ≤ 5) :
    boundaryMass N δ Δ V p j ≤ (5 ^ 2 / (η / 10)) * (N : ℝ) ^ (-(η / 10)) *
      ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hinner (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      (∑ t ∈ badTriples N δ p j d, mainWeight N d t) ≤
        (((N : ℝ) / d) / ((η / 10) * log N)) * (N : ℝ) ^ (-(η / 10)) * 5 ^ 2 := by
    have hrec := bad_pair_reciprocal_le (N := N) (d := d) (δ := δ) (P := p) (j := j)
    have hpair := pair_reciprocal_le (actualPairs N δ p j d)
      (pairs_slab hb (by omega) hη hδ p hp hs hd j) (hmass d hd)
    calc
      _ ≤ ∑ t ∈ badTriples N δ p j d,
          ((((N : ℝ) / d) / ((η / 10) * log N)) * (N : ℝ) ^ (-(η / 10))) *
            (1 / ((t.1 : ℝ) * t.2.1)) :=
        sum_le_sum (fun t ht => boundary_weight hb hN hη hδ p hp hd ht)
      _ = ((((N : ℝ) / d) / ((η / 10) * log N)) * (N : ℝ) ^ (-(η / 10))) *
          (∑ t ∈ badTriples N δ p j d, 1 / ((t.1 : ℝ) * t.2.1)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrec.trans hpair) (by positivity)
  unfold boundaryMass boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        ((((N : ℝ) / d) / ((η / 10) * log N)) * (N : ℝ) ^ (-(η / 10)) * 5 ^ 2) :=
      mul_le_mul_of_nonneg_left (hinner d hd) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem boundary_paid (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ j : Fin 6,
      finiteBuchstabMain N δ Δ V p j ≤ unshiftedFiniteBuchstabMain N δ Δ V p j +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  let C : ℝ := 5 ^ 2 / (η / 10)
  have hlim : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(η / 10))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_apply] using
      ((tendsto_rpow_neg_atTop (show 0 < η / 10 by positivity)).comp
        tendsto_natCast_atTop_atTop).const_mul C
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds he))
  obtain ⟨T1,hT14,hm⟩ := roughBox_cube_mass m (δ := δ) hη
  refine ⟨max T0 T1,hT14.trans (le_max_right _ _),?_⟩
  intro N hN i Δ V hb p hp hs j
  have hc := (hT0 N (by omega)).le
  have hbound := boundary_mass hb (by omega) hη hδ p hp hs j (hm N (by omega) i Δ V hb)
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hX : 0 ≤ ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg N) hlogN.le) (sum_nonneg (fun _ _ => by positivity))
  have hpay := mul_le_mul_of_nonneg_right hc hX
  rw [main_split]
  dsimp only [C] at hpay
  nlinarith only [hbound,hpay]

end Wu18938Campaign.M1.Confirmed.Triple

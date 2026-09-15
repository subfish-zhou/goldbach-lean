import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleFiniteErrorPayment

namespace Wu2008DoubleSieve.LowerTripleGroupedFinite
open Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

/-- The actual source quotient has square at most the residual scale. -/
theorem sourceR_square_le {k i N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    ((N:ℝ)^(1/2-δ)/d)^2 ≤ (N:ℝ)/d := by
  have hd0 : 0 < d := boxConvolutionSupport_pos
    (fun _ _ h => (mem_convolutionWuWindows.mp h).1.pos) hd
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd0
  have hdR : (0:ℝ) < d := by positivity
  have hg := omega3XPhi_source_bounds hN hδ hδhi hb hd
  have hX : (0:ℝ) < (N:ℝ)/d := div_pos (by positivity) hdR
  have hphi : 2 ≤ omega3XPhi N d δ := le_trans
    (le_add_of_nonneg_right (div_nonneg (by positivity) (by linarith))) hg.2.2.1
  rw [omega3XPhi, le_div_iff₀ (log_pos hg.2.1)] at hphi
  apply (log_le_log_iff (sq_pos_of_pos (lt_trans zero_lt_one hg.2.1)) hX).mp
  simpa only [log_pow, Nat.cast_ofNat] using hphi

/-- Each complete triple has the genuine three-coordinate power cap. -/
theorem actual_tuple_product_le {k i N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {j : Fin 6} {t : PrimeTriple} (ht : t ∈ actualPrimeTriples N δ p j d) :
    ((tupleList t).prod : ℝ) ≤ (((N:ℝ)^(1/2-δ)/d)^(3/2:ℝ)) := by
  let R := (N:ℝ)^(1/2-δ)/d
  have hR : 0 < R := lt_trans zero_lt_one
    (omega3XPhi_source_bounds hN hδ hδhi hb hd).2.1
  have hc := actual_tuple_cube hN hδ hδhi hb p hp hs hd ht
  have hcoord (j : Fin 3) : (tupleCoordinates t j : ℝ) ≤ R^(1/2:ℝ) := by
    have hj : j.val < (tupleList t).length := by rw [tupleList_length]; exact j.isLt
    have hm : tupleCoordinates t j ∈ tupleList t := by
      simp only [tupleCoordinates, List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    exact ((mem_primesIcc (rpow_nonneg hR.le _)).mp (hc _ hm)).2.2
  have hh := prod_le_prod (s := (univ : Finset (Fin 3)))
    (fun j _ => Nat.cast_nonneg (tupleCoordinates t j)) (fun j _ => hcoord j)
  rw [tupleCoordinates_product, prod_const, card_univ, Fintype.card_fin] at hh
  have he : (R^(1/2:ℝ))^3 = R^(3/2:ℝ) := by
    rw [← rpow_natCast, ← rpow_mul hR.le]
    norm_num
  exact hh.trans_eq he

/-- Pointwise power saving, with the original sigma coefficient exactly once. -/
theorem unitMass_power_le {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 6)
    (hmass : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (∑ q ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d), 1/(q:ℝ)) ≤ 5) :
    unitMass N δ Δ V p j ≤ 5^3 * (N:ℝ) * (N:ℝ)^(-wuLocalExponent k δ/2) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  have inner (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      (∑ t ∈ actualPrimeTriples N δ p j d, if tupleProduct d t ≤ N then (1:ℝ) else 0) ≤
        5^3 * ((N:ℝ)/d) * (N:ℝ)^(-wuLocalExponent k δ/2) := by
    let R := (N:ℝ)^(1/2-δ)/d
    have hg := omega3XPhi_source_bounds hN hδ hδhi hb hd
    have hR : 0 < R := lt_trans zero_lt_one hg.2.1
    have hrec := tuple_reciprocal_le (actualPrimeTriples N δ p j d)
      (fun t ht => actual_tuple_cube hN hδ hδhi hb p hp hs hd ht) (hmass d hd)
    have hpw : R^(3/2:ℝ) ≤ ((N:ℝ)/d) * (N:ℝ)^(-wuLocalExponent k δ/2) := by
      have he : R^(3/2:ℝ) = R^2 * R^(-(1/2):ℝ) := by
        rw [← rpow_two, ← rpow_add hR]
        norm_num
      have hn := rpow_le_rpow_of_nonpos
        (rpow_pos_of_pos (by positivity : (0:ℝ) < N) _) hg.1 (by norm_num : (-(1/2):ℝ) ≤ 0)
      rw [← rpow_mul (by positivity : (0:ℝ) ≤ N)] at hn
      have hexp : wuLocalExponent k δ * (-(1/2)) = -wuLocalExponent k δ/2 := by ring
      rw [hexp] at hn
      rw [he]
      exact mul_le_mul (sourceR_square_le hN hδ hδhi hb hd) hn
        (rpow_nonneg hR.le _) (by positivity)
    calc
      _ ≤ ∑ t ∈ actualPrimeTriples N δ p j d,
          R^(3/2:ℝ) * (1/((tupleList t).prod : ℝ)) := by
        apply sum_le_sum
        intro t ht
        have ht0 : 0 < (tupleList t).prod := by
          have hh := tupleProduct_pos (show 0 < 1 by omega) ht
          simpa only [tupleProduct_literal, one_mul] using hh
        have htR : (0:ℝ) < (tupleList t).prod := by exact_mod_cast ht0
        have hc : (1:ℝ) ≤ R^(3/2:ℝ) / ((tupleList t).prod : ℝ) :=
          (le_div_iff₀ htR).mpr (by
            simpa only [one_mul] using actual_tuple_product_le hN hδ hδhi hb p hp hs hd ht)
        calc
          _ ≤ (1:ℝ) := by split_ifs <;> norm_num
          _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul] using hc
      _ = R^(3/2:ℝ) * (∑ t ∈ actualPrimeTriples N δ p j d,
          1/((tupleList t).prod : ℝ)) := by rw [mul_sum]
      _ ≤ R^(3/2:ℝ) * 5^3 := mul_le_mul_of_nonneg_left hrec (rpow_nonneg hR.le _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hpw (by norm_num : (0:ℝ) ≤ 5^3)]
  unfold unitMass boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        (5^3 * ((N:ℝ)/d) * (N:ℝ)^(-wuLocalExponent k δ/2)) :=
      mul_le_mul_of_nonneg_left (inner d hd) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The full six-band power bound uses the actual slab producer internally. -/
theorem unitMass_six_power_bound (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      (∀ j : Fin 6, unitMass N δ Δ V p j ≤ 5^3 * (N:ℝ) *
        (N:ℝ)^(-wuLocalExponent k δ/2) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) ∧
      (∑ j : Fin 6, unitMass N δ Δ V p j) ≤ (6*5^3) * (N:ℝ) *
        (N:ℝ)^(-wuLocalExponent k δ/2) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hm⟩ := HighNonunit.source_cube_mass k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp hs
  have hj := fun j => unitMass_power_le (by omega) hδ hδhi hb p hp hs j
    (hm N hN i Δ V hb)
  refine ⟨hj,?_⟩
  have hh := sum_le_sum (s := (univ : Finset (Fin 6))) (fun j _ => hj j)
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    mul_assoc] using hh

/-- Genuine logarithm versus power decay, with no numerical threshold oracle. -/
theorem unit_power_log_decay {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => log (N:ℝ) * (N:ℝ)^(-a)) atTop (nhds 0) := by
  have hh := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  have he : Tendsto (fun R : ℝ => log R * R^(-a)) atTop (nhds 0) := by
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    rw [rpow_neg hR.le, div_eq_mul_inv]
  exact he.comp tendsto_natCast_atTop_atTop

/-- One threshold precedes all boxes, mother parameters and six bands. -/
theorem unitMass_six_negligible (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      (∀ j : Fin 6, unitMass N δ Δ V p j ≤ ε * ((N:ℝ)/log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) ∧
      (∑ j : Fin 6, unitMass N δ Δ V p j) ≤ ε * ((N:ℝ)/log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT0,h0⟩ := HighNonunit.source_cube_mass k hδ hδhi
  have ha : 0 < wuLocalExponent k δ/2 := half_pos (wuLocalExponent_pos k hδ hδhi)
  obtain ⟨T1,h1⟩ := eventually_atTop.mp
    ((unit_power_log_decay ha).eventually (gt_mem_nhds (show (0:ℝ) < ε/(6*5^3) by positivity)))
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp hs
  have hN0 := (le_max_left T0 T1).trans hN
  have hN4 := hT0.trans hN0
  have hl : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsmall := (h1 N ((le_max_right T0 T1).trans hN)).le
  have hn : (N:ℝ)^(-wuLocalExponent k δ/2) ≤ ε/(6*5^3)/log N := by
    apply (le_div_iff₀ hl).mpr
    simpa only [neg_div, mul_comm] using hsmall
  let W := boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)
  have hW : 0 ≤ W := sum_nonneg (fun _ _ => by positivity)
  have hj (j : Fin 6) : unitMass N δ Δ V p j ≤
      (ε/6) * ((N:ℝ)/log N) * W := by
    apply (unitMass_power_le (by omega) hδ hδhi hb p hp hs j (h0 N hN0 i Δ V hb)).trans
    calc
      _ ≤ 5^3 * (N:ℝ) * (ε/(6*5^3)/log N) * W :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by positivity)) hW
      _ = _ := by ring
  constructor
  · intro j
    exact (hj j).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : ε/6 ≤ ε) (div_nonneg (by positivity) hl.le)) hW)
  · have hh := sum_le_sum (s := (univ : Finset (Fin 6))) (fun j _ => hj j)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hh
    calc
      _ ≤ 6 * ((ε/6) * ((N:ℝ)/log N) * W) := hh
      _ = _ := by dsimp only [W]; ring

end Wu2008DoubleSieve.LowerTripleGroupedFinite

import WR2GammaHighLowerTripleClosedK
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleUnitNegligible

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGroupedFinite HighBoxRecovery Real Finset LiLiuPrereqBuchstab
open scoped Classical

/-- The actual source quotient has square at most the residual scale. -/
theorem sourceR_square_le {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hd : d ∈ boxConvolutionSupport (windows j N)) :
    ((N:ℝ)^(1/2-δ)/d)^2 ≤ (N:ℝ)/d := by
  have hd0 : 0 < d := boxConvolutionSupport_pos
    (fun _ _ h => (mem_primeWindow.mp h).1.pos) hd
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd0
  have hdR : (0:ℝ) < d := by positivity
  have hg := phi_bounds j hN hδ hδhi hd
  have hX : (0:ℝ) < (N:ℝ)/d := div_pos (by positivity) hdR
  have hphi : 2 ≤ omega3XPhi N d δ := le_trans
    (le_add_of_nonneg_right (div_nonneg (by positivity) (by linarith))) hg.2.2.1
  rw [omega3XPhi, le_div_iff₀ (log_pos hg.2.1)] at hphi
  apply (log_le_log_iff (sq_pos_of_pos (lt_trans zero_lt_one hg.2.1)) hX).mp
  simpa only [log_pow, Nat.cast_ofNat] using hphi

/-- Each complete triple has the genuine three-coordinate power cap. -/
theorem actual_tuple_product_le {N d : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hd : d ∈ boxConvolutionSupport (windows j N))
    {k : Fin 6} {t : PrimeTriple} (ht : t ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d) :
    ((tupleList t).prod : ℝ) ≤ (((N:ℝ)^(1/2-δ)/d)^(3/2:ℝ)) := by
  let R := (N:ℝ)^(1/2-δ)/d
  have hR : 0 < R := lt_trans zero_lt_one
    (phi_bounds j hN hδ hδhi hd).2.1
  have hc := actual_tuple_cube j hN hδ hδhi hd ht
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
theorem unitMass_power_le {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (k : Fin 6)
    (hmass : ∀ d ∈ boxConvolutionSupport (windows j N),
      (∑ q ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d), 1/(q:ℝ)) ≤ 5) :
    unitMass j N δ k ≤ 5^3 * (N:ℝ) * (N:ℝ)^(-(10*highEta)/2) *
      boxConvolutionReciprocalMass (windows j N) := by
  have inner (d : ℕ) (hd : d ∈ boxConvolutionSupport (windows j N)) :
      (∑ t ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d, if tupleProduct d t ≤ N then (1:ℝ) else 0) ≤
        5^3 * ((N:ℝ)/d) * (N:ℝ)^(-(10*highEta)/2) := by
    let R := (N:ℝ)^(1/2-δ)/d
    have hg := phi_bounds j hN hδ hδhi hd
    have hR : 0 < R := lt_trans zero_lt_one hg.2.1
    have hrec := tuple_reciprocal_le (actualPrimeTriples N δ (Wu04RemainingCore.row j) k d)
      (fun t ht => actual_tuple_cube j hN hδ hδhi hd ht) (hmass d hd)
    have hpw : R^(3/2:ℝ) ≤ ((N:ℝ)/d) * (N:ℝ)^(-(10*highEta)/2) := by
      have he : R^(3/2:ℝ) = R^2 * R^(-(1/2):ℝ) := by
        rw [← rpow_two, ← rpow_add hR]
        norm_num
      have hn := rpow_le_rpow_of_nonpos
        (rpow_pos_of_pos (by positivity : (0:ℝ) < N) _) hg.1 (by norm_num : (-(1/2):ℝ) ≤ 0)
      rw [← rpow_mul (by positivity : (0:ℝ) ≤ N)] at hn
      have hexp : (10*highEta) * (-(1/2)) = -(10*highEta)/2 := by ring
      rw [hexp] at hn
      rw [he]
      exact mul_le_mul (sourceR_square_le j hN hδ hδhi hd) hn
        (rpow_nonneg hR.le _) (by positivity)
    calc
      _ ≤ ∑ t ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d,
          R^(3/2:ℝ) * (1/((tupleList t).prod : ℝ)) := by
        apply sum_le_sum
        intro t ht
        have ht0 : 0 < (tupleList t).prod := by
          have hh := tupleProduct_pos (show 0 < 1 by omega) ht
          simpa only [tupleProduct_literal, one_mul] using hh
        have htR : (0:ℝ) < (tupleList t).prod := by exact_mod_cast ht0
        have hc : (1:ℝ) ≤ R^(3/2:ℝ) / ((tupleList t).prod : ℝ) :=
          (le_div_iff₀ htR).mpr (by
            simpa only [one_mul] using actual_tuple_product_le j hN hδ hδhi hd ht)
        calc
          _ ≤ (1:ℝ) := by split_ifs <;> norm_num
          _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul] using hc
      _ = R^(3/2:ℝ) * (∑ t ∈ actualPrimeTriples N δ (Wu04RemainingCore.row j) k d,
          1/((tupleList t).prod : ℝ)) := by rw [mul_sum]
      _ ≤ R^(3/2:ℝ) * 5^3 := mul_le_mul_of_nonneg_left hrec (rpow_nonneg hR.le _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hpw (by norm_num : (0:ℝ) ≤ 5^3)]
  unfold unitMass boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (windows j N) d : ℝ) *
        (5^3 * ((N:ℝ)/d) * (N:ℝ)^(-(10*highEta)/2)) :=
      mul_le_mul_of_nonneg_left (inner d hd) (Nat.cast_nonneg _)
    _ = _ := by ring

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.unitMass_power_le

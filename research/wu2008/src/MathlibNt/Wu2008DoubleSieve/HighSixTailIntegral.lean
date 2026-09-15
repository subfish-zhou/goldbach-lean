import MathlibNt.Wu2008DoubleSieve.HighSixTailPayment

namespace Wu2008DoubleSieve.HighSixTail
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open SingleUpperCounts SingleUpperSplice SingleUpperNormalization
open SingleUpperQuadrature SingleUpperPrimePayment SingleUpperHighQuadrature
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
theorem tail_integral_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100) :
    0 ≤ ∫ t in HighSix.right..(1/3 : ℝ), weight δ t/t := by
  apply intervalIntegral.integral_nonneg (by norm_num [HighSix.right])
  intro t ht
  have ht' : t ∈ Icc (1/15 : ℝ) (1/3) :=
    ⟨by norm_num [HighSix.right] at ht ⊢; linarith [ht.1],ht.2⟩
  exact div_nonneg (weight_nonneg hδ hδhi ht') (by linarith [ht'.1])

/-- Every analytic producer is consumed at a common threshold. The original
closed quadrature absorbs the extra upper atom, even for a zero-length interval. -/
theorem actual_tail_with_tau {δ τ : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      HighSix.U3tailCount N ≤
        (4*(1+τ)^2*((∫ t in (HighSix.right)..(1/3 : ℝ), weight δ t/t)+301*τ)+τ) *
          truncatedSixthMassScale N := by
  obtain ⟨TA,hTA4,hA⟩ := actual_tail_density hδ hδhi
    (show 0 < exp eulerMascheroniConstant*τ/2 by positivity) hτ
  obtain ⟨TD,_hTD4,hD⟩ := tail_density_normalized hδ.le hδhi hτ hτ1
  obtain ⟨TS,_hTS4,hS⟩ := tail_weight_sum_upper hδ.le hδhi hτ
  obtain ⟨TQ,_hTQ4,hQ⟩ := weighted_prime_quadrature hτ
  obtain ⟨TL,_hTL4,hL⟩ := trueLi_upper hτ
  refine ⟨max TA (max TD (max TS (max TQ TL))),
    hTA4.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hrlo : HighSix.right ≤ (1/3 : ℝ) := by norm_num [HighSix.right]
  have hrhi : (1/3 : ℝ) ≤ 1/3 := le_rfl
  have hNA : TA ≤ N := (le_max_left _ _).trans hN
  have hND : TD ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNS : TS ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNQ : TQ ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
  have hNL : TL ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
  have hN4 := hTA4.trans hNA
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  have hcoef : 0 ≤ 4*logarithmicIntegral N*wuSingularSeries N/log N := by positivity
  let I := ∫ t in (HighSix.right)..(1/3 : ℝ), weight δ t/t
  have hI : 0 ≤ I := tail_integral_nonneg hδ.le hδhi
  have hquad := (abs_lt.mp (hQ N hNQ δ (HighSix.right) (1/3 : ℝ) hδ.le hδhi
    (by norm_num [HighSix.right]) hrlo hrhi)).2
  have hsum := (hS N hNS).trans
    (mul_le_mul_of_nonneg_left
      (show (∑ p ∈ primesIcc ((N : ℝ)^(HighSix.right)) ((N : ℝ)^(1/3 : ℝ)),
        weight δ (log p/log N)/(p : ℝ)) + 300*τ ≤ I+301*τ by dsimp [I]; linarith)
      (show 0 ≤ 1+τ by positivity))
  have hcoeff : 4*logarithmicIntegral N*wuSingularSeries N/log N ≤
      4*(1+τ)*truncatedSixthMassScale N := by
    calc
      _ ≤ 4*((1+τ)*(N : ℝ)/log N)*wuSingularSeries N/log N := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hL N hNL) (by norm_num)) hC)
          hlog.le
      _ = _ := by unfold truncatedSixthMassScale; ring
  have hdensity := (hD N hND he).trans (mul_le_mul_of_nonneg_left hsum hcoef)
  have hpaid := hdensity.trans (mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ (1+τ)*(I+301*τ) by positivity))
  have hactual := (hA N hNA he).trans (add_le_add hpaid le_rfl)
  convert hactual using 1 <;> first | rfl | ring

/-- The actual masked tail, with the whole prime mass and true li error paid before N. -/
theorem actual_tail_classical_upper {δ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      HighSix.U3tailCount N ≤
        (4*(∫ t in HighSix.right..(1/3 : ℝ), weight δ t/t)+ε)*truncatedSixthMassScale N := by
  let I := ∫ t in HighSix.right..(1/3 : ℝ), weight δ t/t
  obtain ⟨τ,hτ,hτ1,hbudget⟩ := polynomial_budget
    (show 0 < |I|+1 by positivity) hε
  obtain ⟨T,hT4,hT⟩ := actual_tail_with_tau hδ hδhi hτ hτ1
  refine ⟨T,hT4,?_⟩
  intro N hN he
  have hN4 := hT4.trans hN
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hscale : 0 ≤ truncatedSixthMassScale N := by unfold truncatedSixthMassScale; positivity
  exact (hT N hN he).trans (mul_le_mul_of_nonneg_right
    (hbudget I ((le_abs_self I).trans (by linarith))) hscale)

end Wu2008DoubleSieve.HighSixTail

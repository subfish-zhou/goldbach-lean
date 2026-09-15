import MixedEtaDebit

namespace MixedEta
open Finset Real Wu2008DoubleSieve Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.PrimeReciprocalLogRectangle
noncomputable section

/-- A fixed enclosing rectangle, only for an upper bound on the eta debit. -/
def envelopeReciprocal (N : ℕ) : ℝ :=
  primeReciprocalLogRectangle N (truncatedSixthLowerAlpha/2) 1 (truncatedSixthLowerAlpha/2) 1

def envelopeMass : ℝ :=
  logarithmicRectangleMass (truncatedSixthLowerAlpha/2) 1 (truncatedSixthLowerAlpha/2) 1

def etaConstant : ℝ := (16/truncatedSixthLowerAlpha)*(envelopeMass+1)

theorem etaConstant_pos : 0 < etaConstant := by
  have he : 0 ≤ envelopeMass := by
    unfold envelopeMass logarithmicRectangleMass
    exact mul_self_nonneg _
  unfold etaConstant
  exact mul_pos (div_pos (by norm_num) truncatedSixthLower_parameters.1) (by linarith)

theorem reciprocal_enclosed {N : ℕ} {δ : ℝ} (hN : 1 < N) :
    (∑ p ∈ truncatedSixthLowerPairs N δ, 1/((p.1:ℝ)*p.2)) ≤ envelopeReciprocal N := by
  let P := (range (MathlibNt.SieveTheory.PrimeReciprocalLogScale.rpowFloor N 1+1)).filter
    (fun p => Nat.Prime p ∧ (N:ℝ)^(truncatedSixthLowerAlpha/2) < p ∧ (p:ℝ) ≤ (N:ℝ)^(1:ℝ))
  have hNR : (1:ℝ) < N := by exact_mod_cast hN
  have hpar := truncatedSixthLower_parameters
  have hmem {p : ℕ} {a b : ℝ} (ha : truncatedSixthLowerAlpha ≤ a) (hb : b ≤ 1)
      (hp : p ∈ primeWindow N ((N:ℝ)^a) ((N:ℝ)^b)) : p ∈ P := by
    obtain ⟨hp,hcop,hlo,hhi⟩ := mem_primeWindow.mp hp
    have hup : (p:ℝ) ≤ (N:ℝ)^(1:ℝ) := hhi.le.trans (rpow_le_rpow_of_exponent_le hNR.le hb)
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hup)),hp,?_,hup⟩
    exact (rpow_lt_rpow_of_exponent_lt hNR (show truncatedSixthLowerAlpha/2 < a by linarith [hpar.1])).trans_le hlo
  have hsub : truncatedSixthLowerPairs N δ ⊆ P ×ˢ P := by
    intro p hp
    obtain ⟨hp,hq⟩ := mem_product.mp (mem_filter.mp hp).1
    exact mem_product.mpr ⟨hmem le_rfl (by linarith [hpar.2.2.1,hpar.2.2.2.1]) hp,
      hmem hpar.2.1.le (by linarith [hpar.2.2.2.1]) hq⟩
  have hs := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
    (show 0 ≤ 1/((p.1:ℝ)*p.2) by positivity))
  simpa only [envelopeReciprocal,primeReciprocalLogRectangle,sum_product,P] using hs

/-- Pointwise retained-polygon bound uses actual totient and actual retained logarithm. -/
theorem classical_point_upper {N : ℕ} {δ : ℝ} {p : ℕ × ℕ}
    (hN : 4 ≤ N) (hδ : 0 ≤ δ) (hp : p ∈ truncatedSixthLowerPairs N δ)
    (hli : logarithmicIntegral N ≤ 2*(N:ℝ)/log N) :
    truncatedSixthLowerClassicalTheta N δ p ≤
      (16/truncatedSixthLowerAlpha)*truncatedSixthMassScale N*(1/((p.1:ℝ)*p.2)) := by
  have hN1 : 1 < N := by omega
  have hN0 : 0 < N := by omega
  have hlog : 0 < log (N:ℝ) := log_pos (by exact_mod_cast hN1)
  obtain ⟨hpm,hqm⟩ := mem_product.mp (mem_filter.mp hp).1
  have hpP := (mem_primeWindow.mp hpm).1
  have hqP := (mem_primeWindow.mp hqm).1
  have hp0 : (0:ℝ) < p.1 := by exact_mod_cast hpP.pos
  have hq0 : (0:ℝ) < p.2 := by exact_mod_cast hqP.pos
  have ha := truncatedSixthLower_parameters.1
  have hC := (wuSingularSeries_pos N hN0).le
  have ht := MixedRecovery.pair_totient_lower hpP hqP
  have hl := MixedRecovery.retained_log_lower hN1 hδ hp
  have hbase : 0 < (p.1:ℝ)*p.2/4 := by positivity
  have hden : (p.1:ℝ)*p.2/4*(2*truncatedSixthLowerAlpha*log N) ≤
      (Nat.totient (p.1*p.2):ℝ)*log ((N:ℝ)^truncatedSixthLowerC δ/(p.1*p.2:ℕ)) :=
    mul_le_mul ht hl (by positivity) (Nat.cast_nonneg _)
  have hden0 : 0 < (p.1:ℝ)*p.2/4*(2*truncatedSixthLowerAlpha*log N) := by positivity
  have hnum := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hli (show (0:ℝ) ≤ 4 by norm_num)) hC
  unfold truncatedSixthLowerClassicalTheta
  apply (div_le_div_of_nonneg_right hnum (hden0.le.trans hden)).trans
  apply (div_le_div_of_nonneg_left (show 0 ≤ 4*(2*(N:ℝ)/log N)*wuSingularSeries N by positivity)
    hden0 hden).trans
  apply le_of_eq
  unfold truncatedSixthMassScale
  field_simp
  ring

/-- A genuine full-domain upper constant, uniform in all nonnegative delta. -/
theorem total_classical_upper : ∀ᶠ N : ℕ in atTop, ∀ δ : ℝ, 0 ≤ δ →
    classicalMass N δ (truncatedSixthLowerPairs N δ) ≤ etaConstant*truncatedSixthMassScale N := by
  have ha := truncatedSixthLower_parameters.1
  have ha1 : truncatedSixthLowerAlpha/2 < (1:ℝ) := by
    have hp := truncatedSixthLower_parameters
    linarith [hp.2.1,hp.2.2.1,hp.2.2.2.1]
  have hm := tendsto_primeReciprocalLogRectangle (half_pos ha) ha1 (half_pos ha) ha1
  have he : ∀ᶠ N : ℕ in atTop, envelopeReciprocal N < envelopeMass+1 :=
    hm.eventually_lt_const (by unfold envelopeMass; linarith)
  obtain ⟨T,hT,hli⟩ := SingleUpperPrimePayment.trueLi_upper (show (0:ℝ) < 1 by norm_num)
  filter_upwards [he,eventually_ge_atTop T] with N hmass hN
  intro δ hδ
  have hN4 : 4 ≤ N := hT.trans hN
  have hl : logarithmicIntegral N ≤ 2*(N:ℝ)/log N := by
    have h := hli N hN
    norm_num at h
    exact h
  have hs := sum_le_sum (fun p hp => classical_point_upper hN4 hδ hp hl)
  have hscale := truncatedSixthClosure_scale_nonneg hN4
  have hc : 0 ≤ (16/truncatedSixthLowerAlpha)*truncatedSixthMassScale N := by positivity
  rw [← mul_sum] at hs
  apply hs.trans
  have hb := (reciprocal_enclosed (δ := δ) (show 1 < N by omega)).trans hmass.le
  have hh := mul_le_mul_of_nonneg_left hb hc
  unfold etaConstant
  convert hh using 1
  ring

end
end MixedEta

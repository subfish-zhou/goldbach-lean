import MathlibNt.Wu2008DoubleSieve.HighSixTailNormalization

namespace Wu2008DoubleSieve.HighSixTail
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open SingleUpperCounts SingleUpperSplice SingleUpperNormalization
open SingleUpperQuadrature SingleUpperPrimePayment SingleUpperHighQuadrature
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
/-- Half-open coprime tail embeds into the closed prime interval only by inclusion. -/
theorem tail_subset_closed {N : ℕ} :
    tailPrimes N ⊆ primesIcc ((N : ℝ)^HighSix.right) ((N : ℝ)^(1/3 : ℝ)) := by
  intro p hp
  obtain ⟨hpp,_,hlo,hhi⟩ := mem_primeWindow.mp hp
  exact (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) _)).mpr ⟨hpp,hlo,hhi.le⟩

/-- Pointwise phi correction and the 6*tau loss are paid before enlargement.
The closed reciprocal mass bounds the whole loss, not individual atoms. -/
theorem tail_weight_sum_upper {δ τ : ℝ} (hδ : 0 ≤ δ)
    (hδhi : δ ≤ 1/100) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      (∑ p ∈ tailPrimes N,
        (wuUpperCoefficient (((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha)+6*τ) /
          ((Nat.totient p : ℝ)*((1/2-δ)-log (p : ℝ)/log N))) ≤
        (1+τ)*((∑ p ∈ primesIcc ((N : ℝ)^(HighSix.right)) ((N : ℝ)^(1/3 : ℝ)),
          weight δ (log p/log N)/(p : ℝ)) + 300*τ) := by
  obtain ⟨TD,hTD4,hD⟩ := denominator_payment hτ
  obtain ⟨TM,_hTM4,hM⟩ := reciprocal_mass_bound
  refine ⟨max TD TM, hTD4.trans (le_max_left _ _), ?_⟩
  intro N hN
  have hrlo : HighSix.right ≤ (1/3 : ℝ) := by norm_num [HighSix.right]
  have hrhi : (1/3 : ℝ) ≤ 1/3 := le_rfl
  have hND : TD ≤ N := (le_max_left _ _).trans hN
  have hNM : TM ≤ N := (le_max_right _ _).trans hN
  have hN4 := hTD4.trans hND
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 2 ≤ N by omega)
  have hb : (1/15 : ℝ) ≤ HighSix.right := by norm_num [HighSix.right]
  let P := primesIcc ((N : ℝ)^(HighSix.right)) ((N : ℝ)^(1/3 : ℝ))
  have hcoord (p : ℕ) (hp : p ∈ P) : log (p : ℝ)/log N ∈ Icc (1/15 : ℝ) (1/3) := by
    have h := closed_coordinate (by omega : 2 ≤ N) hp
    exact ⟨hb.trans h.1,h.2.trans hrhi⟩
  have hterm (p : ℕ) (hp : p ∈ tailPrimes N) :
      (wuUpperCoefficient (((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha)+6*τ) /
        ((Nat.totient p : ℝ)*((1/2-δ)-log (p : ℝ)/log N)) ≤
      (1+τ)*(weight δ (log p/log N)/(p : ℝ)+60*τ/(p : ℝ)) := by
    have hpP := tail_subset_closed hp
    have hpp := (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) _)).mp hpP
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.1.pos
    have ht := hcoord p hpP
    have hc : (1/10 : ℝ) ≤ (1/2-δ)-log (p : ℝ)/log N := by linarith [ht.2]
    have hc0 : 0 < (1/2-δ)-log (p : ℝ)/log N := by linarith
    have hw := weight_nonneg hδ hδhi ht
    have hden := (hD N hND p hpp.1
      ((rpow_le_rpow_of_exponent_le hN1.le hb).trans hpp.2.1)).2.2
    have herr : 6*τ/((1/2-δ)-log (p : ℝ)/log N) ≤ 60*τ := by
      apply (div_le_iff₀ hc0).mpr
      have h := mul_le_mul_of_nonneg_left hc (show 0 ≤ 60*τ by positivity)
      nlinarith
    have heq :
        (wuUpperCoefficient (((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha)+6*τ) /
          ((Nat.totient p : ℝ)*((1/2-δ)-log (p : ℝ)/log N)) =
        (weight δ (log p/log N)+6*τ/((1/2-δ)-log (p : ℝ)/log N)) *
          (1/(Nat.totient p : ℝ)) := by
      unfold weight
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq]
    calc
      _ ≤ (weight δ (log p/log N)+6*τ/((1/2-δ)-log (p : ℝ)/log N))*((1+τ)/p) :=
        mul_le_mul_of_nonneg_left hden (add_nonneg hw (by positivity))
      _ ≤ (weight δ (log p/log N)+60*τ)*((1+τ)/p) :=
        mul_le_mul_of_nonneg_right (add_le_add le_rfl herr) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ p ∈ tailPrimes N,
        (1+τ)*(weight δ (log p/log N)/(p : ℝ)+60*τ/(p : ℝ)) := sum_le_sum hterm
    _ ≤ ∑ p ∈ P, (1+τ)*(weight δ (log p/log N)/(p : ℝ)+60*τ/(p : ℝ)) := by
      apply sum_le_sum_of_subset_of_nonneg tail_subset_closed
      intro p hp _
      have hw := weight_nonneg hδ hδhi (hcoord p hp)
      positivity
    _ = (1+τ)*((∑ p ∈ P, weight δ (log p/log N)/(p : ℝ)) +
        60*τ*(∑ p ∈ P, 1/(p : ℝ))) := by
      rw [← mul_sum, sum_add_distrib, mul_sum]
      congr 2
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ _ := by
      have hh := hM N hNM (HighSix.right) (1/3 : ℝ) hb hrlo hrhi
      have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 60*τ by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1+τ)
      dsimp [P] at *
      linarith

end Wu2008DoubleSieve.HighSixTail

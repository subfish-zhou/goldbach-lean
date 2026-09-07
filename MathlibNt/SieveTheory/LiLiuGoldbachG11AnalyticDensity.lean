import MathlibNt.SieveTheory.LiLiuGoldbachG11ProgressionEuler
import MathlibNt.SieveTheory.LiLiuFouvryG9BaseEuler

open Finset
open scoped BigOperators Classical
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11EulerCorrection (N : ℕ) : ℝ := (1+1/((N : ℝ)^(4/53 : ℝ)-2))^21

/-- Uniform analytic evaluation of a finite weighted progression-density main
term. Its hypotheses are literal rough support and nonnegative weights, not an
assumed distribution estimate. The constants precede all changing finite data. -/
theorem goldbachG11_weighted_density_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 1 < K ∧ ∀ θ : ℝ, 0 < θ → θ < 1/8 →
    ∃ Q₀ : ℝ, 4 ≤ Q₀ ∧ ∀ N : ℕ, 4 ≤ N → Even N →
    4 ≤ (N : ℝ)^(4/53 : ℝ) → ∀ Q : ℝ, Q₀ ≤ Q → Q ≤ N → Real.sqrt (N : ℝ) ≤ Q^2 →
    0 ≤ fouvryG9UpperFactor N Q C K θ ∧
    ∀ (ι : Type) (I : Finset ι) (a : ι → ℕ) (w : ι → ℝ),
    (∀ i ∈ I, 0 ≤ w i) →
    (∀ i ∈ I, w i ≠ 0 → 0 < a i ∧
      (∀ p ∈ (a i).primeFactors,(N : ℝ)^(4/53 : ℝ) ≤ (p : ℝ)) ∧
      (a i).primeFactors.card ≤ 21) →
    (∑ i ∈ I,w i*externalDensity true (fouvryG9SievePrimes N (Real.sqrt N))
      (externalInternalLevel Q θ) θ (Real.sqrt N) (progressionDensity (a i))) ≤
      fouvryG9UpperFactor N Q C K θ*fouvryG9BaseEuler N (Real.sqrt N)*
        goldbachG11EulerCorrection N*(∑ i ∈ I,w i) := by
  obtain ⟨C,hC,K,hK,hden⟩ := g9ProgressionDensity_upper
  refine ⟨C,hC,K,hK,?_⟩
  intro θ hθ hθu
  obtain ⟨Q₀,hQ₀,hupper⟩ := hden θ hθ hθu
  refine ⟨Q₀,hQ₀,?_⟩
  intro N hN hEven hbig Q hQ hQN hzQ
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hz : 2 ≤ Real.sqrt (N : ℝ) := by nlinarith [Real.sq_sqrt hn.le,Real.sqrt_nonneg (N : ℝ)]
  have hQ4 := hQ₀.trans hQ
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log (Real.sqrt N) := Real.log_pos (by linarith)
  have hcoord : Real.log Q/Real.log (Real.sqrt N) ≤ 2 := by
    apply (div_le_iff₀ hlogz).2
    rw [Real.log_sqrt hn.le]
    have hlog := Real.log_le_log (by linarith : 0 < Q) hQN
    linarith
  have hf : 0 ≤ fouvryG9UpperFactor N Q C K θ := by
    unfold fouvryG9UpperFactor
    rw [jr1965F_eq_of_le_three (by linarith)]
    positivity
  refine ⟨hf,?_⟩
  intro ι I a w hw ha
  let P := fouvryG9SievePrimes N (Real.sqrt N)
  have heuler := G11FiniteGate.weighted_progressionEuler_rough_le I a w P
    (fouvryG9SievePrimes_odd hEven _) hbig hw ha
  have hd : ∀ i ∈ I, w i*externalDensity true P (externalInternalLevel Q θ) θ
      (Real.sqrt N) (progressionDensity (a i)) ≤
      fouvryG9UpperFactor N Q C K θ*(w i*(∏ p ∈ P,(1-progressionDensity (a i) p))) := by
    intro i hi
    have hh := hupper Q hQ (a i) P (fouvryG9SievePrimes_odd hEven _) (Real.sqrt N) hz hzQ
      (fun p hp => ((fouvryG9SievePrimes_mem N p _).mp hp).2.2)
    exact (mul_le_mul_of_nonneg_left hh (hw i hi)).trans_eq (by unfold fouvryG9UpperFactor; ring)
  calc
    _ ≤ ∑ i ∈ I,fouvryG9UpperFactor N Q C K θ*(w i*(∏ p ∈ P,(1-progressionDensity (a i) p))) := sum_le_sum hd
    _ = fouvryG9UpperFactor N Q C K θ*(∑ i ∈ I,w i*(∏ p ∈ P,(1-progressionDensity (a i) p))) := (mul_sum _ _ _).symm
    _ ≤ fouvryG9UpperFactor N Q C K θ*(g9BaseEuler P*(1+1/((N : ℝ)^(4/53 : ℝ)-2))^21*(∑ i ∈ I,w i)) :=
      mul_le_mul_of_nonneg_left heuler hf
    _ = _ := by unfold fouvryG9BaseEuler g9BaseEuler goldbachG11EulerCorrection P; ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
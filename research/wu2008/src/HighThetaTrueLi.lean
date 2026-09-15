import HighThetaMassPayment
import MathlibNt.Wu2004MeanValue.BalancedPrincipal

namespace HighTheta
open Finset Real Wu2008DoubleSieve HighBoxRecovery Wu2004MeanValue
open scoped Classical
noncomputable section

/-- Literal logarithmic integral over each actual full-cofactor interval.
The weights and empty varying-prime fibres are unchanged. -/
def liX {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  ∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ)*
    (wuLi (min ((N : ℝ)/omega3CofactorValue c) (wuLocalCutoff N δ c.1 s)) - wuLi c.2.1)

/-- Explicit identity with the same true li used in boxTheta. -/
theorem liX_true_li {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ) :
    liX N δ s t W =
      ∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ)*
        (AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral
          (min ((N : ℝ)/omega3CofactorValue c) (wuLocalCutoff N δ c.1 s)) -
         AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral c.2.1) := rfl

/-- The original actual support constructs every principal layer and pays its
true-li error. This is separate from the prime-centred R1 theorem. -/
theorem X_true_li_log_saving (k : ℕ) {δ η A : ℝ} (hη : 0 < η) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, i ≤ k → ∀ W : Fin i → Finset ℕ,
      (∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ)^η ≤ p) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        |omega3SieveX N δ s t W-liX N δ s t W| ≤ C*N/log (N : ℝ)^A := by
  let F : ℝ := (max 1 (1/η))^(k+2)
  let B : ℕ := ⌈F⌉₊
  have hF : 0 ≤ F := by dsimp [F]; positivity
  obtain ⟨C,hC,x0,hmain⟩ := balanced_principal_moving_sum_bound A η F hA hη hF
  refine ⟨((B : ℝ)+1)*(2*C),by positivity,max 4 ⌈x0⌉₊,le_max_left _ _,?_⟩
  intro N hN i hi W hW hsize s t hs hst ht
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNx : x0 ≤ (N : ℝ) := (Nat.le_ceil x0).trans (by exact_mod_cast (le_max_right 4 ⌈x0⌉₊).trans hN)
  have hcut : ∀ d ∈ boxConvolutionSupport W, (N : ℝ)^η ≤ wuLocalCutoff N δ d t :=
    fun d hd => cutoff_lower (show 2 ≤ N by omega)
      (boxConvolutionSupport_pos (fun j p hp => (hW j p hp).1.pos) hd) hη
      (show 0 < t by linarith) ht (hsize d hd)
  let L := omega3CofactorLabels N δ s t W
  have hweight : ∀ e, (∑ c ∈ omega3LayerFibre L e, (convolutionCoeff W c.1 : ℝ)) ≤ F :=
    actual_fibre_weight W hi (by omega) hη hW hcut
  have hcard : ∀ e, (omega3LayerFibre L e).card ≤ B := by
    intro e
    exact_mod_cast (omega3_cofactor_fibre_card_le_weight N δ s t W e).trans
      ((hweight e).trans (Nat.le_ceil F))
  have hgeom := fun {c : Omega3CofactorIndex} (hc : c ∈ L) =>
    actual_profile W (show 2 ≤ N by omega) (fun j p hp => (hW j p hp).1) hcut hc
  have hbounds (j : ℕ) :
      (∀ e ∈ omega3LayerSupport L j, 1 ≤ e ∧ (e : ℝ) ≤ (N : ℝ)^(1-η)) ∧
      (∀ e ∈ omega3LayerSupport L j, |omega3LayerCoefficient W L j e| ≤ F) ∧
      (∀ e ∈ omega3LayerSupport L j, 2 ≤ omega3LayerLower L j e ∧
        omega3LayerLower L j e ≤ omega3LayerUpper N δ s L j e ∧
        (e : ℝ)*omega3LayerUpper N δ s L j e ≤ N) := by
    refine ⟨?_,?_,?_⟩
    · intro e he
      have hl := omega3LayerLabel_mem he
      have hg := hgeom hl.1
      exact hl.2 ▸ ⟨hg.1,hg.2.2.2.1⟩
    · intro e _
      rw [abs_of_nonneg (omega3LayerCoefficient_nonneg W L j e)]
      exact omega3LayerCoefficient_le W L j e hF (hweight e)
    · intro e he
      have hl := omega3LayerLabel_mem he
      have hg := hgeom hl.1
      simpa only [omega3LayerLower, omega3LayerUpper, hl.2] using hg.2.2.2.2
  have hsum : omega3SieveX N δ s t W-liX N δ s t W =
      ∑ j ∈ range B, ∑ e ∈ omega3LayerSupport L j, omega3LayerCoefficient W L j e *
        (principalError (omega3LayerUpper N δ s L j e)-principalError (omega3LayerLower L j e)) := by
    unfold omega3SieveX liX
    rw [← sum_sub_distrib]
    simp only [← mul_sub]
    rw [omega3Layer_weighted_sum W L B hcard]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro e he
    have hl := omega3LayerLabel_mem he
    have hb := (hbounds j).2.2 e he
    have hepos : 0 < e := (hbounds j).1 e he |>.1
    have hbN : omega3LayerUpper N δ s L j e ≤ N := by
      have he1 : (1 : ℝ) ≤ e := by exact_mod_cast hepos
      exact (le_mul_of_one_le_left (by linarith : 0 ≤ omega3LayerUpper N δ s L j e) he1).trans hb.2.2
    rw [omega3Layer_prime_fibre_eq_profile he hepos,
      omega3ProfilePrimes_card_eq_primeCount_sub (by linarith) hb.2.1 hbN]
    simp only [principalError, omega3LayerLower, omega3LayerUpper, hl.2]
    ring
  have hj (j : ℕ) :
      |∑ e ∈ omega3LayerSupport L j, omega3LayerCoefficient W L j e *
        (principalError (omega3LayerUpper N δ s L j e)-principalError (omega3LayerLower L j e))| ≤
      2*C*N/log (N : ℝ)^A := by
    have hb := hbounds j
    have hu := hmain (N : ℝ) hNx (omega3LayerSupport L j) (omega3LayerCoefficient W L j)
      (omega3LayerUpper N δ s L j) hb.1 hb.2.1
      (fun e he => ⟨(hb.2.2 e he).1.trans (hb.2.2 e he).2.1,(hb.2.2 e he).2.2⟩)
    have hl := hmain (N : ℝ) hNx (omega3LayerSupport L j) (omega3LayerCoefficient W L j)
      (omega3LayerLower L j) hb.1 hb.2.1
      (fun e he => ⟨(hb.2.2 e he).1,
        (mul_le_mul_of_nonneg_left (hb.2.2 e he).2.1 (Nat.cast_nonneg e)).trans (hb.2.2 e he).2.2⟩)
    simp only [mul_sub, sum_sub_distrib]
    apply (abs_sub _ _).trans
    calc
      _ ≤ C*N/log (N : ℝ)^A + C*N/log (N : ℝ)^A := add_le_add hu hl
      _ = _ := by ring
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ range B, |∑ e ∈ omega3LayerSupport L j, omega3LayerCoefficient W L j e *
        (principalError (omega3LayerUpper N δ s L j e)-principalError (omega3LayerLower L j e))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range B, 2*C*N/log (N : ℝ)^A := sum_le_sum (fun j _ => hj j)
    _ = (B : ℝ)*(2*C*N/log (N : ℝ)^A) := by simp
    _ ≤ ((B : ℝ)+1)*(2*C*N/log (N : ℝ)^A) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end
end HighTheta

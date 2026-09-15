import HighThetaSwitchedCount
import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralNormalization

namespace HighO3
open Finset Real Wu2008DoubleSieve HighBoxRecovery HighTheta Filter
open scoped Classical Topology
noncomputable section

/-- The only product input is a total supported-product gap. No Uk condition. -/
theorem phi_bounds {N d : ℕ} {δ η : ℝ} (hN : 2 ≤ N) (hd : 0 < d)
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η)
    (hsize : (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) :
    (N : ℝ)^(10*η) ≤ (N : ℝ)^(1/2-δ)/d ∧
    1 < (N : ℝ)^(1/2-δ)/d ∧
    2+2*δ/(1/2-δ) ≤ omega3XPhi N d δ ∧
    omega3XPhi N d δ ≤ 1/(10*η) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hR : (N : ℝ)^(10*η) ≤ (N : ℝ)^(1/2-δ)/d := by
    apply (le_div_iff₀ hdpos).mpr
    calc
      _ ≤ (N : ℝ)^(10*η)*(N : ℝ)^(1/2-δ-10*η) :=
        mul_le_mul_of_nonneg_left hsize (by positivity)
      _ = _ := by rw [← rpow_add hN0]; congr 1; ring
  have hR1 := (one_lt_rpow hN1 (show 0 < 10*η by positivity)).trans_le hR
  have hL := log_pos hR1
  have hc : 0 < 1/2-δ := by linarith
  have hlogR : log ((N : ℝ)^(1/2-δ)/d) = (1/2-δ)*log N-log d := by
    rw [log_div (rpow_pos_of_pos hN0 _).ne' hdpos.ne',log_rpow hN0]
  have hlogNd : log ((N : ℝ)/d) = log N-log d := log_div hN0.ne' hdpos.ne'
  have hlogd : 0 ≤ log (d : ℝ) := log_nonneg hd1
  have hlo := log_le_log (rpow_pos_of_pos hN0 _) hR
  rw [log_rpow hN0] at hlo
  refine ⟨hR,hR1,?_,?_⟩
  · have heq : 2+2*δ/(1/2-δ) = 1/(1/2-δ) := by
      apply (eq_div_iff hc.ne').mpr
      rw [add_mul,div_mul_cancel₀ _ hc.ne']; ring
    rw [heq,omega3XPhi,le_div_iff₀ hL,one_div,← div_eq_inv_mul]
    apply (div_le_iff₀ hc).mpr
    rw [hlogR,hlogNd]
    nlinarith
  · rw [omega3XPhi,div_le_iff₀ hL,one_div,← div_eq_inv_mul]
    apply (le_div_iff₀ (show 0 < 10*η by positivity)).mpr
    rw [hlogNd]
    nlinarith

/-- All actual cutoff bounds required by finite counting, on the original scale. -/
theorem support_bounds {N d : ℕ} {δ η s t : ℝ} (hN : 2 ≤ N) (hd : 0 < d)
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η)
    (hsize : (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    0 < d ∧ d ≤ N ∧ 1 < (N : ℝ)^(1/2-δ)/d ∧
      wuLocalCutoff N δ d t ≤ wuLocalCutoff N δ d s ∧
      (N : ℝ)^η ≤ wuLocalCutoff N δ d t ∧
      wuLocalCutoff N δ d s ≤ ((N : ℝ)^(1/2-δ)/d)^(1/2 : ℝ) := by
  have hg := phi_bounds hN hd hδ hδhi hη hsize
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdN : (d : ℝ) ≤ N := hsize.trans (by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hN1
      (show 1/2-δ-10*η ≤ 1 by linarith))
  exact ⟨hd,by exact_mod_cast hdN,hg.2.1,
    rpow_le_rpow_of_exponent_le hg.2.1.le (one_div_le_one_div_of_le (by linarith) hst),
    cutoff_lower hN hd hη (by linarith) ht hsize,
    rpow_le_rpow_of_exponent_le hg.2.1.le (one_div_le_one_div_of_le (by norm_num) hs)⟩

/-- Closed real exponent support, not merely a statement on the prime atoms. -/
theorem continuous_domain {N d : ℕ} {δ η s t : ℝ} (hN : 2 ≤ N) (hd : 0 < d)
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η)
    (hsize : (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    {p : ℝ × ℝ × ℝ} (hp : p ∈ omega3XExponentRegion s t) :
    2 < omega3XPhi N d δ ∧ omega3XPhi N d δ ≤ 1/(10*η) ∧
    1+2*δ/(1/2-δ) < (omega3XPhi N d δ-p.1-p.2.1-p.2.2)/p.2.1 ∧
    (omega3XPhi N d δ-p.1-p.2.1-p.2.2)/p.2.1 ≤ 1/η := by
  have hg := phi_bounds hN hd hδ hδhi hη hsize
  have hgap : 0 < 2*δ/(1/2-δ) := by positivity
  have hφ : 2 < omega3XPhi N d δ := by linarith [hg.2.2.1]
  obtain ⟨ha,hb,hc⟩ := omega3XExponentRegion_bounds hs hst ht hp
  have hu := omega3X_argument_bounds hφ.le ha hb hc
  refine ⟨hφ,hg.2.2.2,by linarith [hu.1,hg.2.2.1],?_⟩
  calc
    _ ≤ 10*omega3XPhi N d δ := hu.2.1
    _ ≤ 10*(1/(10*η)) := mul_le_mul_of_nonneg_left hg.2.2.2 (by norm_num)
    _ = _ := by ring

end
end HighO3

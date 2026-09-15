import HighO2TerminalQuadrature
import HighO2TerminalLocal
import HighO2TerminalFinite

namespace InsertedO2
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery HighOmega2 HighO2Terminal
open scoped Classical Topology
noncomputable section

/-- The true support gap implies polynomial residual level, without any
original-Fin2 strengthening. -/
theorem residual_level {N d : ℕ} {δ : ℝ} (hN : 2 ≤ N) (hδ : 0 ≤ δ)
    (hd : 0 < d) (hsize : (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta)) :
    d ≤ N ∧ (N : ℝ)^(10*highEta) ≤ (N : ℝ)^(1/2-δ)/d ∧
      1 < (N : ℝ)^(1/2-δ)/d := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 : (0 : ℝ) < N := by linarith
  have he : 0 < highEta := by norm_num [highEta]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlevel : (N : ℝ)^(10*highEta) ≤ (N : ℝ)^(1/2-δ)/d := by
    apply (le_div_iff₀ hd0).mpr
    calc
      _ ≤ (N : ℝ)^(10*highEta)*(N : ℝ)^(1/2-δ-10*highEta) :=
        mul_le_mul_of_nonneg_left hsize (by positivity)
      _ = _ := by rw [← rpow_add hn0]; congr 1; ring
  refine ⟨?_,hlevel,(one_lt_rpow hn (by positivity : 0 < 10*highEta)).trans_le hlevel⟩
  exact_mod_cast hsize.trans (show (N : ℝ)^(1/2-δ-10*highEta) ≤ N by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hn.le
      (show 1/2-δ-10*highEta ≤ (1 : ℝ) by linarith))

/-- Full prime interval, with the exact factor-two loss of residual gap. -/
theorem full_prime_half_gap {N d p : ℕ} {δ s t : ℝ}
    (hN : 2 ≤ N) (hδ : 0 ≤ δ) (hd : 0 < d)
    (hsize : (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta))
    (hs : 2 ≤ s) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hp : p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)) :
    (N : ℝ)^highEta ≤ p ∧ (p : ℝ) ≤ N ∧
      ((d*p : ℕ) : ℝ) ≤ (N : ℝ)^(1/2-δ-10*(highEta/2)) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 : (0 : ℝ) < N := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have he : 0 < highEta := by norm_num [highEta]
  have hg := residual_level hN hδ hd hsize
  have hp' := mem_primeWindow.mp hp
  have hhalf : (p : ℝ) ≤ ((N : ℝ)^(1/2-δ)/d)^(1/2 : ℝ) :=
    hp'.2.2.2.le.trans (rpow_le_rpow_of_exponent_le hg.2.2.le
      (one_div_le_one_div_of_le (by norm_num) hs))
  have hq0 : 0 < (N : ℝ)^(1/2-δ)/d := by linarith [hg.2.2]
  have hsq : (p : ℝ)^2 ≤ (N : ℝ)^(1/2-δ)/d := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg p : (0 : ℝ) ≤ p) hhalf 2
    have heq : (((N : ℝ)^(1/2-δ)/d)^(1/2 : ℝ))^2 = (N : ℝ)^(1/2-δ)/d := by
      rw [← rpow_two,← rpow_mul hq0.le]; norm_num
    rwa [heq] at hh
  have hpow : (N : ℝ)^(1/2-δ)*d ≤ ((N : ℝ)^(1/2-δ-10*(highEta/2)))^2 := by
    calc
      _ ≤ (N : ℝ)^(1/2-δ)*(N : ℝ)^(1/2-δ-10*highEta) :=
        mul_le_mul_of_nonneg_left hsize (by positivity)
      _ = _ := by rw [← rpow_add hn0,← rpow_two,← rpow_mul hn0.le]; congr 1; ring
  have hdp : ((d*p : ℕ) : ℝ) ≤ (N : ℝ)^(1/2-δ-10*(highEta/2)) := by
    have hh := mul_le_mul_of_nonneg_right ((le_div_iff₀ hd0).mp hsq) hd0.le
    rw [Nat.cast_mul]
    nlinarith [rpow_nonneg hn0.le (1/2-δ-10*(highEta/2))]
  refine ⟨?_,?_,hdp⟩
  · apply le_trans _ hp'.2.2.1
    change (N : ℝ)^highEta ≤ ((N : ℝ)^(1/2-δ)/d)^(1/t)
    calc
      _ ≤ (N : ℝ)^((10*highEta)*(1/t)) := rpow_le_rpow_of_exponent_le hn.le (by
        rw [mul_one_div]; apply (le_div_iff₀ (show 0 < t by linarith)).mpr; nlinarith)
      _ = ((N : ℝ)^(10*highEta))^(1/t) := rpow_mul hn0.le _ _
      _ ≤ _ := rpow_le_rpow (by positivity) hg.2.1 (by positivity)
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hpdp : (p : ℝ) ≤ d*p := by nlinarith [Nat.cast_nonneg (α := ℝ) p]
    rw [Nat.cast_mul] at hdp
    apply hpdp.trans (hdp.trans ?_)
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hn.le
      (show 1/2-δ-10*(highEta/2) ≤ (1 : ℝ) by linarith)

end
end InsertedO2

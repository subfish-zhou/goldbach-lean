import CoverMassSelected

namespace CoverMass
open Finset Real Wu2008DoubleSieve HighBoxRecovery
open scoped Classical
noncomputable section

/-- Both actual endpoints lie in the complete original r+2 grid. The upper
overshoot is exactly at most two original Delta factors, including s=2. -/
theorem complete_endpoint_bounds {q D Δ s : ℝ} {r : ℕ}
    (hq : 1 < q) (hΔ : 1 < Δ) (hDlo : q ≤ D) (hDhi : D ≤ q*Δ^2)
    (hs : 2 ≤ s) (hs3 : s ≤ 3)
    (hrlo : reboxingAlpha q Δ 3 r ≤ q^(1/s))
    (hrhi : q^(1/s) < reboxingAlpha q Δ 3 (r+1)) :
    q^(1/3 : ℝ) ≤ D^(1/3 : ℝ) ∧ D^(1/3 : ℝ) ≤ D^(1/s) ∧
    D^(1/s) ≤ reboxingAlpha q Δ 3 (r+2) ∧
    reboxingAlpha q Δ 3 (r+2) ≤ q^(1/s)*Δ^2 := by
  have hq0 : 0 < q := by linarith
  have hD : 1 < D := hq.trans_le hDlo
  have hΔ0 : 0 < Δ := by linarith
  have hsp : 0 < s := by linarith
  refine ⟨rpow_le_rpow hq0.le hDlo (by norm_num),
    rpow_le_rpow_of_exponent_le hD.le (one_div_le_one_div_of_le hsp hs3),?_,?_⟩
  · have hpow : (q*Δ^2)^(1/s) ≤ q^(1/s)*Δ := by
      rw [mul_rpow hq0.le (sq_nonneg Δ),← rpow_natCast_mul hΔ0.le]
      apply mul_le_mul_of_nonneg_left _ (rpow_nonneg hq0.le _)
      calc
        _ ≤ Δ^(1 : ℝ) := rpow_le_rpow_of_exponent_le hΔ.le (by
          rw [Nat.cast_ofNat,mul_one_div]; exact (div_le_one hsp).mpr hs)
        _ = Δ := rpow_one _
    calc
      _ ≤ (q*Δ^2)^(1/s) := rpow_le_rpow (by linarith) hDhi (by positivity)
      _ ≤ q^(1/s)*Δ := hpow
      _ ≤ reboxingAlpha q Δ 3 (r+1)*Δ := mul_le_mul_of_nonneg_right hrhi.le hΔ0.le
      _ = _ := by rw [← reboxingAlpha_step hΔ0]; congr 1; ring
  · calc
      _ = reboxingAlpha q Δ 3 r*Δ^2 := by
        rw [show (r : ℝ)+2=((r : ℝ)+1)+1 by ring,reboxingAlpha_step hΔ0,reboxingAlpha_step hΔ0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hrlo (sq_nonneg Δ)

/-- Uniform logarithmic widths of the two forced endpoint bands. -/
theorem endpoint_log_widths {q D Δ s b : ℝ}
    (hq : 1 < q) (hΔ : 1 < Δ) (hDlo : q ≤ D) (hDhi : D ≤ q*Δ^2)
    (hs : 2 ≤ s) (hb : 0 < b) (hbu : b ≤ q^(1/s)*Δ^2) :
    log (D^(1/3 : ℝ)/q^(1/3 : ℝ)) ≤ 2*log Δ ∧
    log (b/D^(1/s)) ≤ 2*log Δ := by
  have hq0 : 0 < q := by linarith
  have hD0 : 0 < D := hq0.trans_le hDlo
  have hΔ0 : 0 < Δ := by linarith
  have hLD : log D ≤ log q+2*log Δ := by
    have h := log_le_log hD0 hDhi
    simpa [log_mul hq0.ne' (pow_pos hΔ0 2).ne',log_pow] using h
  have hLq : log q ≤ log D := log_le_log hq0 hDlo
  have hLΔ : 0 ≤ log Δ := (log_pos hΔ).le
  constructor
  · rw [log_div (rpow_pos_of_pos hD0 _).ne' (rpow_pos_of_pos hq0 _).ne',
      log_rpow hD0,log_rpow hq0]
    linarith
  · have hlog := log_le_log hb hbu
    rw [log_mul (rpow_pos_of_pos hq0 _).ne' (pow_pos hΔ0 2).ne',log_rpow hq0,log_pow] at hlog
    rw [log_div hb.ne' (rpow_pos_of_pos hD0 _).ne',log_rpow hD0]
    have := mul_le_mul_of_nonneg_left hLq (show 0 ≤ 1/s by positivity)
    linarith

/-- The top boundary can exceed the square root. A genuine quarter-gap
pays it without misusing a quadrature theorem requiring s>=2. -/
theorem enlarged_kernel_bound {q D Δ s p : ℝ}
    (hq : 1 < q) (hΔ : 1 < Δ) (hDlo : q ≤ D) (hs : 2 ≤ s)
    (hmesh : 8*log Δ ≤ log q) (hp4 : 4 ≤ p)
    (hp : p ≤ q^(1/s)*Δ^2) :
    1/4 ≤ 1-log p/log D ∧
    0 ≤ 1/((p-2)*(1-log p/log D)) ∧
    1/((p-2)*(1-log p/log D)) ≤ 8/p := by
  have hq0 : 0 < q := by linarith
  have hD : 1 < D := hq.trans_le hDlo
  have hLD : 0 < log D := log_pos hD
  have hLq : 0 < log q := log_pos hq
  have hlog := log_le_log (by linarith : 0 < p) hp
  rw [log_mul (rpow_pos_of_pos hq0 _).ne' (pow_pos (by linarith : 0 < Δ) 2).ne',
    log_rpow hq0,log_pow] at hlog
  have hsi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs
  have hterm := mul_le_mul_of_nonneg_right hsi hLq.le
  have hqD := log_le_log hq0 hDlo
  have hfrac : log p/log D ≤ 3/4 := (div_le_iff₀ hLD).mpr (by linarith)
  have hgap : 1/4 ≤ 1-log p/log D := by linarith
  have hp2 : 0 < p-2 := by linarith
  have hg0 : 0 < 1-log p/log D := by linarith
  refine ⟨hgap,by positivity,?_⟩
  apply (div_le_div_iff₀ (by positivity : 0 < (p-2)*(1-log p/log D)) (by linarith : 0 < p)).mpr
  nlinarith [mul_nonneg (by linarith : 0 ≤ p-2) (by linarith : 0 ≤ 1-log p/log D-1/4)]

end
end CoverMass

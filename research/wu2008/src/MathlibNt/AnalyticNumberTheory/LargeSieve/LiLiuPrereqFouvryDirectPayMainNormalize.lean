import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPayMainGrowth

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Exact transport of the real reciprocal and T² normalization under a root. -/
theorem directPayMain_root_identity {A m E T : ℝ} (hA : 0 ≤ A) (hm : 0 ≤ m) (hE : 0 ≤ E) :
    A * Real.sqrt m * Real.sqrt E / T^2 = Real.sqrt (A^2*m*E/T^4) := by
  rw [Real.sqrt_div (by positivity : 0 ≤ A^2*m*E)]
  rw [Real.sqrt_mul (by positivity : 0 ≤ A^2*m), Real.sqrt_mul (sq_nonneg A),
    Real.sqrt_sq hA, show T^4 = (T^2)^2 by ring, Real.sqrt_sq (sq_nonneg T)]

/-- An upper dyadic n endpoint is paid by a fixed factor two, not by n=T. -/
theorem directPayMain_npow {n T p : ℝ} (hn : 0 ≤ n) (hT : 0 ≤ T)
    (hnT : n ≤ 2*T) (hp : 0 ≤ p) (hp2 : p ≤ 2) : n^p ≤ 4*T^p := by
  calc
    _ ≤ (2*T)^p := Real.rpow_le_rpow hn hnT hp
    _ = (2 : ℝ)^p*T^p := Real.mul_rpow (by norm_num) hT
    _ ≤ 4*T^p := by
      have hh : (2 : ℝ)^p ≤ 4 := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp2
        norm_num at h ⊢
        exact h
      gcongr

/-- Both long-interval and D' summands have nonnegative post-payment exponents. -/
theorem directPayMain_two_monomials {k n r s Dp Z T R S : ℝ}
    (hk : 0 ≤ k) (hn : 0 ≤ n) (hr : 0 ≤ r) (hs : 0 ≤ s) (hDp : 0 ≤ Dp)
    (hZ : 1 ≤ Z) (hT : 1 ≤ T) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hkRS : k ≤ R*S) (hnT : n ≤ 2*T) (hrR : r ≤ R) (hsS : s ≤ S)
    (hDpZ : Dp ≤ Z^5) :
    k*n^(3/2 : ℝ)*r^(5/2 : ℝ)*s^3*Dp +
      2*k^2*n^(1/2 : ℝ)*r^(3/2 : ℝ)*s ≤
      12*Z^5*T^(3/2 : ℝ)*R^(7/2 : ℝ)*S^4 := by
  have hT0 : 0 ≤ T := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hRpos : 0 < R := by linarith
  have hnp := directPayMain_npow hn hT0 hnT (by norm_num : (0 : ℝ) ≤ 3/2) (by norm_num)
  have hnq := directPayMain_npow hn hT0 hnT (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
  have hTp : T^(1/2 : ℝ) ≤ T^(3/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have hZ5 : 1 ≤ Z^5 := one_le_pow₀ hZ
  have hs34 : S^3 ≤ S^4 := pow_le_pow_right₀ hS (by omega)
  have hm : k*n^(3/2 : ℝ)*r^(5/2 : ℝ)*s^3*Dp ≤
      4*Z^5*T^(3/2 : ℝ)*R^(7/2 : ℝ)*S^4 := by
    calc
      _ ≤ (R*S)*(4*T^(3/2 : ℝ))*R^(5/2 : ℝ)*S^3*Z^5 := by gcongr
      _ = _ := by
        rw [show (7/2 : ℝ) = (5/2 : ℝ)+1 by norm_num, Real.rpow_add hRpos, Real.rpow_one]
        ring
  have hl : 2*k^2*n^(1/2 : ℝ)*r^(3/2 : ℝ)*s ≤
      8*Z^5*T^(3/2 : ℝ)*R^(7/2 : ℝ)*S^4 := by
    calc
      _ ≤ 2*(R*S)^2*(4*T^(3/2 : ℝ))*R^(3/2 : ℝ)*S := by
        gcongr
        exact hnq.trans (by gcongr)
      _ = 8*T^(3/2 : ℝ)*R^(7/2 : ℝ)*S^3 := by
        rw [show (7/2 : ℝ) = (3/2 : ℝ)+2 by norm_num, Real.rpow_add hRpos]
        norm_num only [Real.rpow_ofNat]
        ring
      _ ≤ 8*Z^5*T^(3/2 : ℝ)*R^(7/2 : ℝ)*S^4 := by
        calc
          _ = 8*1*T^(3/2 : ℝ)*R^(7/2 : ℝ)*S^3 := by ring
          _ ≤ _ := by gcongr
  linarith

/-- Exact squared normalization after the reciprocal, before floor payment.
The second summand is the actual span/q contribution. -/
theorem directPayMain_square_expand {A C L H k n r s Dp T : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (hT : 0 < T) :
    A^2*(8*C*k*r*T)*
      (256*L*H^2*n^(3/2 : ℝ)*T^2*r^(3/2 : ℝ)*s^3*(Dp+2*k/(n*r*s^2)))/T^4 =
      2048*C*L*(A*H)^2/T *
        (k*n^(3/2 : ℝ)*r^(5/2 : ℝ)*s^3*Dp + 2*k^2*n^(1/2 : ℝ)*r^(3/2 : ℝ)*s) := by
  rw [show (3/2 : ℝ) = (1/2 : ℝ)+1 by norm_num,
    show (5/2 : ℝ) = ((1/2 : ℝ)+1)+1 by norm_num]
  simp only [Real.rpow_add hn, Real.rpow_add hr, Real.rpow_one]
  field_simp
  ring

/-- The real floor bound is substituted before all global enlargement. -/
theorem directPayMain_square_paid {A C L H k n r s Dp Z T R S x : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hk : 0 < k) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (hDp : 0 ≤ Dp)
    (hZ : 1 ≤ Z) (hT : 1 ≤ T) (hR : 1 ≤ R) (hS : 1 ≤ S) (hx : 0 < x)
    (hAH : A*H ≤ 32*Z*T/x) (hkRS : k ≤ R*S) (hnT : n ≤ 2*T)
    (hrR : r ≤ R) (hsS : s ≤ S) (hDpZ : Dp ≤ Z^5) :
    A^2*(8*C*k*r*T)*
      (256*L*H^2*n^(3/2 : ℝ)*T^2*r^(3/2 : ℝ)*s^3*(Dp+2*k/(n*r*s^2)))/T^4 ≤
      25165824*C*L*Z^7*T^(5/2 : ℝ)*R^(7/2 : ℝ)*S^4/x^2 := by
  have hTpos : 0 < T := by linarith
  rw [directPayMain_square_expand hn hr hs hTpos]
  calc
    _ ≤ 2048*C*L*(32*Z*T/x)^2/T *
      (12*Z^5*T^(3/2 : ℝ)*R^(7/2 : ℝ)*S^4) := by
      apply mul_le_mul
      · gcongr
      · exact directPayMain_two_monomials hk.le hn.le hr.le hs.le hDp hZ hT hR hS
          hkRS hnT hrR hsS hDpZ
      · positivity
      · positivity
    _ = _ := by
      rw [show (5/2 : ℝ) = (3/2 : ℝ)+1 by norm_num, Real.rpow_add hTpos, Real.rpow_one]
      field_simp
      ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

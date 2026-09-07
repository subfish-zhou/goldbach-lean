import MathlibNt.SieveTheory.LiLiuPrereqBuchstabIntegral

set_option autoImplicit false

#check LiLiuPrereqBuchstab.hasDerivAt_buchstab_log_primitive
#check LiLiuPrereqBuchstab.intervalIntegrable_buchstab_log_kernel
#check LiLiuPrereqBuchstab.integral_buchstab_log_kernel
#check LiLiuPrereqBuchstab.integral_buchstab_log_substitution
#check LiLiuPrereqBuchstab.log_div_log_sqrt
#check LiLiuPrereqBuchstab.two_le_log_div_log_of_sq_le
#check LiLiuPrereqBuchstab.integral_buchstab_log_kernel_sqrt
#check LiLiuPrereqBuchstab.mul_integral_buchstab_log_kernel_sqrt

#print axioms LiLiuPrereqBuchstab.hasDerivAt_buchstab_log_primitive
#print axioms LiLiuPrereqBuchstab.intervalIntegrable_buchstab_log_kernel
#print axioms LiLiuPrereqBuchstab.integral_buchstab_log_kernel
#print axioms LiLiuPrereqBuchstab.integral_buchstab_log_substitution
#print axioms LiLiuPrereqBuchstab.log_div_log_sqrt
#print axioms LiLiuPrereqBuchstab.two_le_log_div_log_of_sq_le
#print axioms LiLiuPrereqBuchstab.integral_buchstab_log_kernel_sqrt
#print axioms LiLiuPrereqBuchstab.mul_integral_buchstab_log_kernel_sqrt

example (x y : ℝ) (hy : 1 < y) (hxy : y ^ 2 ≤ x) :
    x * (∫ t in y..Real.sqrt x,
      LiLiuPrereqBuchstab.buchstab (Real.log x / Real.log t - 1) /
        (t * (Real.log t) ^ 2)) =
      x / Real.log x *
        ((Real.log x / Real.log y) *
          LiLiuPrereqBuchstab.buchstab (Real.log x / Real.log y) - 1) :=
  LiLiuPrereqBuchstab.mul_integral_buchstab_log_kernel_sqrt hy hxy
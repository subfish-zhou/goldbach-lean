import MathlibNt.SieveTheory.LiLiuPrereqWFRoughComparison
import MathlibNt.SieveTheory.LiLiuPrereqWFRoughEuler

/-!
# Analytic control of the actual same-box collisions

The original dimension-one product hypothesis controls each geometric
interval, including its closed lower and strict upper endpoint. Summing over
the actual distinct prime pairs retains the rough Euler normalization.
No count of prime subsets or bound on a different family is used.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset SmallRosser
open scoped Classical

namespace CollisionAnalytic

theorem sum_le_inverseProduct_sub_one (S : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ S, 0 ≤ g p ∧ g p < 1) :
    (∑ p ∈ S, g p) ≤ (∏ p ∈ S, (1 - g p)⁻¹) - 1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      have hgp := hg p (mem_insert_self _ _)
      have hgS : ∀ q ∈ S, 0 ≤ g q ∧ g q < 1 :=
        fun q hq => hg q (mem_insert_of_mem hq)
      have hi := ih hgS
      have hsum : 0 ≤ ∑ q ∈ S, g q := sum_nonneg (fun q hq => (hgS q hq).1)
      have hfactor : 1 + g p ≤ (1 - g p)⁻¹ := by
        rw [inv_eq_one_div]
        apply (le_div_iff₀ (sub_pos.mpr hgp.2)).mpr
        nlinarith [sq_nonneg (g p)]
      rw [sum_insert hp, prod_insert hp]
      have hm := mul_le_mul_of_nonneg_left (show 1 + ∑ q ∈ S, g q ≤
          ∏ q ∈ S, (1 - g q)⁻¹ by linarith)
        (inv_nonneg.mpr (sub_nonneg.mpr hgp.2.le))
      have hn := mul_le_mul_of_nonneg_right hfactor (show 0 ≤ 1 + ∑ q ∈ S, g q by positivity)
      nlinarith [mul_nonneg hgp.1 hsum]

/-- The interval product hypothesis pays an actual subinterval prime sum.
The `-1` is essential to keep the geometric width small. -/
theorem interval_sum_le (P S : Finset ℕ) {g : ℕ → ℝ} {K w z : ℝ}
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) (hw : 2 ≤ w) (hwz : w < z)
    (hS : S ⊆ P.filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z)) :
    (∑ p ∈ S, g p) ≤ Real.log z / Real.log w * (1 + K / Real.log w) - 1 := by
  have hs := sum_le_inverseProduct_sub_one S g
    (fun p hp => hg p (mem_filter.mp (hS hp)).1)
  apply hs.trans
  apply sub_le_sub_right
  apply le_trans _ (hdim w z hw hwz)
  apply Finset.prod_le_prod_of_subset_of_one_le hS
  · intro p hp
    exact inv_nonneg.mpr (sub_nonneg.mpr (hg p (mem_filter.mp (hS hp)).1).2.le)
  · intro p hp _
    exact (one_le_inv₀ (sub_pos.mpr (hg p (mem_filter.mp hp).1).2)).mpr
      (by linarith [(hg p (mem_filter.mp hp).1).1])

theorem rough_parameters {D ε : ℝ} (hD : 2 ≤ D) (hε : 0 < ε)
    (hεsmall : ε < 1 / 8) (hlarge : 1 ≤ ε ^ 2 * Real.log D) :
    2 ≤ D ^ (ε ^ 2) ∧ D ^ (ε ^ 2) < D ∧
      0 < Real.log D ∧ Real.log (D ^ (ε ^ 2)) = ε ^ 2 * Real.log D := by
  have hD0 : 0 < D := by linarith
  have hlog : Real.log (D ^ (ε ^ 2)) = ε ^ 2 * Real.log D :=
    Real.log_rpow hD0 _
  have hu : Real.exp 1 ≤ D ^ (ε ^ 2) := by
    apply (Real.log_le_log_iff (Real.exp_pos _) (Real.rpow_pos_of_pos hD0 _)).mp
    simpa only [Real.log_exp, hlog] using hlarge
  refine ⟨(by linarith [Real.add_one_le_exp (1 : ℝ)] : (2 : ℝ) ≤ Real.exp 1).trans hu,
    ?_, Real.log_pos (by linarith), hlog⟩
  calc
    D ^ (ε ^ 2) < D ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by nlinarith)
    _ = D := Real.rpow_one _

theorem rough_prime_lower (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D ε : ℝ) {p : ℕ} (hp : p ∈ P \ geometricSmallPrimes P D ε) :
    D ^ (ε ^ 2) ≤ (p : ℝ) := by
  by_contra h
  exact (mem_sdiff.mp hp).2
    (mem_filter.mpr ⟨(mem_sdiff.mp hp).1, hP p (mem_sdiff.mp hp).1, lt_of_not_ge h⟩)

/-- No geometric-grid cardinality is needed: the distinct later partners
of `p` lie in `[p,p^(1+epsilon^9))`. -/
theorem sameBox_partner_sum_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {D ε K : ℝ} (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlarge : 1 ≤ ε ^ 2 * Real.log D) (hK : 0 ≤ K)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K)
    {p : ℕ} (hp : p ∈ P \ geometricSmallPrimes P D ε) :
    let R := P \ geometricSmallPrimes P D ε
    let b := fun q => geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε q)
    (∑ q ∈ R.filter (fun q => p < q ∧ b p = b q), g q) ≤
      ε ^ 9 + 2 * K / (ε ^ 2 * Real.log D) := by
  dsimp only
  have hpar := rough_parameters hD hε hεsmall hlarge
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p (mem_sdiff.mp hp).1).two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  have hθ : 0 < ε ^ 9 := pow_pos hε 9
  have hθ1 : ε ^ 9 ≤ 1 := by
    simpa using pow_le_pow_left₀ hε.le (by linarith : ε ≤ 1) 9
  have hwidth : (p : ℝ) < (p : ℝ) ^ (1 + ε ^ 9) := by
    conv_lhs => rw [← Real.rpow_one (p : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
  have hsum := interval_sum_le P
    ((P \ geometricSmallPrimes P D ε).filter (fun q => p < q ∧
      geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε p) =
        geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε q)))
    hg hdim hp2 hwidth (by
      intro q hq
      obtain ⟨hqR, hpq, heq⟩ := mem_filter.mp hq
      have hbp := ((mem_geometricPrimeBox _ _ _ _ _ _).mp
        (geometricSieveLabel_mem P hP (by linarith) hε p hp)).2.2.1
      have hqu := geometricPrimeBox_upper P (by linarith) _ q
        (geometricSieveLabel_mem P hP (by linarith) hε q hqR)
      rw [← heq] at hqu
      refine mem_filter.mpr ⟨(mem_sdiff.mp hqR).1, hP q (mem_sdiff.mp hqR).1,
        ?_, hqu.trans_le ?_⟩
      · exact_mod_cast hpq.le
      · exact Real.rpow_le_rpow
          ((by norm_num : (0 : ℝ) ≤ 1).trans
            (geometricLower_one_le (by linarith) hθ.le _))
          hbp (by positivity))
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hloglow : ε ^ 2 * Real.log D ≤ Real.log (p : ℝ) := by
    rw [← hpar.2.2.2]
    exact Real.log_le_log (by positivity)
      (rough_prime_lower P hP D ε hp)
  have ht0 : 0 < ε ^ 2 * Real.log D := by positivity
  have hdiv : K / Real.log (p : ℝ) ≤ K / (ε ^ 2 * Real.log D) :=
    div_le_div_of_nonneg_left hK ht0 hloglow
  rw [Real.log_rpow hp0, mul_div_cancel_right₀ _ (ne_of_gt hlogp)] at hsum
  have hm := mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ 1 + ε ^ 9)
  have hn := mul_le_mul_of_nonneg_right (show 1 + ε ^ 9 ≤ 2 by linarith)
    (div_nonneg hK ht0.le)
  apply hsum.trans
  calc
    (1 + ε ^ 9) * (1 + K / Real.log (p : ℝ)) - 1 =
        ε ^ 9 + (1 + ε ^ 9) * (K / Real.log (p : ℝ)) := by ring
    _ ≤ ε ^ 9 + 2 * (K / (ε ^ 2 * Real.log D)) := add_le_add le_rfl (hm.trans hn)
    _ = _ := by ring

/-- A same-carrier pair bound from the original product hypothesis. -/
theorem roughCollisionPairMass_le_dimensionOne (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε K : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlarge : 1 ≤ ε ^ 2 * Real.log D) (hK : 0 ≤ K)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) :
    let R := P \ geometricSmallPrimes P D ε
    let b := fun p => geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε p)
    roughCollisionPairMass b R g ≤
      (ε ^ 9 + 2 * K / (ε ^ 2 * Real.log D)) *
        ((1 + K / (ε ^ 2 * Real.log D)) / ε ^ 2) := by
  dsimp only
  have hpar := rough_parameters hD hε hεsmall hlarge
  have hsum := interval_sum_le P (P \ geometricSmallPrimes P D ε)
    hg hdim hpar.1 hpar.2.1 (by
      intro p hp
      refine mem_filter.mpr ⟨(mem_sdiff.mp hp).1, hP p (mem_sdiff.mp hp).1,
        rough_prime_lower P hP D ε hp, (hcut p hp).trans_le ?_⟩
      nlinarith [Real.sq_sqrt (show 0 ≤ D by linarith), Real.sqrt_nonneg D])
  rw [hpar.2.2.2] at hsum
  have htotal : (∑ p ∈ P \ geometricSmallPrimes P D ε, g p) ≤
      (1 + K / (ε ^ 2 * Real.log D)) / ε ^ 2 := by
    have hid : Real.log D / (ε ^ 2 * Real.log D) *
        (1 + K / (ε ^ 2 * Real.log D)) =
          (1 + K / (ε ^ 2 * Real.log D)) / ε ^ 2 := by
      field_simp [ne_of_gt hpar.2.2.1]
    rw [hid] at hsum
    linarith
  calc
    _ ≤ ∑ p ∈ P \ geometricSmallPrimes P D ε,
        g p * (ε ^ 9 + 2 * K / (ε ^ 2 * Real.log D)) := by
      unfold roughCollisionPairMass
      apply sum_le_sum
      intro p hp
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left
        (sameBox_partner_sum_le P hP hD hε hεsmall hlarge hK hg hdim hp)
        (hg p (mem_sdiff.mp hp).1).1
    _ = (ε ^ 9 + 2 * K / (ε ^ 2 * Real.log D)) *
        ∑ p ∈ P \ geometricSmallPrimes P D ε, g p := by rw [← sum_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal (by positivity)

end CollisionAnalytic

#check CollisionAnalytic.sameBox_partner_sum_le
#print axioms CollisionAnalytic.sameBox_partner_sum_le
#check CollisionAnalytic.roughCollisionPairMass_le_dimensionOne
#print axioms CollisionAnalytic.roughCollisionPairMass_le_dimensionOne

end MathlibNt.SieveTheory.LiLiuPrereqWF

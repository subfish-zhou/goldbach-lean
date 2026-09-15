import WSrcFourEnclosureReduction

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass

namespace WuSource.SrcFourEnclosure

theorem endpoint_logs :
    0 ≤ smallW cut ∧ smallW cut ≤ 4 ∧ largeW beta ≤ 4 ∧ largeQ beta ≤ 11 := by
  have ha : 0 < alpha := geometry.1
  have hb : 0 < beta := ha.trans_le geometry.2.1
  have hc : 0 < cut := by norm_num [cut]
  have ha1 : 0 < 1-alpha := by
    have := geometry.2.2.2.2.2.1
    linarith only [this]
  have hc1 : 0 < 1-cut := by norm_num [cut]
  have h1 : (1 : ℝ) ≤ cut/alpha := by
    norm_num [cut,alpha,truncatedSixthLowerAlpha]
  have h2 : (1 : ℝ) ≤ (1-alpha)/(1-cut) := by
    norm_num [cut,alpha,truncatedSixthLowerAlpha]
  have h3 : (1 : ℝ) ≤ beta/cut := by
    norm_num [cut,beta,truncatedSixthLowerBeta]
  have l1 := SharpLogRecurrence.log_lower h1
  have u1 := SharpLogRecurrence.log_upper h1
  have l2 := SharpLogRecurrence.log_lower h2
  have u2 := SharpLogRecurrence.log_upper h2
  have l3 := SharpLogRecurrence.log_lower h3
  have u3 := SharpLogRecurrence.log_upper h3
  rw [log_div hc.ne' ha.ne'] at l1 u1
  rw [log_div ha1.ne' hc1.ne'] at l2 u2
  rw [log_div hb.ne' hc.ne'] at l3 u3
  norm_num [SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog,
    cut,alpha,beta,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at l1 u1 l2 u2 l3 u3
  norm_num [smallW,smallQ,largeW,largeQ,cut,alpha,beta,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  constructor
  · linarith only [l1,l2]
  constructor
  · linarith only [u1,u2]
  constructor
  · linarith only [u1,u2,u3]
  · linarith only [l1,l2,l3]

theorem monotone_of_derivative {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Icc a b, 0 ≤ f' x) : MonotoneOn f (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hn x (interior_subset hx))

theorem smallW_mono : MonotoneOn smallW (Icc alpha cut) := by
  apply monotone_of_derivative (f' := fun x => (36/5)/(x*(1-x)))
  · intro x hx
    exact smallW_derivative (geometry.1.trans_le hx.1).ne' (by
      have hxc : x ≤ (1/10 : ℝ) := hx.2
      linarith only [hxc])
  · intro x hx
    have hx0 := geometry.1.trans_le hx.1
    have hx1 : 0 ≤ 1-x := by
      have hxc : x ≤ (1/10 : ℝ) := hx.2
      linarith only [hxc]
    positivity

theorem largeW_mono : MonotoneOn largeW (Icc cut beta) := by
  apply monotone_of_derivative (f' := fun x => 8/x)
  · intro x hx
    exact largeW_derivative (by have hxc : (1/10 : ℝ) ≤ x := hx.1; linarith only [hxc])
  · intro x hx
    have hx0 : 0 ≤ x := by have hxc : (1/10 : ℝ) ≤ x := hx.1; linarith only [hxc]
    positivity

theorem W_bounds :
    (∀ x ∈ Icc alpha cut, 0 ≤ smallW x ∧ smallW x ≤ 4) ∧
      (∀ x ∈ Icc cut beta, 0 ≤ largeW x ∧ largeW x ≤ 4) := by
  have hac : alpha ≤ cut := geometry.2.2.2.2.2.1
  have hcb : cut ≤ beta := geometry.2.2.2.2.2.2
  constructor
  · intro x hx
    have h1 := smallW_mono ⟨le_rfl,hac⟩ hx hx.1
    have h2 := smallW_mono hx ⟨hac,le_rfl⟩ hx.2
    rw [primitives_boundary.1] at h1
    exact ⟨h1,h2.trans endpoint_logs.2.1⟩
  · intro x hx
    have h1 := largeW_mono ⟨le_rfl,hcb⟩ hx hx.1
    have h2 := largeW_mono hx ⟨hcb,le_rfl⟩ hx.2
    rw [primitives_boundary.2.2.1] at h1
    exact ⟨endpoint_logs.1.trans h1,h2.trans endpoint_logs.2.2.1⟩

theorem smallQ_mono : MonotoneOn smallQ (Icc alpha cut) := by
  apply monotone_of_derivative (f' := fun x => smallW x/x^2)
  · intro x hx
    exact smallQ_derivative (geometry.1.trans_le hx.1).ne' (by
      have hxc : x ≤ (1/10 : ℝ) := hx.2
      linarith only [hxc])
  · exact fun x hx => div_nonneg (W_bounds.1 x hx).1 (sq_nonneg x)

theorem largeQ_mono : MonotoneOn largeQ (Icc cut beta) := by
  apply monotone_of_derivative (f' := fun x => largeW x/x^2)
  · intro x hx
    exact largeQ_derivative (by have hxc : (1/10 : ℝ) ≤ x := hx.1; linarith only [hxc])
  · exact fun x hx => div_nonneg (W_bounds.2 x hx).1 (sq_nonneg x)

theorem Q_bounds :
    (∀ x ∈ Icc alpha cut, 0 ≤ smallQ x ∧ smallQ x ≤ 11) ∧
      (∀ x ∈ Icc cut beta, 0 ≤ largeQ x ∧ largeQ x ≤ 11) := by
  have hac : alpha ≤ cut := geometry.2.2.2.2.2.1
  have hcb : cut ≤ beta := geometry.2.2.2.2.2.2
  have hcut0 := smallQ_mono ⟨le_rfl,hac⟩ ⟨hac,le_rfl⟩ hac
  have hcut1 := largeQ_mono ⟨le_rfl,hcb⟩ ⟨hcb,le_rfl⟩ hcb
  rw [primitives_boundary.2.1] at hcut0
  rw [primitives_boundary.2.2.2.1] at hcut1
  constructor
  · intro x hx
    have h1 := smallQ_mono ⟨le_rfl,hac⟩ hx hx.1
    have h2 := smallQ_mono hx ⟨hac,le_rfl⟩ hx.2
    rw [primitives_boundary.2.1] at h1
    exact ⟨h1,h2.trans (hcut1.trans endpoint_logs.2.2.2)⟩
  · intro x hx
    have h1 := largeQ_mono ⟨le_rfl,hcb⟩ hx hx.1
    have h2 := largeQ_mono hx ⟨hcb,le_rfl⟩ hx.2
    rw [primitives_boundary.2.2.2.1] at h1
    exact ⟨hcut0.trans h1,h2.trans endpoint_logs.2.2.2⟩

theorem elementary_bounds {x : ℝ} (hx : x ∈ Icc alpha beta) :
    |x⁻¹| ≤ 14 ∧ |(lam-x)⁻¹| ≤ 5 ∧ |cross x| ≤ 3/2 := by
  have hx0 := geometry.1.trans_le hx.1
  have hl0 : 0 < lam-x := by linarith only [hx.2,geometry.2.2.2.1]
  have hxinv : x⁻¹ ≤ 14 := by
    rw [← one_div,div_le_iff₀ hx0]
    have ha : (1 : ℝ) ≤ 14*alpha := by norm_num [alpha,truncatedSixthLowerAlpha]
    linarith only [ha,hx.1]
  have hlinv : (lam-x)⁻¹ ≤ 5 := by
    rw [← one_div,div_le_iff₀ hl0]
    have hb : (1 : ℝ) ≤ 5*(lam-beta) := by
      norm_num [lam,beta,truncatedSixthLowerLambda,truncatedSixthLowerAlpha,
        truncatedSixthLowerBeta]
    linarith only [hb,hx.2]
  have hlo := cross_nonneg hx
  have hlog : cross x ≤ log ((lam-alpha)/alpha) := by
    have hla : 0 < lam-alpha := by linarith only [hl0,hx.1]
    rw [log_div hla.ne' geometry.1.ne']
    unfold cross
    exact sub_le_sub (log_le_log hl0 (by linarith only [hx.1]))
      (log_le_log geometry.1 hx.1)
  have hu := SharpLogRecurrence.log_upper (t := (lam-alpha)/alpha)
    (by norm_num [lam,alpha,truncatedSixthLowerLambda,truncatedSixthLowerAlpha])
  have hu' : SharpLogRecurrence.upperLog ((lam-alpha)/alpha) ≤ (3/2 : ℝ) := by
    norm_num [SharpLogRecurrence.upperLog,lam,alpha,truncatedSixthLowerLambda,
      truncatedSixthLowerAlpha]
  exact ⟨by simpa only [abs_of_nonneg (inv_nonneg.mpr hx0.le)] using hxinv,
    by simpa only [abs_of_nonneg (inv_nonneg.mpr hl0.le)] using hlinv,
    by simpa only [abs_of_nonneg hlo] using hlog.trans (hu.trans hu')⟩

theorem w_bounds :
    (∀ x ∈ Icc alpha cut, |(36/5)/(x*(1-x))| ≤ 108) ∧
      (∀ x ∈ Icc cut beta, |8/x| ≤ 108) := by
  constructor
  · intro x hx
    have hx0 := geometry.1.trans_le hx.1
    have hx1 : (9/10 : ℝ) ≤ 1-x := by
      have hxc : x ≤ (1/10 : ℝ) := hx.2
      linarith only [hxc]
    have hden : 0 < x*(1-x) := mul_pos hx0 (by linarith only [hx1])
    rw [abs_of_nonneg (div_nonneg (by norm_num) hden.le),div_le_iff₀ hden]
    have hlow := mul_le_mul hx.1 hx1 (by norm_num : (0 : ℝ) ≤ 9/10) hx0.le
    norm_num [alpha,truncatedSixthLowerAlpha] at hlow
    linarith only [hlow]
  · intro x hx
    have hxc : (1/10 : ℝ) ≤ x := hx.1
    have hx0 : 0 < x := by linarith only [hxc]
    rw [abs_of_nonneg (div_nonneg (by norm_num) hx0.le),div_le_iff₀ hx0]
    linarith only [hxc]

#check @W_bounds
#check @Q_bounds
#check @elementary_bounds
#check @w_bounds
#print axioms W_bounds
#print axioms Q_bounds
#print axioms elementary_bounds
#print axioms w_bounds
end WuSource.SrcFourEnclosure

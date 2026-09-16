import Wu18938Campaign.M3.Confirmed.JCounts
import Wu18938Campaign.M3.Confirmed.ExistingClassical

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.FifthShape

open Real Set Wu2008DoubleSieve

def center : ℝ := 1098612/1000000
def linear : ℝ := 1/12-center/16
def quadratic : ℝ := center/64-5/144
def cubic : ℝ := 1/324-quadratic/4
def quartic : ℝ := (cubic+5/1296)/(17/5)
def shape (s : ℝ) : ℝ :=
  center/4+linear*(s-4)+quadratic*(s-4)^2+cubic*(s-4)^3-quartic*(s-4)^4
def remainder (s : ℝ) : ℝ :=
  log (s-1)-log 3-(s-4)/3+(s-4)^2/18-(s-4)^3/81+(5/1296)*(s-4)^4

theorem center_lower : center ≤ log (3:ℝ) := by
  have h := TableBounds.logLower_le (by norm_num : (1:ℝ) ≤ 3)
  have hn : center ≤ TableBounds.logLower 3 := by
    norm_num [center,TableBounds.logLower,Finset.sum_range_succ]
  exact hn.trans h

theorem remainder_derivative {s : ℝ} (hs : 17/5 ≤ s) :
    HasDerivAt remainder ((s-4)^3*(5*s-17)/(324*(s-1))) s := by
  have hn : s-1 ≠ 0 := by linarith
  have hd := ((((((hasDerivAt_id s).sub_const 1).log hn).sub_const (log 3)).sub
    (((hasDerivAt_id s).sub_const 4).div_const 3)).add
    ((((hasDerivAt_id s).sub_const 4).pow 2).div_const 18)).sub
    ((((hasDerivAt_id s).sub_const 4).pow 3).div_const 81)
  convert! hd.add ((((hasDerivAt_id s).sub_const 4).pow 4).const_mul (5/1296)) using 1
  dsimp
  field_simp [hn]
  ring

theorem remainder_nonnegative {s : ℝ} (hs : 17/5 ≤ s) : 0 ≤ remainder s := by
  have hz : remainder 4 = 0 := by norm_num [remainder]
  by_cases h4 : 4 ≤ s
  · have hm : MonotoneOn remainder (Icc 4 s) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      · intro x hx
        exact (remainder_derivative (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        exact (remainder_derivative (by
          have hh := interior_subset hx
          linarith [hh.1])).hasDerivWithinAt
      · intro x hx
        have hh := interior_subset hx
        exact div_nonneg (mul_nonneg (pow_nonneg (by linarith [hh.1]) _)
          (by linarith [hh.1])) (by linarith [hh.1])
    simpa only [hz] using hm ⟨le_rfl,h4⟩ ⟨h4,le_rfl⟩ h4
  · have h4' : s ≤ 4 := (lt_of_not_ge h4).le
    have hm : AntitoneOn remainder (Icc s 4) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      · intro x hx
        exact (remainder_derivative (hs.trans hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        exact (remainder_derivative (hs.trans (interior_subset hx).1)).hasDerivWithinAt
      · intro x hx
        have hh := interior_subset hx
        apply div_nonpos_of_nonpos_of_nonneg _ (by linarith [hh.1])
        apply mul_nonpos_of_nonpos_of_nonneg _ (by linarith [hh.1])
        rw [pow_succ]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith [hh.2])
    simpa only [hz] using hm ⟨le_rfl,h4'⟩ ⟨h4',le_rfl⟩ h4'

theorem scalar_lower {s : ℝ} (hs : 17/5 ≤ s) :
    shape s ≤ log (s-1)/s := by
  have he : center+(s-4)/3-(s-4)^2/18+(s-4)^3/81-
      (5/1296)*(s-4)^4-shape s*s =
      quartic*(s-17/5)*(s-4)^4 := by
    simp only [shape,linear,quadratic,cubic,quartic]
    ring
  have hq : 0 ≤ quartic := by norm_num [quartic,cubic,quadratic,center]
  have hp := mul_nonneg (mul_nonneg hq (sub_nonneg.mpr hs)) (by positivity : 0 ≤ (s-4)^4)
  have hr := remainder_nonnegative hs
  unfold remainder at hr
  apply (le_div_iff₀ (by linarith : 0 < s)).2
  linarith only [hr,center_lower,he,hp]

end Wu18938Campaign.M3.Confirmed.FifthShape

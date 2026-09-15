import Wu04WholeCostPaid
import Mathlib.Analysis.Convex.Deriv

namespace Wu04ThreeTail
open Wu2008DoubleSieve Real Set MeasureTheory LiLiuPrereqBuchstab
open SecondFunctionalFourSevenths SharpLogRecurrence JointLogTotalComparison
noncomputable section

def cap : ℝ := (1+V 2)/3

theorem fixed_seed : (1:ℝ)/2+V (3/2)-lowerLog 2/2 ≤ cap := by
  norm_num [cap,V,upperLog,lowerLog]

theorem cap_value : cap = (2743:ℝ)/4860 := by norm_num [cap,V,upperLog,lowerLog]

theorem cap_lt_main : cap < Wu04MainTail.cap := by rw [cap_value]; norm_num [Wu04MainTail.cap]

/-- This is a relaxation of the actual sharper upperLog, not a redefinition of it. -/
theorem log_le_half {x : ℝ} (hx : 1 ≤ x) : log x ≤ (x-1/x)/2 := by
  apply (log_upper hx).trans
  have hx0 : 0 < x := by linarith
  have hxp : 0 < x+1 := by linarith
  have he : (x-1/x)/2-upperLog x = (x-1)^3/(3*x*(x+1)) := by
    unfold upperLog
    field_simp
    ring
  have hn : 0 ≤ (x-1)^3/(3*x*(x+1)) := by positivity
  linarith only [he,hn]

def g (t : ℝ) : ℝ := 1/2+1/t-1/(2*(t-1))
def prim (t : ℝ) : ℝ := t/2+log t-log (t-1)/2

theorem g_cont : ContinuousOn g (Icc 2 3) := by
  apply_rules [ContinuousOn.sub, ContinuousOn.add, continuousOn_const]
  · exact continuousOn_const.div continuousOn_id (fun t ht => by linarith [ht.1])
  · exact continuousOn_const.div (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
      (fun t ht => by nlinarith [ht.1])

theorem prim_deriv {t : ℝ} (ht : 2 ≤ t) : HasDerivAt prim (g t) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t-1 ≠ 0 := by linarith
  have h := (((hasDerivAt_id t).div_const 2).add (hasDerivAt_log ht0)).sub
    ((((hasDerivAt_id t).sub_const 1).log ht1).div_const 2)
  convert h using 1 <;> first | rfl | (dsimp [g]; field_simp)

theorem g_mono : MonotoneOn g (Icc 2 3) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hx1 : 0 < x-1 := by linarith [hx.1]
  have hy1 : 0 < y-1 := by linarith [hy.1]
  have hp : (x-2)*(y-2) ≤ 1 := by nlinarith [hx.2,hy.2,mul_nonneg (show 0≤3-x by linarith [hx.2]) (show 0≤y-2 by linarith [hy.1])]
  have he : g y-g x = (y-x)*(2-(x-2)*(y-2))/(2*x*y*(x-1)*(y-1)) := by
    unfold g
    field_simp
    ring
  have hdiff : 0 ≤ y-x := sub_nonneg.mpr hxy
  have hnum : 0 ≤ 2-(x-2)*(y-2) := by linarith
  have hn : 0 ≤ (y-x)*(2-(x-2)*(y-2))/(2*x*y*(x-1)*(y-1)) := by positivity
  linarith only [he,hn]

theorem prim_convex : ConvexOn ℝ (Icc 2 3) prim := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _)
    (fun t ht => (prim_deriv ht.1).continuousAt.continuousWithinAt)
    (fun t ht => (prim_deriv (interior_subset ht).1).differentiableAt.differentiableWithinAt)
  intro x hx y hy hxy
  rw [(prim_deriv (interior_subset hx).1).deriv, (prim_deriv (interior_subset hy).1).deriv]
  exact g_mono (interior_subset hx) (interior_subset hy) hxy

theorem g_integral {v : ℝ} (hv : 2 ≤ v) (hv3 : v ≤ 3) :
    (∫ t in (2:ℝ)..v, g t) = prim v-prim 2 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => prim_deriv (by rw [uIcc_of_le hv] at ht; exact ht.1))
    ((g_cont.mono (show uIcc 2 v ⊆ Icc 2 3 by rw [uIcc_of_le hv]; exact Icc_subset_Icc le_rfl hv3)).intervalIntegrable)

theorem g_full : prim 3-prim 2 = (1:ℝ)/2+log (3/2)-log 2/2 := by
  unfold prim
  rw [log_div (by norm_num : (3:ℝ)≠0) (by norm_num : (2:ℝ)≠0)]
  norm_num
  ring

theorem history_average {v : ℝ} (hv : 2 ≤ v) (hv3 : v ≤ 3) :
    (∫ t in (2:ℝ)..v, buchstab t) ≤ (v-2)*cap := by
  have hmono := intervalIntegral.integral_mono_on (μ:=volume) hv
    (continuous_buchstab.intervalIntegrable 2 v)
    ((g_cont.mono (show uIcc 2 v ⊆ Icc 2 3 by rw [uIcc_of_le hv]; exact Icc_subset_Icc le_rfl hv3)).intervalIntegrable)
    (fun t ht => show buchstab t ≤ g t from by
      rw [buchstab_log_segment ht.1 (ht.2.trans hv3)]
      have ht0 : 0 < t := by linarith [ht.1]
      have ht1 : t-1 ≠ 0 := by linarith [ht.1]
      have h := div_le_div_of_nonneg_right
        (add_le_add_left (log_le_half (show 1 ≤ t-1 by linarith [ht.1])) 1) ht0.le
      calc
        _ ≤ (1+(t-1-1/(t-1))/2)/t := by simpa only [add_comm] using h
        _ = g t := by unfold g; field_simp; ring)
  rw [g_integral hv hv3] at hmono
  have hconv := prim_convex.2 (show (2:ℝ)∈Icc 2 3 by norm_num)
    (show (3:ℝ)∈Icc 2 3 by norm_num)
    (show 0≤3-v by linarith) (show 0≤v-2 by linarith) (show 3-v+(v-2)=1 by ring)
  simp only [smul_eq_mul] at hconv
  have he : (3-v)*2+(v-2)*3=v := by ring
  rw [he] at hconv
  have hfull : prim 3-prim 2 ≤ cap := by
    rw [g_full]
    have hu := log_le_V (by norm_num : (1:ℝ)≤3/2)
    have hl := log_lower (by norm_num : (1:ℝ)≤2)
    linarith only [hu,hl,fixed_seed]
  have hmul := mul_le_mul_of_nonneg_left hfull (show 0≤v-2 by linarith)
  nlinarith only [hmono,hconv,hmul]

theorem seed {u : ℝ} (hu : 3 ≤ u) (hu4 : u ≤ 4) : buchstab u ≤ cap := by
  have he := buchstab_increment (v:=3) (by norm_num) hu
  have hi := history_average (v:=u-1) (by linarith) (by linarith)
  have hb : 3*buchstab 3 ≤ 3*cap := by
    rw [buchstab_log_segment (by norm_num) le_rfl]
    have h := log_le_V (by norm_num : (1:ℝ)≤2)
    norm_num only [show (3:ℝ)-1=2 by norm_num]
    unfold cap
    linarith only [h]
  norm_num only [show (3:ℝ)-1=2 by norm_num] at he
  have hmul : u*buchstab u ≤ u*cap := by nlinarith only [he,hi,hb]
  exact (mul_le_mul_iff_right₀ (show 0<u by linarith)).mp hmul

/-- Parameterized continuation from a genuinely paid unit history interval. -/
theorem continuation_step {c v : ℝ} (hv : 4 ≤ v)
    (hh : ∀ t : ℝ, 3 ≤ t → t ≤ v → buchstab t ≤ c)
    {u : ℝ} (hvu : v ≤ u) (hu : u ≤ v+1) : buchstab u ≤ c := by
  have hi := intervalIntegral.integral_mono_on (μ:=volume) (show v-1≤u-1 by linarith)
    (continuous_buchstab.intervalIntegrable (v-1) (u-1))
    (intervalIntegrable_const (c:=c))
    (fun t ht => hh t (by linarith [ht.1]) (by linarith [ht.2]))
  rw [intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  have he := buchstab_increment (by linarith : 2≤v) hvu
  have hb := mul_le_mul_of_nonneg_left (hh v (by linarith) le_rfl) (by linarith : 0≤v)
  have hmul : u*buchstab u ≤ u*c := by nlinarith only [hi,he,hb]
  exact (mul_le_mul_iff_right₀ (by linarith : 0<u)).mp hmul

theorem tail_prefix (n : ℕ) : ∀ u : ℝ, 3≤u → u≤(n:ℝ)+4 → buchstab u≤cap := by
  induction n with
  | zero => simpa using fun u hu hu4 => seed (u:=u) hu hu4
  | succ n ih =>
    intro u hu hub
    by_cases hn : u≤(n:ℝ)+4
    · exact ih u hu hn
    · apply continuation_step (v:=(n:ℝ)+4) (by linarith [Nat.cast_nonneg (α:=ℝ) n]) ih (le_of_not_ge hn)
      push_cast at hub
      linarith

theorem buchstab_le {u : ℝ} (hu : 3≤u) : buchstab u≤cap := by
  obtain ⟨n,hn⟩ := exists_nat_gt u
  exact tail_prefix n u hu (by linarith)

end
end Wu04ThreeTail

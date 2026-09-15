import WSrcFourEnclosureQuadrature

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass

namespace WuSource.SrcFourEnclosure

def logLo (t : ℝ) : ℝ :=
  2*∑ i ∈ Finset.range 12, ((t-1)/(t+1))^(2*i+1)/(2*i+1 : ℝ)
def logHi (t : ℝ) : ℝ :=
  logLo t+2*((t-1)/(t+1))^25/(1-((t-1)/(t+1))^2)

theorem log_bounds {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ logLo t ∧ logLo t ≤ log t ∧ log t ≤ logHi t := by
  have ht0 : 0 < t := by linarith only [ht]
  have ht1 : 0 < t+1 := by linarith only [ht]
  have hr0 : 0 ≤ (t-1)/(t+1) := div_nonneg (by linarith only [ht]) ht1.le
  have hr1 : (t-1)/(t+1) < 1 := (div_lt_one ht1).mpr (by linarith)
  have he : (1+(t-1)/(t+1))/(1-(t-1)/(t+1)) = t := by
    have hn : 1-(t-1)/(t+1) ≠ 0 := by linarith only [hr1]
    field_simp
    ring
  have hl := Real.sum_range_le_log_div hr0 hr1 12
  have hu := Real.log_div_le_sum_range_add hr0 hr1 12
  rw [he] at hl hu
  have hpos : 0 ≤ logLo t := by
    unfold logLo
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    exact div_nonneg (pow_nonneg hr0 _) (by positivity)
  refine ⟨hpos,?_,?_⟩
  · unfold logLo
    linarith only [hl]
  · unfold logHi logLo
    norm_num only [show 2*12+1 = (25 : ℕ) by omega] at hu
    rw [mul_div_assoc]
    linarith only [hu]

def smallWLo (x : ℝ) : ℝ := (36/5)*(logLo (x/alpha)+logLo ((1-alpha)/(1-x)))
def smallWHi (x : ℝ) : ℝ := (36/5)*(logHi (x/alpha)+logHi ((1-alpha)/(1-x)))
def smallQLo (x : ℝ) : ℝ :=
  max 0 ((36/5)*(1/alpha-1/x)+(1-1/x)*smallWHi x)
def smallQHi (x : ℝ) : ℝ :=
  (36/5)*(1/alpha-1/x)+(1-1/x)*smallWLo x
def largeQLo (x : ℝ) : ℝ :=
  max 0 ((36/5)*(1/alpha-1/cut)+(1-1/x)*smallWHi cut+
    8*(1/cut-1/x)-8*logHi (x/cut)/x)
def largeQHi (x : ℝ) : ℝ :=
  (36/5)*(1/alpha-1/cut)+(1-1/x)*smallWLo cut+
    8*(1/cut-1/x)-8*logLo (x/cut)/x
def smallLo (x : ℝ) : ℝ := smallQLo x*logLo ((lam-x)/x)/x
def smallHi (x : ℝ) : ℝ := smallQHi x*logHi ((lam-x)/x)/x
def largeLo (x : ℝ) : ℝ := largeQLo x*logLo ((lam-x)/x)/x
def largeHi (x : ℝ) : ℝ := largeQHi x*logHi ((lam-x)/x)/x

theorem smallW_log_bounds {x : ℝ} (hx : x ∈ Icc alpha cut) :
    smallWLo x ≤ smallW x ∧ smallW x ≤ smallWHi x := by
  have hx0 := geometry.1.trans_le hx.1
  have hx1 : 0 < 1-x := by
    have hxc : x ≤ (1/10 : ℝ) := hx.2
    linarith only [hxc]
  have ha1 : 0 < 1-alpha := by linarith only [hx.1,hx1]
  have h1 := log_bounds (t := x/alpha)
    ((le_div_iff₀ geometry.1).mpr (by simpa using hx.1))
  have h2 := log_bounds (t := (1-alpha)/(1-x))
    ((le_div_iff₀ hx1).mpr (by linarith only [hx.1]))
  rw [log_div hx0.ne' geometry.1.ne'] at h1
  rw [log_div ha1.ne' hx1.ne'] at h2
  unfold smallWLo smallWHi smallW
  constructor <;> linarith only [h1.2.1,h1.2.2,h2.2.1,h2.2.2]

theorem smallQ_log_bounds {x : ℝ} (hx : x ∈ Icc alpha cut) :
    0 ≤ smallQLo x ∧ smallQLo x ≤ smallQ x ∧ smallQ x ≤ smallQHi x := by
  have hx0 := geometry.1.trans_le hx.1
  have hc : 1-1/x ≤ 0 := by
    have hxc : x ≤ (1/10 : ℝ) := hx.2
    have h1 : (1 : ℝ) ≤ 1/x := (le_div_iff₀ hx0).mpr (by linarith only [hxc])
    linarith only [h1]
  have hW := smallW_log_bounds hx
  have h1 := mul_le_mul_of_nonpos_left hW.2 hc
  have h2 := mul_le_mul_of_nonpos_left hW.1 hc
  refine ⟨le_max_left _ _,max_le (Q_bounds.1 x hx).1 ?_,?_⟩
  · unfold smallQ
    linarith only [h1]
  · unfold smallQ smallQHi
    linarith only [h2]

theorem largeQ_formula (x : ℝ) :
    largeQ x = (36/5)*(1/alpha-1/cut)+(1-1/x)*smallW cut+
      8*(1/cut-1/x)-8*(log x-log cut)/x := by
  unfold largeQ smallQ largeW
  ring

theorem largeQ_log_bounds {x : ℝ} (hx : x ∈ Icc cut beta) :
    0 ≤ largeQLo x ∧ largeQLo x ≤ largeQ x ∧ largeQ x ≤ largeQHi x := by
  have hc0 : 0 < cut := by norm_num [cut]
  have hx0 := hc0.trans_le hx.1
  have hc : 1-1/x ≤ 0 := by
    have h1 : (1 : ℝ) ≤ 1/x :=
      (le_div_iff₀ hx0).mpr (by linarith only [hx.2,geometry.2.2.1])
    linarith only [h1]
  have hW := smallW_log_bounds (x := cut) ⟨geometry.2.2.2.2.2.1,le_rfl⟩
  have hlog := log_bounds (t := x/cut) ((le_div_iff₀ hc0).mpr (by simpa using hx.1))
  rw [log_div hx0.ne' hc0.ne'] at hlog
  have h1 := mul_le_mul_of_nonpos_left hW.2 hc
  have h2 := mul_le_mul_of_nonpos_left hW.1 hc
  have hl := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog.2.1 (by norm_num : (0 : ℝ) ≤ 8)) hx0.le
  have hu := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog.2.2 (by norm_num : (0 : ℝ) ≤ 8)) hx0.le
  refine ⟨le_max_left _ _,max_le (Q_bounds.2 x hx).1 ?_,?_⟩
  · rw [largeQ_formula]
    linarith only [h1,hu]
  · rw [largeQ_formula]
    unfold largeQHi
    linarith only [h2,hl]

theorem cross_log_bounds {x : ℝ} (hx : x ∈ Icc alpha beta) :
    0 ≤ logLo ((lam-x)/x) ∧ logLo ((lam-x)/x) ≤ cross x ∧
      cross x ≤ logHi ((lam-x)/x) := by
  have hx0 := geometry.1.trans_le hx.1
  have hlx : 0 < lam-x := by linarith only [hx.2,geometry.2.2.2.1]
  have harg : (1 : ℝ) ≤ (lam-x)/x :=
    (le_div_iff₀ hx0).mpr (by linarith only [hx.2,geometry.2.2.2.2.1])
  have h := log_bounds harg
  rwa [log_div hlx.ne' hx0.ne'] at h

theorem small_node_enclosure {x : ℝ} (hx : x ∈ Icc alpha cut) :
    smallLo x ≤ smallF x ∧ smallF x ≤ smallHi x := by
  have hxb : x ∈ Icc alpha beta := ⟨hx.1,hx.2.trans geometry.2.2.2.2.2.2⟩
  have hq := smallQ_log_bounds hx
  have hc := cross_log_bounds hxb
  have hx0 := geometry.1.trans_le hx.1
  exact ⟨div_le_div_of_nonneg_right
    (mul_le_mul hq.2.1 hc.2.1 hc.1 (Q_bounds.1 x hx).1) hx0.le,
    div_le_div_of_nonneg_right
      (mul_le_mul hq.2.2 hc.2.2 (cross_nonneg hxb)
        ((Q_bounds.1 x hx).1.trans hq.2.2)) hx0.le⟩

theorem large_node_enclosure {x : ℝ} (hx : x ∈ Icc cut beta) :
    largeLo x ≤ largeF x ∧ largeF x ≤ largeHi x := by
  have hxb : x ∈ Icc alpha beta := ⟨geometry.2.2.2.2.2.1.trans hx.1,hx.2⟩
  have hq := largeQ_log_bounds hx
  have hc := cross_log_bounds hxb
  have hx0 := geometry.1.trans_le hxb.1
  exact ⟨div_le_div_of_nonneg_right
    (mul_le_mul hq.2.1 hc.2.1 hc.1 (Q_bounds.2 x hx).1) hx0.le,
    div_le_div_of_nonneg_right
      (mul_le_mul hq.2.2 hc.2.2 (cross_nonneg hxb)
        ((Q_bounds.2 x hx).1.trans hq.2.2)) hx0.le⟩

theorem mass_rational_sums :
    midpointSum smallLo alpha cut+midpointSum largeLo cut beta-
      (error alpha cut+error cut beta) ≤ mass ∧
    mass ≤ midpointSum smallHi alpha cut+midpointSum largeHi cut beta+
      (error alpha cut+error cut beta) := by
  have hm := mass_midpoint_enclosure
  have hs1 : midpointSum smallLo alpha cut ≤ midpointSum smallF alpha cut := by
    unfold midpointSum
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi =>
      (small_node_enclosure (midpoint_coverage geometry.2.2.2.2.2.1 (Finset.mem_range.mp hi))).1))
      (by have h := geometry.2.2.2.2.2.1; change alpha ≤ cut at h; linarith only [h])
  have hs2 : midpointSum smallF alpha cut ≤ midpointSum smallHi alpha cut := by
    unfold midpointSum
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi =>
      (small_node_enclosure (midpoint_coverage geometry.2.2.2.2.2.1 (Finset.mem_range.mp hi))).2))
      (by have h := geometry.2.2.2.2.2.1; change alpha ≤ cut at h; linarith only [h])
  have hl1 : midpointSum largeLo cut beta ≤ midpointSum largeF cut beta := by
    unfold midpointSum
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi =>
      (large_node_enclosure (midpoint_coverage geometry.2.2.2.2.2.2 (Finset.mem_range.mp hi))).1))
      (by have h := geometry.2.2.2.2.2.2; change cut ≤ beta at h; linarith only [h])
  have hl2 : midpointSum largeF cut beta ≤ midpointSum largeHi cut beta := by
    unfold midpointSum
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi =>
      (large_node_enclosure (midpoint_coverage geometry.2.2.2.2.2.2 (Finset.mem_range.mp hi))).2))
      (by have h := geometry.2.2.2.2.2.2; change cut ≤ beta at h; linarith only [h])
  constructor <;> linarith only [hm.1,hm.2,hs1,hs2,hl1,hl2]

#check @small_node_enclosure
#check @large_node_enclosure
#check @mass_rational_sums
#print axioms small_node_enclosure
#print axioms large_node_enclosure
#print axioms mass_rational_sums
end WuSource.SrcFourEnclosure

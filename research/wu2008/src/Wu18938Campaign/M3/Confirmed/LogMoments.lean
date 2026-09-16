import Wu18938Campaign.M3.Confirmed.SecondClassical

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.LogMoments

open Real Set MeasureTheory Finset

def logUpper (n : ℕ) (x : ℝ) : ℝ :=
  2 * (∑ i ∈ range n, ((x-1)/(x+1))^(2*i+1)/(2*i+1:ℝ)) +
    2*((x-1)/(x+1))^(2*n+1)/(1-((x-1)/(x+1))^2)

theorem log_upper {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    log x ≤ logUpper n x := by
  have hp : 0 < x+1 := by linarith
  have h0 : 0 ≤ (x-1)/(x+1) := div_nonneg (by linarith) hp.le
  have h1 : (x-1)/(x+1) < 1 := (div_lt_one hp).mpr (by linarith)
  have he : (1+(x-1)/(x+1))/(1-(x-1)/(x+1)) = x := by
    field_simp
    ring
  have h := Real.log_div_le_sum_range_add h0 h1 n
  rw [he] at h
  unfold logUpper
  ring_nf at h ⊢
  linarith only [h]

def moment (d : ℝ) : ℕ → ℝ → ℝ
  | 0, z => -log (d-z)
  | k+1, z => d*moment d k z-z^(k+1)/(k+1:ℝ)

theorem moment_derivative (d : ℝ) (k : ℕ) {z : ℝ} (hz : z < d) :
    HasDerivAt (moment d k) (z^k/(d-z)) z := by
  have hn : d-z ≠ 0 := sub_pos.mpr hz |>.ne'
  induction k with
  | zero =>
    convert! (((hasDerivAt_id z).const_sub d).log hn).neg using 1
    simp only [pow_zero, one_div, id_eq]
    ring
  | succ k ih =>
    have hk : (k+1:ℝ) ≠ 0 := by positivity
    have h := (ih.const_mul d).sub (((hasDerivAt_id z).pow (k+1)).div_const (k+1:ℝ))
    convert h using 1 <;> first | rfl | (dsimp; push_cast; field_simp; ring)

def momentBound (d l r L : ℝ) : ℕ → ℝ
  | 0 => L
  | k+1 => d*momentBound d l r L k-(r^(k+1)-l^(k+1))/(k+1:ℝ)

theorem moment_bound {d l r L : ℝ} (hd : 0 ≤ d) (hl : l < d) (hr : r < d)
    (hlog : log ((d-l)/(d-r)) ≤ L) (k : ℕ) :
    moment d k r-moment d k l ≤ momentBound d l r L k := by
  induction k with
  | zero =>
    simpa only [moment, momentBound, log_div (sub_pos.mpr hl).ne'
      (sub_pos.mpr hr).ne', neg_sub_neg] using hlog
  | succ k ih =>
    have h := mul_le_mul_of_nonneg_left ih hd
    simp only [moment, momentBound]
    ring_nf at h ⊢
    linarith only [h]

def primitive (n : ℕ) (d b z : ℝ) : ℝ :=
  2*(∑ i ∈ range n, moment d (2*i+1) z/(2*i+1:ℝ)) +
    2*moment d (2*n+1) z/(1-b^2)

def polynomial (n : ℕ) (b z : ℝ) : ℝ :=
  2*(∑ i ∈ range n, z^(2*i+1)/(2*i+1:ℝ)) + 2*z^(2*n+1)/(1-b^2)

theorem primitive_derivative (n : ℕ) {d b z : ℝ} (hz : z < d) :
    HasDerivAt (primitive n d b) (polynomial n b z/(d-z)) z := by
  have h := ((HasDerivAt.fun_sum fun i (_hi : i ∈ range n) =>
    (moment_derivative d (2*i+1) hz).div_const (2*i+1:ℝ)).const_mul 2).add
      (((moment_derivative d (2*n+1) hz).const_mul 2).div_const (1-b^2))
  have hs : (∑ i ∈ range n, z^(2*i+1)/(d-z)/(2*i+1:ℝ)) =
      (∑ i ∈ range n, z^(2*i+1)/(2*i+1:ℝ))/(d-z) := by
    rw [sum_div]
    apply sum_congr rfl
    intro i _
    ring
  convert! h using 1
  rw [hs]
  unfold polynomial
  ring

theorem polynomial_upper (n : ℕ) {b z : ℝ}
    (hz : 0 ≤ z) (hzb : z ≤ b) (hb : b < 1) :
    log ((1+z)/(1-z)) ≤ polynomial n b z := by
  have hz1 : z < 1 := hzb.trans_lt hb
  have hb0 : 0 ≤ b := hz.trans hzb
  have hd : 0 < 1-b^2 := by nlinarith
  have hpow := pow_le_pow_left₀ hz hzb 2
  have h := Real.log_div_le_sum_range_add hz hz1 n
  have he := div_le_div_of_nonneg_left (pow_nonneg hz (2*n+1)) hd
    (by linarith [hpow] : 1-b^2 ≤ 1-z^2)
  unfold polynomial
  ring_nf at h he ⊢
  linarith only [h, he]

def endpointBound (n : ℕ) (d b l r L : ℝ) : ℝ :=
  2*(∑ i ∈ range n, momentBound d l r L (2*i+1)/(2*i+1:ℝ)) +
    2*momentBound d l r L (2*n+1)/(1-b^2)

theorem endpoint_bound (n : ℕ) {d b l r L : ℝ}
    (hd : 0 ≤ d) (hb0 : 0 ≤ b) (hb : b < 1)
    (hl : l < d) (hr : r < d) (hlog : log ((d-l)/(d-r)) ≤ L) :
    primitive n d b r-primitive n d b l ≤ endpointBound n d b l r L := by
  have hs := sum_le_sum (s := range n) (fun i _ =>
    div_le_div_of_nonneg_right (moment_bound hd hl hr hlog (2*i+1))
      (show 0 ≤ (2*i+1:ℝ) by positivity))
  have ht := div_le_div_of_nonneg_right (moment_bound hd hl hr hlog (2*n+1))
    (show 0 ≤ 1-b^2 by nlinarith)
  unfold primitive endpointBound
  simp only [sub_div, sum_sub_distrib] at hs
  ring_nf at hs ht ⊢
  linarith only [hs, ht]

end Wu18938Campaign.M3.Confirmed.LogMoments

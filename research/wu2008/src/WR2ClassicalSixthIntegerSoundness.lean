import WR2ClassicalSixthIntegerData
import WR2ClassicalSixthTableCheck
set_option maxRecDepth 3000
set_option maxHeartbeats 40000
namespace WuPaper.SixthIntegerPayment
open IntegerLogHorner

theorem upper_abstract (U V : ℕ) (hu : 54356435000 ≤ U) (hv : 27812929320000 ≤ V) :
    53080000*gridDenominator^2 ≤ U*V ∧ 0 < 53080000*gridDenominator^2 := by
  constructor
  · have h : 53080000*gridDenominator^2 ≤ 54356435000*27812929320000 := by
      norm_num [gridDenominator]
    exact h.trans (Nat.mul_le_mul hu hv)
  · norm_num [gridDenominator]

theorem lower_abstract (U V : ℕ) (hu : 70187110400 ≤ U)
    (hv : V ≤ 84115691929600) (hp : 27812929320000 ≤ V) :
    V ≤ 1327*U ∧ 0 < V := by
  have h : 84115691929600 ≤ 1327*70187110400 := by norm_num
  exact ⟨hv.trans (h.trans (Nat.mul_le_mul_left 1327 hu)), by omega⟩

theorem grid_bounds (upper : Bool) {i : ℕ} (hi : i < 4096) :
    2*gridDenominator ≤ gridNumerator upper i ∧ gridNumerator upper i ≤ 679153377 := by
  cases upper <;> dsimp [gridNumerator,gridDenominator] <;> omega

theorem linear_bounds (upper : Bool) {i : ℕ} (hi : i < 4096) :
    54356435000 ≤ uNumerator upper i ∧ 27812929320000 ≤ vNumerator upper i ∧
      88107475000 ≤ weightNumerator upper i := by
  have h := grid_bounds upper hi
  dsimp [uNumerator,vNumerator,weightNumerator,gridDenominator] at *
  omega

theorem lower_s_max {i : ℕ} (hi : i < 4096) : gridNumerator false i ≤ 600000000 := by
  dsimp [gridNumerator]
  omega

theorem lower_u_min {i : ℕ} (hi : i < 4096) : 70187110400 ≤ uNumerator false i := by
  have hs := lower_s_max hi
  dsimp [uNumerator,gridDenominator]
  omega

theorem lower_v_max {i : ℕ} (hi : i < 4096) : vNumerator false i ≤ 84115691929600 := by
  have hs := (grid_bounds false hi).1
  dsimp [vNumerator,gridDenominator] at *
  omega

theorem ratio_bounds_upper {i : ℕ} (hi : i < 4096) :
    ratioDenominator true i ≤ ratioNumerator true i ∧ 0 < ratioDenominator true i := by
  simp only [ratioDenominator,ratioNumerator,↓reduceIte]
  exact upper_abstract (uNumerator true i) (vNumerator true i)
    (linear_bounds true hi).1 (linear_bounds true hi).2.1

theorem ratio_bounds_lower {i : ℕ} (hi : i < 4096) :
    ratioDenominator false i ≤ ratioNumerator false i ∧ 0 < ratioDenominator false i := by
  simp only [ratioDenominator,ratioNumerator,Bool.false_eq_true,↓reduceIte]
  exact lower_abstract (uNumerator false i) (vNumerator false i)
    (lower_u_min hi) (lower_v_max hi) (linear_bounds false hi).2.1

theorem ratio_bounds (upper : Bool) {i : ℕ} (hi : i < 4096) :
    ratioDenominator upper i ≤ ratioNumerator upper i ∧ 0 < ratioDenominator upper i := by
  cases upper
  · exact ratio_bounds_lower hi
  · exact ratio_bounds_upper hi


def rationalRatio (upper : Bool) (s : ℚ) : ℚ :=
  if upper then ClassicalSixthTableCheck.u s*ClassicalSixthTableCheck.v s/ClassicalSixthTableCheck.r
  else ClassicalSixthTableCheck.r*ClassicalSixthTableCheck.u s/ClassicalSixthTableCheck.v s
def rationalValue (upper : Bool) (s : ℚ) : ℚ := ClassicalSixthTableCheck.value (rationalRatio upper s) s

theorem midpoint_lower (i : ℕ) :
    (gridNumerator false i:ℚ)/(gridDenominator:ℚ) =
      ExactRational.midpoint 2 ClassicalSixthTableCheck.split 4096 i := by
  simp only [gridNumerator,gridDenominator,ExactRational.midpoint,
    ClassicalSixthTableCheck.split,Nat.cast_ofNat]
  norm_num
  ring

theorem midpoint_upper (i : ℕ) :
    (gridNumerator true i:ℚ)/(gridDenominator:ℚ) =
      ExactRational.midpoint ClassicalSixthTableCheck.split ClassicalSixthTableCheck.endpoint 4096 i := by
  simp only [gridNumerator,gridDenominator,ExactRational.midpoint,
    ClassicalSixthTableCheck.split,ClassicalSixthTableCheck.endpoint,
    Nat.cast_ofNat]
  norm_num
  ring

theorem u_grid (upper : Bool) {i : ℕ} (hi : i < 4096) :
    ClassicalSixthTableCheck.u ((gridNumerator upper i:ℚ)/gridDenominator) =
      (uNumerator upper i:ℚ)/(200*gridDenominator) := by
  have hg := grid_bounds upper hi
  have hu : 200*gridNumerator upper i ≤ 1127*gridDenominator := by
    dsimp [gridDenominator] at *; omega
  rw [uNumerator,Nat.cast_sub hu]
  push_cast
  norm_num [ClassicalSixthTableCheck.u,ClassicalSixthTableCheck.R,gridDenominator]
  ring

theorem v_grid (upper : Bool) {i : ℕ} (hi : i < 4096) :
    ClassicalSixthTableCheck.v ((gridNumerator upper i:ℚ)/gridDenominator) =
      (vNumerator upper i:ℚ)/(164800*gridDenominator) := by
  have hg := grid_bounds upper hi
  have hv : 164800*gridNumerator upper i ≤ 828048*gridDenominator := by
    dsimp [gridDenominator] at *; omega
  rw [vNumerator,Nat.cast_sub hv]
  push_cast
  norm_num [ClassicalSixthTableCheck.v,ClassicalSixthTableCheck.R,ClassicalSixthTableCheck.r,gridDenominator]
  ring

/-- Rational branch algebra is kept separate from the degree-23 log identities. -/
theorem lower_ratio_algebra (U V D : ℚ) (hD : D ≠ 0) (hV : V ≠ 0) :
    (1327/824)*(U/(200*D))/(V/(164800*D)) = 1327*U/V := by
  field_simp [hD,hV]
  ring

theorem upper_ratio_algebra (U V D : ℚ) (hD : D ≠ 0) :
    (U/(200*D))*(V/(164800*D))/(1327/824) = U*V/(53080000*D^2) := by
  field_simp [hD]
  ring

theorem ratio_grid (upper : Bool) {i : ℕ} (hi : i < 4096) :
    rationalRatio upper ((gridNumerator upper i:ℚ)/gridDenominator) =
      (ratioNumerator upper i:ℚ)/(ratioDenominator upper i:ℚ) := by
  have hd : (gridDenominator:ℚ) ≠ 0 := by norm_num [gridDenominator]
  have hv : (vNumerator upper i:ℚ) ≠ 0 := by
    exact_mod_cast (show vNumerator upper i ≠ 0 by have h := linear_bounds upper hi; omega)
  unfold rationalRatio
  cases upper
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [u_grid false hi,v_grid false hi]
    simpa only [ClassicalSixthTableCheck.r,ratioNumerator,ratioDenominator,
      Bool.false_eq_true,↓reduceIte,Nat.cast_mul,Nat.cast_ofNat] using
      lower_ratio_algebra (uNumerator false i:ℚ) (vNumerator false i:ℚ) (gridDenominator:ℚ) hd hv
  · simp only [↓reduceIte]
    rw [u_grid true hi,v_grid true hi]
    simpa only [ClassicalSixthTableCheck.r,ratioNumerator,ratioDenominator,
      ↓reduceIte,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
      upper_ratio_algebra (uNumerator true i:ℚ) (vNumerator true i:ℚ) (gridDenominator:ℚ) hd

theorem weight_grid (upper : Bool) {i : ℕ} (hi : i < 4096) :
    1-2*(100/1327)*((gridNumerator upper i:ℚ)/gridDenominator) =
      (weightNumerator upper i:ℚ)/(1327*gridDenominator) := by
  have hg := grid_bounds upper hi
  have hw : 200*gridNumerator upper i ≤ 1327*gridDenominator := by
    dsimp [gridDenominator] at *; omega
  rw [weightNumerator,Nat.cast_sub hw]
  push_cast
  norm_num [gridDenominator]
  ring

theorem scaled_product (K D S W A B C E : ℚ) (hD : D ≠ 0) :
    K*1327*D^2*A*B/(C*E*S*W) =
      K*((A/C)*(B/E)/((S/D)*(W/(1327*D)))) := by
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  field_simp [hD]

theorem raw_fraction_eq (upper : Bool) {i : ℕ} (hi : i < 4096) :
    (rawNumerator upper i:ℚ)/(rawDenominator upper i:ℚ) =
      (scale:ℚ)*rationalValue upper ((gridNumerator upper i:ℚ)/gridDenominator) := by
  have hg := grid_bounds upper hi
  have hr := ratio_bounds upper hi
  have hd : 0 < gridDenominator := by decide
  have hs : gridDenominator ≤ gridNumerator upper i := by omega
  have hs' : gridDenominator ≤ gridNumerator upper i-gridDenominator := by omega
  have hfirst := logLo_nat_ratio hr.1 hr.2
  have hsecond := logLo_nat_ratio hs' hd
  rw [show gridNumerator upper i-gridDenominator-gridDenominator =
      gridNumerator upper i-2*gridDenominator by omega,
    show gridNumerator upper i-gridDenominator+gridDenominator = gridNumerator upper i by omega] at hsecond
  have harg : ((gridNumerator upper i-gridDenominator:ℕ):ℚ)/(gridDenominator:ℚ) =
      (gridNumerator upper i:ℚ)/(gridDenominator:ℚ)-1 := by
    rw [Nat.cast_sub hs]
    norm_num [gridDenominator]
    ring
  rw [harg] at hsecond
  unfold rationalValue ClassicalSixthTableCheck.value
  rw [ratio_grid upper hi,hfirst,hsecond,weight_grid upper hi]
  simpa only [rawNumerator,rawDenominator,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
    scaled_product (scale:ℚ) (gridDenominator:ℚ) (gridNumerator upper i:ℚ)
      (weightNumerator upper i:ℚ)
      (numerator (ratioNumerator upper i-ratioDenominator upper i)
        (ratioNumerator upper i+ratioDenominator upper i):ℚ)
      (numerator (gridNumerator upper i-2*gridDenominator) (gridNumerator upper i):ℚ)
      (denominator (ratioNumerator upper i+ratioDenominator upper i):ℚ)
      (denominator (gridNumerator upper i):ℚ) (by norm_num [gridDenominator])

theorem integer_paid_rat (upper : Bool) {i : ℕ} (hi : i < 4096) :
    (paymentNumerator upper i:ℚ)/(scale:ℚ) ≤
      rationalValue upper ((gridNumerator upper i:ℚ)/gridDenominator) := by
  simpa only [paymentNumerator,if_pos hi] using
    quotient_payment_of_exact (show 0 < scale by decide) (raw_fraction_eq upper hi)

theorem lower_paid {i : ℕ} (hi : i < 4096) :
    ClassicalSixthTableCheck.lowerCondition (paymentNumerator false) i := by
  simpa only [ClassicalSixthTableCheck.lowerCondition,scale,Nat.cast_ofNat,rationalValue,rationalRatio,
    Bool.false_eq_true,↓reduceIte,ClassicalSixthTableCheck.lowerValue,midpoint_lower] using
    integer_paid_rat false hi

theorem upper_paid {i : ℕ} (hi : i < 4096) :
    ClassicalSixthTableCheck.upperCondition (paymentNumerator true) i := by
  simpa only [ClassicalSixthTableCheck.upperCondition,scale,Nat.cast_ofNat,rationalValue,rationalRatio,
    ↓reduceIte,ClassicalSixthTableCheck.upperValue,midpoint_upper] using integer_paid_rat true hi
end WuPaper.SixthIntegerPayment
#print axioms WuPaper.SixthIntegerPayment.raw_fraction_eq
#print axioms WuPaper.SixthIntegerPayment.lower_paid
#print axioms WuPaper.SixthIntegerPayment.upper_paid

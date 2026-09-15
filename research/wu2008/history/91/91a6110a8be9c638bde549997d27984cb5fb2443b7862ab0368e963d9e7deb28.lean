import SrcFourEnclosureDerivatives

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass

namespace WuSource.SrcFourEnclosure

theorem minimum_of_second {f f' f'' : ℝ → ℝ} {a b m x : ℝ}
    (hm : m ∈ Icc a b) (hx : x ∈ Icc a b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc a b, HasDerivAt f' (f'' t) t)
    (hf'' : ∀ t ∈ Icc a b, 0 ≤ f'' t) (hm' : f' m = 0) :
    f m ≤ f x := by
  have hmono := monotone_of_derivative hf' hf''
  by_cases hmx : m ≤ x
  · have hsub : Icc m x ⊆ Icc a b := fun t ht => ⟨hm.1.trans ht.1,ht.2.trans hx.2⟩
    have hpos : ∀ t ∈ Icc m x, 0 ≤ f' t := by
      intro t ht
      have hh := hmono hm (hsub ht) ht.1
      rwa [hm'] at hh
    exact monotone_of_derivative (fun t ht => hf t (hsub ht)) hpos
      ⟨le_rfl,hmx⟩ ⟨hmx,le_rfl⟩ hmx
  · have hxm := (lt_of_not_ge hmx).le
    have hsub : Icc x m ⊆ Icc a b := fun t ht => ⟨hx.1.trans ht.1,ht.2.trans hm.2⟩
    have hneg : ∀ t ∈ Icc x m, f' t ≤ 0 := by
      intro t ht
      have hh := hmono (hsub ht) hm ht.2
      rwa [hm'] at hh
    have hant : AntitoneOn f (Icc x m) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x m)
        (fun t ht => (hf t (hsub ht)).continuousAt.continuousWithinAt)
        (fun t ht => (hf t (hsub (interior_subset ht))).hasDerivWithinAt)
        (fun t ht => hneg t (interior_subset ht))
    exact hant ⟨le_rfl,hxm⟩ ⟨hxm,le_rfl⟩ hxm

theorem taylor_two_sided {f f' f'' : ℝ → ℝ} {a b m x B : ℝ}
    (hm : m ∈ Icc a b) (hx : x ∈ Icc a b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc a b, HasDerivAt f' (f'' t) t)
    (hB : ∀ t ∈ Icc a b, |f'' t| ≤ B) :
    f m+f' m*(x-m)-B*(x-m)^2/2 ≤ f x ∧
      f x ≤ f m+f' m*(x-m)+B*(x-m)^2/2 := by
  have hupper := minimum_of_second (f := fun t =>
    B*(t-m)^2/2-f t+f m+f' m*(t-m))
    (f' := fun t => B*(t-m)-f' t+f' m) (f'' := fun t => B-f'' t)
    hm hx
    (fun t ht => by
      convert (((((hasDerivAt_id t).sub_const m).pow 2).const_mul B |>.div_const 2).sub
        (hf t ht) |>.add_const (f m)).add
        (((hasDerivAt_id t).sub_const m).const_mul (f' m)) using 1 <;>
          first | rfl | (dsimp; ring))
    (fun t ht => by
      convert ((((hasDerivAt_id t).sub_const m).const_mul B).sub
        (hf' t ht)).add_const (f' m) using 1 <;> first | rfl | ring)
    (fun t ht => sub_nonneg.mpr (abs_le.mp (hB t ht)).2) (by ring)
  have hlower := minimum_of_second (f := fun t =>
    B*(t-m)^2/2+f t-f m-f' m*(t-m))
    (f' := fun t => B*(t-m)+f' t-f' m) (f'' := fun t => B+f'' t)
    hm hx
    (fun t ht => by
      convert (((((hasDerivAt_id t).sub_const m).pow 2).const_mul B |>.div_const 2).add
        (hf t ht) |>.sub_const (f m)).sub
        (((hasDerivAt_id t).sub_const m).const_mul (f' m)) using 1 <;>
          first | rfl | (dsimp; ring))
    (fun t ht => by
      convert ((((hasDerivAt_id t).sub_const m).const_mul B).add
        (hf' t ht)).sub_const (f' m) using 1 <;> first | rfl | ring)
    (fun t ht => by linarith only [(abs_le.mp (hB t ht)).1]) (by ring)
  constructor <;> linarith only [hupper,hlower]

theorem polynomial_integral (a b v d B : ℝ) :
    (∫ x in a..b, v+d*(x-(a+b)/2)+B*(x-(a+b)/2)^2/2) =
      (b-a)*v+B*(b-a)^3/24 := by
  let P := fun x : ℝ => v*x+d*(x-(a+b)/2)^2/2+B*(x-(a+b)/2)^3/6
  have hd (x : ℝ) : HasDerivAt P
      (v+d*(x-(a+b)/2)+B*(x-(a+b)/2)^2/2) x := by
    convert (((hasDerivAt_id x).const_mul v).add
      ((((hasDerivAt_id x).sub_const ((a+b)/2)).pow 2).const_mul d |>.div_const 2)).add
      ((((hasDerivAt_id x).sub_const ((a+b)/2)).pow 3).const_mul B |>.div_const 6)
      using 1 <;> first | rfl | (dsimp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous (fun x : ℝ =>
      v+d*(x-(a+b)/2)+B*(x-(a+b)/2)^2/2)).intervalIntegrable a b)]
  dsimp [P]
  ring

theorem midpoint_cell {f f' f'' : ℝ → ℝ} {a b B : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hB : ∀ x ∈ Icc a b, |f'' x| ≤ B) :
    (b-a)*f ((a+b)/2)-B*(b-a)^3/24 ≤ ∫ x in a..b, f x ∧
      (∫ x in a..b, f x) ≤ (b-a)*f ((a+b)/2)+B*(b-a)^3/24 := by
  have hm : (a+b)/2 ∈ Icc a b := by constructor <;> linarith only [hab]
  have hfi : IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hp (C : ℝ) : Continuous (fun x : ℝ =>
      f ((a+b)/2)+f' ((a+b)/2)*(x-(a+b)/2)+C*(x-(a+b)/2)^2/2) := by fun_prop
  have hlo := intervalIntegral.integral_mono_on hab ((hp (-B)).intervalIntegrable a b) hfi
    (fun x hx => by
      have h := (taylor_two_sided hm hx hf hf' hB).1
      convert h using 1
      ring)
  have hup := intervalIntegral.integral_mono_on hab hfi ((hp B).intervalIntegrable a b)
    (fun x hx => (taylor_two_sided hm hx hf hf' hB).2)
  rw [polynomial_integral] at hlo hup
  exact ⟨by linarith only [hlo],hup⟩

def point (a b : ℝ) (i : ℕ) : ℝ := a+(i : ℝ)*((b-a)/64)
def midpoint (a b : ℝ) (i : ℕ) : ℝ := (point a b i+point a b (i+1))/2
def midpointSum (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ((b-a)/64)*∑ i ∈ Finset.range 64, f (midpoint a b i)
def error (a b : ℝ) : ℝ := 2000000*(b-a)^3/(24*64^2)

theorem cell_coverage {a b : ℝ} (hab : a ≤ b) {i : ℕ} (hi : i < 64) :
    a ≤ point a b i ∧ point a b i ≤ point a b (i+1) ∧ point a b (i+1) ≤ b := by
  have hi' : (i : ℝ)+1 ≤ 64 := by exact_mod_cast (show i+1 ≤ 64 by omega)
  have hn : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  unfold point
  push_cast
  have hh : 0 ≤ (b-a)/64 := by linarith only [hab]
  constructor
  · nlinarith only [mul_nonneg hn hh]
  constructor
  · linarith only [hh]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr hi') hh]

theorem midpoint_coverage {a b : ℝ} (hab : a ≤ b) {i : ℕ} (hi : i < 64) :
    midpoint a b i ∈ Icc a b := by
  obtain ⟨h1,h2,h3⟩ := cell_coverage hab hi
  unfold midpoint
  constructor <;> linarith only [h1,h2,h3]

theorem midpoint_64 {f f' f'' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hB : ∀ x ∈ Icc a b, |f'' x| ≤ 2000000) :
    midpointSum f a b-error a b ≤ ∫ x in a..b, f x ∧
      (∫ x in a..b, f x) ≤ midpointSum f a b+error a b := by
  have hcell (i : ℕ) (hi : i < 64) :=
    cell_coverage hab hi
  have hs (i : ℕ) (hi : i < 64) : Icc (point a b i) (point a b (i+1)) ⊆ Icc a b :=
    fun x hx => ⟨(hcell i hi).1.trans hx.1,hx.2.trans (hcell i hi).2.2⟩
  have hc (i : ℕ) (hi : i < 64) := midpoint_cell (hcell i hi).2.1
    (fun x hx => hf x (hs i hi hx)) (fun x hx => hf' x (hs i hi hx))
    (fun x hx => hB x (hs i hi hx))
  have hi (i : ℕ) (him : i ∈ Finset.range 64) :
      IntervalIntegrable f volume (point a b i) (point a b (i+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hcell i (Finset.mem_range.mp him)).2.1]
    exact fun x hx => (hf x (hs i (Finset.mem_range.mp him) hx)).continuousAt.continuousWithinAt
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (fun i him => hi i (Finset.mem_range.mpr him))
  have hend0 : point a b 0 = a := by simp [point]
  have hend1 : point a b 64 = b := by norm_num [point]; ring
  rw [hend0,hend1] at hsum
  have hlo := Finset.sum_le_sum (s := Finset.range 64) (fun i hi => (hc i (Finset.mem_range.mp hi)).1)
  have hup := Finset.sum_le_sum (s := Finset.range 64) (fun i hi => (hc i (Finset.mem_range.mp hi)).2)
  have hwidth (i : ℕ) : point a b (i+1)-point a b i = (b-a)/64 := by
    unfold point
    push_cast
    ring
  simp_rw [hwidth] at hlo hup
  rw [hsum] at hlo hup
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,
    ← Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hlo hup
  change ((b-a)/64)*(∑ i ∈ Finset.range 64, f (midpoint a b i))-
    64*(2000000*((b-a)/64)^3/24) ≤ _ at hlo
  change _ ≤ ((b-a)/64)*(∑ i ∈ Finset.range 64, f (midpoint a b i))+
    64*(2000000*((b-a)/64)^3/24) at hup
  constructor
  · convert hlo using 1
    unfold midpointSum error
    ring
  · convert hup using 1
    unfold midpointSum error
    ring

theorem mass_midpoint_enclosure :
    midpointSum smallF alpha cut+midpointSum largeF cut beta-
      (error alpha cut+error cut beta) ≤ mass ∧
    mass ≤ midpointSum smallF alpha cut+midpointSum largeF cut beta+
      (error alpha cut+error cut beta) := by
  have hs := midpoint_64 geometry.2.2.2.2.2.1
    (fun _ hx => (small_derivatives hx).1)
    (fun _ hx => (small_derivatives hx).2.1)
    (fun _ hx => (small_derivatives hx).2.2)
  have hl := midpoint_64 geometry.2.2.2.2.2.2
    (fun _ hx => (large_derivatives hx).1)
    (fun _ hx => (large_derivatives hx).2.1)
    (fun _ hx => (large_derivatives hx).2.2)
  rw [mass_one_dimensional]
  dsimp only [cut]
  constructor <;> linarith only [hs.1,hs.2,hl.1,hl.2]

#check @cell_coverage
#check @mass_midpoint_enclosure
#print axioms cell_coverage
#print axioms mass_midpoint_enclosure
end WuSource.SrcFourEnclosure

import MathlibNt.Wu2008DoubleSieve.FourRoughLowCalculus

namespace Wu2008DoubleSieve.FourRoughClosedMass
open Set Real MeasureTheory LiLiuPrereqBuchstab
noncomputable section

def F (x y z t : ℝ) : ℝ := clippedDensity (cap x) (cap y) (cap z) t

theorem omega_clipped_bound (u : ℝ) : |buchstab (max 2 u)| ≤ 1 := by
  have hu : 1 ≤ max 2 u := le_trans (by norm_num) (le_max_left _ _)
  rw [abs_of_nonneg (buchstab_nonneg hu)]
  exact buchstab_le_one hu

theorem omega_clipped_lip (u v : ℝ) :
    |buchstab (max 2 u)-buchstab (max 2 v)| ≤ |u-v| := by
  apply (primeOrdered_buchstab_lipschitz
    (le_trans (by norm_num) (le_max_left _ _))
    (le_trans (by norm_num) (le_max_left _ _))).trans
  simpa only [max_comm] using abs_max_sub_max_le_abs u v 2

theorem F_bound (x y z t : ℝ) : |F x y z t| ≤ 15 := by
  have hy := (cap_low y).1
  have hy0 : 0 < cap y := fixed_geometry.2.1.trans_le (cap_mem y).1
  unfold F clippedDensity
  rw [abs_div, abs_of_pos hy0]
  apply (div_le_div_of_nonneg_right (omega_clipped_bound _) hy0.le).trans
  apply (div_le_iff₀ hy0).mpr
  linarith

theorem clippedDensity_difference {x y z t x' y' z' t' : ℝ}
    (_hx : x ∈ low) (hy : y ∈ low) (_hz : z ∈ low) (_ht : t ∈ low)
    (hx' : x' ∈ low) (hy' : y' ∈ low) (hz' : z' ∈ low) (ht' : t' ∈ low) :
    |clippedDensity x y z t-clippedDensity x' y' z' t'| ≤
      7200*(|x-x'|+|y-y'|+|z-z'|+|t-t'|) := by
  have hnum : |1-x'-y'-z'-t'| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [hx'.1,hx'.2,hy'.1,hy'.2,hz'.1,hz'.2,ht'.1,ht'.2]
  have hd : |(1-x-y-z-t)-(1-x'-y'-z'-t')| ≤
      |x-x'|+|y-y'|+|z-z'|+|t-t'| := by
    have he : (1-x-y-z-t)-(1-x'-y'-z'-t') =
        -((x-x')+(y-y')+(z-z')+(t-t')) := by ring
    rw [he,abs_neg]
    have h1 := abs_add_le (x-x') (y-y')
    have h2 := abs_add_le ((x-x')+(y-y')) (z-z')
    have h3 := abs_add_le ((x-x')+(y-y')+(z-z')) (t-t')
    linarith only [h1,h2,h3]
  have hp := quotient_low hy.1 hy'.1 hnum (x := 1-x-y-z-t)
  have ho := omega_clipped_lip (parameter x y z t) (parameter x' y' z' t')
  have hq := quotient_low hy.1 hy'.1 (omega_clipped_bound (parameter x' y' z' t'))
    (x := buchstab (max 2 (parameter x y z t)))
  change |clippedDensity x y z t-clippedDensity x' y' z' t'| ≤ _ at hq
  change |parameter x y z t-parameter x' y' z' t'| ≤ _ at hp
  nlinarith only [hd,hp,ho,hq,abs_nonneg (x-x'),abs_nonneg (y-y'),
    abs_nonneg (z-z'),abs_nonneg (t-t')]

theorem F_difference {x y z t x' y' z' t' : ℝ}
    (hx : x ∈ low) (hy : y ∈ low) (hz : z ∈ low) (ht : t ∈ low)
    (hx' : x' ∈ low) (hy' : y' ∈ low) (hz' : z' ∈ low) (ht' : t' ∈ low) :
    |F x y z t-F x' y' z' t'| ≤
      7200*(|x-x'|+|y-y'|+|z-z'|+|t-t'|) := by
  have h := clippedDensity_difference (cap_low x) (cap_low y) (cap_low z) ht
    (cap_low x') (cap_low y') (cap_low z') ht'
  have h1 := cap_lip x hx x' hx'
  have h2 := cap_lip y hy y' hy'
  have h3 := cap_lip z hz z' hz'
  change |F x y z t-F x' y' z' t'| ≤ _ at h
  linarith

theorem F_first {y z t : ℝ} (hy : y ∈ low) (hz : z ∈ low) (ht : t ∈ low) :
    lip 7200 (fun x => F x y z t) := by
  intro x hx x' hx'
  simpa only [sub_self,abs_zero,add_zero] using F_difference hx hy hz ht hx' hy hz ht

theorem F_second {x z t : ℝ} (hx : x ∈ low) (hz : z ∈ low) (ht : t ∈ low) :
    lip 7200 (fun y => F x y z t) := by
  intro y hy y' hy'
  simpa only [sub_self,abs_zero,zero_add,add_zero] using F_difference hx hy hz ht hx hy' hz ht

theorem F_third {x y t : ℝ} (hx : x ∈ low) (hy : y ∈ low) (ht : t ∈ low) :
    lip 7200 (fun z => F x y z t) := by
  intro z hz z' hz'
  simpa only [sub_self,abs_zero,zero_add,add_zero] using F_difference hx hy hz ht hx hy hz' ht

theorem F_fourth {x y z : ℝ} (hx : x ∈ low) (hy : y ∈ low) (hz : z ∈ low) :
    lip 7200 (F x y z) := by
  intro t ht t' ht'
  simpa only [sub_self,abs_zero,zero_add] using F_difference hx hy hz ht hx hy hz ht'

def lower (eleven : Bool) (z : ℝ) : ℝ := if eleven then beta else cap z
def upper (eleven : Bool) (z : ℝ) : ℝ := if eleven then lam-cap z else beta

theorem lower_low (e : Bool) (z : ℝ) : lower e z ∈ low := by
  cases e <;> simp only [lower, Bool.false_eq_true, ↓reduceIte] <;> first | exact cap_low z | exact beta_low
 theorem upper_low (e : Bool) (z : ℝ) : upper e z ∈ low := by
  cases e <;> simp only [upper, Bool.false_eq_true, ↓reduceIte] <;> first | exact top_low z | exact beta_low

theorem lower_lip (e : Bool) : lip 1 (lower e) := by
  cases e
  · exact cap_lip
  · intro x _ y _; simp [lower]
 theorem upper_lip (e : Bool) : lip 1 (upper e) := by
  cases e
  · intro x _ y _; simp [upper]
  · exact top_lip

theorem lower_le_upper (e : Bool) (z : ℝ) : lower e z ≤ upper e z := by
  cases e
  · exact (cap_mem z).2
  · change beta ≤ lam-cap z
    linarith [(cap_mem z).2,fixed_geometry.2.2.2.2.2.2.1]

def J3 (e : Bool) (x y z : ℝ) : ℝ := ∫ t in lower e z..upper e z, F x y z t/t
def J2 (e : Bool) (x y : ℝ) : ℝ := ∫ z in cap y..beta, J3 e x y z/z
def J1 (e : Bool) (x : ℝ) : ℝ := ∫ y in cap x..beta, J2 e x y/y
def J0 (e : Bool) : ℝ := ∫ x in alpha..beta, J1 e x/x

end
end Wu2008DoubleSieve.FourRoughClosedMass

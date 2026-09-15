import Wu08LargeQuadrature

noncomputable section
open Finset Set Real MeasureTheory
open scoped Classical
open Wu2008DoubleSieve FourRoughClosedMass
namespace Wu08FirstPrimeFour.SmallQuadrature

/-- Literal Wu small-first-prime weight; the outer prime measure is still 1/a. -/
def W (x : ℝ) : ℝ := (36/5)/(1-x)
def Q (N : ℕ) (e : Bool) : ℝ :=
  primeOrderedClosedSum N FourRoughClosedMass.alpha (1/10) (fun x => W x*Q1 N e x)
def I (e : Bool) : ℝ :=
  ∫ x in FourRoughClosedMass.alpha..(1/10 : ℝ), W x*J1 e x/x

theorem W_bounds {x : ℝ} (hx : x ∈ low) : 0 ≤ W x ∧ W x ≤ 11 := by
  have hp : 0 < 1-x := by linarith [hx.2]
  refine ⟨div_nonneg (by norm_num) hp.le,?_⟩
  unfold W
  apply (div_le_iff₀ hp).mpr
  linarith [hx.2]

theorem weighted_bound (e : Bool) : bounded 11000 (fun x => W x*J1 e x) := by
  intro x hx
  rw [abs_mul,abs_of_nonneg (W_bounds hx).1]
  exact (mul_le_mul (W_bounds hx).2 (J1_bound e x) (abs_nonneg _) (by norm_num)).trans (by norm_num)

theorem weighted_lip (e : Bool) : lip 60000000 (fun x => W x*J1 e x) := by
  intro x hx y hy
  have hq := quotient_low (x := J1 e x) (y := J1 e y)
    (b := 1-x) (d := 1-y) (by linarith [hx.2]) (by linarith [hy.2]) (J1_bound e y)
  have hd : |(1-x)-(1-y)|=|x-y| := by
    rw [show (1-x)-(1-y)=-(x-y) by ring,abs_neg]
  rw [hd] at hq
  have hj := J1_lip e x hx y hy
  have he : W x*J1 e x-W y*J1 e y = (36/5)*(J1 e x/(1-x)-J1 e y/(1-y)) := by
    unfold W
    ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<36/5)]
  have hh := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ)≤36/5)
  nlinarith only [hh,hj,abs_nonneg (x-y)]

/-- Closed prime endpoints are retained in the finite quadrature. The inner
three layers use the already proved uniform arithmetic quadrature, not the
old full-domain unweighted mass upper bound. -/
theorem weighted_quadrature {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ e : Bool, |Q N e-I e| < ε := by
  have hη : 0 < ε/56 := by positivity
  obtain ⟨T0,hT0,h0⟩ := windowMass_uniform
  obtain ⟨T1,_,h1⟩ := Large.inner_uniform hη
  obtain ⟨T2,_,h2⟩ := SeventhEighth.classical_low_weighted_uniform 11000 60000000 (ε/56)
    (by norm_num) (by norm_num) hη
  refine ⟨max T0 (max T1 T2),hT0.trans (le_max_left _ _),?_⟩
  intro N hN e
  have hn : 1 < N := by omega
  have hd : ∀ x ∈ low, |W x*Q1 N e x-W x*J1 e x| ≤ 11*(ε/56) := by
    intro x hx
    rw [← mul_sub,abs_mul,abs_of_nonneg (W_bounds hx).1]
    exact mul_le_mul (W_bounds hx).2 (h1 N (by omega) e x hx) (abs_nonneg _) (by norm_num)
  have hr := closed_replace hn alpha_low Large.cutoff_geometry.2 (h0 N (by omega))
    (show 0 ≤ 11*(ε/56) by positivity) hd
  have hq := h2 N (by omega) (fun x => W x*J1 e x) FourRoughClosedMass.alpha (1/10)
    (low_continuous (weighted_lip e)) (weighted_bound e) (weighted_lip e)
    alpha_low.1 Large.cutoff_geometry.1.1 Large.cutoff_geometry.2.2
  have ht := abs_sub_le (Q N e)
    (primeOrderedClosedSum N FourRoughClosedMass.alpha (1/10) (fun x => W x*J1 e x)) (I e)
  change |Q N e-primeOrderedClosedSum N FourRoughClosedMass.alpha (1/10) (fun x => W x*J1 e x)| ≤ _ at hr
  change |primeOrderedClosedSum N FourRoughClosedMass.alpha (1/10) (fun x => W x*J1 e x)-I e| < _ at hq
  linarith only [hr,hq,ht]

/-- The exact original small-domain fourfold Buchstab integral, including
36/5, the outer x*(1-x), and the inner second-coordinate square. -/
theorem integral_literal (e : Bool) :
    I e = ∫ x in FourRoughClosedMass.alpha..(1/10 : ℝ),
      (36/5)/(1-x)*(if e then regularOuter11 x else regularOuter10 x) := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le Large.cutoff_geometry.1.1] at hx
  have hx' : x ∈ Icc FourRoughClosedMass.alpha FourRoughClosedMass.beta :=
    ⟨hx.1,hx.2.trans Large.cutoff_geometry.1.2⟩
  dsimp only
  rw [← Large.outer_identification e hx']
  unfold W
  ring

#print axioms weighted_quadrature
#print axioms integral_literal
end Wu08FirstPrimeFour.SmallQuadrature

import Wu08LargeSieve
import MathlibNt.Wu2008DoubleSieve.FourRoughClassicalSharpMass

noncomputable section
open Finset Set Real MeasureTheory
open scoped Classical
open Wu2008DoubleSieve FourRoughClosedMass
namespace Wu08FirstPrimeFour.Large

def Q (N : ℕ) (e : Bool) : ℝ := primeOrderedClosedSum N (1/10) FourRoughClosedMass.beta (Q1 N e)
def I (e : Bool) : ℝ := ∫ x in (1/10 : ℝ)..FourRoughClosedMass.beta, J1 e x/x

theorem cutoff_geometry : (1/10 : ℝ) ∈ Icc FourRoughClosedMass.alpha FourRoughClosedMass.beta ∧ (1/10 : ℝ) ∈ low := by
  norm_num [FourRoughClosedMass.alpha,FourRoughClosedMass.beta,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,low]

/-- Uniform in all outer coordinates, using the existing three inner closed-prime
quadratures. No whole-domain counting theorem is subtracted. -/
theorem inner_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ e : Bool, ∀ x ∈ low,
      |Q1 N e x-J1 e x| ≤ ε := by
  let η := ε/31
  have hη : 0 < η := div_pos hε (by norm_num)
  obtain ⟨T0,hT0,h0⟩ := windowMass_uniform
  obtain ⟨T1,_,h1⟩ := SeventhEighth.classical_low_weighted_uniform 15 7200 η
    (by norm_num) (by norm_num) hη
  obtain ⟨T2,_,h2⟩ := SeventhEighth.classical_low_weighted_uniform 60 29250 η
    (by norm_num) (by norm_num) hη
  obtain ⟨T3,_,h3⟩ := SeventhEighth.classical_low_weighted_uniform 240 116100 η
    (by norm_num) (by norm_num) hη
  refine ⟨max T0 (max T1 (max T2 T3)),hT0.trans (le_max_left _ _),?_⟩
  intro N hN e x hx
  have hn : 1 < N := by omega
  have hm := h0 N (by omega)
  have hinner (y z : ℝ) (hy : y ∈ low) (hz : z ∈ low) :
      |Q3 N e x y z-J3 e x y z| ≤ η :=
    (h1 N (by omega) (F x y z) (lower e z) (upper e z)
      (low_continuous (F_fourth hx hy hz)) (fun t _ => F_bound x y z t)
      (F_fourth hx hy hz) (lower_low e z).1 (lower_le_upper e z) (upper_low e z).2).le
  have hmiddle (y : ℝ) (hy : y ∈ low) : |Q2 N e x y-J2 e x y| ≤ 6*η := by
    have hr := closed_replace hn (cap_low y) beta_low hm hη.le (fun z hz => hinner y z hy hz)
    have hq := (h2 N (by omega) (J3 e x y) (cap y) FourRoughClosedMass.beta
      (low_continuous (J3_third e hx hy)) (fun z _ => J3_bound e x y z)
      (J3_third e hx hy) (cap_low y).1 (cap_mem y).2 beta_low.2).le
    have ht := abs_sub_le (Q2 N e x y) (primeOrderedClosedSum N (cap y) FourRoughClosedMass.beta (J3 e x y)) (J2 e x y)
    change |Q2 N e x y-primeOrderedClosedSum N (cap y) FourRoughClosedMass.beta (J3 e x y)| ≤ _ at hr
    change |primeOrderedClosedSum N (cap y) FourRoughClosedMass.beta (J3 e x y)-J2 e x y| ≤ _ at hq
    linarith only [hr,hq,ht]
  have hr := closed_replace hn (cap_low x) beta_low hm (show 0 ≤ 6*η by positivity) hmiddle
  have hq := (h3 N (by omega) (J2 e x) (cap x) FourRoughClosedMass.beta
    (low_continuous (J2_second e hx)) (fun y _ => J2_bound e x y)
    (J2_second e hx) (cap_low x).1 (cap_mem x).2 beta_low.2).le
  have ht := abs_sub_le (Q1 N e x) (primeOrderedClosedSum N (cap x) FourRoughClosedMass.beta (J2 e x)) (J1 e x)
  change |Q1 N e x-primeOrderedClosedSum N (cap x) FourRoughClosedMass.beta (J2 e x)| ≤ _ at hr
  change |primeOrderedClosedSum N (cap x) FourRoughClosedMass.beta (J2 e x)-J1 e x| ≤ _ at hq
  dsimp [η] at hr hq
  linarith only [hr,hq,ht]

/-- The CLOSED partial first-prime domain has its own quadrature; hence any
integer atom at a=N^(1/10) is included and paid, never discarded as measure zero. -/
theorem partial_quadrature {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ e : Bool, |Q N e-I e| < ε := by
  have hε6 : 0 < ε/6 := by positivity
  obtain ⟨T0,hT0,h0⟩ := windowMass_uniform
  obtain ⟨T1,_,h1⟩ := inner_uniform hε6
  obtain ⟨T2,_,h2⟩ := SeventhEighth.classical_low_weighted_uniform 960 464400 (ε/6)
    (by norm_num) (by norm_num) hε6
  refine ⟨max T0 (max T1 T2),hT0.trans (le_max_left _ _),?_⟩
  intro N hN e
  have hn : 1 < N := by omega
  have hr := closed_replace hn cutoff_geometry.2 beta_low (h0 N (by omega)) hε6.le
    (h1 N (by omega) e)
  have hq := h2 N (by omega) (J1 e) (1/10) FourRoughClosedMass.beta (low_continuous (J1_lip e))
    (fun x _ => J1_bound e x) (J1_lip e) cutoff_geometry.2.1 cutoff_geometry.1.2 beta_low.2
  have ht := abs_sub_le (Q N e) (primeOrderedClosedSum N (1/10) FourRoughClosedMass.beta (J1 e)) (I e)
  change |Q N e-primeOrderedClosedSum N (1/10) FourRoughClosedMass.beta (J1 e)| ≤ _ at hr
  change |primeOrderedClosedSum N (1/10) FourRoughClosedMass.beta (J1 e)-I e| < _ at hq
  linarith only [hr,hq,ht]

/-- Pointwise identification, preserving original FourRoughClosedMass.alpha/FourRoughClosedMass.beta and fourfold kernel. -/
theorem outer_identification (e : Bool) {x : ℝ} (hx : x ∈ Icc FourRoughClosedMass.alpha FourRoughClosedMass.beta) :
    J1 e x/x = if e then regularOuter11 x else regularOuter10 x := by
  unfold J1 J2 J3
  simp_rw [← intervalIntegral.integral_div]
  rw [cap_eq hx]
  apply Eq.symm
  cases e
  · rw [if_neg (by decide),outer10_eq hx]
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp only
    rw [uIcc_of_le hx.2] at hy
    have hy' : y ∈ Icc FourRoughClosedMass.alpha FourRoughClosedMass.beta := ⟨hx.1.trans hy.1,hy.2⟩
    rw [cap_eq hy']
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp only
    rw [uIcc_of_le hy.2] at hz
    have hz' : z ∈ Icc FourRoughClosedMass.alpha FourRoughClosedMass.beta := ⟨hy'.1.trans hz.1,hz.2⟩
    simp only [lower,upper,Bool.false_eq_true,↓reduceIte,cap_eq hz']
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le hz.2] at ht
    rw [F,cap_eq hx,cap_eq hy',cap_eq hz',ten_clip_identity hx.1 hy.1 hz.1 ht.1 ht.2]
    rw [← kernel_identity]
    ring
  · rw [if_pos rfl,outer11_eq hx]
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp only
    rw [uIcc_of_le hx.2] at hy
    have hy' : y ∈ Icc FourRoughClosedMass.alpha FourRoughClosedMass.beta := ⟨hx.1.trans hy.1,hy.2⟩
    rw [cap_eq hy']
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp only
    rw [uIcc_of_le hy.2] at hz
    have hz' : z ∈ Icc FourRoughClosedMass.alpha FourRoughClosedMass.beta := ⟨hy'.1.trans hz.1,hz.2⟩
    simp only [lower,upper,↓reduceIte,cap_eq hz']
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    have hb : FourRoughClosedMass.beta ≤ lam-z := by linarith [fixed_geometry.2.2.2.2.2.2.1,hz.2]
    rw [uIcc_of_le hb] at ht
    rw [F,cap_eq hx,cap_eq hy',cap_eq hz',eleven_clip_identity hx.1 hy.1 hz.1 hz.2 ht.2]
    rw [← kernel_identity]
    ring

theorem integral_literal (e : Bool) :
    I e = ∫ x in (1/10 : ℝ)..FourRoughClosedMass.beta, if e then regularOuter11 x else regularOuter10 x := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le cutoff_geometry.1.2] at hx
  exact outer_identification e ⟨cutoff_geometry.1.1.trans hx.1,hx.2⟩

theorem integral_nonneg (e : Bool) : 0 ≤ I e := by
  rw [integral_literal]
  apply intervalIntegral.integral_nonneg cutoff_geometry.1.2
  intro x hx
  have hh : x ∈ Icc FourRoughClosedMass.alpha FourRoughClosedMass.beta := ⟨cutoff_geometry.1.1.trans hx.1,hx.2⟩
  cases e
  · exact Wu08OriginalFourWeights.outer10_nonneg hh
  · exact Wu08OriginalFourWeights.outer11_nonneg hh

#print axioms partial_quadrature
#print axioms integral_literal
end Wu08FirstPrimeFour.Large

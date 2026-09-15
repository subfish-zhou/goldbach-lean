import SrcFourDiagnostic

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass
open Wu08OriginalFourWeights

namespace WuSource.SrcFour

theorem inner_pair_merged (x y z : ℝ) :
    regularInner10 x y z+regularInner11 x y z =
      ∫ t in z..lam-z, regularKernel x y z t := by
  have hc := regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop)
  exact intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable z beta) (hc.intervalIntegrable beta (lam-z))

theorem middle_pair_merged (x y : ℝ) :
    regularMiddle10 x y+regularMiddle11 x y =
      ∫ z in y..beta, ∫ t in z..lam-z, regularKernel x y z t := by
  have h10 := (regularInner10_continuous.comp
    (f := fun z : ℝ => (x,y,z)) (by fun_prop)).intervalIntegrable (μ := volume) y beta
  have h11 := (regularInner11_continuous.comp
    (f := fun z : ℝ => (x,y,z)) (by fun_prop)).intervalIntegrable (μ := volume) y beta
  change IntervalIntegrable (fun z => regularInner10 x y z) volume y beta at h10
  change IntervalIntegrable (fun z => regularInner11 x y z) volume y beta at h11
  rw [regularMiddle10,regularMiddle11,← intervalIntegral.integral_add h10 h11]
  simp_rw [inner_pair_merged]

theorem outer_pair_merged {x : ℝ} (hx : x ∈ Icc alpha beta) :
    regularOuter10 x+regularOuter11 x =
      ∫ y in x..beta, ∫ z in y..beta, ∫ t in z..lam-z, kernel x y z t := by
  have h10 := (regularMiddle10_continuous.comp
    (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable (μ := volume) x beta
  have h11 := (regularMiddle11_continuous.comp
    (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable (μ := volume) x beta
  change IntervalIntegrable (fun y => regularMiddle10 x y) volume x beta at h10
  change IntervalIntegrable (fun y => regularMiddle11 x y) volume x beta at h11
  rw [regularOuter10,regularOuter11,← intervalIntegral.integral_add h10 h11]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hx.2] at hy
  dsimp only
  rw [middle_pair_merged]
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hy.2] at hz
  apply intervalIntegral.integral_congr
  intro t ht
  have hzlam : z ≤ lam-z := by linarith only [hz.2,geometry.2.2.2.2.2]
  rw [uIcc_of_le hzlam] at ht
  by_cases htb : t ≤ beta
  · exact kernel_source_ten ⟨hx.1,hy.1,hz.1,ht.1,htb⟩
  · exact kernel_source_eleven ⟨hx.1,hy.1,hz.1,hz.2,(lt_of_not_ge htb).le,ht.2⟩

theorem original_pair_source :
    original10+original11 =
      (36/5)*(∫ x in alpha..(1/10 : ℝ),
        (∫ y in x..beta, ∫ z in y..beta, ∫ t in z..lam-z,
          LiLiuPrereqBuchstab.buchstab ((1-x-y-z-t)/y)/(x*y^2*z*t))/(1-x))+
      8*(∫ x in (1/10 : ℝ)..beta,
        ∫ y in x..beta, ∫ z in y..beta, ∫ t in z..lam-z,
          LiLiuPrereqBuchstab.buchstab ((1-x-y-z-t)/y)/(x*y^2*z*t)) := by
  have hsmall := geometry.1.le
  have hlarge := geometry.2.1.le.trans geometry.2.2.1.le
  have hs10 := weighted_integrable regularOuter10_continuous
  have hs11 := weighted_integrable regularOuter11_continuous
  have hl10 := regularOuter10_continuous.intervalIntegrable (μ := volume) (1/10 : ℝ) beta
  have hl11 := regularOuter11_continuous.intervalIntegrable (μ := volume) (1/10 : ℝ) beta
  have hs : (∫ x in alpha..(1/10 : ℝ), regularOuter10 x/(1-x))+
      (∫ x in alpha..(1/10 : ℝ), regularOuter11 x/(1-x)) =
      ∫ x in alpha..(1/10 : ℝ),
        (∫ y in x..beta, ∫ z in y..beta, ∫ t in z..lam-z, kernel x y z t)/(1-x) := by
    rw [← intervalIntegral.integral_add hs10 hs11]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hsmall] at hx
    dsimp only
    rw [← add_div,outer_pair_merged ⟨hx.1,hx.2.trans hlarge⟩]
  have hl : (∫ x in (1/10 : ℝ)..beta, regularOuter10 x)+
      (∫ x in (1/10 : ℝ)..beta, regularOuter11 x) =
      ∫ x in (1/10 : ℝ)..beta,
        ∫ y in x..beta, ∫ z in y..beta, ∫ t in z..lam-z, kernel x y z t := by
    rw [← intervalIntegral.integral_add hl10 hl11]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hlarge] at hx
    exact outer_pair_merged ⟨hsmall.trans hx.1,hx.2⟩
  unfold kernel parameter at hs hl
  unfold original10 original11 original
  linarith only [hs,hl]

theorem actual_pair_fineCap {c σ : ℝ} (hc0 : 0 ≤ c) (hc4 : c ≤ (4/7 : ℝ))
    (hc : ∀ u : ℝ, (17/5 : ℝ) ≤ u → LiLiuPrereqBuchstab.buchstab u ≤ c)
    (hσ : 0 < σ) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
        (fineCap c+σ)*U8CanonicalMother.M N := by
  obtain ⟨T,_,hN⟩ := Wu08FourMother.original_pair_paid hσ
  refine ⟨max T 512,by omega,fun N hn he => ?_⟩
  have hp := hN N (by omega) he
  rw [Wu08FourMother.originalIntegral_false,Wu08FourMother.originalIntegral_true] at hp
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (by omega)).le
  exact hp.trans (mul_le_mul_of_nonneg_right
    (add_le_add (original_pair_fineCap hc0 hc4 hc) (le_refl σ)) hM)

def replacementCoefficient (c : ℝ) : ℝ :=
  Wu08FourMother.Qoriginal+(original10+original11-fineCap c)/4

theorem replacementCoefficient_exact (c : ℝ) :
    replacementCoefficient c =
      (3*Wu08TerminalAlignment.firstMain+Wu08TerminalAlignment.secondMain-
        Wu08TerminalAlignment.thirdMain-Wu08TerminalAlignment.fourthMain+
        Wu08TerminalAlignment.fifthMain+Wu08TerminalAlignment.sixthMain-
        2*Wu08TerminalAlignment.seventhMain-Wu08TerminalAlignment.eighthMain-
        Wu08TerminalAlignment.ninthMain-fineCap c+
        8*PositiveSecondPayment.secondGain+PositiveCoreResume.fifthGain+
        FeedbackLimit.Cinf+4*Phase20.rawPsi+4*Phase18.g18)/4 := by
  unfold replacementCoefficient Wu08FourMother.Qoriginal
  ring

theorem ordinary_P2_conditional {c ζ dmax : ℝ}
    (hc0 : 0 ≤ c) (hc4 : c ≤ (4/7 : ℝ))
    (hc : ∀ u : ℝ, (17/5 : ℝ) ≤ u → LiLiuPrereqBuchstab.buchstab u ≤ c)
    (hζ : 0 < ζ) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (replacementCoefficient c-ζ)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  have hcoef : replacementCoefficient c ≤ Wu08FourMother.Qoriginal := by
    unfold replacementCoefficient
    linarith only [original_pair_fineCap hc0 hc4 hc]
  obtain ⟨_,_,_,hp⟩ := Wu08FourMother.ordinary_P2_parameters hζ
    (show (0 : ℝ) < 1/2 by norm_num)
  obtain ⟨δ,_,_,_,hδ,hδmax,hδhi,_,_,_,_,_,_,_,h⟩ := hp dmax hdmax
  obtain ⟨T,hT,hN⟩ := h 3
  refine ⟨δ,hδ,hδmax,hδhi,T,hT,fun N hn he => ?_⟩
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hn)).le
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hcoef ζ) hM).trans (hN N hn he).2

#check @original_pair_source
#check @actual_pair_fineCap
#check @replacementCoefficient_exact
#check @ordinary_P2_conditional
#print axioms original_pair_source
#print axioms actual_pair_fineCap
#print axioms replacementCoefficient_exact
#print axioms ordinary_P2_conditional
end WuSource.SrcFour

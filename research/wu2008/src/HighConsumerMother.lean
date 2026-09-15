import HighConsumerPacking
import HighConsumerProfile
import Wu08FourMotherTerminal

namespace HighConsumer
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open PositiveTwoPayment PositiveCoreResume PositiveSecondPayment
open scoped Classical
noncomputable section

/-- Only literal finite geometry, no analytic or count hypothesis. -/
def PackingGeometry (N : ℕ) (δ Δ : ℝ) (I J : Finset ℕ)
    (x y s X Y t : ℕ → ℝ) (G : Finset ℝ) : Prop :=
  (∀ i ∈ I, truncatedSixthLowerAdmissibleRegion δ (x i) (y i)) ∧
  (∀ i ∈ I, (N : ℝ)^truncatedSixthLowerAlpha ≤ (N : ℝ)^(x i)/Δ) ∧
  (∀ i ∈ I, (N : ℝ)^truncatedSixthLowerBeta ≤ (N : ℝ)^(y i)/Δ) ∧
  (∀ i ∈ I, s i ∈ G ∧ s i ≤ truncatedSixthLowerS δ (x i) (y i)) ∧
  (Set.PairwiseDisjoint (I : Set ℕ) (fun i => truncatedSixthLowerBoxPairs N Δ (x i) (y i))) ∧
  (∀ j ∈ J, truncatedSixthLowerRegion δ (X j) (Y j) ∧ 1/4 < Y j) ∧
  (∀ j ∈ J, (N : ℝ)^truncatedSixthLowerAlpha ≤ (N : ℝ)^(X j)/Δ) ∧
  (∀ j ∈ J, (N : ℝ)^(1/4 : ℝ) ≤ (N : ℝ)^(Y j)/Δ) ∧
  (∀ j ∈ J, 2 ≤ t j ∧ t j ≤ 29/10 ∧ t j ≤ truncatedSixthLowerS δ (X j) (Y j)) ∧
  (Set.PairwiseDisjoint (J : Set ℕ) (fun j => truncatedSixthLowerBoxPairs N Δ (X j) (Y j)))

/-- A value in the original sixth slot, with its classical complement removed first. -/
def mixedMain (N : ℕ) (δ Δ η : ℝ) (I J : Finset ℕ) (x y s X Y t : ℕ → ℝ) : ℝ :=
  let L := I.biUnion (fun i => truncatedSixthLowerBoxPairs N Δ (x i) (y i))
  let H := J.biUnion (fun j => truncatedSixthLowerBoxPairs N Δ (X j) (Y j))
  truncatedSixthLowerNormalizedMain N δ η (truncatedSixthLowerPairs N δ \ (L ∪ H)) +
    (∑ i ∈ I, (wuLowerCoefficient (s i)+wuImprovementLimit false δ (s i)-η)*
      boxTheta N ((N : ℝ)^(1/2-δ))
        (convolutionWuWindows N Δ ![(N : ℝ)^(y i),(N : ℝ)^(x i)])) +
    (∑ j ∈ J, (log (t j-1)+(1/10000)*log (2/(t j-1))-η)*
      boxTheta N ((N : ℝ)^(1/2-δ))
        (convolutionWuWindows N Δ ![(N : ℝ)^(X j),(N : ℝ)^(Y j)]))

theorem mixed_count {δ η ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta)
    (hd : δ < 1/100) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε)
    (G : Finset ℝ) (hG : ∀ s ∈ G, 2 ≤ s ∧ s ≤ 5) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ (I J : Finset ℕ) (x y s X Y t : ℕ → ℝ),
      PackingGeometry N δ Δ I J x y s X Y t G →
      mixedMain N δ Δ η I J x y s X Y t - ε*U8CanonicalMother.M N ≤ SixthSlotCore.sixth N := by
  obtain ⟨T,hT,hcount⟩ := mixed_packing_actual hδ hδhi hd hη hηhi hε G hG
  refine ⟨T,hT,?_⟩
  intro N hN he Δ hlo hhi I J x y s X Y t hg
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := hg
  simpa only [mixedMain,U8CanonicalMother.M,SixthSlotCore.sixth,mul_div_assoc,mul_assoc] using
    hcount N hN he Δ hlo hhi I J x y s X Y t h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

/-- Same signed mother, not addition of two independent total count estimates.
The original restored F10/F11 debit is used once via ordinary_rebuilt. -/
theorem signed_mixed {δ η ε σ : ℝ} (pair : Wu08FourMother.PairUpper σ)
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hd : δ < 1/100)
    (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε)
    (G : Finset ℝ) (hG : ∀ s ∈ G, 2 ≤ s ∧ s ≤ 5) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ (I J : Finset ℕ) (x y s X Y t : ℕ → ℝ),
      PackingGeometry N δ Δ I J x y s X Y t G →
      (FullLogMother.psiCoefficient δ-truncatedSixthLowerF6lin-FullSourceLog.GammaLog6+
        increment secondGain fifthGain+Wu08FourMother.restoredDebit+8*U8CanonicalMother.L-
        8*U8CanonicalMother.I-σ-ε)*U8CanonicalMother.M N+
        mixedMain N δ Δ η I J x y s X Y t ≤
      4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have heps : 0 < ε/3 := by positivity
  obtain ⟨Tr,_,hr⟩ := Wu08FourMother.ordinary_rebuilt pair hδ hd.le heps
  obtain ⟨T6,_,h6⟩ := mixed_count hδ hδhi hd hη hηhi heps G hG
  obtain ⟨Ts,hs⟩ := OriginalU8.Weighted.physicalSmall_original_integral (ε/3) heps
  refine ⟨max 512 (max Tr (max T6 Ts)),le_max_left _ _,?_⟩
  intro N hN he Δ hlo hhi I J x y s X Y t hg
  have hrN := hr N (by omega) he
  have h6N := h6 N (by omega) he Δ hlo hhi I J x y s X Y t hg
  have hsN := hs N (by omega) he
  have hnorm := U8CanonicalMother.scale_eq_liu (show 0 < N by omega)
  rw [← U8CanonicalMother.small_eq_physicalSmall] at hsN
  have hsM : ((U8MotherInsertion.small N).card : ℝ) ≤
      (8*U8CanonicalMother.I+ε/3)*U8CanonicalMother.M N := by
    rw [hnorm]
    convert hsN using 1
    ring
  unfold SixthSlotCore.remainderCoefficient at hrN
  rw [← U8CanonicalMother.L_eq_oldSmallIntegral] at hrN
  dsimp [U8CanonicalMother.M] at hsM h6N ⊢
  ring_nf at hrN h6N hsM ⊢
  linarith only [hrN,h6N,hsM]

/-- Original Qoriginal consumer with a displayed mixed-sixth excess. Its sign
is NOT asserted: the missing normalization is precisely the sign of this excess.
All original Q10/Q11, classical and small errors are paid at the same delta. -/
theorem ordinary_P2_mixed_excess {ζ dmax η : ℝ} (hζ : 0 < ζ) (hdmax : 0 < dmax)
    (hη : 0 < η) (hηhi : η ≤ 1)
    (G : Finset ℝ) (hG : ∀ s ∈ G, 2 ≤ s ∧ s ≤ 5) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ < 1/100 ∧ δ ≤ 50*highEta ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ (I J : Finset ℕ) (x y s X Y t : ℕ → ℝ),
      PackingGeometry N δ Δ I J x y s X Y t G →
      (Wu08FourMother.Qoriginal-ζ)*U8CanonicalMother.M N+
        (mixedMain N δ Δ η I J x y s X Y t-
          (truncatedSixthLowerF6lin+FeedbackLimit.Cinf)*U8CanonicalMother.M N)/4 ≤
      ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
        ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨a,ha,ha1,hcoef⟩ := Wu08FourMother.coefficient_cap hζ
  obtain ⟨ξ,_,_,hpair⟩ := Wu08FirstPrimeFour.SmallBoundaryRecovery.original_pair_integral_parameters
    (half_pos hζ) (show (0 : ℝ) < 1/2 by norm_num)
  let cap := min dmax (min a (min (1/100) (50*highEta)))
  have hcap : 0 < cap := by
    dsimp [cap]
    exact lt_min hdmax (lt_min ha (lt_min (by norm_num) (by norm_num [highEta])))
  obtain ⟨δ,_,_,_,hδ,hδcap,_,_,_,_,_,_,_,_,hraw⟩ := hpair cap hcap
  have hdmax' : δ < dmax := hδcap.trans_le (min_le_left _ _)
  have hda : δ < a := hδcap.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hd : δ < 1/100 := hδcap.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdhi : δ ≤ 50*highEta := hδcap.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have pair : Wu08FourMother.PairUpper ζ := by
    obtain ⟨Tq,_,hq⟩ := hraw 3
    obtain ⟨Tr,_,hr⟩ := Wu08FourMother.raw_error_paid (half_pos hζ)
    obtain ⟨Tn,hTn⟩ := exists_nat_ge Tq
    refine ⟨max 4 (max Tn Tr),le_max_left _ _,?_⟩
    intro N hN he
    have hqN := hq N (hTn.trans (by exact_mod_cast (show Tn ≤ N by omega))) he
    have hrN := hr N (by omega)
    change _ ≤ _*U8CanonicalMother.M N+_ at hqN
    linarith only [hqN,hrN]
  obtain ⟨T,hT,hcount⟩ := signed_mixed pair hδ hdhi hd hη hηhi hζ G hG
  refine ⟨δ,hδ,hdmax',hd,hdhi,T,hT,?_⟩
  intro N hN he Δ hlo hhi I J x y s X Y t hg
  have hc := hcount N hN he Δ hlo hhi I J x y s X Y t hg
  have hco := hcoef δ hδ hda
  have hM := (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  change 0 ≤ U8CanonicalMother.M N at hM
  have hscaled := mul_le_mul_of_nonneg_right hco hM
  change _ ≤ 4*((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
    ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) at hc
  nlinarith only [hc,hscaled,mul_nonneg hζ.le hM]

end
end HighConsumer

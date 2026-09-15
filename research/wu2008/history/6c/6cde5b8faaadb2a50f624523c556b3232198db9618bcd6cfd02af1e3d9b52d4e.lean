import WE10FourMajorWeighted

noncomputable section
open Wu2008DoubleSieve Wu08OriginalFourWeights

namespace WuTarget.E10FourMajor

def replacementCap : ℝ := 7/10
def additionalCredit : ℝ := (E10Four.pairUpper-replacementCap)/4
def totalCredit : ℝ := (W13Tight.pairUpper-replacementCap)/4
def paidCoefficient : ℝ := W17Accepted.paidCoefficient+totalCredit
def remainingCoefficient : ℝ := W17Accepted.remainingCoefficient+totalCredit

theorem replacement_upper : original10+original11 ≤ replacementCap :=
  original_pair_target

theorem replacement_strict : replacementCap < E10Four.pairUpper := by
  rw [E10Four.pairUpper_exact]
  norm_num [replacementCap]

theorem additionalCredit_lower : (29/800 : ℝ) < additionalCredit := by
  rw [additionalCredit,E10Four.pairUpper_exact]
  norm_num [replacementCap]

theorem totalCredit_lower : (33/800 : ℝ) < totalCredit := by
  rw [totalCredit,W13Tight.pairUpper_exact]
  norm_num [replacementCap]

theorem totalCredit_exact : totalCredit =
    ((26875435940533312228039000328979770798335983204226556846125448310403759489773059933399307753781372028836762611769214239837171110424285006609 /
      31056238955554783684880132090014895082157336063748158774085392966780320600050047236645407782538827346182611039854112280896035211618041856000 : ℝ)-7/10)/4 := by
  rw [totalCredit,W13Tight.pairUpper_exact]
  rfl

theorem additionalCredit_exact : additionalCredit =
    ((32552230430458819268289158270894402654410226271007019884390475629642237676592004617874043735224181764042923177847589487077698213913170752237424478098075669859 /
      38505392819428692512922483799422960816618117515019303921651960295130914202588378001961674290472294401853213957276913114180362448664319597957947312050323456000 : ℝ)-7/10)/4 := by
  rw [additionalCredit,E10Four.pairUpper_exact]
  rfl

theorem no_double_payment : totalCredit = E10Four.netCredit+additionalCredit := by
  unfold totalCredit additionalCredit E10Four.pairUpper E10Four.netCredit
  ring

theorem paid_relative_first :
    paidCoefficient = E10Four.paidCoefficient+additionalCredit := by
  unfold paidCoefficient E10Four.paidCoefficient
  rw [no_double_payment]
  ring

theorem paid_gain_identity :
    paidCoefficient-E10Four.paidCoefficient =
      (E10Four.pairUpper-replacementCap)/4 := by
  rw [paid_relative_first]
  unfold additionalCredit
  ring

theorem paid_gain :
    E10Four.paidCoefficient+29/800 < paidCoefficient := by
  rw [paid_relative_first]
  linarith only [additionalCredit_lower]

theorem paid_exact : paidCoefficient =
    W11CreditAccepted.paidCoefficient+(original10+original11-replacementCap)/4+
      W17Accepted.jointCredit := by
  unfold paidCoefficient W17Accepted.paidCoefficient totalCredit
  rw [W13TightAccepted.paid_exact]
  ring

theorem paid_lt_actual :
    paidCoefficient < W01.ordinaryCoefficient W17Accepted.enhanced := by
  have hnew :
      W11CreditAccepted.paidCoefficient+(original10+original11-replacementCap)/4 ≤
        W11CreditAccepted.paidCoefficient := by
    linarith only [replacement_upper]
  have h := hnew.trans_lt W11CreditAccepted.paid_lt_actual
  rw [paid_exact]
  unfold W17Accepted.jointCredit
  linarith only [h]

theorem actual_pair_upper {σ : ℝ} (hσ : 0 < σ) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
        (replacementCap+σ)*U8CanonicalMother.M N := by
  obtain ⟨T,_,hN⟩ := Wu08FourMother.original_pair_paid hσ
  refine ⟨max T 512,by omega,fun N hn he => ?_⟩
  have hp := hN N (by omega) he
  rw [Wu08FourMother.originalIntegral_false,Wu08FourMother.originalIntegral_true] at hp
  have hm0 : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (by omega)).le
  exact hp.trans (mul_le_mul_of_nonneg_right
    (add_le_add replacement_upper (le_refl σ)) hm0)

theorem ordinary_P2_paid {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (paidCoefficient-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hd,hm,hs,_,_,T,hT,hc⟩ := W17Accepted.enhanced_ordinary_P2 hε hdmax
  refine ⟨δ,hd,hm,hs,T,hT,?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right paid_lt_actual.le ε) hM).trans
    (hc N hN he)

theorem paid_threshold_iff : (4491/5000 : ℝ) ≤ paidCoefficient ↔
    (840977/800000 : ℝ) ≤ remainingCoefficient := by
  unfold paidCoefficient remainingCoefficient W17Accepted.paidCoefficient
    W17Accepted.remainingCoefficient W13TightAccepted.paidCoefficient
  constructor <;> intro h <;> linarith only [h]

end WuTarget.E10FourMajor

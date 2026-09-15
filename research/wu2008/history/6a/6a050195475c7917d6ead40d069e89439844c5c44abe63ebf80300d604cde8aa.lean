import SrcSixthGainAnalyticBoundary
import BuchstabCountFinal

noncomputable section
namespace WuSource.SrcSixthGain.Analytic
open Real Finset Wu2008DoubleSieve HighBoxRecovery
open scoped Classical

def paidHigh (s : ℝ) : ℝ := (1/10000)*log (2/(s-1))

def hRemainder (delta s : ℝ) : ℝ :=
  max 0 (wuImprovementLimit false delta s-paidHigh s)

theorem retained_h_exact (delta s : ℝ) :
    wuImprovementLimit false delta s-hRemainder delta s =
      min (wuImprovementLimit false delta s) (paidHigh s) := by
  unfold hRemainder
  by_cases h : wuImprovementLimit false delta s ≤ paidHigh s
  · rw [max_eq_left (sub_nonpos.mpr h),min_eq_left h,sub_zero]
  · rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge h)),min_eq_right (le_of_not_ge h)]
    ring

theorem retained_h_le_paid (delta s : ℝ) :
    wuImprovementLimit false delta s-hRemainder delta s ≤ paidHigh s := by
  rw [retained_h_exact]
  exact min_le_right _ _

theorem remainder_nonneg (delta s : ℝ) : 0 ≤ hRemainder delta s := le_max_left _ _

theorem retained_h_nonneg {delta s : ℝ} (hd : 0 < delta) (hdhi : delta < 1/2)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) :
    0 ≤ wuImprovementLimit false delta s-hRemainder delta s := by
  rw [retained_h_exact]
  apply le_min (wuImprovementLimit_nonneg false hd hdhi (by linarith) (by linarith))
  unfold paidHigh
  apply mul_nonneg (by norm_num)
  apply log_nonneg
  exact (le_div_iff₀ (by linarith : 0 < s-1)).mpr (by linarith)

theorem remainder_zero_iff (delta s : ℝ) :
    hRemainder delta s = 0 ↔ wuImprovementLimit false delta s ≤ paidHigh s := by
  unfold hRemainder
  constructor
  · intro h
    have hm := le_max_right (0 : ℝ) (wuImprovementLimit false delta s-paidHigh s)
    rw [h] at hm
    linarith
  · intro h
    exact max_eq_left (sub_nonpos.mpr h)

theorem high_original_h_closed {delta eps : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 50*highEta) (heps : 0 < eps) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Delta : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Delta →
      Delta < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) →
      OriginalRectangles N V →
      ∀ s : ℝ, 2 ≤ s → s ≤ 29/10 →
      0 < boxTheta N ((N : ℝ)^(1/2-delta)) (convolutionWuWindows N Delta V) ∧
      (wuLowerCoefficient s+wuImprovementLimit false delta s-hRemainder delta s-eps)*
        boxTheta N ((N : ℝ)^(1/2-delta)) (convolutionWuWindows N Delta V) ≤
        wuBoxPhiLE N delta (convolutionWuWindows N Delta V) s := by
  obtain ⟨T,hT,hc⟩ := HighConsumer.original_closed_lower hd hdhi heps
  refine ⟨T,hT,?_⟩
  intro N hN he Delta hlo hhi V hV hrect s hs hsmax
  obtain ⟨hTheta,hphi⟩ := hc N hN he Delta hlo hhi V hV hrect s hs hsmax
  have ha : wuLowerCoefficient s = log (s-1) :=
    WuTarget.Wu08FifthSource.coefficient_initial hs (by linarith)
  refine ⟨hTheta,?_⟩
  have hcoef : wuLowerCoefficient s+wuImprovementLimit false delta s-
      hRemainder delta s-eps ≤ log (s-1)+paidHigh s-eps := by
    rw [ha]
    linarith only [retained_h_le_paid delta s]
  exact (mul_le_mul_of_nonneg_right hcoef hTheta.le).trans hphi

theorem high_original_h_actual_box {delta eps : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 50*highEta) (heps : 0 < eps) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Delta x y : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Delta →
      Delta < 1+2*log (N : ℝ)^(-4 : ℝ) →
      truncatedSixthLowerRegion delta x y → 1/4 < y →
      (N : ℝ)^truncatedSixthLowerAlpha ≤ (N : ℝ)^x/Delta →
      (N : ℝ)^truncatedSixthLowerAlpha ≤ (N : ℝ)^y/Delta →
      ∀ s : ℝ, 2 ≤ s → s ≤ 29/10 → s ≤ truncatedSixthLowerS delta x y →
      (wuLowerCoefficient s+wuImprovementLimit false delta s-hRemainder delta s-eps)*
        boxTheta N ((N : ℝ)^(1/2-delta))
          (convolutionWuWindows N Delta ![(N : ℝ)^x,(N : ℝ)^y]) ≤
      ∑ b ∈ truncatedSixthLowerBoxPairs N Delta x y,
        (sieveCount N (b.1*b.2) N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨T,hT,hc⟩ := high_original_h_closed hd hdhi heps
  refine ⟨T,hT,?_⟩
  intro N hN he Delta x y hlo hhi hr hy hp hq s hs hsmax hsource
  have hN1 : 1 < N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1.le
  have hV : ∀ j : Fin 2, (N : ℝ)^(100/1327 : ℝ) ≤ ![(N : ℝ)^x,(N : ℝ)^y] j := by
    intro j
    fin_cases j
    · exact rpow_le_rpow_of_exponent_le hNR hr.1
    · exact rpow_le_rpow_of_exponent_le hNR
        (truncatedSixthLower_parameters.2.1.le.trans hr.2.2.1)
  have hl := (hc N hN he Delta hlo hhi _ hV
    (HighConsumer.high_original_rectangles hN1 hd.le hr hy) s hs hsmax).2
  have hswap : s ≤ truncatedSixthLowerS delta y x := by
    convert hsource using 1
    unfold truncatedSixthLowerS
    congr 1
    ring
  exact hl.trans ((wuBoxPhiLE_le_strict N delta _ s).trans
    (truncatedSixthLower_box_phi_le hN1 (by linarith) hq hp hswap))

def originalHMain (N : ℕ) (delta Delta eta : ℝ) (I J : Finset ℕ)
    (x y s X Y t : ℕ → ℝ) : ℝ :=
  let L := I.biUnion (fun i => truncatedSixthLowerBoxPairs N Delta (x i) (y i))
  let H := J.biUnion (fun j => truncatedSixthLowerBoxPairs N Delta (X j) (Y j))
  truncatedSixthLowerNormalizedMain N delta eta (truncatedSixthLowerPairs N delta \ (L ∪ H)) +
    (∑ i ∈ I, (wuLowerCoefficient (s i)+wuImprovementLimit false delta (s i)-eta)*
      boxTheta N ((N : ℝ)^(1/2-delta))
        (convolutionWuWindows N Delta ![(N : ℝ)^(y i),(N : ℝ)^(x i)])) +
    (∑ j ∈ J, (wuLowerCoefficient (t j)+wuImprovementLimit false delta (t j)-eta)*
      boxTheta N ((N : ℝ)^(1/2-delta))
        (convolutionWuWindows N Delta ![(N : ℝ)^(X j),(N : ℝ)^(Y j)]))

def packedRemainder (N : ℕ) (delta Delta : ℝ) (J : Finset ℕ)
    (X Y t : ℕ → ℝ) : ℝ :=
  ∑ j ∈ J, hRemainder delta (t j)*
    boxTheta N ((N : ℝ)^(1/2-delta))
      (convolutionWuWindows N Delta ![(N : ℝ)^(X j),(N : ℝ)^(Y j)])

theorem mixed_original_h_with_remainder {delta eta eps : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 50*highEta) (hdsmall : delta < 1/100)
    (heta : 0 < eta) (hetahi : eta ≤ 1) (heps : 0 < eps)
    (G : Finset ℝ) (hG : ∀ s ∈ G, 2 ≤ s ∧ s ≤ 5) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Delta : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Delta →
      Delta < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ (I J : Finset ℕ) (x y s X Y t : ℕ → ℝ),
      HighConsumer.PackingGeometry N delta Delta I J x y s X Y t G →
      0 ≤ packedRemainder N delta Delta J X Y t ∧
      originalHMain N delta Delta eta I J x y s X Y t -
        packedRemainder N delta Delta J X Y t - eps*U8CanonicalMother.M N ≤
          SixthSlotCore.sixth N := by
  obtain ⟨T0,hT0,hc⟩ := HighConsumer.mixed_count hd hdhi hdsmall heta hetahi heps G hG
  obtain ⟨T1,_,hpos⟩ := HighConsumer.original_closed_lower hd hdhi heta
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN he Delta hlo hhi I J x y s X Y t hg
  have hN1 : 1 < N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1.le
  obtain ⟨_,_,_,_,_,hh,_,_,ht,_⟩ := hg
  have hTheta (j : ℕ) (hj : j ∈ J) :
      0 ≤ boxTheta N ((N : ℝ)^(1/2-delta))
        (convolutionWuWindows N Delta ![(N : ℝ)^(X j),(N : ℝ)^(Y j)]) := by
    have hV : ∀ k : Fin 2,
        (N : ℝ)^(100/1327 : ℝ) ≤ ![(N : ℝ)^(X j),(N : ℝ)^(Y j)] k := by
      intro k
      fin_cases k
      · exact rpow_le_rpow_of_exponent_le hNR (hh j hj).1.1
      · exact rpow_le_rpow_of_exponent_le hNR
          (truncatedSixthLower_parameters.2.1.le.trans (hh j hj).1.2.2.1)
    exact (hpos N (by omega) he Delta hlo hhi _ hV
      (HighConsumer.high_original_rectangles hN1 hd.le (hh j hj).1 (hh j hj).2)
      (t j) (ht j hj).1 (ht j hj).2.1).1.le
  refine ⟨Finset.sum_nonneg (fun j hj => mul_nonneg (remainder_nonneg delta (t j)) (hTheta j hj)),?_⟩
  have hsum :
      (∑ j ∈ J, (wuLowerCoefficient (t j)+wuImprovementLimit false delta (t j)-eta)*
        boxTheta N ((N : ℝ)^(1/2-delta))
          (convolutionWuWindows N Delta ![(N : ℝ)^(X j),(N : ℝ)^(Y j)])) -
      packedRemainder N delta Delta J X Y t ≤
      ∑ j ∈ J, (log (t j-1)+paidHigh (t j)-eta)*
        boxTheta N ((N : ℝ)^(1/2-delta))
          (convolutionWuWindows N Delta ![(N : ℝ)^(X j),(N : ℝ)^(Y j)]) := by
    rw [packedRemainder,← sum_sub_distrib]
    apply sum_le_sum
    intro j hj
    have ha := WuTarget.Wu08FifthSource.coefficient_initial (ht j hj).1
      (show t j ≤ 4 by linarith [(ht j hj).2.1])
    have hcoef : wuLowerCoefficient (t j)+wuImprovementLimit false delta (t j)-eta-
        hRemainder delta (t j) ≤ log (t j-1)+paidHigh (t j)-eta := by
      rw [ha]
      linarith only [retained_h_le_paid delta (t j)]
    simpa only [sub_mul] using mul_le_mul_of_nonneg_right hcoef (hTheta j hj)
  have hcN := hc N (by omega) he Delta hlo hhi I J x y s X Y t hg
  unfold originalHMain
  unfold HighConsumer.mixedMain at hcN
  change _ ≤ _ at hsum
  unfold paidHigh at hsum
  linarith only [hsum,hcN]

def occupiedTail (N r : ℕ) (delta Delta s : ℝ) (V : Fin 2 → ℝ) : ℝ :=
  ∑ j ∈ InsertedGain.occupiedCells N delta Delta V s r,
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Delta V),
      (convolutionCoeff (convolutionWuWindows N Delta V) d : ℝ) *
      ∑ p ∈ primeWindow (d*N) (wuLocalCutoff N delta d 3) (wuLocalCutoff N delta d s) ∩
        HighOmega2.cell N ((N : ℝ)^(1/2-delta)/(∏ l, V l)) Delta 3 j,
        (sourceSieveCount N (d*p) (d*p*N) (p : ℝ) : ℝ)

theorem exact_buchstab_h_gap {N r : ℕ} {delta Delta s : ℝ} {V : Fin 2 → ℝ}
    (hN : 0 < N) (hDelta : 1 < Delta) (hV : ∀ j, 0 < V j)
    (hQ : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Delta V),
      1 ≤ (N : ℝ)^(1/2-delta)/d)
    (hs : 2 ≤ s) (hs3 : s ≤ 3)
    (hr : ((N : ℝ)^(1/2-delta)/(∏ l, V l))^(1/s) <
      reboxingAlpha ((N : ℝ)^(1/2-delta)/(∏ l, V l)) Delta 3 (r+1)) :
    (wuLowerCoefficient s+wuImprovementLimit false delta s)*
        boxTheta N ((N : ℝ)^(1/2-delta)) (convolutionWuWindows N Delta V) -
        wuBoxPhi N delta (convolutionWuWindows N Delta V) s =
      (log (s-1)+wuImprovementLimit false delta s-log 2)*
        boxTheta N ((N : ℝ)^(1/2-delta)) (convolutionWuWindows N Delta V) +
        occupiedTail N r delta Delta s V -
        (wuBoxPhi N delta (convolutionWuWindows N Delta V) 3-
          log 2*boxTheta N ((N : ℝ)^(1/2-delta)) (convolutionWuWindows N Delta V)) := by
  have h := BuchstabCount.buchstab_occupied_exact hN hDelta hV hQ hs hs3 hr
  change wuBoxPhi N delta (convolutionWuWindows N Delta V) 3 =
    wuBoxPhi N delta (convolutionWuWindows N Delta V) s + occupiedTail N r delta Delta s V at h
  rw [WuTarget.Wu08FifthSource.coefficient_initial hs (by linarith)]
  linarith only [h]

#print axioms high_original_h_closed
#print axioms high_original_h_actual_box
#print axioms mixed_original_h_with_remainder
#print axioms exact_buchstab_h_gap
end WuSource.SrcSixthGain.Analytic

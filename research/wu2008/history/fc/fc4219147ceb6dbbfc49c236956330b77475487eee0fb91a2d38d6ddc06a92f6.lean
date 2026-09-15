import W04AcceptedCount

namespace WuTarget.ParentScalarCount
open Wu2008DoubleSieve ActualNineFeedback NodeExtension

/-- Consume a scalar minorant of the same finite-vector signed coefficient. -/
theorem from_finite_vector {x : Fin 9 → ℝ} {q d0 ε dmax : ℝ}
    (hn : ∀ i, 0 ≤ x i) (hd0 : 0 < d0)
    (hx : ∀ δ : ℝ, 0 < δ → δ ≤ d0 → ∀ i, x i ≤ actualNine δ i)
    (hq : q ≤ W01.ordinaryCoefficient x) (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ < d0 ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (q-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hδ,hmax,hδ0,hsmall,T,hT,h⟩ := W01.ordinary_P2 hn hd0 hx hε hdmax
  refine ⟨δ,hδ,hmax,hδ0,hsmall,T,hT,?_⟩
  intro N hN he
  have hM := (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  change 0 ≤ U8CanonicalMother.M N at hM
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hq ε) hM).trans (h N hN he)

theorem from_enhanced {q ε dmax : ℝ}
    (hq : q ≤ W01.ordinaryCoefficient W04Accepted.enhanced)
    (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (q-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨d,hd,_,hx⟩ := W04Accepted.enhanced_actual
  obtain ⟨δ,hδ,hmax,_,hsmall,T,hT,h⟩ :=
    from_finite_vector W04Accepted.enhanced_nonneg hd hx hq hε hdmax
  exact ⟨δ,hδ,hmax,hsmall,T,hT,h⟩

end WuTarget.ParentScalarCount

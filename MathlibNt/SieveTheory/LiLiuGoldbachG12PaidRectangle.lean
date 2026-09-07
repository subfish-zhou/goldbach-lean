import MathlibNt.SieveTheory.LiLiuGoldbachG12LogBudgetTools

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace G12SafeGridBudget

/-- All three fees from moving normalization, including the numerical correction
budget itself. The stronger C2 exponent is fixed before N and every cell. -/
theorem all_fees (B : ℕ) {η e : ℝ} (hη : 0 < η) (hηu : η < 1/8) (he : 0 < e) :
    ∀ᶠ N : ℕ in atTop, ∀ x Q Z : ℝ,
      e*N ≤ x → x ≤ 4*N → (N : ℝ)^(1/3 : ℝ) ≤ Q → Q ≤ N →
      2 ≤ externalInternalLevel Q η → Z = Real.sqrt Q →
      let S := externalTags true (goldbachB10SiftingPrimes N Z)
        (externalInternalLevel Q η) η Z
      400*(S.card : ℝ)*(x/Real.log x^(B+1)) +
        400*(S.card : ℝ)*G12FlexibleWF.correctionBudget N Q η +
        8000*(Nat.ceil Z : ℝ) ≤ N/Real.log (N : ℝ)^B := by
  let E := Real.exp (8*(η⁻¹)^3)
  let C := 400*E*(4*2^(B+1))+800*E+16000
  filter_upwards [fixed_prefix_log he, correction_numerical (B+1) hη hηu,
    small_numerical (B+1), absorb_constant C B] with N hx hc hs ha
  intro x Q Z hxl hxu hQl hQu hD hZ
  subst Z
  dsimp only
  let S := externalTags true (goldbachB10SiftingPrimes N (Real.sqrt Q))
    (externalInternalLevel Q η) η (Real.sqrt Q)
  let R := (N : ℝ)/Real.log (N : ℝ)^(B+1)
  have hr : 0 ≤ R := by dsimp [R]; positivity
  have hcard : (S.card : ℝ) ≤ E :=
    (externalTags_card_and_wellFactorable true (goldbachB10SiftingPrimes N (Real.sqrt Q))
      (Real.sqrt Q) hD hη hηu).1.le
  have hlog : 0 < Real.log (N : ℝ) := by linarith [hx.1]
  have hdisc := scaled_discrepancy (B+1) (Nat.cast_nonneg N) hlog hxu (hx.2 x hxl)
  have hd : 400*(S.card : ℝ)*(x/Real.log x^(B+1)) ≤
      (400*E*(4*2^(B+1)))*R := by
    calc
      _ ≤ 400*(S.card : ℝ)*((4*2^(B+1))*R) :=
        mul_le_mul_of_nonneg_left hdisc (by positivity)
      _ ≤ 400*E*((4*2^(B+1))*R) := by gcongr
      _ = _ := by ring
  have hcor : 400*(S.card : ℝ)*G12FlexibleWF.correctionBudget N Q η ≤ 800*E*R := by
    calc
      _ ≤ 400*(S.card : ℝ)*(2*R) :=
        mul_le_mul_of_nonneg_left (hc Q hQl hQu) (by positivity)
      _ ≤ 400*E*(2*R) := by gcongr
      _ = _ := by ring
  have hsmall := hs Q hQu
  calc
    _ ≤ C*R := by dsimp [C]; linarith only [hd,hcor,hsmall]
    _ ≤ _ := ha

/-- A real scaled rectangle with every additive fee discharged. -/
theorem exists_rectangle_paid :
    ∃ K C : ℝ, 1 < K ∧ 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1/100 ∧ ∃ η : ℝ, 0 < η ∧ η < 1/8 ∧
      ∀ e : ℝ, 0 < e → e ≤ 1 → ∀ B : ℕ,
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, Even N → ∀ M U T V : ℕ,
        1 ≤ M → M ≤ U → U ≤ 2*M → 1 ≤ T → T ≤ V → V ≤ 2*T →
        (N : ℝ)^(4/53 : ℝ) ≤ T → (V : ℝ) < (N : ℝ)^(1/10 : ℝ) →
        e*N ≤ 4*(M : ℝ)*T → 4*(M : ℝ)*T ≤ 4*N → ∀ ε : ℝ,
        let A := G12FlexibleRectangle.rectangle N ε M U T V
        (400*∑ p ∈ A, goldbachG12NormalizedCoefficient N p.1*
          (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) ≤
          (36/(5*(1-Real.log T/Real.log N))+δ)*400*G12FlexibleWF.mass N A*
            SingularSeries.liuSingularSeries N/Real.log (N : ℝ) + N/Real.log (N : ℝ)^B := by
  obtain ⟨K,C,hK,hC,h⟩ := G12MovingEuler.exists_scaled_rectangle_normalized
  refine ⟨K,C,hK,hC,?_⟩
  intro δ hδ
  obtain ⟨ζ,hζ,hζu,η,hη,hηu,h⟩ := h δ hδ
  refine ⟨ζ,hζ,hζu,η,hη,hηu,?_⟩
  intro e he he1 B
  obtain ⟨J,hJ,hj⟩ := h e he he1 (B+1)
  obtain ⟨L,hL⟩ := eventually_atTop.mp (all_fees B hη hηu he)
  refine ⟨max J L,hJ.trans (le_max_left _ _),?_⟩
  intro N hN hEven M U T V hM hMU hU hT hTV hV hlo hhi hxlo hxhi ε
  have hThi : (T : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) :=
    (show (T : ℝ) ≤ V by exact_mod_cast hTV).trans hhi.le
  obtain ⟨hadmit,_,hout⟩ := hj N ((le_max_left _ _).trans hN) hEven
    M U T V hM hMU hU hT hTV hV hlo hhi hxlo hxhi T le_rfl hlo hThi
  dsimp only at hadmit hout ⊢
  have hpaid := hL N ((le_max_right _ _).trans hN) (4*(M : ℝ)*T)
    (G12LocalScale.level (4*(M : ℝ)*T) T ζ)
    (Real.sqrt (G12LocalScale.level (4*(M : ℝ)*T) T ζ))
    hxlo hxhi hadmit.1 hadmit.2.1 hadmit.2.2 rfl
  dsimp only at hpaid
  linarith only [hout ε,hpaid]

end G12SafeGridBudget

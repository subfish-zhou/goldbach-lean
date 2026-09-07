import MathlibNt.SieveTheory.LiLiuGoldbachG12MovingEuler

noncomputable section
open Classical Finset Filter
open scoped BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace G12MovingEuler

/-- The original mother mass is nonnegative; no division by the mass is used. -/
theorem mass_nonneg (N : ℕ) (B : Finset (ℕ × ℕ)) : 0 ≤ G12FlexibleWF.mass N B := by
  exact sum_nonneg (fun p _ => (goldbachG12NormalizedCoefficient_bounds N p.1).1)

/-- Actual fine-cell main-term consumer. It preserves the physical C2 tag fee,
signed-correction budget, and small-output fee. It is not a low-band integral closure.
Choices are K,C then delta then zeta then eta, with e fixed before the common N0. -/
theorem exists_scaled_rectangle_normalized :
    ∃ K C : ℝ, 1 < K ∧ 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1/100 ∧
      ∃ η : ℝ, 0 < η ∧ η < 1/8 ∧
      ∀ e : ℝ, 0 < e → e ≤ 1 → ∀ A : ℕ,
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, Even N → ∀ M U T V : ℕ,
        1 ≤ M → M ≤ U → U ≤ 2*M → 1 ≤ T → T ≤ V → V ≤ 2*T →
        (N : ℝ)^(4/53 : ℝ) ≤ T → (V : ℝ) < (N : ℝ)^(1/10 : ℝ) →
        e*N ≤ 4*(M : ℝ)*T → 4*(M : ℝ)*T ≤ 4*N →
        ∀ r : ℝ, (T : ℝ) ≤ r → (N : ℝ)^(4/53 : ℝ) ≤ r → r ≤ (N : ℝ)^(1/10 : ℝ) →
        let x := 4*(M : ℝ)*T
        let Q := G12LocalScale.level x T ζ
        let Z := Real.sqrt Q
        let P := goldbachB10SiftingPrimes N Z
        let D := externalInternalLevel Q η
        let S := externalTags true P D η Z
        ((N : ℝ)^(1/3 : ℝ) ≤ Q ∧ Q ≤ N ∧ 2 ≤ D) ∧ 2 ≤ Z ∧
        ∀ ε : ℝ,
          let B := G12FlexibleRectangle.rectangle N ε M U T V
          (400*∑ p ∈ B, goldbachG12NormalizedCoefficient N p.1*
            (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) ≤
            (36/(5*(1-Real.log r/Real.log N))+δ)*400*G12FlexibleWF.mass N B*
              SingularSeries.liuSingularSeries N/Real.log (N : ℝ) +
            400*(S.card : ℝ)*(x/Real.log x^A) +
            400*(S.card : ℝ)*G12FlexibleWF.correctionBudget N Q η + 8000*(Nat.ceil Z : ℝ) := by
  obtain ⟨K,C,hK,hC,hs⟩ := G12FlexibleWF.exists_scaled_rectangle_C2_sieve
  refine ⟨K,C,hK,hC,?_⟩
  intro δ hδ
  obtain ⟨ζ,hζ,hζu,hscale⟩ := hs (δ/2) (by positivity)
  obtain ⟨η,hη,hηu,L,hL,hnorm⟩ := normalized K C (δ/2) hK hC (by positivity)
  refine ⟨ζ,hζ,hζu,η,hη,hηu,?_⟩
  intro e he he1 A
  obtain ⟨G,hG,hcell⟩ := hscale e η he he1 hη hηu A
  refine ⟨max G L,hG.trans (le_max_left _ _),?_⟩
  intro N hN hEven M U T V hM hMU hU hT hTV hV hlo hhi hxlo hxhi r hTr hrlo hrhi
  have hNG : G ≤ N := (le_max_left _ _).trans hN
  have hNL : L ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hadmit,hcoef,hsieve⟩ := hcell N hNG hEven M U T V
    hM hMU hU hT hTV hV hlo hhi hxlo hxhi r hTr hrlo hrhi
  dsimp only at hadmit hcoef hsieve ⊢
  let x := 4*(M : ℝ)*T
  let Q := G12LocalScale.level x T ζ
  let Z := Real.sqrt Q
  obtain ⟨hZ,heuler⟩ := hnorm N hNL hEven Q hadmit.1 hadmit.2.1
  refine ⟨hadmit,hZ,?_⟩
  intro ε
  let B := G12FlexibleRectangle.rectangle N ε M U T V
  have hraw := hsieve ε Z hZ le_rfl
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by
    have : 4 ≤ N := hL.trans hNL
    exact_mod_cast (show 1 < N by omega))
  have hscalar :
      (4*Real.log (N : ℝ)/Real.log Q+δ/2)*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) ≤
      (36/(5*(1-Real.log r/Real.log N))+δ)*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) := by
    apply div_le_div_of_nonneg_right _ hlogN.le
    apply mul_le_mul_of_nonneg_right _ (SingularSeries.liuSingularSeries_pos N).le
    dsimp [Q,x]
    linarith only [hcoef]
  have hmain := mul_le_mul_of_nonneg_left (heuler.trans hscalar)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 400) (mass_nonneg N B))
  have hmain' :
      400*G12FlexibleWF.mass N B*
        (∏ p ∈ goldbachB10SiftingPrimes N Z, (1-AnalyticNumberTheory.Sieve.goldbachNu p))*
        (jr1965F (Real.log Q/Real.log Z)+
          C*(η+(η^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ)))) ≤
      (36/(5*(1-Real.log r/Real.log N))+δ)*400*G12FlexibleWF.mass N B*
        SingularSeries.liuSingularSeries N/Real.log (N : ℝ) := by
    simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hmain
  exact hraw.trans (add_le_add (add_le_add (add_le_add hmain' le_rfl) le_rfl) le_rfl)

end G12MovingEuler

import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexiblePaidSieve
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleCorrectionSaving
noncomputable section
open Classical Finset Filter
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace G12FlexibleWF

/-- An actual flexible-cell C2 sieve: no discrepancy, gate, or outside residual is
carried as an unproved premise. Only numerical level/geometry admissibility remains. -/
theorem exists_rectangle_paid_C2_sieve :
    ∃ K C : ℝ, 1 < K ∧ 0 < C ∧ ∀ η : ℝ, 0 < η → η < 1/8 →
      ∀ Cscale ζ : ℝ, 1 ≤ Cscale → 0 < ζ → ζ ≤ 1/10 → ∀ A : ℕ,
        ∀ᶠ x : ℝ in atTop, ∀ M U T V : ℕ,
          1 ≤ M → M ≤ U → U ≤ 2*M → 1 ≤ T → T ≤ V → V ≤ 2*T →
          ∀ ν : ℝ, 4*(M : ℝ)*T = x → ζ ≤ ν → ν ≤ 1/10+ζ/10 →
          (T : ℝ) = x^ν → ∀ N : ℕ, 0 < N → (N : ℝ) ≤ Cscale*x →
          Even N → (N : ℝ)^(4/53 : ℝ) ≤ T → (V : ℝ) < (N : ℝ)^(1/10 : ℝ) →
          ∀ ε Z : ℝ, 2 ≤ Z → Z ≤ Real.sqrt (x^((5-5*ν)/9-ζ)) →
          x^((5-5*ν)/9-ζ) ≤ N → 2 ≤ externalInternalLevel (x^((5-5*ν)/9-ζ)) η →
          let Q := x^((5-5*ν)/9-ζ)
          let P := goldbachB10SiftingPrimes N Z
          let D := externalInternalLevel Q η
          let S := externalTags true P D η Z
          let B := G12FlexibleRectangle.rectangle N ε M U T V
          let Euler := ∏ p ∈ P, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)
          let E := C*(η+(η^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ)))
          (400*∑ p ∈ B,
            goldbachG12NormalizedCoefficient N p.1*(if (N-p.2*p.1).Prime then 1 else 0)) ≤
            400*mass N B*Euler*(jr1965F (Real.log Q/Real.log Z)+E) +
            400*(S.card : ℝ)*(x/Real.log x^A) +
            400*(S.card : ℝ)*correctionBudget N Q η + 8000*(Nat.ceil Z : ℝ) := by
  obtain ⟨K,C,hK,hC,hs⟩ := exists_rectangle_paid_sieve
  refine ⟨K,C,hK,hC,?_⟩
  intro η hη hηu Cscale ζ hscale hζ hζu A
  obtain ⟨Q₀,hQ₀,hs⟩ := hs η hη hηu
  have hlarge := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).eventually
    (eventually_ge_atTop Q₀)
  filter_upwards [family_C2_bound A hscale hζ, hlarge,
    eventually_ge_atTop (4 : ℝ)] with x hx hlarge hx4
  intro M U T V hM hMU hU hT hTV hV ν hprod hν hνu hTscale N hN hNC hEven hlo hhi
    ε Z hZ hZQ hQN hD
  have hpow : (1/3 : ℝ) ≤ (5-5*ν)/9-ζ := by linarith
  have hQ : Q₀ ≤ x^((5-5*ν)/9-ζ) := hlarge.trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith) hpow)
  have hN2 : 2 ≤ N := by obtain ⟨k,hk⟩ := hEven; omega
  obtain ⟨hf,hu⟩ := hs _ hQ N hN2 hEven ε Z M U T V hlo hhi hZ hZQ hQN hD
  dsimp only at hf hu ⊢
  let Q := x^((5-5*ν)/9-ζ)
  let P := goldbachB10SiftingPrimes N Z
  let D := externalInternalLevel Q η
  let S := externalTags true P D η Z
  let c := fun t => externalTerm true P D η Z t
  let B := G12FlexibleRectangle.rectangle N ε M U T V
  have hsum : (∑ t ∈ S, |G12FlexibleRectangle.discrepancy N B (Ioc 0 ⌊Q⌋₊) (c t)|) ≤
      (S.card : ℝ)*(x/Real.log x^A) := by
    calc
      _ ≤ ∑ _t ∈ S, (x/Real.log x^A) := by
        apply sum_le_sum
        intro t ht
        exact hx M U T V hM hMU hU hT hTV hV ν hprod hν hνu hTscale N hN hNC
          ε η Z t (hf t ht).1
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  have hp := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 400 by norm_num)
  dsimp only [S,c,B,D,P,Q] at hp
  linarith only [hu,hp]

end G12FlexibleWF

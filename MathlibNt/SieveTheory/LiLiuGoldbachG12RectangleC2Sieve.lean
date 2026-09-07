import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFSmall

noncomputable section
open Classical Finset Filter
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace G12RectangleWF

/-- The actual producer and C2 consume the same full family. The only signed
remainders left here are the explicit gcd and outside-primorial corrections.
No boundary payment or sharp low-band asymptotic is asserted. -/
theorem exists_rectangle_C2_sieve :
    ∃ K C : ℝ, 1 < K ∧ 0 < C ∧ ∀ η : ℝ, 0 < η → η < 1/8 →
      ∀ Cscale ζ : ℝ, 1 ≤ Cscale → 0 < ζ → ζ ≤ 1/10 → ∀ A : ℕ,
        ∀ᶠ x : ℝ in atTop, ∀ M T : ℕ, 1 ≤ M → 1 ≤ T →
          ∀ ν : ℝ, 4*(M : ℝ)*T = x → ζ ≤ ν → ν ≤ 1/10+ζ/10 →
          (T : ℝ) = x^ν → ∀ N : ℕ, 0 < N → (N : ℝ) ≤ Cscale*x →
          Even N → ∀ ε Z : ℝ, 2 ≤ Z → Z ≤ Real.sqrt (x^((5-5*ν)/9-ζ)) →
          let Q := x^((5-5*ν)/9-ζ)
          let P := goldbachB10SiftingPrimes N Z
          let D := externalInternalLevel Q η
          let S := externalTags true P D η Z
          let V := ∏ p ∈ P, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)
          let E := C*(η+(η^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ)))
          (400*∑ p ∈ G12LowRectangle.rectangle N ε M T,
            goldbachG12NormalizedCoefficient N p.1*(if (N-p.2*p.1).Prime then 1 else 0)) ≤
            400*mass N ε M T*V*(jr1965F (Real.log Q/Real.log Z)+E) +
            400*(S.card : ℝ)*(x/Real.log x^A) -
            400*(∑ t ∈ S,
              (gate N (G12LowRectangle.rectangle N ε M T) (Ioc 0 ⌊Q⌋₊)
                (externalTerm true P D η Z t) +
              outsidePrimorial N ε Z Q M T (externalTerm true P D η Z t))) +
            smallOutput N ε Z M T := by
  obtain ⟨K,C,hK,hC,hs⟩ := exists_rectangle_full_sieve
  refine ⟨K,C,hK,hC,?_⟩
  intro η hη hηu Cscale ζ hscale hζ hζu A
  obtain ⟨Q₀,hQ₀,hs⟩ := hs η hη hηu
  have hlarge := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).eventually
    (eventually_ge_atTop Q₀)
  filter_upwards [G12LowRectangle.rectangle_C2_bound 1 A hscale hζ,
    hlarge, eventually_ge_atTop (4 : ℝ)] with x hx hlarge hx4
  intro M T hM hT ν hprod hν hνu hTscale N hN hNC hEven ε Z hZ hZQ
  have hpow : (1/3 : ℝ) ≤ (5-5*ν)/9-ζ := by linarith
  have hQ : Q₀ ≤ x^((5-5*ν)/9-ζ) := hlarge.trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith) hpow)
  obtain ⟨hf,hu⟩ := hs _ hQ N hEven ε Z M T hZ hZQ
  dsimp only at hf hu ⊢
  let Q := x^((5-5*ν)/9-ζ)
  let P := goldbachB10SiftingPrimes N Z
  let D := externalInternalLevel Q η
  let S := externalTags true P D η Z
  let c := fun t => externalTerm true P D η Z t
  let B := G12LowRectangle.rectangle N ε M T
  have hsum : (∑ t ∈ S,
      (G12LowRectangle.discrepancy N B (Ioc 0 ⌊Q⌋₊) (c t) -
        gate N B (Ioc 0 ⌊Q⌋₊) (c t) - outsidePrimorial N ε Z Q M T (c t))) ≤
      (S.card : ℝ)*(x/Real.log x^A) -
        ∑ t ∈ S, (gate N B (Ioc 0 ⌊Q⌋₊) (c t) + outsidePrimorial N ε Z Q M T (c t)) := by
    calc
      _ ≤ ∑ t ∈ S, (x/Real.log x^A -
          (gate N B (Ioc 0 ⌊Q⌋₊) (c t) + outsidePrimorial N ε Z Q M T (c t))) := by
        apply sum_le_sum
        intro t ht
        have hd := hx M T hM hT ν hprod hν hνu hTscale N hN hNC ε (c t) (hf t ht)
        have hb := le_abs_self (G12LowRectangle.discrepancy N B (Ioc 0 ⌊Q⌋₊) (c t))
        linarith only [hd,hb]
      _ = _ := by rw [sum_sub_distrib,sum_const,nsmul_eq_mul]
  have hpaid := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 400 by norm_num)
  dsimp only [S,c,B,D,P,Q] at hpaid
  linarith only [hu,hpaid]

end G12RectangleWF

import MathlibNt.SieveTheory.LiLiuGoldbachG12OccupiedSource
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexiblePaidC2Sieve

noncomputable section
open Classical Finset Filter
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace G12FineGrid

/-- Actual occupied grid atoms supply every geometric hypothesis of the full
same-family C2 sieve. No per-cell source-size premise is carried by the caller. -/
theorem exists_occupied_C2_sieve :
    ∃ K C : ℝ, 1 < K ∧ 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1/100 ∧
      ∀ e η : ℝ, 0 < e → e ≤ 1 → 0 < η → η < 1/8 → ∀ A : ℕ,
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, Even N → ∀ ρ : ℝ,
        1 < ρ → ρ ≤ 3/2 → ∀ k p : ℕ × ℕ, p ∈ motherCell ρ N e k →
        let x := 4*(longLower ρ k : ℝ)*shortLower ρ N k
        let Q := G12LocalScale.level x (shortLower ρ N k) ζ
        ((N : ℝ)^(1/3 : ℝ) ≤ Q ∧ Q ≤ N ∧ 2 ≤ externalInternalLevel Q η) ∧
        (4/53 ≤ Real.log (p.2 : ℝ)/Real.log N ∧ Real.log (p.2 : ℝ)/Real.log N ≤ 1/10) ∧
        (4*Real.log (N : ℝ)/Real.log Q ≤ 36/(5*(1-Real.log (p.2 : ℝ)/Real.log N))+δ) ∧
        ∀ Z : ℝ, 2 ≤ Z → Z ≤ Real.sqrt Q →
          let P := goldbachB10SiftingPrimes N Z
          let D := externalInternalLevel Q η
          let S := externalTags true P D η Z
          let B := safe ρ N e k
          let Euler := ∏ q ∈ P, (1-AnalyticNumberTheory.Sieve.goldbachNu q)
          let E := C*(η+(η^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ)))
          (400*∑ q ∈ B, goldbachG12NormalizedCoefficient N q.1*
            (if (N-q.2*q.1).Prime then (1 : ℝ) else 0)) ≤
            400*G12FlexibleWF.mass N B*Euler*(jr1965F (Real.log Q/Real.log Z)+E) +
            400*(S.card : ℝ)*(x/Real.log x^A) +
            400*(S.card : ℝ)*G12FlexibleWF.correctionBudget N Q η + 8000*(Nat.ceil Z : ℝ) := by
  obtain ⟨K,C,hK,hC,hs⟩ := G12FlexibleWF.exists_rectangle_paid_C2_sieve
  refine ⟨K,C,hK,hC,?_⟩
  intro δ hδ
  obtain ⟨ζ,hζ,hζu,hpkg⟩ := uniform_occupied_source δ hδ
  refine ⟨ζ,hζ,hζu,?_⟩
  intro e η he he1 hη hηu A
  obtain ⟨L,hL4,hL⟩ := hpkg e η he hη hηu
  have hscale : (1 : ℝ) ≤ 1/e := (le_div_iff₀ he).mpr (by simpa using he1)
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp
    (hs η hη hηu (1/e) ζ hscale hζ (hζu.trans (by norm_num)) A)
  refine ⟨max L ⌈x₀/e⌉₊,hL4.trans (le_max_left _ _),?_⟩
  intro N hN hEven ρ hρ hρu k p hp
  have hNL : L ≤ N := (le_max_left _ _).trans hN
  have hN4 : 4 ≤ N := hL4.trans hNL
  obtain ⟨g,_hx,_ht,hrep,hνl,hνu,hQl,hQu,hD,hul,huu,hcoef⟩ :=
    hL N hNL ρ hρ hρu k p hp
  have hbase : x₀/e ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right L ⌈x₀/e⌉₊).trans hN)
  have hxbase : x₀ ≤ e*(N : ℝ) := by
    have h := (div_le_iff₀ he).mp hbase
    nlinarith only [h]
  have hNC : (N : ℝ) ≤ (1/e)*(4*(longLower ρ k : ℝ)*shortLower ρ N k) := by
    have h : (N : ℝ) ≤ (4*(longLower ρ k : ℝ)*shortLower ρ N k)/e :=
      (le_div_iff₀ he).mpr (by nlinarith only [g.scale_lower])
    simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using h
  refine ⟨⟨hQl,hQu,hD⟩,⟨hul,huu⟩,hcoef,?_⟩
  intro Z hZ hZQ
  exact hx₀ _ (hxbase.trans g.scale_lower) _ _ _ _ (by have := g.long_three; omega) g.long_order g.long_twice
    (by have := g.short_three; omega) g.short_order g.short_twice _ rfl hνl hνu hrep.symm N (by omega) hNC
    hEven g.source_lower g.source_upper e Z hZ hZQ hQu hD

end G12FineGrid

import MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScalePackage
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexiblePaidC2Sieve

noncomputable section
open Classical Finset Filter
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace G12FlexibleWF

/-- Uniform ambient admission is genuinely fed to the physical same-family C2
sieve. The scalar coefficient estimate is retained alongside, not advertised as
an already-normalized Euler or Buchstab main term. -/
theorem exists_scaled_rectangle_C2_sieve :
    ∃ K C : ℝ, 1 < K ∧ 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1/100 ∧
      ∀ e η : ℝ, 0 < e → e ≤ 1 → 0 < η → η < 1/8 → ∀ A : ℕ,
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, Even N → ∀ M U T V : ℕ,
        1 ≤ M → M ≤ U → U ≤ 2*M → 1 ≤ T → T ≤ V → V ≤ 2*T →
        (N : ℝ)^(4/53 : ℝ) ≤ T → (V : ℝ) < (N : ℝ)^(1/10 : ℝ) →
        e*N ≤ 4*(M : ℝ)*T → 4*(M : ℝ)*T ≤ 4*N →
        ∀ r : ℝ, (T : ℝ) ≤ r → (N : ℝ)^(4/53 : ℝ) ≤ r → r ≤ (N : ℝ)^(1/10 : ℝ) →
        let x := 4*(M : ℝ)*T
        let Q := G12LocalScale.level x T ζ
        ((N : ℝ)^(1/3 : ℝ) ≤ Q ∧ Q ≤ N ∧ 2 ≤ externalInternalLevel Q η) ∧
        (4*Real.log (N : ℝ)/Real.log Q ≤ 36/(5*(1-Real.log r/Real.log N))+δ) ∧
        ∀ ε Z : ℝ, 2 ≤ Z → Z ≤ Real.sqrt Q →
          let P := goldbachB10SiftingPrimes N Z
          let D := externalInternalLevel Q η
          let S := externalTags true P D η Z
          let B := G12FlexibleRectangle.rectangle N ε M U T V
          let Euler := ∏ p ∈ P, (1-AnalyticNumberTheory.Sieve.goldbachNu p)
          let E := C*(η+(η^8)⁻¹*Real.exp (6*K+2)*Real.log Q^(-(1/3 : ℝ)))
          (400*∑ p ∈ B, goldbachG12NormalizedCoefficient N p.1*
            (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) ≤
            400*mass N B*Euler*(jr1965F (Real.log Q/Real.log Z)+E) +
            400*(S.card : ℝ)*(x/Real.log x^A) +
            400*(S.card : ℝ)*correctionBudget N Q η + 8000*(Nat.ceil Z : ℝ) := by
  obtain ⟨K,C,hK,hC,hs⟩ := exists_rectangle_paid_C2_sieve
  refine ⟨K,C,hK,hC,?_⟩
  intro δ hδ
  obtain ⟨ζ,hζ,hζu,hpkg⟩ := G12LocalScale.uniform_source_package δ hδ
  refine ⟨ζ,hζ,hζu,?_⟩
  intro e η he he1 hη hηu A
  obtain ⟨L,hL⟩ := hpkg e η he hη hηu
  have hscale : (1 : ℝ) ≤ 1/e := (le_div_iff₀ he).mpr (by simpa using he1)
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp
    (hs η hη hηu (1/e) ζ hscale hζ (hζu.trans (by norm_num)) A)
  refine ⟨max 4 (max L ⌈x₀/e⌉₊),le_max_left _ _,?_⟩
  intro N hN hEven M U T V hM hMU hU hT hTV hV hlo hhi hxlo hxhi r hTr hrlo hrhi
  have hNL : L ≤ N := (le_max_left L _).trans ((le_max_right 4 _).trans hN)
  have hN4 : 4 ≤ N := (le_max_left 4 _).trans hN
  have hbase : x₀/e ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right L ⌈x₀/e⌉₊).trans ((le_max_right 4 _).trans hN))
  have hxbase : x₀ ≤ e*(N : ℝ) := by
    have h := (div_le_iff₀ he).mp hbase
    nlinarith only [h]
  have hNC : (N : ℝ) ≤ (1/e)*(4*(M : ℝ)*T) := by
    have h : (N : ℝ) ≤ (4*(M : ℝ)*T)/e := (le_div_iff₀ he).mpr (by nlinarith only [hxlo])
    simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using h
  obtain ⟨_hx,_ht,hrep,hνl,hνu,hQl,hQu,hD,_hul,_huu,hcoef⟩ :=
    hL N hNL (4*(M : ℝ)*T) T r hxlo hxhi
      (by nlinarith only [hlo,Real.rpow_nonneg (Nat.cast_nonneg N) (4/53 : ℝ)]) hTr hrlo hrhi
  refine ⟨⟨hQl,hQu,hD⟩,hcoef,?_⟩
  intro ε Z hZ hZQ
  exact hx₀ _ (hxbase.trans hxlo) M U T V hM hMU hU hT hTV hV
    (G12LocalScale.nu (4*(M : ℝ)*T) T) rfl hνl hνu hrep.symm N (by omega) hNC
    hEven hlo hhi ε Z hZ hZQ hQu hD

end G12FlexibleWF

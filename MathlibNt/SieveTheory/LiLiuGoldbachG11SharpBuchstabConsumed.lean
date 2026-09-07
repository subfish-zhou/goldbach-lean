import MathlibNt.SieveTheory.LiLiuBuchstabSharpClosure
import MathlibNt.SieveTheory.LiLiuGoldbachWeightG11IntegralConsumed

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Actual G11 with the proved sharp Buchstab constant, at the uniform sieve level.
This is not the author's stronger low-band coefficient. -/
theorem goldbachWeightG11_le_sharpBuchstabIntegral (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε : ℝ), 0 ≤ ε →
      (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
        (8*(561522/1000000 : ℝ)*goldbachG11PrimeIntegral (fun _ => 1)+δ) *
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  exact goldbachWeightG11_le_normalizedIntegral (561522/1000000) δ (by norm_num) hδ
    (fun _ hu => LiLiuBuchstabSharp.buchstab_sharp_tail_closed hu.1)

/-- The sharp function constant is physically consumed by the actual signed D19 bound.
The signed base and the low-prefix count remain unestimated. -/
theorem goldbachWeight_g11SharpBuchstabIntegral_consumed
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ)/15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ _hEven : Even N,
      ∀ Zlow : ℝ, 1 ≤ Zlow → Zlow ≤ Real.sqrt (N : ℝ) →
      (goldbachWeightG11PaidBase N ε : ℝ) -
        (goldbachB9LowPositivePrefixSiftedCount N ε Zlow : ℝ) +
        (goldbachWeightHighFirstCoefficient ε -
          8*(561522/1000000 : ℝ)*goldbachG11PrimeIntegral (fun _ => 1) - δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
        4*(D19 N : ℝ) := by
  exact goldbachWeight_g11NormalizedIntegral_consumed (561522/1000000) δ ε
    (by norm_num) hδ (fun _ hu => LiLiuBuchstabSharp.buchstab_sharp_tail_closed hu.1) hε hεu

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanUnweightedUnconditional
import MathlibNt.SieveTheory.Chen.ChenVerifiedPrerequisites

/-! Unconditional Chen 1+2, using the proved Liu--Pan distribution source
and the existing verified Jurkat--Richert / Selberg counting assembly.
This file makes no claim about the separate 1+1.9 contract. -/
namespace MathlibNt.ChensTheorem
open Filter

/-- The original public good-representation count, with all analytic inputs supplied. -/
theorem chen_good_representations_lower_bound_unconditional :
    ∀ᶠ N : ℕ in atTop, Even N →
      (0.67 : ℝ) * SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
        Real.log N ^ (2 : ℕ) ≤
      ((SieveTheory.SwitchingPrinciple.chenGoodRepresentations N).card : ℝ) :=
  SieveTheory.ChenVerifiedPrerequisites.chen_good_representations_lower_bound_of_liu_coprime
    SieveTheory.LiuWeight.liuPanCanonicalCoprimeTheorem_proved

/-- Every sufficiently large even natural is a prime plus a number at least two
with at most two prime factors, counted with multiplicity. No hypothesis parameter. -/
theorem chens_theorem_unconditional :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ N = p + q :=
  SieveTheory.ChenVerifiedPrerequisites.chens_theorem_of_liu_coprime
    SieveTheory.LiuWeight.liuPanCanonicalCoprimeTheorem_proved

end MathlibNt.ChensTheorem
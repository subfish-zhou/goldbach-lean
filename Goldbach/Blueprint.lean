import Architect
import Goldbach.Theorem

attribute [blueprint "thm:liu-pan"
  (proofUses := [-"ZetaUpperBnd", -"ResidueTheoremOnRectangleWithSimplePole",
    -"MediumPNT", -"Smooth1Properties_below", -"Smooth1Properties_above", -"Smooth1",
    -"RectangleIntegral", -"Smooth1Nonneg", -"HolomorphicOn.vanishesOnRectangle",
    -"Smooth1ContinuousAt", -"existsDifferentiableOn_of_bddAbove",
    -"SmoothedChebyshevDirichlet_aux_integrable", -"MellinOfSmooth1b",
    -"Smooth1LeOne", -"VerticalIntegral"])
  (title := "Proved Liu-Pan distribution input")
  (statement := /-- The canonical coprime switched-source distribution estimate
    holds with all analytic inputs supplied. -/)]
  MathlibNt.SieveTheory.LiuWeight.liuPanCanonicalCoprimeTheorem_proved

attribute [blueprint "thm:conditional-count"
  (proofUses := [-"ZetaUpperBnd", -"ResidueTheoremOnRectangleWithSimplePole",
    -"MediumPNT", -"Smooth1Properties_below", -"Smooth1Properties_above", -"Smooth1",
    -"RectangleIntegral", -"Smooth1Nonneg", -"HolomorphicOn.vanishesOnRectangle",
    -"Smooth1ContinuousAt", -"existsDifferentiableOn_of_bddAbove",
    -"SmoothedChebyshevDirichlet_aux_integrable", -"MellinOfSmooth1b",
    -"Smooth1LeOne", -"VerticalIntegral"])
  (title := "Conditional representation bound")
  (statement := /-- The canonical Liu-Pan input supplies the triple penalty
    estimate required for the eventual representation lower bound. -/)]
  MathlibNt.SieveTheory.ChenVerifiedPrerequisites.chen_good_representations_lower_bound_of_liu_coprime

attribute [blueprint "thm:conditional-chen"
  (proofUses := [-"ZetaUpperBnd", -"ResidueTheoremOnRectangleWithSimplePole",
    -"MediumPNT", -"Smooth1Properties_below", -"Smooth1Properties_above", -"Smooth1",
    -"RectangleIntegral", -"Smooth1Nonneg", -"HolomorphicOn.vanishesOnRectangle",
    -"Smooth1ContinuousAt", -"existsDifferentiableOn_of_bddAbove",
    -"SmoothedChebyshevDirichlet_aux_integrable", -"MellinOfSmooth1b",
    -"Smooth1LeOne", -"VerticalIntegral"])
  (title := "Conditional Chen assembly")
  (statement := /-- The proved weighted lower sieve and canonical Liu-Pan input
    yield the prime-plus-at-most-two-primes conclusion. -/)]
  MathlibNt.SieveTheory.ChenVerifiedPrerequisites.chens_theorem_of_liu_coprime

attribute [blueprint "thm:count-internal"
  (title := "Unconditional representation bound")
  (statement := /-- Supplying the proved distribution input discharges the
    remaining premise of the quantitative assembly. -/)]
  MathlibNt.ChensTheorem.chen_good_representations_lower_bound_unconditional

attribute [blueprint "thm:chen-internal"
  (title := "Unconditional Chen endpoint")
  (statement := /-- Supplying the proved distribution input discharges the
    remaining premise of the qualitative assembly. -/)]
  MathlibNt.ChensTheorem.chens_theorem_unconditional

attribute [blueprint "thm:representation"
  (title := "Public representation lower bound")
  (statement := /-- For sufficiently large even natural numbers, the actual
    representation count has lower bound $0.67$ times the normalized singular
    series scale $N / (\log N)^2$. -/)]
  Goldbach.representation_lower_bound

attribute [blueprint "thm:chen"
  (title := "Chen's theorem")
  (statement := /-- Every sufficiently large even natural number is the sum of
    a prime and either a prime or a product of two primes. The two factors may
    be equal. -/)]
  Goldbach.chen_theorem
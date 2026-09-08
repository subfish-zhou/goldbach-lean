import Architect
import Goldbach.All

attribute [blueprint "thm:liu-pan"
  (proofUses := [-"ZetaUpperBnd", -"ResidueTheoremOnRectangleWithSimplePole",
    -"MediumPNT", -"Smooth1Properties_below", -"Smooth1Properties_above", -"Smooth1",
    -"RectangleIntegral", -"pi_alt", -"Smooth1Nonneg", -"HolomorphicOn.vanishesOnRectangle",
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
    -"RectangleIntegral", -"pi_alt", -"Smooth1Nonneg", -"HolomorphicOn.vanishesOnRectangle",
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
    -"RectangleIntegral", -"pi_alt", -"Smooth1Nonneg", -"HolomorphicOn.vanishesOnRectangle",
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

attribute [blueprint "thm:pair-transport"
  (title := "Unique prime-pair transport")
  (statement := /-- An arbitrary filtered sum on supported integers is reindexed by their unique admissible ordered prime pair. The cutoff and additive kernel remain arbitrary. -/)]
  MathlibNt.SieveTheory.LiuWeight.sum_liuWeightSupport_filter_eq_sum_pairs

attribute [blueprint "thm:log-saving"
  (title := "Uniform logarithmic error absorption")
  (statement := /-- A fixed positive logarithmic saving absorbs a fixed coefficient uniformly over normalization exponents and weights with a positive common lower bound. -/)]
  MathlibNt.Analysis.eventually_log_rpow_remainder_lt_of_lower_bound

attribute [blueprint "thm:grid-error"
  (title := "Integral error from a finite boundary cover")
  (statement := /-- A local error on the common region and a finite cover of the excess bound the difference between the grid integral and the source integral. -/)]
  MathlibNt.Analysis.IntegralExcessCover.integral_sub_setIntegral_le_of_excess_cover

attribute [blueprint "thm:liliu-finite"
  (proofUses := [-"ZetaUpperBnd", -"ResidueTheoremOnRectangleWithSimplePole",
    -"MediumPNT", -"Smooth1Properties_below", -"Smooth1Properties_above", -"Smooth1",
    -"RectangleIntegral", -"pi_alt", -"Smooth1Nonneg", -"HolomorphicOn.vanishesOnRectangle",
    -"Smooth1ContinuousAt", -"existsDifferentiableOn_of_bddAbove",
    -"SmoothedChebyshevDirichlet_aux_integrable", -"MellinOfSmooth1b",
    -"Smooth1LeOne", -"VerticalIntegral"])
  (title := "Finite weights detect eligible primes")
  (statement := /-- The finite Li--Liu weight sum is bounded by the number of distinct eligible primes, retaining the factor-size condition in the representation. -/)]
  MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachBasic_finite_le_D19

attribute [blueprint "thm:liliu-margin"
  (proofUses := [-"ZetaUpperBnd", -"ResidueTheoremOnRectangleWithSimplePole",
    -"MediumPNT", -"Smooth1Properties_below", -"Smooth1Properties_above", -"Smooth1",
    -"RectangleIntegral", -"pi_alt", -"Smooth1Nonneg", -"HolomorphicOn.vanishesOnRectangle",
    -"Smooth1ContinuousAt", -"existsDifferentiableOn_of_bddAbove",
    -"SmoothedChebyshevDirichlet_aux_integrable", -"MellinOfSmooth1b",
    -"Smooth1LeOne", -"VerticalIntegral"])
  (title := "Positive margin for existence")
  (statement := /-- Certified integral bounds give a strictly positive sieve margin and supply the qualitative Li--Liu existence route. -/)]
  MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachSharpElementaryMargin_pos

attribute [blueprint "thm:liliu-ledger"
  (proofUses := [-"ZetaUpperBnd", -"ResidueTheoremOnRectangleWithSimplePole",
    -"MediumPNT", -"Smooth1Properties_below", -"Smooth1Properties_above", -"Smooth1",
    -"RectangleIntegral", -"pi_alt", -"Smooth1Nonneg", -"HolomorphicOn.vanishesOnRectangle",
    -"Smooth1ContinuousAt", -"existsDifferentiableOn_of_bddAbove",
    -"SmoothedChebyshevDirichlet_aux_integrable", -"MellinOfSmooth1b",
    -"Smooth1LeOne", -"VerticalIntegral"])
  (title := "Quantitative weighted-count estimate")
  (statement := /-- The author G11 bound and the certified remaining terms give a positive quantitative lower bound for four times the original distinct-prime count. -/)]
  MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_authorG11_numericLedger

attribute [blueprint "thm:liliu-family"
  (title := "Fixed-coefficient lower bounds")
  (statement := /-- Each fixed real coefficient strictly below $515093/800000000$ has a common eventual threshold for the normalized distinct-prime lower bound. -/)]
  MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbach_D19_author_lower_of_coefficient_lt

attribute [blueprint "thm:liliu-count"
  (title := "Public strict 0.0004 bound")
  (statement := /-- For every sufficiently large even natural number, the distinct eligible prime count exceeds $0.0004$ times the Liu singular-series scale. -/)]
  Goldbach.one_plus_one_nine_count

attribute [blueprint "thm:liliu-existence"
  (proofUses := [-"ZetaUpperBnd", -"ResidueTheoremOnRectangleWithSimplePole",
    -"MediumPNT", -"Smooth1Properties_below", -"Smooth1Properties_above", -"Smooth1",
    -"RectangleIntegral", -"pi_alt", -"Smooth1Nonneg", -"HolomorphicOn.vanishesOnRectangle",
    -"Smooth1ContinuousAt", -"existsDifferentiableOn_of_bddAbove",
    -"SmoothedChebyshevDirichlet_aux_integrable", -"MellinOfSmooth1b",
    -"Smooth1LeOne", -"VerticalIntegral"])
  (title := "Li--Liu's 1+1.9 theorem")
  (statement := /-- Every sufficiently large even natural number admits $N=p+rq$, with $p,q$ prime, $r=1$ or $r$ prime, and $r^{10}\le q^9$. -/)]
  Goldbach.one_plus_one_nine

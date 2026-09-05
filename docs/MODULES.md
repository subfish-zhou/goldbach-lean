# Module guide

Start with the literal statement and the public theorem, then follow the two
analytic inputs into the counting assembly.

## Reading order

| File | Responsibility |
|---|---|
| [`Goldbach/Statement.lean`](../Goldbach/Statement.lean) | Independent literal statement |
| [`Goldbach/Theorem.lean`](../Goldbach/Theorem.lean) | Public qualitative and quantitative results |
| [`MathlibNt/ChensTheorem.lean`](../MathlibNt/ChensTheorem.lean) | Almost-prime vocabulary and literal characterization |
| [`MathlibNt/ChensTheoremUnconditional.lean`](../MathlibNt/ChensTheoremUnconditional.lean) | Unconditional implementation endpoints |
| [`MathlibNt/SieveTheory/Chen/ChenVerifiedPrerequisites.lean`](../MathlibNt/SieveTheory/Chen/ChenVerifiedPrerequisites.lean) | Final sieve and counting assembly |
| [`MathlibNt/SieveTheory/LinearSieve/JurkatRichert/JurkatRichert1965ChenRichertConsumer.lean`](../MathlibNt/SieveTheory/LinearSieve/JurkatRichert/JurkatRichert1965ChenRichertConsumer.lean) | Weighted lower bound for the actual Goldbach source |
| [`MathlibNt/SieveTheory/Distribution/LiuPan/LiuPanUnweightedUnconditional.lean`](../MathlibNt/SieveTheory/Distribution/LiuPan/LiuPanUnweightedUnconditional.lean) | Proved switched-source distribution input |
| [`MathlibNt/SieveTheory/Selberg/Liu/LiuSelbergCorrectedChenBridge.lean`](../MathlibNt/SieveTheory/Selberg/Liu/LiuSelbergCorrectedChenBridge.lean) | Selberg-square and triple-count transport |
| [`MathlibNt/AnalyticNumberTheory/BombieriVinogradov/Bombieri1965Richert418Unconditional.lean`](../MathlibNt/AnalyticNumberTheory/BombieriVinogradov/Bombieri1965Richert418Unconditional.lean) | Unconditional averaged-distribution foundation |
| [`AnalyticNumberTheory/PrimeDistribution/PrimeNumberTheorem.lean`](../AnalyticNumberTheory/PrimeDistribution/PrimeNumberTheorem.lean) | Natural-number prime-counting interface |
| [`PrimeNumberTheoremAnd/MediumPNT.lean`](../PrimeNumberTheoremAnd/MediumPNT.lean) | Attributed prime-number-theorem implementation |

## Focused implementation directories

- `MathlibNt/AnalyticNumberTheory/LargeSieve/`: common moment, character, and large-sieve estimates.
- `MathlibNt/AnalyticNumberTheory/Vaughan/`: decomposition and Type I/II estimates.
- `MathlibNt/AnalyticNumberTheory/DirichletL/`: Dirichlet L-function estimates.
- `MathlibNt/AnalyticNumberTheory/Siegel/`: the Siegel-bound proof components.
- `MathlibNt/AnalyticNumberTheory/BombieriVinogradov/`: distribution assembly.
- `MathlibNt/AnalyticNumberTheory/Chen1973/`: retained source-specific analytic ingredients.
- `MathlibNt/SieveTheory/Arithmetic/`: singular-series, Mertens and prime-sum normalization.
- `MathlibNt/SieveTheory/LinearSieve/`: finite weights, Rosser boundary analysis, and applications.
- `MathlibNt/SieveTheory/LinearSieve/Suzuki/`: comparison and source-layer estimates.
- `MathlibNt/SieveTheory/LinearSieve/JurkatRichert/`: delay functions and the actual source consumer.
- `MathlibNt/SieveTheory/LinearSieve/Richert/`: weighted-sieve finite identities and error payment.
- `MathlibNt/SieveTheory/LinearSieve/LevelSupported/`: supported-coefficient interfaces.
- `MathlibNt/SieveTheory/Distribution/`: Chen-facing distribution consumers and Liu–Pan estimates.
- `MathlibNt/SieveTheory/Selberg/`: upper sieve and Liu source specialization.
- `MathlibNt/SieveTheory/Liu/`: source weights, prime-pair estimates and logarithmic-integral bridges.
- `MathlibNt/SieveTheory/Switching/`: weighted finite counting, boundary comparisons and endpoint assembly.

The `SwitchingPrinciple.lean` and `LinearSieve.lean` facades expose their focused
submodules without changing the existing mathematical declaration namespaces.
A physical module path identifies where to import a proof; a declaration
namespace identifies its stable mathematical name.

## The two extracted module families

The former monolithic switching file is split into 19 modules from `Weights`
through `EndpointAssembly`. The former monolithic linear-sieve file is split
into seven modules: `FiniteWeights`, `RosserChains`, `BoundaryMass`,
`BoundaryRegularity`, `BoundaryIntegrals`, `UpperRosserDensity`, and
`SieveApplications`. Cross-module helper visibility is confined to the respective
`Internal` namespaces; the original proof statements and bodies were preserved.

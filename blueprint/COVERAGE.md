# Mathematical coverage of the proof Blueprint

The Blueprint explains the high-level mathematical argument, not every Lean
helper. Its chapter statements and proof sketches are editorial work checked
against the implementation; extracting a dependency graph does not certify the
correctness or completeness of that prose.

## Reading structure

- **Overview:** counting objects, normalizations, both finite reductions and the
  input/estimate/positivity pattern. The overview graph compresses existing
  compiled dependency paths between major stages.
- **Analytic foundations:** reusable distribution and sieve theorems, with their
  actual sources, parameter ranges and error payments.
- **Chen:** the finite detector, weighted lower bound, genuine triple penalty,
  switching and Selberg upper bound, and the representation budget.
- **Li–Liu:** literal fibres and signed decompositions, normalized term estimates,
  geometric integrals, and two independently assembled theorem exits.
- **Implementation and sources:** code navigation, logical foundations and
  academic attribution.

A reader can start with a proof chapter and consult the foundations as needed.
The chapter graphs retain compiled dependencies and mark inputs introduced
elsewhere. The complete selected graph is available separately.

## Coverage obligations and where they are discharged

| Mathematical obligation | Exposition and source navigation |
|---|---|
| Actual prime partners, units, repeated prime factors and factor-size constraint | Overview; opening definitions of both proof chapters |
| Prime number theorem, Mertens products, singular-series normalization | Foundations: prime counting and moving products |
| Progression errors and their exact logarithmic-integral centering | Foundations: ordinary prime distribution, including zero/one endpoints |
| Why lower and upper Rosser sums control a finite sifted count | Foundations: finite coefficients, parity conditions and divisor-sum certificates |
| Constructed sieve functions, Suzuki error envelope and admissible ratios | Foundations: hats, source cutoff, adaptive depth and actual consumer ranges |
| Ordinary BV and its weighted Chen consequence | Foundations: low/high-conductor branches; Chen: combined-modulus remainder |
| Switched distribution, signed weights and coprimality | Foundations: Pan aggregates and well-factorable rectangles; Chen: remainder grouping |
| Chen's finite detector and distinct/valuation correction | Chen: corrected weight, source weight and repeated-prime payment |
| Genuine triple penalty and its endpoint fibres | Chen: triple regions and the transfer to the switched source |
| Selberg square, optimization and its actual main mass | Chen: square majorant, quadratic form, source integral and genuine-li correction |
| Chen's final positive representation budget | Chen: fixed margins and the two public conclusions |
| Li–Liu's literal S1–S6 and G1–G12 domains | Li–Liu: finite fibres, closed endpoints and twelve-term decomposition |
| Corrected tenth term and actual output-sieve consumer | Li–Liu: corrected twelve-term input, Pi10 fibres and I10 consumption |
| Each positive/negative coefficient and its sieve range | Li–Liu: normalized inputs; foundations: level-six and upper-through-six producers |
| G9 low/high split and the extra low kernel factor | Li–Liu: both exact inner-integral reductions |
| Pair lower bound and its finite integral certificate | Li–Liu: source-mass epsilon window and five sum-coordinate integrals |
| G11/G12 original domains, Buchstab factors and actual-count payments | Li–Liu: full rough upper mothers, mixed levels, pointwise bounds and integral transfers |
| Error tolerances before epsilon, then integer thresholds | Local node statements and each corresponding estimate; final common budget |
| Strict 0.0004 and the separate qualitative implementation | Li–Liu: author-route coefficient and the independently defined older margin |

Every row is developed in the chapter prose, with named declarations and/or
revision-pinned source-file links. The node catalogue is
[`nodes.json`](nodes.json); the actual annotations are
[`Goldbach/Blueprint.lean`](../Goldbach/Blueprint.lean). The source chapters are
under [`src/chapters`](src/chapters).

## Independent checks

`verify_blueprint.py` checks the exact extracted graph, its documented theorem
exits, and that every selected node has a compiled path to an exit. It also
checks that chapter/overview edges follow paths in the full graph, natural
labels agree with the catalogue, and source-file targets exist. The checked
snapshot is [`graph.json`](graph.json).

These structural checks accompany, rather than replace, mathematical and
reader-oriented review. Rendering checks additionally exercise the generated
formulas, node dialogs, source links and responsive pages. Lean proof checking,
editorial review, browser verification and deployment remain distinct claims.

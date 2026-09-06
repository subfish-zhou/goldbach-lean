import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace MathlibNt.SieveTheory

/-- Normalize the Case-I sigma-eleven scalar factor using the sigma-cubed bound. -/
lemma caseI_endpoint_sigma11_normalization
    (K σ logσ logD logLog Δ : ℝ)
    (hlog : 0 < logD) (hll : 0 < logLog) (hσ : 0 < σ)
    (hscalar : K ^ 2 * σ ^ 3 * logσ * logLog ≤ logD ^ (1 - Δ))
    (hpowe : logD ^ (-Δ) * logD = logD ^ (1 - Δ)) :
    K ^ 2 * σ ^ 2 * logσ / logD ≤
      logD ^ (-Δ) / (logLog * σ) := by
  apply (div_le_div_iff₀ hlog (mul_pos hll hσ)).2
  calc
    K ^ 2 * σ ^ 2 * logσ * (logLog * σ) =
      K ^ 2 * σ ^ 3 * logσ * logLog := by ring
    _ ≤ logD ^ (1 - Δ) := hscalar
    _ = logD ^ (-Δ) * logD := hpowe.symm

end MathlibNt.SieveTheory
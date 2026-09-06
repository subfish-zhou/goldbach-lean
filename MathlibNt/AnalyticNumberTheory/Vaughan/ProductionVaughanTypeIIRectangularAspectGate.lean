import MathlibNt.AnalyticNumberTheory.Vaughan.ProductionVaughanTypeIIRectangularExplicitShell

/-!
# Aspect-gated scalar bound for one actual Vaughan Type-II rectangle

This checker leaf expands the *actual* weak `largeSieveBound`.  It proves a
scalar estimate only for one active rectangle satisfying the displayed aspect
hypothesis; it makes no assertion about all shells.  The coefficient `L¹` error
in the actual weighted-mean corollary is retained literally.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

private lemma aspect_product_bound
    (n d x t A c H : ℝ)
    (hn : 0 ≤ n) (hd : 0 ≤ d) (hx : 0 ≤ x) (ht : 0 ≤ t)
    (hA : 0 < A) (hc : 1 ≤ c) (hH : 0 ≤ H)
    (hdx : d * x ≤ n) (htx : t ≤ x)
    (hAspect : d + x ≤ H * (n / A + A)) :
    d * x * (d + c * A) * (t + c * A) ≤
      c ^ 2 * (H + 1) * (n + A * Real.sqrt n) ^ 2 := by
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  have hA0 : 0 ≤ A := hA.le
  have hsqrtn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsqrtn_sq : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn
  have hAspectA : A * (d + x) ≤ H * (n + A ^ 2) := by
    calc
      A * (d + x) ≤ A * (H * (n / A + A)) :=
        mul_le_mul_of_nonneg_left hAspect hA0
      _ = H * (n + A ^ 2) := by field_simp [hA.ne']
  have hdt : d + c * A ≥ 0 := by positivity
  have htxA : t + c * A ≤ x + c * A := by linarith
  have hrect : (d + c * A) * (t + c * A) ≤
      c ^ 2 * (H + 1) * (n + A ^ 2) := by
    calc
      (d + c * A) * (t + c * A) ≤
          (d + c * A) * (x + c * A) :=
        mul_le_mul_of_nonneg_left htxA hdt
      _ = d * x + c * (A * (d + x)) + c ^ 2 * A ^ 2 := by ring
      _ ≤ n + c * (H * (n + A ^ 2)) + c ^ 2 * A ^ 2 := by
        gcongr
      _ ≤ c ^ 2 * (H + 1) * (n + A ^ 2) := by
        nlinarith [sq_nonneg (c - 1), mul_nonneg hH hn,
          mul_nonneg hH (sq_nonneg A)]
  have hleft0 : 0 ≤ d * x := mul_nonneg hd hx
  calc
    d * x * (d + c * A) * (t + c * A)
        = (d * x) * ((d + c * A) * (t + c * A)) := by ring
    _ ≤ n * (c ^ 2 * (H + 1) * (n + A ^ 2)) := by
      exact mul_le_mul hdx hrect (mul_nonneg hdt (by positivity)) hn
    _ ≤ c ^ 2 * (H + 1) * (n + A * Real.sqrt n) ^ 2 := by
      have hfac : 0 ≤ c ^ 2 * (H + 1) := by positivity
      have hinner : n * (n + A ^ 2) ≤
          (n + A * Real.sqrt n) ^ 2 := by
        nlinarith [mul_nonneg hA0 hsqrtn]
      calc
        n * (c ^ 2 * (H + 1) * (n + A ^ 2))
            = (c ^ 2 * (H + 1)) * (n * (n + A ^ 2)) := by ring
        _ ≤ (c ^ 2 * (H + 1)) * (n + A * Real.sqrt n) ^ 2 :=
          mul_le_mul_of_nonneg_left hinner hfac

/-- Honest aspect-gated scalarization of the actual weak-large-sieve rank-one
term for one active canonical rectangle.  Here `D=2^k`, `X=N/D`,
`T=X-2^l+1`, `A=Q^2`, and the logarithmic coefficient is the literal
`primitiveBilinearQFactor Q` coming from `largeSieveBound`. -/
theorem vaughanTypeIIRectangularRexp_le_aspectGate
    (N Q u v k l : ℕ) (H : ℝ)
    (hN : 3 ≤ N) (hQ : 0 < Q)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v)
    (hH : 0 ≤ H)
    (hAspect :
      (vaughanTypeIIRectangularD k : ℝ) +
          (vaughanTypeIIRectangularX N k : ℝ) ≤
        H * (((N : ℝ) / (Q : ℝ) ^ 2) + (Q : ℝ) ^ 2)) :
    vaughanTypeIIRectangularRexp N k l Q ≤
      primitiveBilinearQFactor Q *
        Real.sqrt (27 * (H + 1) *
          Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5) *
        ((N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N) := by
  let d : ℝ := vaughanTypeIIRectangularD k
  let x : ℝ := vaughanTypeIIRectangularX N k
  let t : ℝ := vaughanTypeIIRectangularT N k l
  let A : ℝ := (Q : ℝ) ^ 2
  let c : ℝ := primitiveBilinearQFactor Q
  let L : ℝ := Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5
  let n : ℝ := N
  have hn : 0 ≤ n := by positivity
  have hd : 0 ≤ d := by positivity
  have hx : 0 ≤ x := by positivity
  have ht : 0 ≤ t := by positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hc : 1 ≤ c := by simpa [c] using one_le_primitiveBilinearQFactor Q
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  have hcorner : 2 ^ k * 2 ^ l ≤ N :=
    (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).2
  have hl : 2 ^ l ≤ N / 2 ^ k :=
    (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).2
      (by simpa [mul_comm] using hcorner)
  have htxNat : vaughanTypeIIRectangularT N k l ≤
      vaughanTypeIIRectangularX N k := by
    have hlone : 1 ≤ 2 ^ l :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    unfold vaughanTypeIIRectangularT vaughanTypeIIRectangularX
    omega
  have htx : t ≤ x := by
    dsimp [t, x]
    exact_mod_cast htxNat
  have hdxNat : vaughanTypeIIRectangularD k *
      vaughanTypeIIRectangularX N k ≤ N := by
    simpa [vaughanTypeIIRectangularD, vaughanTypeIIRectangularX] using
      Nat.mul_div_le N (2 ^ k)
  have hdx : d * x ≤ n := by
    dsimp [d, x, n]
    exact_mod_cast hdxNat
  have hAspect' : d + x ≤ H * (n / A + A) := by
    simpa [d, x, n, A] using hAspect
  have hcore := aspect_product_bound n d x t A c H hn hd hx ht hA hc hH
    hdx htx hAspect'
  have hL : 0 ≤ L := by
    dsimp [L]
    have hXone : 1 ≤ (vaughanTypeIIRectangularX N k + 1 : ℕ) := by omega
    have hlog : 0 ≤ Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) := by
      exact Real.log_nonneg (by exact_mod_cast hXone)
    positivity
  have hLSD : largeSieveBound (vaughanTypeIIRectangularD k)
      (1 / (Q : ℝ) ^ 2) = d + c * A := by
    simpa only [vaughanBilinearLargeSieveConstant, d, c, A,
      primitiveBilinearQFactor] using
      vaughanBilinearLargeSieveConstant_eq_explicit
        (vaughanTypeIIRectangularD k) Q hQ
  have hLST : largeSieveBound (vaughanTypeIIRectangularT N k l)
      (1 / (Q : ℝ) ^ 2) = t + c * A := by
    simpa only [vaughanBilinearLargeSieveConstant, t, c, A,
      primitiveBilinearQFactor] using
      vaughanBilinearLargeSieveConstant_eq_explicit
        (vaughanTypeIIRectangularT N k l) Q hQ
  have hrad1 : 0 ≤ (d + c * A) * d := by positivity
  have hrad2 : 0 ≤ (t + c * A) * (27 * x * L) := by positivity
  have hradR : 0 ≤ 27 * (H + 1) * L := by positivity
  have hsum : 0 ≤ n + A * Real.sqrt n := by positivity
  have hsq :
      (Real.sqrt ((d + c * A) * d) *
          Real.sqrt ((t + c * A) * (27 * x * L))) ^ 2 ≤
        (c * Real.sqrt (27 * (H + 1) * L) *
          (n + A * Real.sqrt n)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad1, Real.sq_sqrt hrad2,
      mul_pow, mul_pow, Real.sq_sqrt hradR]
    calc
      ((d + c * A) * d) * ((t + c * A) * (27 * x * L))
          = 27 * L * (d * x * (d + c * A) * (t + c * A)) := by ring
      _ ≤ 27 * L * (c ^ 2 * (H + 1) *
          (n + A * Real.sqrt n) ^ 2) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = c ^ 2 * (27 * (H + 1) * L) *
          (n + A * Real.sqrt n) ^ 2 := by ring
  unfold vaughanTypeIIRectangularRexp
    vaughanTypeIIRectangularEright at ⊢
  rw [hLSD, hLST]
  change Real.sqrt ((d + c * A) * d) *
      Real.sqrt ((t + c * A) * (27 * x * L)) ≤
    c * Real.sqrt (27 * (H + 1) * L) *
      (n + A * Real.sqrt n)
  have hlhs : 0 ≤ Real.sqrt ((d + c * A) * d) *
      Real.sqrt ((t + c * A) * (27 * x * L)) := by positivity
  have hrhs : 0 ≤ c * Real.sqrt (27 * (H + 1) * L) *
      (n + A * Real.sqrt n) := by positivity
  exact (sq_le_sq₀ hlhs hrhs).mp hsq

/-- The actual one-shell weighted mean under the same aspect gate.  The
rectangular coefficient-`L¹` error is deliberately retained. -/
theorem vaughanActualCanonicalCollectedShellWeightedMean_le_aspectGate
    (N Q u v k l : ℕ) (H : ℝ)
    (hN : 3 ≤ N) (hQ : 0 < Q)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v)
    (hH : 0 ≤ H)
    (hAspect :
      (vaughanTypeIIRectangularD k : ℝ) +
          (vaughanTypeIIRectangularX N k : ℝ) ≤
        H * (((N : ℝ) / (Q : ℝ) ^ 2) + (Q : ℝ) ^ 2)) :
    vaughanActualCanonicalCollectedShellWeightedMean N u v k l S ≤
      (1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) *
        (primitiveBilinearQFactor Q *
          Real.sqrt (27 * (H + 1) *
            Real.log (vaughanTypeIIRectangularX N k + 1 : ℕ) ^ 5) *
          ((N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N)) +
      (8 / (Real.pi * ((2 * N : ℕ) : ℝ))) *
        vaughanTypeIIRectangularL1exp N k l * weightedPrimitiveFamilyMass S := by
  refine (vaughanActualCanonicalCollectedShellWeightedMean_le_explicit
    N Q u v k l hN hQ S hS hactive).trans ?_
  have hR := vaughanTypeIIRectangularRexp_le_aspectGate
    N Q u v k l H hN hQ hactive hH hAspect
  have hdamp : 0 ≤
      (1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) := by
    have hlog : 0 ≤ Real.log ((2 * N : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 2 * N by omega)
    positivity
  gcongr

end
end AnalyticNumberTheory.LargeSieve

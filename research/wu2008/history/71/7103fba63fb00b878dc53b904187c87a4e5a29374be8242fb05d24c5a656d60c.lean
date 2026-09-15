import MathlibNt.Wu2004MeanValue.OriginalTriplesCover
import MathlibNt.Wu2004MeanValue.OriginalCountPayment
import MathlibNt.Wu2004MeanValue.OriginalTailAsymptotics

/-!
# The two original manuscript counting estimates

The tail theorem is imported with its literal quotient-sieve definition.
Here the actual small-product prime triples are counted through the exact
dyadic cover, including its final block. All block estimates use one threshold
independent of the later integer and of the moving number of blocks.
-/

namespace Wu2004MeanValue

open Filter Finset
open MathlibNt.SieveTheory.SingularSeries
open scoped BigOperators
noncomputable section

/-- The constant depends only on `a`, before `eta`, `epsilon`, and the
eventual even integer. This counts the literal triples, not their values. -/
theorem originalTripleCount_small_product_upper (a : ℝ)
    (ha : 3 / 2 < a) (ha2 : a < 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
        (originalTripleCount N a η : ℝ) ≤
          (K * η + ε) * liuSingularSeries N * N / Real.log N ^ 2 := by
  obtain ⟨B, C, H₀, hB, hC, hsieve⟩ := blockSiftedCount_uniform_upper a ha ha2
  refine ⟨16 * C, by positivity, ?_⟩
  intro η hη hη2 ε hε
  obtain ⟨T, hT16, hT⟩ := dyadic_uniform_nat_threshold η H₀ hη hη2
  refine eventually_atTop.mp ?_
  filter_upwards [eventually_originalTripleExceptionBudget_paid ε hε,
    eventually_ge_atTop T] with N hpay hNT hEven
  have hN16 : 16 ≤ N := hT16.trans hNT
  have hx16 : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hx0 : (0 : ℝ) < N := by linarith
  have hη1 : η ≤ 1 := by linarith
  obtain ⟨hfirst, hscale, hsum, _⟩ := hT N hNT
  let J := dyadicLast η N
  let H : ℕ → ℝ := dyadicScale η N
  let z : ℕ → ℝ := fun j =>
    Real.sqrt (Real.sqrt (2 * H j) / Real.log (2 * H j) ^ B)
  let S := range (J + 1)
  let R := H J
  have hRpos : 0 < R := dyadicScale_pos hη hx0 J
  have hRlt : R < Real.sqrt N := (dyadicLast_spec hη hx0).1
  have hHpos : ∀ j ∈ S, 0 < H j := fun j _ => dyadicScale_pos hη hx0 j
  have hcut : ∀ j ∈ S, z j ≤ (1 - η) * N := by
    intro j hj
    have hjJ : j ≤ J := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hz := (hscale j hjJ).2.2.2.2 B hB.le
    exact hz.trans (by nlinarith)
  have hcover : ∀ x : ℝ, R < x → x ≤ η * N →
      ∃ j ∈ S, H j < x ∧ x ≤ 2 * H j := by
    intro x hxR hxη
    rcases (dyadic_cover_iff hη hx0 J).mp ⟨hRpos.trans hxR, hxη⟩ with
      hlow | ⟨j, hj, hblock⟩
    · exact False.elim ((not_lt_of_ge hlow.2) hxR)
    · exact ⟨j, mem_range.mpr (Nat.lt_succ_iff.mpr hj), hblock⟩
  have hfinite := originalTripleCount_le_cover_real S H z N a η R
    (by linarith) hη2 hRpos.le hHpos hcut hcover
  have hlow : (Real.sqrt R + 1) * (R + 1) ≤
      (Real.sqrt (Real.sqrt N) + 1) * (Real.sqrt N + 1) :=
    mul_le_mul (add_le_add (Real.sqrt_le_sqrt hRlt.le) le_rfl)
      (add_le_add hRlt.le le_rfl) (by positivity) (by positivity)
  have hsifted : (∑ j ∈ S, (blockSiftedCount (H j) N a η (z j) : ℝ)) ≤
      (16 * C) * η * liuSingularSeries N * N / Real.log N ^ 2 := by
    calc
      _ ≤ ∑ j ∈ S, C * liuSingularSeries N * H j / Real.log (H j) ^ 2 := by
        apply sum_le_sum
        intro j hj
        have hjJ : j ≤ J := Nat.lt_succ_iff.mp (mem_range.mp hj)
        exact hsieve (H j) (hscale j hjJ).1.le N hEven (by omega) η hη1
      _ = (C * liuSingularSeries N) *
          (∑ j ∈ S, H j / Real.log (H j) ^ 2) := by
        simp only [mul_sum, mul_div_assoc]
      _ ≤ (C * liuSingularSeries N) * (16 * η * N / Real.log N ^ 2) :=
        mul_le_mul_of_nonneg_left hsum
          (mul_nonneg hC.le (liuSingularSeries_pos N).le)
      _ = _ := by ring
  have hboundary := dyadic_target_boundary_sum_le hη hη1 hx16 hfirst
  have hbound :
      (originalTripleCount N a η : ℝ) ≤
        (16 * C) * η * liuSingularSeries N * N / Real.log N ^ 2 +
          originalTripleExceptionBudget N := by
    change _ ≤ _ +
      ((Real.sqrt (Real.sqrt N) + 1) * (Real.sqrt N + 1) +
        (3 / Real.log 2) * Real.log N * (Real.sqrt N + 1))
    dsimp only [S, J, H] at hfinite hsifted
    linarith
  calc
    _ ≤ _ := hbound
    _ ≤ (16 * C) * η * liuSingularSeries N * N / Real.log N ^ 2 +
        ε * liuSingularSeries N * N / Real.log N ^ 2 := add_le_add le_rfl hpay
    _ = _ := by ring

end
end Wu2004MeanValue

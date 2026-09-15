import MathlibNt.Wu2004MeanValue.OriginalTailSwitching

/-!
# The sharp upper bound for the original quotient-sieve sum

The finite exceptional budget is at most `6 N^(5/6)`. It is paid using the
accepted inverse-log-cube payment, hence the uniform positive lower bound
for the Liu singular series. No analytic estimate is a caller hypothesis.
-/

namespace Wu2004MeanValue

open Filter Finset
open MathlibNt.SieveTheory.SingularSeries
noncomputable section

theorem originalTailPrimes_source_iff {N p : ℕ} {η : ℝ} (hη : 0 ≤ η) :
    p ∈ originalTailPrimes N η ↔ p.Prime ∧ (p : ℝ) ≤ (1 - η) * N := by
  rw [mem_originalTailPrimes]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have hh : (p : ℝ) ≤ N := by
      nlinarith [h.2, mul_nonneg hη (Nat.cast_nonneg (α := ℝ) N)]
    exact_mod_cast hh

theorem originalTailA_source_iff {N a : ℕ} {η : ℝ} (hη : 0 ≤ η) :
    a ∈ originalTailA N η ↔
      ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (1 - η) * N ∧ N - p = a := by
  simp only [originalTailA, mem_image, originalTailPrimes_source_iff hη]
  aesop

private theorem cube_third_rpow (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem eventually_tailSource_cube (c τ : ℝ) (hc : 0 < c) (hτ : 1 / 3 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ r ∈ tailSource N c τ, N < r ^ 3 := by
  have hcut := tendsto_natCast_atTop_atTop.eventually
    (eventually_power_le_tail_cutoff c (1 / 3) τ hc hτ)
  filter_upwards [hcut] with N hN r hr
  have hlt : (N : ℝ) ^ (1 / 3 : ℝ) < r := hN.trans_lt (mem_tailSource.mp hr).2.2.1
  have hh : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) < (r : ℝ) ^ (3 : ℕ) := by
    gcongr
  rw [cube_third_rpow _ (Nat.cast_nonneg N)] at hh
  exact_mod_cast hh

def originalTailExceptionBudget (N : ℕ) : ℕ :=
  (⌊Real.sqrt N⌋₊ + 1) * (⌊(N : ℝ) ^ (1 / 3 : ℝ)⌋₊ + 1) +
    (⌊Real.sqrt N⌋₊ + 1)

theorem originalTailExceptionBudget_le {N : ℕ} (hN : 1 ≤ N) :
    (originalTailExceptionBudget N : ℝ) ≤ 6 * (N : ℝ) ^ (5 / 6 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hs1 : 1 ≤ Real.sqrt N := by
    simpa using Real.sqrt_le_sqrt hN1
  have hc1 : 1 ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow hN1 (by norm_num)
  have hs := Nat.floor_le (Real.sqrt_nonneg (N : ℝ))
  have hc := Nat.floor_le (Real.rpow_nonneg hN0.le (1 / 3 : ℝ))
  have hleft : (⌊Real.sqrt N⌋₊ : ℝ) + 1 ≤ 2 * Real.sqrt N := by linarith
  have hright : (⌊(N : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) + 2 ≤
      3 * (N : ℝ) ^ (1 / 3 : ℝ) := by linarith
  calc
    (originalTailExceptionBudget N : ℝ) =
        ((⌊Real.sqrt N⌋₊ : ℝ) + 1) * ((⌊(N : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) + 2) := by
      simp only [originalTailExceptionBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring
    _ ≤ (2 * Real.sqrt N) * (3 * (N : ℝ) ^ (1 / 3 : ℝ)) :=
      mul_le_mul hleft hright (by positivity) (by positivity)
    _ = 6 * (N : ℝ) ^ (5 / 6 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      have heq : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) =
          (N : ℝ) ^ (5 / 6 : ℝ) := by
        rw [← Real.rpow_add hN0]
        norm_num
      nlinarith [heq]

theorem eventually_originalTailExceptionBudget_paid (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (originalTailExceptionBudget N : ℝ) ≤
        ε * liuSingularSeries N * N / Real.log N ^ 2 := by
  have hlog := (isLittleO_log_rpow_rpow_atTop 3
    (show (0 : ℝ) < 1 / 6 by norm_num)).bound (show (0 : ℝ) < 1 by norm_num)
  have hlarge : ∀ᶠ x : ℝ in atTop,
      6 * x ^ (5 / 6 : ℝ) ≤ 6 * x / Real.log x ^ (3 : ℝ) := by
    filter_upwards [hlog, eventually_ge_atTop (2 : ℝ)] with x hl hx
    have hx0 : 0 < x := by linarith
    have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
    have hl3 : Real.log x ^ (3 : ℝ) ≤ x ^ (1 / 6 : ℝ) := by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hl0.le _),
        abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] using hl
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hl0 3)).mpr
    calc
      (6 * x ^ (5 / 6 : ℝ)) * Real.log x ^ (3 : ℝ) ≤
          (6 * x ^ (5 / 6 : ℝ)) * x ^ (1 / 6 : ℝ) := by gcongr
      _ = 6 * x := by
        rw [mul_assoc, ← Real.rpow_add hx0]
        norm_num
  have hlargeN := tendsto_natCast_atTop_atTop.eventually hlarge
  have hpay := tendsto_natCast_atTop_atTop.eventually
    (eventually_logCube_le_singular_margin 6 ε hε)
  filter_upwards [hlargeN, hpay, eventually_ge_atTop (1 : ℕ)] with N hl hp hN
  exact (originalTailExceptionBudget_le hN).trans (hl.trans (hp N))

/-- The literal original quotient-sieve sum, with the unchanged `c*N^tau`
cutoff. The internal switched-sieve exponent does not occur in the conclusion. -/
theorem tailOriginalSum_sharp_upper (c τ η ε : ℝ) (hc : 0 < c)
    (hτ : 1 / 3 < τ) (hτh : τ < 1 / 2) (hη : 0 < η) (hηh : η < 1 / 2)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      (tailOriginalSum N c τ η : ℝ) ≤
        (8 * (∫ u in τ..(1 / 2 : ℝ), 1 / (u * (1 - u))) + ε) *
          liuSingularSeries N * N / Real.log N ^ 2 := by
  obtain ⟨B, hB, M, hM⟩ := tailSiftedCount_sharp_upper c τ η (ε / 2)
    hc hτ hτh hη (by linarith) (by positivity)
  obtain ⟨R, _, hR⟩ := tail_real_sieve_cutoff_separation 1 (1 / 3)
    (by norm_num) (by norm_num)
  have hRlarge : ∀ᶠ N : ℕ in atTop, R ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R)
  refine eventually_atTop.mp ?_
  filter_upwards [eventually_tailSource_cube c τ hc hτ,
    eventually_originalTailExceptionBudget_paid (ε / 2) (by positivity),
    hRlarge, eventually_ge_atTop M] with N hcube hpay hNR hNM hEven
  let z := Real.sqrt (Real.sqrt N / Real.log N ^ B)
  have hz : z ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    simpa only [one_mul] using hR N hNR B hB.le _ le_rfl
  have hfinite := tailOriginalSum_le_sifted_add_rectangle hη
    (Real.rpow_nonneg (Nat.cast_nonneg N) (1 / 3 : ℝ))
    (cube_third_rpow (N : ℝ) (Nat.cast_nonneg N)).ge hz hcube
  have hbound : (tailOriginalSum N c τ η : ℝ) ≤
      (tailSiftedCount N c τ η z : ℝ) + originalTailExceptionBudget N := by
    have hh : tailOriginalSum N c τ η ≤
        tailSiftedCount N c τ η z + originalTailExceptionBudget N := by
      simpa only [originalTailExceptionBudget, Nat.add_assoc] using hfinite
    exact_mod_cast hh
  calc
    _ ≤ _ := hbound
    _ ≤ (8 * (∫ u in τ..(1 / 2 : ℝ), 1 / (u * (1 - u))) + ε / 2) *
        liuSingularSeries N * N / Real.log N ^ 2 +
        (ε / 2) * liuSingularSeries N * N / Real.log N ^ 2 :=
      add_le_add (hM N hNM hEven) hpay
    _ = _ := by ring

end
end Wu2004MeanValue

import MathlibNt.SieveTheory.SwitchingPrinciple

/-!
# The triple main-term estimate (`hTripleMain`)

This file proves the structural reduction for the triple main-term estimate

    Σ_{p₁ ∈ [z,y)} Σ_{p₂ ∈ [y,N]} switchingCount N (p₁·p₂) ≤ cₘ·𝔖_trunc·N/log²N

from an explicit prime-pair hypothesis.
Here switchingCount N a = #{p ∈ C(N) : a·p₃ = N−p, p₃ prime} is a
twin-prime-type count requiring both p₃ and p = N−a·p₃ to be prime.
The required analytic upper bound, of the type arising in Chen's method and
Bombieri-Vinogradov distribution estimates, is stated as the proposition
`ChenPrimePairInput`. The remaining steps are proved here:

  1. Region reduction: p ∈ C(N) implies that N−p has no prime factor < z,
     so p₃ ≥ z and the effective region is p₁p₂ ≤ N/z, not merely 2p₁p₂ ≤ N.
     This gives log(N/(p₁p₂)) ≥ log z, a lower bound proportional to log N
     that is essential for the correct triple main-term scale.
  2. Apply the input pairwise:
     switchingCount ≤ C·(N/φ(p₁p₂))/(log N·log(N/(p₁p₂))).
  3. Use φ(p₁p₂) ≥ p₁p₂/4 for primes p₁,p₂ ≥ 2 and
     1/log(N/(p₁p₂)) ≤ 1/log z.
  4. Bound the double prime-reciprocal sum by a constant using
     `AnalyticNumberTheory.Sieve.primeReciprocal_doubleSum_le`.
  5. Estimate the parameters: log z ≥ (1/20)log N,
     log y ≤ log 2 + (1/3)log N, and related bounds.
  6. Absorb constants using 𝔖_trunc ≥ 1/2
     (`singularSeriesTruncated_ge_half`).

Thus `ChenPrimePairInput` implies the existence of cₘ and N₀ₘ satisfying
`hTripleMain`. This supplies the triple main-term hypothesis of
`corrected_chens_theorem_of_q1Count_and_triple`; the Pan, q¹, and numerical
hypotheses remain explicit in the final conditional theorem.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset

open scoped Classical

/-! ## 1. Analytic input: a prime-pair bound (Chen's method / BV scale) -/

/-- Prime-pair input: the analytic core of `hTripleMain`.

For positive a, switchingCount N a = #{p ∈ C(N) : ∃p₃ prime, a·p₃ = N−p}
counts p₃ for which p₃ and p = N−a·p₃ are prime
(membership in C(N) implies that p is prime). This is a count of prime pairs
in two linear forms. The input requires a uniform upper bound of the form
used in Chen's method, Bombieri-Vinogradov estimates, and the linear sieve
for two linear forms, with the singular series and local factors absorbed
into the constant C:

    switchingCount N a ≤ C · (N/φ(a)) · 1/(log N · log(N/a)),  (1 ≤ a, 2a ≤ N)

The motivating classical estimate has the shape
#{p₃ ≤ X : p₃, N−ap₃ prime} ≤ C·(a/φ(a))·X/(log X·log N), with X = N/a.
This is the only additional analytic input to the triple main-term reduction;
a Pan-distribution or prime-pair argument must supply it separately.
Prime-counting upper bounds and Mertens estimates alone give only the
N/log N scale: they lack the extra 1/log N factor from the primality of p
and do not reach N/log²N. See the module introduction. -/
def ChenPrimePairInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N a : ℕ, 1 ≤ a → 2 * a ≤ N →
    (switchingCount N a : ℝ) ≤
      C * (N : ℝ) / (Nat.totient a : ℝ) /
        (log (N : ℝ) * log ((N : ℝ) / (a : ℝ)))

/-! ## 2. Region reduction: p₃ ≥ z and p₁p₂ ≤ N/z -/

/-- If a·z > N (equivalently, N < z·a), then switchingCount N a = 0.

Proof: suppose p ∈ C(N), a·p₃ = N−p, and p₃ is prime. The condition defining
C(N) says that N−p = a·p₃ has no prime factor < z. If p₃ < z, it would be
such a factor, a contradiction. Hence p₃ ≥ z, so
a·p₃ ≥ a·z > N ≥ N−p, contradicting a·p₃ = N−p. -/
theorem switchingCount_eq_zero_of_N_lt_z_mul (N a : ℕ)
    (haz : N < correctedChenZ N * a) :
    switchingCount N a = 0 := by
  unfold switchingCount
  have hsub : (correctedChenCandidates N).filter
      (fun p => ∃ p₃ : ℕ, p₃.Prime ∧ a * p₃ = N - p) = ∅ := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp
      rcases hp with ⟨hpC, hpw⟩
      rcases hpw with ⟨p₃, hp₃p, hprod⟩
      have hpC' : p.Prime ∧ 2 ≤ N - p ∧
          ∀ r : ℕ, r.Prime → r < correctedChenZ N → ¬ r ∣ N - p := by
        unfold correctedChenCandidates at hpC
        exact (Finset.mem_filter.mp hpC).2
      have hp₃z : correctedChenZ N ≤ p₃ := by
        by_contra hlt
        have hp₃lt : p₃ < correctedChenZ N := Nat.lt_of_not_ge hlt
        have hp₃dvd : p₃ ∣ N - p := by
          rw [← hprod]
          exact dvd_mul_left p₃ a
        exact hpC'.2.2 p₃ hp₃p hp₃lt hp₃dvd
      have hbig : N < a * p₃ := by
        calc
          N < correctedChenZ N * a := haz
          _ ≤ a * p₃ := by
            have hmul : correctedChenZ N * a ≤ p₃ * a :=
              Nat.mul_le_mul_right a hp₃z
            simpa [mul_comm] using hmul
      have hle : a * p₃ ≤ N := by
        rw [hprod]
        exact Nat.sub_le N p
      omega
    · intro hp
      simp at hp
  rw [hsub]
  simp

/-- Reduction of the triple main term to the z-region: contributing pairs
satisfy z·(p₁p₂) ≤ N; all other pairs contribute zero by
`switchingCount_eq_zero_of_N_lt_z_mul`.
This region gives N/(p₁p₂) ≥ z and hence log(N/(p₁p₂)) ≥ log z,
the lower bound needed for the N/log²N scale of the triple main term. -/
theorem switchingCount_sum_eq_z_region (N : ℕ) :
    (∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
      ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
        (switchingCount N (p₁ * p₂) : ℝ)) =
    (∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
      ∑ p₂ ∈ ((Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂)).filter
          (fun p₂ => correctedChenZ N * (p₁ * p₂) ≤ N),
        (switchingCount N (p₁ * p₂) : ℝ)) := by
  apply Finset.sum_congr rfl
  intro p₁ hp₁
  symm
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂))
    (fun p₂ => correctedChenZ N * (p₁ * p₂) ≤ N) (fun p₂ => switchingCount N (p₁ * p₂))]
  have hnot : (∑ p₂ ∈ (((Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂)).filter
      (fun p₂ => ¬ correctedChenZ N * (p₁ * p₂) ≤ N)), switchingCount N (p₁ * p₂)) = 0 := by
    apply Finset.sum_eq_zero
    intro p₂ hp₂
    have hp₂' : ¬ correctedChenZ N * (p₁ * p₂) ≤ N := (Finset.mem_filter.mp hp₂).2
    have hlt : N < correctedChenZ N * (p₁ * p₂) := by omega
    exact switchingCount_eq_zero_of_N_lt_z_mul N (p₁ * p₂) hlt
  rw [hnot]
  simp

/-! ## 3. φ(p₁p₂) ≥ p₁p₂/4 -/

/-- Totient lower bound for a product of two primes (each ≥ 2): φ(p₁p₂) ≥ p₁p₂/4.

If p₁ = p₂, then φ(p²) = p(p−1) ≥ p²/2 ≥ p²/4.
If p₁ ≠ p₂, they are coprime, and
φ(p₁p₂) = (p₁−1)(p₂−1) ≥ (p₁/2)(p₂/2) = p₁p₂/4. -/
theorem totient_mul_prime_ge_quarter {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) :
    (p₁ * p₂ : ℝ) / 4 ≤ (Nat.totient (p₁ * p₂) : ℝ) := by
  have hp₁2 : 2 ≤ p₁ := hp₁.two_le
  have hp₂2 : 2 ≤ p₂ := hp₂.two_le
  by_cases h : p₁ = p₂
  · subst p₂
    have hφ : Nat.totient (p₁ * p₁) = p₁ * (p₁ - 1) := by
      have hpp : Nat.totient (p₁ ^ 2) = p₁ ^ (2 - 1) * (p₁ - 1) :=
        Nat.totient_prime_pow hp₁ (by norm_num : 0 < 2)
      simpa [pow_two] using hpp
    rw [hφ]
    norm_num [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p₁)]
    have hle : (p₁ : ℝ) * (p₁ : ℝ) / 4 ≤ (p₁ : ℝ) * ((p₁ : ℝ) - 1) := by
      have h2 : (2 : ℝ) ≤ p₁ := by exact_mod_cast hp₁2
      have hh : (p₁ : ℝ) / 2 ≤ (p₁ : ℝ) - 1 := by linarith
      nlinarith
    simpa [pow_two] using hle
  · have hcop : Nat.Coprime p₁ p₂ := (Nat.coprime_primes hp₁ hp₂).2 h
    have hφ : Nat.totient (p₁ * p₂) = (p₁ - 1) * (p₂ - 1) := by
      rw [Nat.totient_mul hcop]
      simp [Nat.totient_prime hp₁, Nat.totient_prime hp₂]
    rw [hφ]
    norm_num [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p₁),
      Nat.cast_sub (by omega : 1 ≤ p₂)]
    have h₁ : (p₁ : ℝ) / 2 ≤ (p₁ : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ p₁ := by exact_mod_cast hp₁2
      linarith
    have h₂ : (p₂ : ℝ) / 2 ≤ (p₂ : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ p₂ := by exact_mod_cast hp₂2
      linarith
    have hmul : ((p₁ : ℝ) / 2) * ((p₂ : ℝ) / 2) ≤ ((p₁ : ℝ) - 1) * ((p₂ : ℝ) - 1) :=
      mul_le_mul h₁ h₂ (by positivity) (by linarith)
    nlinarith [hmul]

/-- Real-valued reciprocal form: 1/φ(p₁p₂) ≤ 4/(p₁p₂). -/
theorem one_div_totient_mul_prime_le (p₁ p₂ : ℕ) (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) :
    (1 : ℝ) / (Nat.totient (p₁ * p₂) : ℝ) ≤ 4 / (p₁ * p₂ : ℝ) := by
  have ht : (p₁ * p₂ : ℝ) / 4 ≤ (Nat.totient (p₁ * p₂) : ℝ) :=
    totient_mul_prime_ge_quarter hp₁ hp₂
  have hφpos : 0 < (Nat.totient (p₁ * p₂) : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos hp₁.pos hp₂.pos))
  have hprod : 0 < (p₁ * p₂ : ℝ) := by
    exact_mod_cast (Nat.mul_pos hp₁.pos hp₂.pos)
  rw [div_le_div_iff₀ hφpos hprod]
  nlinarith [ht]/-! ## 4. Parameter estimates (logarithmic bounds) -/

/-- z = max 2 ⌊N^{1/10}⌋ ≥ N^{1/10}/2 for N > 2^110. -/
theorem correctedChenZ_ge_root_half (N : ℕ) (hNbig : 2 ^ 110 < N) :
    (N : ℝ) ^ (1 / 10 : ℝ) / 2 ≤ correctedChenZ N := by
  exact Internal.chenZ_ge_root_half N hNbig

/-- log N ≥ 110·log 2 for N > 2^110. -/
theorem log_ge_110_log_two {N : ℕ} (hNbig : 2 ^ 110 < N) :
    (110 : ℝ) * log 2 ≤ log (N : ℝ) := by
  have hNcast : ((2 ^ 110 : ℕ) : ℝ) < (N : ℝ) := by exact_mod_cast hNbig
  have hlog2 : log ((2 ^ 110 : ℕ) : ℝ) ≤ log (N : ℝ) := by
    apply Real.log_le_log (by positivity : 0 < ((2 ^ 110 : ℕ) : ℝ))
    exact le_of_lt hNcast
  have hrew : log ((2 ^ 110 : ℕ) : ℝ) = (110 : ℝ) * log 2 := by
    rw [Nat.cast_pow]
    rw [Real.log_pow]
    norm_num
  rwa [hrew] at hlog2

/-- log z ≥ (1/20)·log N for N > 2^110. -/
theorem correctedChenZ_log_ge_logN_div_twenty (N : ℕ) (hNbig : 2 ^ 110 < N) :
    (1 / 20 : ℝ) * log (N : ℝ) ≤ log (correctedChenZ N : ℝ) := by
  have hz := correctedChenZ_ge_root_half N hNbig
  have hlogz : log ((N : ℝ) ^ (1 / 10 : ℝ) / 2) ≤ log (correctedChenZ N : ℝ) := by
    apply Real.log_le_log (by positivity : 0 < (N : ℝ) ^ (1 / 10 : ℝ) / 2)
    exact hz
  have hrew : log ((N : ℝ) ^ (1 / 10 : ℝ) / 2) = (1 / 10 : ℝ) * log (N : ℝ) - log 2 := by
    rw [Real.log_div (by positivity : (N : ℝ) ^ (1 / 10 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    rw [Real.log_rpow (by positivity : 0 < (N : ℝ))]
  have hlogz' : (1 / 10 : ℝ) * log (N : ℝ) - log 2 ≤ log (correctedChenZ N : ℝ) := by
    rwa [hrew] at hlogz
  have hNpos : 0 < log (N : ℝ) := by
    have hN1 : (1 : ℝ) < N := by
      have hN2 : 2 ≤ N := by
        have : 2 ≤ 2 ^ 110 := by norm_num
        omega
      exact_mod_cast (show 1 < N by omega)
    exact Real.log_pos hN1
  have hlogN := log_ge_110_log_two hNbig
  have h20 : log 2 ≤ (1 / 20 : ℝ) * log (N : ℝ) := by
    -- 110·log2 ≤ logN ⟹ log2 ≤ (1/110)·logN ≤ (1/20)·logN
    have hstep : log 2 ≤ (1 / 110 : ℝ) * log (N : ℝ) := by
      nlinarith [hlogN]
    have hm : (1 / 110 : ℝ) ≤ (1 / 20 : ℝ) := by norm_num
    have hstep2 : (1 / 110 : ℝ) * log (N : ℝ) ≤ (1 / 20 : ℝ) * log (N : ℝ) := by
      exact mul_le_mul_of_nonneg_right hm (le_of_lt hNpos)
    linarith
  have h20' : (1 / 20 : ℝ) * log (N : ℝ) ≤ (1 / 10 : ℝ) * log (N : ℝ) - log 2 := by
    nlinarith [h20]
  exact le_trans h20' hlogz'

/-- y ≤ 2·N^{1/3}, using the ceiling upper bound. -/
theorem correctedChenY_le_two_mul_root (N : ℕ) (hN : 1 ≤ N) :
    (correctedChenY N : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 3 : ℝ) := by
  unfold correctedChenY
  have hcu : (Nat.ceil ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) + 1 := by
    have hc := Nat.ceil_le_floor_add_one ((N : ℝ) ^ (1 / 3 : ℝ))
    have hfl := Nat.floor_le (by positivity : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    have hc' : (Nat.ceil ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        (Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) + 1 := by exact_mod_cast hc
    linarith
  have hN13 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  linarith

/-- log y ≤ log 2 + (1/3)·log N. -/
theorem correctedChenY_log_le (N : ℕ) (hN : 1 ≤ N) :
    log (correctedChenY N : ℝ) ≤ log 2 + (1 / 3 : ℝ) * log (N : ℝ) := by
  have hy := correctedChenY_le_two_mul_root N hN
  have hypos : 0 < (correctedChenY N : ℝ) := by
    have hle : (1 : ℝ) ≤ (correctedChenY N : ℝ) := by
      have h13 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
        Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
      calc
        (1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := h13
        _ ≤ (correctedChenY N : ℝ) := by
          unfold correctedChenY
          exact Nat.le_ceil ((N : ℝ) ^ (1 / 3 : ℝ))
    linarith
  have hlogy : log (correctedChenY N : ℝ) ≤ log (2 * (N : ℝ) ^ (1 / 3 : ℝ)) := by
    exact Real.log_le_log hypos hy
  have hrew : log (2 * (N : ℝ) ^ (1 / 3 : ℝ)) = log 2 + (1 / 3 : ℝ) * log (N : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (N : ℝ) ^ (1 / 3 : ℝ) ≠ 0)]
    rw [Real.log_rpow (by positivity : 0 < (N : ℝ))]
  rwa [hrew] at hlogy

/-- log y ≥ (1/3)·log N, from y³ ≥ N. -/
theorem correctedChenY_log_ge (N : ℕ) (hN : 1 ≤ N) :
    (1 / 3 : ℝ) * log (N : ℝ) ≤ log (correctedChenY N : ℝ) := by
  have hcube := correctedChen_cube_scale N
  have hlog : log (N : ℝ) ≤ log ((correctedChenY N : ℝ) ^ 3) := by
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) hcube
  have hrew : log ((correctedChenY N : ℝ) ^ 3) = 3 * log (correctedChenY N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  have hlog' : log (N : ℝ) ≤ 3 * log (correctedChenY N : ℝ) := by
    rwa [hrew] at hlog
  nlinarith

/-- y ≤ N for N ≥ 8. -/
theorem correctedChenY_le_N {N : ℕ} (hN : 8 ≤ N) : correctedChenY N ≤ N := by
  have hN1 : 1 ≤ N := by omega
  have hy := correctedChenY_le_two_mul_root N hN1
  have hroot : 2 * (N : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) := by
    have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast hN
    have hpow := Real.rpow_le_rpow (by norm_num : 0 ≤ (8 : ℝ)) hN8
      (by norm_num : 0 ≤ (1 / 3 : ℝ))
    have hval : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
      norm_num [Real.rpow_natCast, Real.rpow_mul, Real.rpow_one]
    have hx2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by rwa [hval] at hpow
    let x : ℝ := (N : ℝ) ^ (1 / 3 : ℝ)
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hx2' : (2 : ℝ) ≤ x := by simpa [x] using hx2
    have hcube : x ^ 3 = (N : ℝ) := by
      dsimp [x]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by positivity : 0 ≤ (N : ℝ))]
      norm_num
    have h2x : 2 * x ≤ x ^ 3 := by
      have h1 : 2 * x ≤ x * x := by nlinarith
      have hx1 : (1 : ℝ) ≤ x := by linarith
      have h2 : x * x ≤ x * x * x := by nlinarith
      linarith
    calc
      2 * (N : ℝ) ^ (1 / 3 : ℝ) = 2 * x := by rfl
      _ ≤ x ^ 3 := h2x
      _ = (N : ℝ) := hcube
  exact_mod_cast (le_trans hy hroot)

/-- Parameter bound: z ≥ 3 for N ≥ 59049. -/
theorem correctedChenZ_ge_three {N : ℕ} (hN : 59049 ≤ N) : 3 ≤ correctedChenZ N := by
  have hz2 := correctedChenZ_sub_one_ge_two_of_large hN
  omega

/-- Parameter bound: z < y for N ≥ 9. -/
theorem correctedChenZ_lt_Y {N : ℕ} (hN : 9 ≤ N) : correctedChenZ N < correctedChenY N := by
  exact (correctedChen_cutoffValid_of_nine_le hN).1
/-! ## 5. Logarithmic parameter bounds for `hTripleMain` -/

/-- 1/log z ≤ 20/log N for N > 2^110. -/
theorem hTripleMain_one_div_log_z_le (N : ℕ) (hNbig : 2 ^ 110 < N) :
    (1 : ℝ) / log (correctedChenZ N : ℝ) ≤ 20 / log (N : ℝ) := by
  have hlogz := correctedChenZ_log_ge_logN_div_twenty N hNbig
  have hz3 : 3 ≤ correctedChenZ N := by
    have h59049 : 59049 ≤ N := by
      have : 59049 < 2 ^ 110 := by norm_num
      exact le_trans (le_of_lt this) (le_of_lt hNbig)
    exact correctedChenZ_ge_three h59049
  have hz1 : (1 : ℝ) < correctedChenZ N := by
    have hz3r : (3 : ℝ) ≤ correctedChenZ N := by exact_mod_cast hz3
    linarith
  have hlogzpos : 0 < log (correctedChenZ N : ℝ) := Real.log_pos hz1
  have hN1 : (1 : ℝ) < N := by
    have hN2 : 2 ≤ N := by
      have : 2 < 2 ^ 110 := by norm_num
      omega
    exact_mod_cast (show 1 < N by omega)
  have hlogNpos : 0 < log (N : ℝ) := Real.log_pos hN1
  rw [div_le_div_iff₀ hlogzpos hlogNpos]
  -- log N ≤ 20·log z ⟸ (1/20)·log N ≤ log z
  nlinarith [hlogz]

/-- log y/log z ≤ 7 for N > 2^110. -/
theorem hTripleMain_log_y_div_log_z_le (N : ℕ) (hNbig : 2 ^ 110 < N) :
    log (correctedChenY N : ℝ) / log (correctedChenZ N : ℝ) ≤ 7 := by
  have hN1n : 1 ≤ N := by
    have : 1 < 2 ^ 110 := by norm_num
    omega
  have hlogy := correctedChenY_log_le N hN1n
  have hlogz := correctedChenZ_log_ge_logN_div_twenty N hNbig
  have hlogN := log_ge_110_log_two hNbig
  have hlog2pos : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogzpos : 0 < log (correctedChenZ N : ℝ) := by
    linarith only [hlogz, hlogN, hlog2pos]
  rw [div_le_iff₀ hlogzpos]
  linarith only [hlogy, hlogz, hlogN, hlog2pos]

/-- log N/log y ≤ 3 for N ≥ 8. -/
theorem hTripleMain_log_N_div_log_y_le (N : ℕ) (hN : 8 ≤ N) :
    log (N : ℝ) / log (correctedChenY N : ℝ) ≤ 3 := by
  have hN1n : 1 ≤ N := by omega
  have hlogy := correctedChenY_log_ge N hN1n
  have hlogNpos : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hypos : 0 < log (correctedChenY N : ℝ) := by
    linarith only [hlogy, hlogNpos]
  rw [div_le_iff₀ hypos]
  linarith only [hlogy]
/-! ## 6. Main theorem: `hTripleMain` -/

/-- Pairwise bound: in the z-region, the input implies the upper bound
C·(4/a)·(N/(log N·log z)), where a = p₁p₂. -/
theorem hTripleMain_pair_bound {C : ℝ} {N p₁ p₂ : ℕ} (hC : 0 ≤ C)
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime)
    (hza : correctedChenZ N * (p₁ * p₂) ≤ N)
    (hin : (switchingCount N (p₁ * p₂) : ℝ) ≤
      C * (N : ℝ) / (Nat.totient (p₁ * p₂) : ℝ) /
        (log (N : ℝ) * log ((N : ℝ) / (p₁ * p₂ : ℝ)))) :
    (switchingCount N (p₁ * p₂) : ℝ) ≤
      C * (4 / (p₁ * p₂ : ℝ)) * ((N : ℝ) / (log (N : ℝ) * log (correctedChenZ N : ℝ))) := by
  let z : ℕ := correctedChenZ N
  let a : ℕ := p₁ * p₂
  have hz2 : 2 ≤ z := by
    dsimp [z]
    unfold correctedChenZ
    exact le_max_left _ _
  have ha1 : 1 ≤ a := by
    dsimp [a]
    have hp₁1 : 1 ≤ p₁ := le_trans (by norm_num : (1 : ℕ) ≤ 2) hp₁.two_le
    have hp₂1 : 1 ≤ p₂ := le_trans (by norm_num : (1 : ℕ) ≤ 2) hp₂.two_le
    exact le_trans (by norm_num : (1 : ℕ) ≤ 1 * 1) (Nat.mul_le_mul hp₁1 hp₂1)
  have hapos : 0 < (a : ℝ) := by
    dsimp [a]
    exact_mod_cast (Nat.mul_pos hp₁.pos hp₂.pos)
  have hlogNpos : 0 < log (N : ℝ) := by
    have hN2 : 2 ≤ N := by
      have hz2n : 2 ≤ correctedChenZ N := by
        unfold correctedChenZ
        exact le_max_left _ _
      have h2a : 2 * a ≤ N := by
        dsimp [a]
        exact le_trans (Nat.mul_le_mul_right (p₁ * p₂) hz2n) hza
      omega
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    exact Real.log_pos hN1
  have hlogzpos : 0 < log (z : ℝ) := by
    have hz1 : (1 : ℝ) < z := by
      have hz2r : (2 : ℝ) ≤ z := by exact_mod_cast hz2
      linarith
    exact Real.log_pos hz1
  have hNa : (z : ℝ) ≤ (N : ℝ) / (a : ℝ) := by
    have hza' : (z : ℝ) * (a : ℝ) ≤ (N : ℝ) := by
      dsimp [z, a]
      rw [← Nat.cast_mul]
      exact_mod_cast hza
    rw [le_div_iff₀ hapos]
    exact hza'
  have hlogNa_pos : 0 < log ((N : ℝ) / (a : ℝ)) := by
    have harg : (1 : ℝ) < (N : ℝ) / (a : ℝ) := by
      have hz2r : (2 : ℝ) ≤ z := by exact_mod_cast hz2
      linarith
    exact Real.log_pos harg
  have hlogzle : log (z : ℝ) ≤ log ((N : ℝ) / (a : ℝ)) :=
    Real.log_le_log (by positivity : 0 < (z : ℝ)) hNa
  have hmain : C * (N : ℝ) / (Nat.totient a : ℝ) /
      (log (N : ℝ) * log ((N : ℝ) / (a : ℝ))) ≤
      C * (4 / (a : ℝ)) * ((N : ℝ) / (log (N : ℝ) * log (z : ℝ))) := by
    calc
      C * (N : ℝ) / (Nat.totient a : ℝ) / (log (N : ℝ) * log ((N : ℝ) / (a : ℝ)))
          = (C * (N : ℝ)) * ((1 : ℝ) / (Nat.totient a : ℝ)) * (1 / log ((N : ℝ) / (a : ℝ))) * (1 / log (N : ℝ)) := by ring
      _ ≤ (C * (N : ℝ)) * (4 / (a : ℝ)) * (1 / log (z : ℝ)) * (1 / log (N : ℝ)) := by
            have hφinv : (1 : ℝ) / (Nat.totient a : ℝ) ≤ 4 / (a : ℝ) := by
              simpa [a, Nat.cast_mul] using one_div_totient_mul_prime_le p₁ p₂ hp₁ hp₂
            have hloginv : (1 : ℝ) / log ((N : ℝ) / (a : ℝ)) ≤ 1 / log (z : ℝ) := by
              rw [div_le_div_iff₀ hlogNa_pos hlogzpos]
              simpa using hlogzle
            have hprod2 : (1 : ℝ) / (Nat.totient a : ℝ) * (1 / log ((N : ℝ) / (a : ℝ))) ≤
                (4 / (a : ℝ)) * (1 / log (z : ℝ)) := by
              exact mul_le_mul hφinv hloginv (by positivity) (by positivity)
            have hnonneg : 0 ≤ (C * (N : ℝ)) * (1 / log (N : ℝ)) := by positivity
            simpa only [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_right hprod2 hnonneg
      _ = C * (4 / (a : ℝ)) * ((N : ℝ) / (log (N : ℝ) * log (z : ℝ))) := by ring
  exact le_trans hin (by simpa [a, z] using hmain)

/-- **The prime-pair input implies `hTripleMain`**, in existential form.

`ChenPrimePairInput` gives a pairwise upper bound on `switchingCount`.
Combining the region reduction (`switchingCount_sum_eq_z_region`),
the totient bound, the double reciprocal-sum bound from
`AnalyticNumberTheory.Sieve`, and the logarithmic parameter bounds gives
cₘ = 160·C·(log 7+E)(log 3+E) and N₀ₘ = 2^220.
Here C comes from the input and E from `primeReciprocal_doubleSum_le`.
The bound 𝔖_trunc ≥ 1/2 absorbs a factor of 2. -/
theorem hTripleMain_of_primePairInput (hPP : ChenPrimePairInput) :
    ∃ cₘ : ℝ, ∃ N₀ₘ : ℕ, ∀ N : ℕ, N₀ₘ ≤ N → Even N →
      (∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
        ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
          (switchingCount N (p₁ * p₂) : ℝ)) ≤
        cₘ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 := by
  rcases hPP with ⟨C, hC, hPP'⟩
  rcases AnalyticNumberTheory.Mertens.primeReciprocal_doubleSum_le with ⟨E, hE, hDS⟩
  let cₘ : ℝ := 160 * C * (log 7 + E) * (log 3 + E)
  let N₀ₘ : ℕ := 2 ^ 220
  refine ⟨cₘ, N₀ₘ, ?_⟩
  intro N hN hEven
  let z : ℕ := correctedChenZ N
  let y : ℕ := correctedChenY N
  let S₁ : Finset ℕ := (Finset.range y).filter (fun p₁ => p₁.Prime ∧ z ≤ p₁)
  let S₂ : Finset ℕ := (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ y ≤ p₂)
  have hNbig : 2 ^ 110 < N := by
    have : 2 ^ 110 < 2 ^ 220 := by norm_num
    exact lt_of_lt_of_le this hN
  have hN9 : 9 ≤ N := by
    have : 9 < 2 ^ 220 := by norm_num
    exact le_trans (le_of_lt this) hN
  have hz3 : 3 ≤ z := by
    dsimp [z]
    have h59049 : 59049 ≤ N := by
      have : 59049 < 2 ^ 220 := by norm_num
      exact le_trans (le_of_lt this) hN
    exact correctedChenZ_ge_three h59049
  have hzy : z < y := by
    dsimp [z, y]
    exact correctedChenZ_lt_Y hN9
  have hyN : y ≤ N := by
    dsimp [y]
    exact correctedChenY_le_N (by omega : 8 ≤ N)
  have hlogzpos : 0 < log (z : ℝ) := by
    have hz1 : (1 : ℝ) < z := by
      have hz3r : (3 : ℝ) ≤ z := by exact_mod_cast hz3
      linarith
    exact Real.log_pos hz1
  have hlogNpos : 0 < log (N : ℝ) := by
    have hN1 : (1 : ℝ) < N := by
      have hN2 : 2 ≤ N := by
        have : 2 < 2 ^ 220 := by norm_num
        omega
      exact_mod_cast (show 1 < N by omega)
    exact Real.log_pos hN1
  have hlogypos : 0 < log (y : ℝ) := by
    have hy1 : (1 : ℝ) < y := by
      have hz1 : (1 : ℝ) < z := by
        have hz3r : (3 : ℝ) ≤ z := by exact_mod_cast hz3
        linarith
      have hzyr : (z : ℝ) < (y : ℝ) := by exact_mod_cast hzy
      linarith
    exact Real.log_pos hy1
  have h1logz : (1 : ℝ) / log (z : ℝ) ≤ 20 / log (N : ℝ) := by
    dsimp [z]
    exact hTripleMain_one_div_log_z_le N hNbig
  have hlogy_logz : log (y : ℝ) / log (z : ℝ) ≤ 7 := by
    dsimp [z, y]
    exact hTripleMain_log_y_div_log_z_le N hNbig
  have hlogN_logy : log (N : ℝ) / log (y : ℝ) ≤ 3 := by
    dsimp [y]
    exact hTripleMain_log_N_div_log_y_le N (by omega : 8 ≤ N)
  have hlogy_logz_le : log (log (y : ℝ) / log (z : ℝ)) ≤ log 7 := by
    apply Real.log_le_log (by positivity : 0 < log (y : ℝ) / log (z : ℝ))
    exact hlogy_logz
  have hlogN_logy_le : log (log (N : ℝ) / log (y : ℝ)) ≤ log 3 := by
    apply Real.log_le_log (by positivity : 0 < log (N : ℝ) / log (y : ℝ))
    exact hlogN_logy
  -- Bound the double reciprocal sum.
  have hDS' : (∑ p₁ ∈ S₁, ∑ p₂ ∈ S₂, (1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ))) ≤
      (log (log (y : ℝ) / log (z : ℝ)) + E) * (log (log (N : ℝ) / log (y : ℝ)) + E) := by
    have hmain := hDS z y N (by dsimp [z]; exact hz3) (by dsimp [z, y]; exact (le_of_lt hzy)) (by dsimp [y]; exact hyN)
    -- For the sets in hmain, S₁ is contained in the p₁ set and S₂ is the p₂ set.
    let T₁ : Finset ℕ := (Finset.range (y + 1)).filter (fun p₁ => p₁.Prime ∧ z ≤ p₁)
    have hsub : S₁ ⊆ T₁ := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      rcases hp with ⟨hp1, hp2⟩
      exact ⟨by rw [Finset.mem_range]; have : p < y := Finset.mem_range.mp hp1; omega, hp2⟩
    have hle1 : (∑ p₁ ∈ S₁, ∑ p₂ ∈ S₂, (1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ))) ≤
        (∑ p₁ ∈ T₁, ∑ p₂ ∈ S₂, (1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hnot
      exact Finset.sum_nonneg (fun q hq => by positivity)
    have hle2 : (∑ p₁ ∈ T₁, ∑ p₂ ∈ S₂, (1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ))) =
        (∑ p₁ ∈ T₁, ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ y ≤ p₂),
          (1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ))) := by
      rfl
    rw [hle2] at hle1
    exact le_trans hle1 hmain
  -- Combine the estimates.
  calc
    (∑ p₁ ∈ S₁, ∑ p₂ ∈ S₂, (switchingCount N (p₁ * p₂) : ℝ))
        = (∑ p₁ ∈ S₁, ∑ p₂ ∈ (S₂.filter (fun p₂ => z * (p₁ * p₂) ≤ N)),
            (switchingCount N (p₁ * p₂) : ℝ)) := by
          dsimp [S₁, S₂, z]
          rw [switchingCount_sum_eq_z_region N]
    _ ≤ (∑ p₁ ∈ S₁, ∑ p₂ ∈ (S₂.filter (fun p₂ => z * (p₁ * p₂) ≤ N)),
            C * (4 / (p₁ * p₂ : ℝ)) * ((N : ℝ) / (log (N : ℝ) * log (z : ℝ)))) := by
          apply Finset.sum_le_sum
          intro p₁ hp₁
          apply Finset.sum_le_sum
          intro p₂ hp₂
          have hp₂mem : p₂ ∈ S₂ := (Finset.mem_filter.mp hp₂).1
          have hp₂z : z * (p₁ * p₂) ≤ N := (Finset.mem_filter.mp hp₂).2
          have hp₁p : p₁.Prime := (Finset.mem_filter.mp hp₁).2.1
          have hp₂p : p₂.Prime := (Finset.mem_filter.mp hp₂mem).2.1
          have ha1 : 1 ≤ p₁ * p₂ := by
            have hp₁1 : 1 ≤ p₁ := le_trans (by norm_num : (1 : ℕ) ≤ 2) hp₁p.two_le
            have hp₂1 : 1 ≤ p₂ := le_trans (by norm_num : (1 : ℕ) ≤ 2) hp₂p.two_le
            exact le_trans (by norm_num : (1 : ℕ) ≤ 1 * 1) (Nat.mul_le_mul hp₁1 hp₂1)
          have h2a : 2 * (p₁ * p₂) ≤ N := by
            have hz2 : 2 ≤ z := by
              dsimp [z]
              unfold correctedChenZ
              exact le_max_left _ _
            calc
              2 * (p₁ * p₂) ≤ z * (p₁ * p₂) := by
                exact Nat.mul_le_mul_right (p₁ * p₂) hz2
              _ ≤ N := hp₂z
          have hin := hPP' N (p₁ * p₂) ha1 h2a
          exact hTripleMain_pair_bound (le_of_lt hC) (p₁ := p₁) (p₂ := p₂) hp₁p hp₂p hp₂z
            (by simpa [Nat.cast_mul] using hin)
    _ = C * (4 * (∑ p₁ ∈ S₁, ∑ p₂ ∈ (S₂.filter (fun p₂ => z * (p₁ * p₂) ≤ N)),
            (1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ)))) * ((N : ℝ) / (log (N : ℝ) * log (z : ℝ))) := by
          let K : ℝ := (N : ℝ) / (log (N : ℝ) * log (z : ℝ))
          have hterm : ∀ p₁ ∈ S₁, ∀ p₂ ∈ S₂,
              C * (4 / ((p₁ : ℝ) * (p₂ : ℝ))) * K =
              (C * K * 4) * ((1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ))) := by
            intro p₁ hp₁ p₂ hp₂
            ring
          calc
            (∑ p₁ ∈ S₁, ∑ p₂ ∈ (S₂.filter (fun p₂ => z * (p₁ * p₂) ≤ N)),
                C * (4 / ((p₁ : ℝ) * (p₂ : ℝ))) * K)
                = (∑ p₁ ∈ S₁, ∑ p₂ ∈ (S₂.filter (fun p₂ => z * (p₁ * p₂) ≤ N)),
                    (C * K * 4) * ((1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ)))) := by
                  apply Finset.sum_congr rfl
                  intro p₁ hp₁
                  apply Finset.sum_congr rfl
                  intro p₂ hp₂
                  exact hterm p₁ hp₁ p₂ (Finset.mem_filter.mp hp₂).1
            _ = (C * K * 4) * (∑ p₁ ∈ S₁, ∑ p₂ ∈ (S₂.filter (fun p₂ => z * (p₁ * p₂) ≤ N)),
                    (1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ))) := by
                  rw [Finset.sum_congr rfl (fun p₁ hp₁ => by rw [← Finset.mul_sum])]
                  rw [← Finset.mul_sum]
            _ = C * (4 * (∑ p₁ ∈ S₁, ∑ p₂ ∈ (S₂.filter (fun p₂ => z * (p₁ * p₂) ≤ N)),
                    (1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ)))) * K := by
                  dsimp [K]
                  ring
    _ ≤ C * (4 * (∑ p₁ ∈ S₁, ∑ p₂ ∈ S₂, (1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ)))) *
            ((N : ℝ) / (log (N : ℝ) * log (z : ℝ))) := by
          -- For each p₁, the sum over the region is at most the full sum.
          have hstep : (∑ p₁ ∈ S₁, ∑ p₂ ∈ (S₂.filter (fun p₂ => z * (p₁ * p₂) ≤ N)),
                (1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ))) ≤
              (∑ p₁ ∈ S₁, ∑ p₂ ∈ S₂, (1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ))) := by
            apply Finset.sum_le_sum
            intro p₁ hp₁
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro p hp
              exact (Finset.mem_filter.mp hp).1
            · intro p hp hnot
              positivity
          have hnonneg : 0 ≤ C * 4 * ((N : ℝ) / (log (N : ℝ) * log (z : ℝ))) := by positivity
          have hmul := mul_le_mul_of_nonneg_left hstep hnonneg
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    _ ≤ C * (4 * ((log (log (y : ℝ) / log (z : ℝ)) + E) * (log (log (N : ℝ) / log (y : ℝ)) + E))) *
            ((N : ℝ) / (log (N : ℝ) * log (z : ℝ))) := by
          have hprod : 0 ≤ C * 4 * ((N : ℝ) / (log (N : ℝ) * log (z : ℝ))) := by positivity
          have hmul := mul_le_mul_of_nonneg_right hDS' hprod
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    _ ≤ cₘ * (1 / 2 : ℝ) * (N : ℝ) / (log (N : ℝ)) ^ 2 := by
          -- Parameter bounds: log(log y/log z) ≤ log 7, log(log N/log y) ≤ log 3, 1/log z ≤ 20/log N.
          have hlogy_logzE : log (log (y : ℝ) / log (z : ℝ)) + E ≤ log 7 + E := by linarith
          have hlogN_logyE : log (log (N : ℝ) / log (y : ℝ)) + E ≤ log 3 + E := by linarith
          have hNlogy_ge1 : (1 : ℝ) ≤ log (N : ℝ) / log (y : ℝ) := by
            have hle : log (y : ℝ) ≤ log (N : ℝ) := by
              apply Real.log_le_log (by exact_mod_cast (by omega : 0 < correctedChenY N))
              exact_mod_cast hyN
            rw [le_div_iff₀ hlogypos]
            simpa using hle
          have hlogargpos : 0 ≤ log (log (N : ℝ) / log (y : ℝ)) := by
            have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hNlogy_ge1
            simpa using h
          have hpos1 : 0 ≤ log (log (N : ℝ) / log (y : ℝ)) + E := by nlinarith [hE]
          have hlog7pos : 0 < log 7 := Real.log_pos (by norm_num : 1 < (7 : ℝ))
          have hpos2 : 0 ≤ log 7 + E := by nlinarith [hE]
          have hD : (log (log (y : ℝ) / log (z : ℝ)) + E) * (log (log (N : ℝ) / log (y : ℝ)) + E) ≤
              (log 7 + E) * (log 3 + E) := by
            exact mul_le_mul hlogy_logzE hlogN_logyE hpos1 hpos2
          have hfact : (N : ℝ) / (log (N : ℝ) * log (z : ℝ)) ≤ 20 * (N : ℝ) / (log (N : ℝ)) ^ 2 := by
            have hnonneg : 0 ≤ (N : ℝ) / log (N : ℝ) := by positivity
            have hm := mul_le_mul_of_nonneg_left h1logz hnonneg
            calc
              (N : ℝ) / (log (N : ℝ) * log (z : ℝ)) = (N : ℝ) / log (N : ℝ) * (1 / log (z : ℝ)) := by ring
              _ ≤ (N : ℝ) / log (N : ℝ) * (20 / log (N : ℝ)) := by
                    exact hm
              _ = 20 * (N : ℝ) / (log (N : ℝ)) ^ 2 := by
                    rw [pow_two]
                    ring
          have hstep1 : C * (4 * ((log (log (y : ℝ) / log (z : ℝ)) + E) * (log (log (N : ℝ) / log (y : ℝ)) + E))) *
                ((N : ℝ) / (log (N : ℝ) * log (z : ℝ))) ≤
              C * (4 * ((log 7 + E) * (log 3 + E))) * ((N : ℝ) / (log (N : ℝ) * log (z : ℝ))) := by
            have hnonneg : 0 ≤ C * ((N : ℝ) / (log (N : ℝ) * log (z : ℝ))) := by positivity
            have hh : (4 * ((log (log (y : ℝ) / log (z : ℝ)) + E) * (log (log (N : ℝ) / log (y : ℝ)) + E))) ≤
                (4 * ((log 7 + E) * (log 3 + E))) := by nlinarith [hD]
            have hmul := mul_le_mul_of_nonneg_right hh hnonneg
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
          have hstep2 : C * (4 * ((log 7 + E) * (log 3 + E))) * ((N : ℝ) / (log (N : ℝ) * log (z : ℝ))) ≤
              cₘ * (1 / 2 : ℝ) * (N : ℝ) / (log (N : ℝ)) ^ 2 := by
            have hnonneg : 0 ≤ 4 * C * (log 7 + E) * (log 3 + E) := by positivity
            have hmul := mul_le_mul_of_nonneg_right hfact hnonneg
            -- hmul: (N/(logN·logz))·(4CD') ≤ (20N/log²N)·(4CD')
            have hcₘ : cₘ * (1 / 2 : ℝ) * (N : ℝ) / (log (N : ℝ)) ^ 2 =
                80 * C * (log 7 + E) * (log 3 + E) * (N : ℝ) / (log (N : ℝ)) ^ 2 := by
              dsimp [cₘ]
              ring
            rw [hcₘ]
            have htmp : C * (4 * ((log 7 + E) * (log 3 + E))) * ((N : ℝ) / (log (N : ℝ) * log (z : ℝ))) =
                ((N : ℝ) / (log (N : ℝ) * log (z : ℝ))) * (4 * C * (log 7 + E) * (log 3 + E)) := by ring
            rw [htmp]
            have htmp2 : 80 * C * (log 7 + E) * (log 3 + E) * (N : ℝ) / (log (N : ℝ)) ^ 2 =
                (20 * (N : ℝ) / (log (N : ℝ)) ^ 2) * (4 * C * (log 7 + E) * (log 3 + E)) := by ring
            rw [htmp2]
            exact hmul
          exact le_trans hstep1 hstep2
    _ ≤ cₘ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            (N : ℝ) / (log (N : ℝ)) ^ 2 := by
          have hz2 : 2 ≤ correctedChenZ N - 1 := by
            have h59049 : 59049 ≤ N := by
              have : 59049 < 2 ^ 220 := by norm_num
              exact le_trans (le_of_lt this) hN
            exact correctedChenZ_sub_one_ge_two_of_large h59049
          have h𝔖 : (1 / 2 : ℝ) ≤ AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) :=
            singularSeriesTruncated_ge_half hz2
          have hcₘpos : 0 ≤ cₘ := by
            dsimp [cₘ]
            positivity
          have hX : 0 ≤ (N : ℝ) / (log (N : ℝ)) ^ 2 := by positivity
          have hmul : cₘ * (1 / 2 : ℝ) * (N : ℝ) / (log (N : ℝ)) ^ 2 ≤
              cₘ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
                (N : ℝ) / (log (N : ℝ)) ^ 2 := by
            -- cₘ·(1/2)·X ≤ cₘ·𝔖·X ⟺ (1/2) ≤ 𝔖 (cₘ ≥ 0, X ≥ 0)
            have h𝔖' : cₘ * (1 / 2 : ℝ) ≤ cₘ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) := by
              exact mul_le_mul_of_nonneg_left h𝔖 hcₘpos
            have : cₘ * (1 / 2 : ℝ) * ((N : ℝ) / (log (N : ℝ)) ^ 2) ≤
                cₘ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) * ((N : ℝ) / (log (N : ℝ)) ^ 2) :=
              mul_le_mul_of_nonneg_right h𝔖' hX
            ring_nf at this ⊢
            exact this
          ring_nf at hmul ⊢
          exact hmul



/-! ## Conditional endpoint with all analytic inputs explicit

`chensTheorem_fully_instantiated` supplies the three inputs of
`corrected_chens_theorem_of_q1Count_and_triple` from explicit analytic hypotheses:

  - `hPan` ← `chenPanInput_of_sourceFaithfulSignedInputs`
    (hI/hII/hM/htrunc); the exact signed pointwise decomposition is provided by
    `AnalyticNumberTheory`, while `PanSourceFaithfulSignedMainBound`
    remains an explicit hypothesis;
  - `hTripleMain` ← `hTripleMain_of_primePairInput` (hPP : `ChenPrimePairInput`);
  - `hq1` ← `hq1_of_q1AnalyticInputs` (hMain + hErr).

`hnum` is a numerical condition applied to the constants (cₘ, Cq) obtained
from hPP and hMain. As stated, it quantifies over every cₘ and every Cq > 0
for which the corresponding eventual bounds hold:
the double switchingCount sum ≤ cₘ·𝔖·N/log²N and q¹ ≤ Cq·𝔖·N/log²N.
It requires (10/3) > (cₘ + (Cq + 1/2))/2.
This final numerical condition is an explicit hypothesis alongside hPP and
hMain, not a numerical estimate established by this theorem. The structural
implication from all these hypotheses is proved below. -/
theorem chensTheorem_fully_instantiated
    {u v : ℕ}
    (hI : AnalyticNumberTheory.Sieve.PanTypeICharacterMeanValue
      (fun N : ℕ => (N : ℝ)) chenPanWeightOne u)
    (hII : AnalyticNumberTheory.Sieve.PanTypeIICharacterMeanValue
      (fun N : ℕ => (N : ℝ)) chenPanWeightOne u v)
    (hM : AnalyticNumberTheory.Sieve.PanSourceFaithfulSignedMainBound
      (fun N : ℕ => (N : ℝ)) chenPanWeightOne u v)
    (htrunc : CorrectedChenPanTruncationInput)
    (hPP : ChenPrimePairInput)
    (hMain : q1MainTermAbsorption) (hErr : q1APErrorUniformBound)
    (hnum : ∀ cₘ Cq : ℝ, 0 < Cq →
      (∃ N₀ₘ : ℕ, ∀ N : ℕ, N₀ₘ ≤ N → Even N →
        (∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
          ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
            (switchingCount N (p₁ * p₂) : ℝ)) ≤
          cₘ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            (N : ℝ) / (log (N : ℝ)) ^ 2) →
      (∃ Nq : ℕ, ∀ N : ℕ, Nq ≤ N → Even N →
        correctedChenQ1Count N ≤ Cq * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) / (log (N : ℝ)) ^ 2) →
      (10 / 3 : ℝ) > (cₘ + (Cq + 1 / 2)) / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧ Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  have hPan : ChenWeightedPanInput :=
    chenPanInput_of_sourceFaithfulSignedInputs hI hII hM htrunc
  rcases hTripleMain_of_primePairInput hPP with ⟨cₘ, N₀ₘ, hTripleMain⟩
  rcases hq1_of_q1AnalyticInputs hMain hErr with ⟨Cq, hCq, Nq, hq1⟩
  have hnum' : (10 / 3 : ℝ) > (cₘ + (Cq + 1 / 2)) / 2 :=
    hnum cₘ Cq hCq ⟨N₀ₘ, hTripleMain⟩ ⟨Nq, hq1⟩
  exact corrected_chens_theorem_of_q1Count_and_triple hPan hTripleMain hq1 hCq hnum'

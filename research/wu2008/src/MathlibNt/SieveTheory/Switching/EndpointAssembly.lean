import MathlibNt.SieveTheory.Switching.PrimePenaltyAsymptotics

/-!
# Switching upper bounds and Chen endpoint assembly

Triple-factor counts are bounded by switched prime counts and Selberg sums.
The corrected analytic inputs assemble Chen endpoints. Historical numerical
heuristics, failed multiplicity premises, and coarse switching errors remain
documented without strengthening their conclusions.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 1000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- For each candidate, the triple-factor penalty is at most the switching weight counting `(p₁,p₂)` pairs.
Dropping constraints such as `p₁ < p₂` and `p₂ ≤ p₃` preserves an upper bound; the equation uniquely determines `p₃`. -/
theorem tripleFactorCount_le_switchingWeight {n z y : ℕ} :
    tripleFactorCount n z y ≤
      ∑ p₁ ∈ (Finset.range y).filter (fun p₁ => p₁.Prime ∧ z ≤ p₁),
        ∑ p₂ ∈ (Finset.range (n + 1)).filter (fun p₂ => p₂.Prime ∧ y ≤ p₂),
          if ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = n then (1 : ℝ) else 0 := by
  unfold tripleFactorCount
  let T : Finset ℕ := (Finset.range (n + 1)).filter (fun p₁ =>
    p₁.Prime ∧ z ≤ p₁ ∧ p₁ < y ∧
    ∃ p₂ p₃, p₂.Prime ∧ p₃.Prime ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
      p₁ * p₂ * p₃ = n ∧ p₁ < p₂ ∧ p₂ ≤ p₃)
  have h1 : ∀ p₁ ∈ T, (1 : ℝ) ≤
      ∑ p₂ ∈ (Finset.range (n + 1)).filter (fun p₂ => p₂.Prime ∧ y ≤ p₂),
        if ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = n then (1 : ℝ) else 0 := by
    intro p₁ hp₁
    rcases Finset.mem_filter.mp hp₁ with ⟨h1r, h1c⟩
    rcases h1c with ⟨hpp, hz, hy, hw⟩
    rcases hw with ⟨p₂, p₃, hp₂p, hp₃p, hy₂, h₂₃, hprod, h₁₂, h₂₃'⟩
    have hw' : ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = n := ⟨p₃, hp₃p, hprod⟩
    have hmem : p₂ ∈ (Finset.range (n + 1)).filter (fun p₂ => p₂.Prime ∧ y ≤ p₂) := by
      rw [Finset.mem_filter, Finset.mem_range]
      constructor
      · -- p₂ ≤ n: p₂ ≤ p₂·p₃ ≤ p₁·p₂·p₃ = n
        have h1a : p₂ ≤ p₂ * p₃ := Nat.le_mul_of_pos_right p₂ hp₃p.pos
        have h1b : p₂ * p₃ ≤ p₁ * (p₂ * p₃) := Nat.le_mul_of_pos_left (p₂ * p₃) hpp.pos
        have hle : p₂ ≤ p₁ * p₂ * p₃ := by
          calc p₂ ≤ p₂ * p₃ := h1a
            _ ≤ p₁ * (p₂ * p₃) := h1b
            _ = p₁ * p₂ * p₃ := by rw [mul_assoc]
        rw [← hprod]
        exact lt_of_le_of_lt hle (Nat.lt_succ_self (p₁ * p₂ * p₃))
      · exact ⟨hp₂p, hy₂⟩
    have hterm : (if ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = n then (1 : ℝ) else 0) = 1 := by
      simp [hw']
    have hnonneg : ∀ q ∈ (Finset.range (n + 1)).filter (fun p₂ => p₂.Prime ∧ y ≤ p₂),
        q ∉ ({p₂} : Finset ℕ) →
        0 ≤ (if ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * q * p₃ = n then (1 : ℝ) else 0) := by
      intro q hq hnot
      by_cases h : ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * q * p₃ = n
      · simp [h]
      · simp [h]
    have hs := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({p₂} : Finset ℕ) ⊆ (Finset.range (n + 1)).filter (fun p₂ => p₂.Prime ∧ y ≤ p₂) from by
        intro q hq
        rw [Finset.mem_singleton] at hq
        subst q
        exact hmem) hnonneg
    have hsing : ({p₂} : Finset ℕ).sum
        (fun q => if ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * q * p₃ = n then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_singleton]
      simp [hw']
    rwa [hsing] at hs
  have hTsub : T ⊆ (Finset.range y).filter (fun p₁ => p₁.Prime ∧ z ≤ p₁) := by
    intro p₁ hp₁
    rcases Finset.mem_filter.mp hp₁ with ⟨h1r, h1c⟩
    rcases h1c with ⟨hpp, hz, hy, hw⟩
    exact Finset.mem_filter.mpr ⟨by
      rw [Finset.mem_range]
      omega, hpp, hz⟩
  have hTle : (∑ p₁ ∈ T, (1 : ℝ)) ≤
      ∑ p₁ ∈ (Finset.range y).filter (fun p₁ => p₁.Prime ∧ z ≤ p₁),
        ∑ p₂ ∈ (Finset.range (n + 1)).filter (fun p₂ => p₂.Prime ∧ y ≤ p₂),
          if ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = n then (1 : ℝ) else 0 := by
    calc
      (∑ p₁ ∈ T, (1 : ℝ)) ≤ ∑ p₁ ∈ T,
          ∑ p₂ ∈ (Finset.range (n + 1)).filter (fun p₂ => p₂.Prime ∧ y ≤ p₂),
            if ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = n then (1 : ℝ) else 0 := by
            exact Finset.sum_le_sum h1
      _ ≤ ∑ p₁ ∈ (Finset.range y).filter (fun p₁ => p₁.Prime ∧ z ≤ p₁),
            ∑ p₂ ∈ (Finset.range (n + 1)).filter (fun p₂ => p₂.Prime ∧ y ≤ p₂),
              if ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = n then (1 : ℝ) else 0 := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun p₁ hp₁ hnot => by
              apply Finset.sum_nonneg
              intro p₂ hp₂
              by_cases h : ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = n
              · simp [h]
              · simp [h])
  have hcard : (T.card : ℝ) = ∑ p₁ ∈ T, (1 : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_ones T)
  rw [hcard]
  exact hTle

/-- Uniform finite expansion of the triple-factor part: its sum over candidates is bounded by the switched count,
summing over `(p₁,p₂)` pairs the number of candidates satisfying `p₁p₂p₃ = N-p`. -/
theorem correctedChenOmega_triple_le_switchingCount (N : ℕ) :
    (correctedChenCandidates N).sum
        (fun p => tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N)) ≤
      ∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
        ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
          ((correctedChenCandidates N).filter
            (fun p => ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = N - p)).card := by
  have hper : ∀ p ∈ correctedChenCandidates N,
      tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N) ≤
        ∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
          ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
            if ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = N - p then (1 : ℝ) else 0 := by
    intro p hp
    have h := tripleFactorCount_le_switchingWeight
      (n := N - p) (z := correctedChenZ N) (y := correctedChenY N)
    calc
      tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N) ≤
          ∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
            ∑ p₂ ∈ (Finset.range (N - p + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
              if ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = N - p then (1 : ℝ) else 0 := h
      _ ≤ ∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
            ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
              if ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = N - p then (1 : ℝ) else 0 := by
            apply Finset.sum_le_sum
            intro p₁ hp₁
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro p₂ hp₂
              rw [Finset.mem_filter, Finset.mem_range] at hp₂ ⊢
              constructor
              · omega
              · exact hp₂.2
            · intro p₂ hp₂ hnot
              by_cases h : ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = N - p
              · simp [h]
              · simp [h]
  calc
    (correctedChenCandidates N).sum
        (fun p => tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N))
        ≤ (correctedChenCandidates N).sum (fun p =>
            ∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
              ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
                if ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = N - p then (1 : ℝ) else 0) :=
          Finset.sum_le_sum hper
    _ = ∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
          ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
            (correctedChenCandidates N).sum (fun p =>
              if ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = N - p then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro p₁ hp₁
          rw [Finset.sum_comm]
    _ = ∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
          ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
            ((correctedChenCandidates N).filter
              (fun p => ∃ p₃ : ℕ, p₃.Prime ∧ p₁ * p₂ * p₃ = N - p)).card := by
          -- For each pair, the sum of indicators over p equals the filtered cardinality.
          simp_rw [Finset.sum_boole]
          norm_cast

/-! ## Analytic switching upper bound: the Selberg sieve on the switched set -/

/-- Density on the switched set: `ν(d) = 1/d`, the proportion of `p₃ ≤ x` with `d | p₃`. -/
noncomputable def switchingSieveNu : ArithmeticFunction ℝ :=
  { toFun := fun d : ℕ => (1 : ℝ) / d
    map_zero' := by simp }

/-- Multiplicativity of `switchingSieveNu`: `1/(mn) = (1/m)(1/n)`. -/
theorem switchingSieveNu_isMultiplicative : switchingSieveNu.IsMultiplicative := by
  constructor
  · simp [switchingSieveNu]
  · intro m n hcop
    simp [switchingSieveNu, one_div, mul_inv_rev, mul_comm]

/-- Sifting product for the switching sieve: the product of all primes below `z`. -/
noncomputable def switchingSiftingProduct (z : ℕ) : ℕ :=
  ((Finset.range z).filter Nat.Prime).prod id

/-- The switching sifting product is nonzero. -/
theorem switchingSiftingProduct_ne_zero (z : ℕ) : switchingSiftingProduct z ≠ 0 := by
  unfold switchingSiftingProduct
  exact ne_of_gt (Finset.prod_pos (fun p hp => Nat.Prime.pos (Finset.mem_filter.mp hp).2))

/-- The prime factors of a product of a set of primes are exactly that set. -/
private lemma primeFactors_prod_of_prime_set (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (S.prod id).primeFactors = S := by
  exact Internal.primeFactors_prod_eq_self hS

/-- The switching sifting product is squarefree, being a product of distinct primes. -/
theorem switchingSiftingProduct_squarefree (z : ℕ) : Squarefree (switchingSiftingProduct z) := by
  unfold switchingSiftingProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · rintro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Finset.mem_filter.mp hp).2
        (Finset.mem_filter.mp hq).2).mpr hpq)
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.squarefree

/-- **Sieve problem on the switched set**: support `{p₃ ≤ x}`, where `x = N/a`; sieve out
multiples of primes `q < z`, with density `ν(d) = 1/d` and total mass equal to the support cardinality.
The sifted sum is `#{p₃ ≤ x : p₃ has no prime factor < z}`. -/
noncomputable def switchingSieve (N a : ℕ) : BoundingSieve where
  support := Finset.range (N / a + 1)
  prodPrimes := switchingSiftingProduct (correctedChenZ N)
  prodPrimes_squarefree := switchingSiftingProduct_squarefree (correctedChenZ N)
  weights := fun _ => 1
  weights_nonneg := by intro n; norm_num
  totalMass := (N / a + 1 : ℕ)
  nu := switchingSieveNu
  nu_mult := switchingSieveNu_isMultiplicative
  nu_pos_of_prime := by
    intro p hp hdiv
    unfold switchingSieveNu
    have hp0 : p ≠ 0 := hp.ne_zero
    simp []
    exact hp.pos
  nu_lt_one_of_prime := by
    intro p hp hdiv
    unfold switchingSieveNu
    have hp0 : p ≠ 0 := hp.ne_zero
    simp []
    simpa [div_eq_mul_inv] using
      (div_lt_one (by exact_mod_cast hp.pos : (0 : ℝ) < (p : ℝ))).mpr
        (by exact_mod_cast hp.one_lt : (1 : ℝ) < (p : ℝ))

/-- **Switched-set count**: for fixed `a = p₁p₂`, count candidates satisfying `a·p₃ = N-p`. -/
noncomputable def switchingCount (N a : ℕ) : ℝ :=
  ((correctedChenCandidates N).filter (fun p => ∃ p₃ : ℕ, p₃.Prime ∧ a * p₃ = N - p)).card

/-- **Prime p₃ counting lemma**: for fixed `a ≥ 1`,
`switchingCount N a = #{p ∈ C(N) : a·p₃ = N-p, p₃ prime}` maps by `p ↦ (N-p)/a`
injectively into the primes `p₃ ≤ N/a`. Hence

    switchingCount N a ≤ #{p ≤ N/a : p prime}.

This is the first step in the triple-factor main-term estimate: the count retains primality of p₃,
the elementary source of the `1/log(N/a)` density, without a PNT in AP. Distribution of candidates in APs can further sharpen it. -/
theorem switchingCount_le_pi (N a : ℕ) (ha : 1 ≤ a) :
    switchingCount N a ≤
      (((Finset.range (N / a + 1)).filter Nat.Prime).card : ℝ) := by
  unfold switchingCount
  let s : Finset ℕ := (correctedChenCandidates N).filter
    (fun p => ∃ p₃ : ℕ, p₃.Prime ∧ a * p₃ = N - p)
  let t : Finset ℕ := (Finset.range (N / a + 1)).filter Nat.Prime
  let f : ℕ → ℕ := fun p => (N - p) / a
  have ha' : 0 < a := by omega
  have hinj : Set.InjOn f (↑s : Set ℕ) := by
    intro p hp q hq hpq
    have hpw : ∃ p₃ : ℕ, p₃.Prime ∧ a * p₃ = N - p := (Finset.mem_filter.mp hp).2
    have hqw : ∃ q₃ : ℕ, q₃.Prime ∧ a * q₃ = N - q := (Finset.mem_filter.mp hq).2
    rcases hpw with ⟨p₃, hp₃p, hp₃eq⟩
    rcases hqw with ⟨q₃, hq₃p, hq₃eq⟩
    have hfp : (N - p) / a = p₃ := by
      rw [← hp₃eq]
      exact Nat.mul_div_right p₃ ha'
    have hfq : (N - q) / a = q₃ := by
      rw [← hq₃eq]
      exact Nat.mul_div_right q₃ ha'
    change (N - p) / a = (N - q) / a at hpq
    have hp₃eqq₃ : p₃ = q₃ := by
      rw [hfp, hfq] at hpq
      exact hpq
    have hpN : p < N := by
      have hpC := (Finset.mem_filter.mp hp).1
      simpa using (Finset.mem_filter.mp hpC).1
    have hqN : q < N := by
      have hqC := (Finset.mem_filter.mp hq).1
      simpa using (Finset.mem_filter.mp hqC).1
    calc
      p = N - a * p₃ := by
            rw [hp₃eq]
            omega
      _ = N - a * q₃ := by rw [hp₃eqq₃]
      _ = q := by
            rw [hq₃eq]
            omega
  have himg_le : (s.image f).card ≤ t.card := by
    apply Finset.card_le_card
    intro q hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨p, hp, rfl⟩
    have hpw : ∃ p₃ : ℕ, p₃.Prime ∧ a * p₃ = N - p := (Finset.mem_filter.mp hp).2
    rcases hpw with ⟨p₃, hp₃p, hp₃eq⟩
    have hqeq : (N - p) / a = p₃ := by
      rw [← hp₃eq]
      exact Nat.mul_div_right p₃ ha'
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_range]
      change (N - p) / a < N / a + 1
      rw [hqeq]
      have hp3le : p₃ ≤ N / a := by
        calc
          p₃ = (N - p) / a := hqeq.symm
          _ ≤ N / a := Nat.div_le_div_right (Nat.sub_le N p)
      omega
    · change Nat.Prime ((N - p) / a)
      rwa [hqeq]
  have hcard : (s.image f).card = s.card := Finset.card_image_of_injOn hinj
  have hs_le : s.card ≤ t.card := by
    calc
      s.card = (s.image f).card := by rw [hcard]
      _ ≤ t.card := himg_le
  exact_mod_cast hs_le

/-- **Region restriction**: if `N < 2a`, `a·p₃ = N-p ≤ N` has no solution with p₃ ≥ 2,
so `switchingCount N a = 0`. Consequently, pairs with `a = p₁p₂ > N/2`
contribute zero to the triple-factor main-term sum. -/
theorem switchingCount_eq_zero_of_N_lt_two_mul (N a : ℕ) (hN : N < 2 * a) :
    switchingCount N a = 0 := by
  unfold switchingCount
  have hsub : ((correctedChenCandidates N).filter
      (fun p => ∃ p₃ : ℕ, p₃.Prime ∧ a * p₃ = N - p)) = ∅ := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp
      rcases hp with ⟨hpC, hpw⟩
      rcases hpw with ⟨p₃, hp₃p, hp₃eq⟩
      have hp3ge2 : 2 ≤ p₃ := hp₃p.two_le
      have hbig : 2 * a ≤ N - p := by
        rw [← hp₃eq]
        calc
          2 * a ≤ a * 2 := by omega
          _ ≤ a * p₃ := Nat.mul_le_mul_left a hp3ge2
      have hle : N - p ≤ N := Nat.sub_le N p
      simpa using (by omega : False)
    · intro hp
      simp at hp
  rw [hsub]
  simp



/-- **Switching count ≤ sifted sum of the switching sieve**: for a candidate p, `p₃ = (N-p)/a` lies in the support
and is coprime to the sifting product. The candidate condition gives no prime factor `< z` in p₃, since all prime factors of `a = p₁p₂` are ≥ z. -/
theorem switchingCount_le_siftedSum (N a : ℕ) :
    switchingCount N a ≤ (switchingSieve N a).siftedSum := by
  unfold switchingCount
  let T : Finset ℕ := (correctedChenCandidates N).filter
    (fun p => ∃ p₃ : ℕ, p₃.Prime ∧ a * p₃ = N - p)
  have hmap : T.image (fun p => (N - p) / a) ⊆
      ((Finset.range (N / a + 1)).filter
        (fun n => Nat.Coprime (switchingSiftingProduct (correctedChenZ N)) n)) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨p, hp, rfl⟩
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨hpc, hwit⟩
    unfold correctedChenCandidates at hpc
    rw [Finset.mem_filter] at hpc
    rcases hpc with ⟨hpN, hpp, hNp2, hqcond⟩
    rcases hwit with ⟨p₃, hp₃p, hprod⟩
    have haeq : a * p₃ = N - p := hprod
    have ha0 : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_mul] at haeq
      have hNp : N - p ≠ 0 := by omega
      exact hNp haeq.symm
    have hp₃eq : p₃ = (N - p) / a := by
      rw [← haeq, mul_comm]
      exact (Nat.mul_div_cancel p₃ (Nat.pos_of_ne_zero ha0)).symm
    have hp₃le : p₃ ≤ N / a := by
      rw [hp₃eq]
      apply Nat.div_le_div_right
      omega
    have hcop : Nat.Coprime (switchingSiftingProduct (correctedChenZ N)) p₃ := by
      rw [AnalyticNumberTheory.Sieve.coprime_prod_iff_no_prime_dvd]
      intro r hrprime hrdvd hra
      have hr_lt : r < correctedChenZ N := by
        have hmem : r ∈ (Finset.range (correctedChenZ N)).filter Nat.Prime := by
          have hrin : r ∈ (switchingSiftingProduct (correctedChenZ N)).primeFactors := by
            rw [Nat.mem_primeFactors]
            exact ⟨hrprime, hrdvd, switchingSiftingProduct_ne_zero (correctedChenZ N)⟩
          have hpf := primeFactors_prod_of_prime_set
            ((Finset.range (correctedChenZ N)).filter Nat.Prime)
            (fun q hq => (Finset.mem_filter.mp hq).2)
          unfold switchingSiftingProduct at hrin
          rwa [hpf] at hrin
        exact (Finset.mem_range.mp (Finset.mem_filter.mp hmem).1)
      have hrdvd_Np : r ∣ N - p := by
        rcases hra with ⟨k, hk⟩
        refine ⟨a * k, ?_⟩
        calc
          N - p = a * p₃ := haeq.symm
          _ = a * (r * k) := by rw [hk]
          _ = r * (a * k) := by ring
      exact hqcond r hrprime hr_lt hrdvd_Np
    rw [Finset.mem_filter]
    exact ⟨by rw [Finset.mem_range]; omega, by simpa [hp₃eq] using hcop⟩
  have hinj : Set.InjOn (fun p => (N - p) / a) (T : Finset ℕ) := by
    intro p₁ hp₁ p₂ hp₂ hdiv
    unfold T at hp₁ hp₂
    change p₁ ∈ (correctedChenCandidates N).filter
        (fun p => ∃ p₃ : ℕ, p₃.Prime ∧ a * p₃ = N - p) at hp₁
    change p₂ ∈ (correctedChenCandidates N).filter
        (fun p => ∃ p₃ : ℕ, p₃.Prime ∧ a * p₃ = N - p) at hp₂
    rw [Finset.mem_filter] at hp₁ hp₂
    rcases hp₁ with ⟨hpc₁, hwit₁⟩
    rcases hp₂ with ⟨hpc₂, hwit₂⟩
    unfold correctedChenCandidates at hpc₁ hpc₂
    rw [Finset.mem_filter] at hpc₁ hpc₂
    rcases hwit₁ with ⟨p₃₁, hp₃₁p, hprod₁⟩
    rcases hwit₂ with ⟨p₃₂, hp₃₂p, hprod₂⟩
    have hp₁ge2 : 2 ≤ N - p₁ := hpc₁.2.2.1
    have hp₂ge2 : 2 ≤ N - p₂ := hpc₂.2.2.1
    have ha0 : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_mul] at hprod₁
      omega
    have h1 : (N - p₁) / a * a = N - p₁ := Nat.div_mul_cancel (by
      exact ⟨p₃₁, hprod₁.symm⟩)
    have h2 : (N - p₂) / a * a = N - p₂ := Nat.div_mul_cancel (by
      exact ⟨p₃₂, hprod₂.symm⟩)
    change (N - p₁) / a = (N - p₂) / a at hdiv
    have hNp : N - p₁ = N - p₂ := by
      calc
        N - p₁ = (N - p₁) / a * a := h1.symm
        _ = (N - p₂) / a * a := by rw [hdiv]
        _ = N - p₂ := h2
    have hp₁N : p₁ < N := Finset.mem_range.mp hpc₁.1
    have hp₂N : p₂ < N := Finset.mem_range.mp hpc₂.1
    omega
  have hcard : T.card = (T.image (fun p => (N - p) / a)).card := by
    exact (Finset.card_image_of_injOn hinj).symm
  calc
    switchingCount N a = (T.card : ℝ) := rfl
    _ = ((T.image (fun p => (N - p) / a)).card : ℝ) := by
          exact_mod_cast hcard
    _ ≤ (((Finset.range (N / a + 1)).filter
          (fun n => Nat.Coprime (switchingSiftingProduct (correctedChenZ N)) n)).card : ℝ) := by
          exact_mod_cast (Finset.card_le_card hmap)
    _ = (switchingSieve N a).siftedSum := by
          unfold BoundingSieve.siftedSum switchingSieve
          simp [Finset.sum_boole]

/-- **Switching-sieve main term = Mertens product**: `(Σ selbergTerms)⁻¹ = ∏_{q<z}(1-1/q)
= primeProduct(z-1)`, since the switching-sieve density is `ν(q) = 1/q`. -/
theorem switchingSieve_mainTerm_eq_primeProduct (N a : ℕ) :
    (∑ l ∈ (switchingSieve N a).prodPrimes.divisors,
      (switchingSieve N a).selbergTerms l)⁻¹ =
    MertensTheorem.primeProduct (correctedChenZ N - 1) := by
  have hmain := AnalyticNumberTheory.Sieve.selbergMainTerm_eq_prod_one_sub_nu (switchingSieve N a)
  rw [hmain]
  have h_pf : (switchingSieve N a).prodPrimes.primeFactors =
      (Finset.range (correctedChenZ N)).filter Nat.Prime := by
    unfold switchingSieve switchingSiftingProduct
    have hprime : ∀ p ∈ (Finset.range (correctedChenZ N)).filter Nat.Prime, p.Prime := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    exact primeFactors_prod_of_prime_set
      ((Finset.range (correctedChenZ N)).filter Nat.Prime) hprime
  rw [h_pf]
  unfold MertensTheorem.primeProduct
  have hz : 1 ≤ correctedChenZ N := by
    unfold correctedChenZ
    omega
  rw [← Nat.sub_add_cancel hz]
  apply Finset.prod_congr rfl
  intro q hq
  have hqprime : q.Prime := (Finset.mem_filter.mp hq).2
  have hq0 : q ≠ 0 := hqprime.ne_zero
  unfold switchingSieve switchingSieveNu
  simp []


/-- **Selberg upper bound with explicit optimal weights**: as above, using
`optimalSelbergWeight`, namely the unit-bounded Möbius weight. -/
theorem switchingSieve_upper_bound_optimal (N a : ℕ) :
    (switchingSieve N a).siftedSum ≤
      (switchingSieve N a).totalMass *
        (∑ l ∈ (switchingSieve N a).prodPrimes.divisors,
          (switchingSieve N a).selbergTerms l)⁻¹ +
      (switchingSieve N a).errSum (BoundingSieve.lambdaSquared
        (AnalyticNumberTheory.Sieve.optimalSelbergWeight (switchingSieve N a))) := by
  have h := AnalyticNumberTheory.Sieve.omega_upper_bound_via_mathlib (switchingSieve N a)
    (AnalyticNumberTheory.Sieve.optimalSelbergWeight (switchingSieve N a))
    (AnalyticNumberTheory.Sieve.optimalSelbergWeight_one (switchingSieve N a))
  rw [AnalyticNumberTheory.Sieve.optimalSelbergMainSum_eq (switchingSieve N a)] at h
  simpa [AnalyticNumberTheory.Sieve.selbergMainTerm] using h

/-- Main term plus error for each switched pair: `totalMass·primeProduct(z-1) + errSum(Λ²w*)`. -/
noncomputable def switchingSieveMainErr (N : ℕ) (p₁ p₂ : ℕ) : ℝ :=
  (switchingSieve N (p₁ * p₂)).totalMass * MertensTheorem.primeProduct (correctedChenZ N - 1) +
    (switchingSieve N (p₁ * p₂)).errSum (BoundingSieve.lambdaSquared
      (AnalyticNumberTheory.Sieve.optimalSelbergWeight (switchingSieve N (p₁ * p₂))))


/-
## Final assembly of the Ω upper bound with the corrected main-term statement

Combine the finite triple-factor and prime-power decompositions with two analytic inputs to obtain `CorrectedChenOmegaUpperBound`:

  1. `hTripleMain`: `Σ_{p₁,p₂} switchingCount(N, p₁p₂) ≤ cₘ·𝔖_trunc·N/log²N`,
     retaining the prime p₃ density `1/log(N/(p₁p₂))`;
  2. `hPrimePower`: the final uniform prime-power bound, from the q¹ distribution input and negligible q² terms;
  3. `hnum`: the numerical condition `(10/3) > (cₘ + Cₚ)/2`.

**Warning:** the former `hTripleMain` target summing `totalMass·primeProduct(z-1)` has the wrong scale:
the "+1" term summed over ~N^{4/3}/log²N pairs gives a left-hand side ~N^{4/3}/log³N, far exceeding a right-hand side ~cₘ·𝔖·N/log²N.
It lacks the prime p₃ density factor. The corrected target no longer requires `hTripleErr`/`hNeg`:
the switching-sieve error route is replaced by a direct main-term estimate. The finite ingredients are the Ω decomposition,
`tripleFactorCount ≤ Σ switchingCount`, the proper-power bounds, and `𝔖 ≥ 1/2`.
-/
theorem CorrectedChenOmegaUpperBound_of_analytic_inputs
    {cₘ Cₚ : ℝ} {N₀ₘ N₀ₚ : ℕ}
    (hTripleMain : ∀ N : ℕ, N₀ₘ ≤ N → Even N →
      (∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
        ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
          (switchingCount N (p₁ * p₂) : ℝ)) ≤
        cₘ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2)
    (hPrimePower : ∀ N : ℕ, N₀ₚ ≤ N → Even N →
      (correctedChenCandidates N).sum
          (fun p => primePowerSum (N - p) (correctedChenZ N) (correctedChenY N)) ≤
        Cₚ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2)
    (hnum : (10 / 3 : ℝ) > (cₘ + Cₚ) / 2) :
    CorrectedChenOmegaUpperBound := by
  let N₀ : ℕ := max N₀ₘ N₀ₚ
  refine ⟨cₘ + Cₚ, hnum, N₀, ?_⟩
  intro N hN hEven
  let S₁ : Finset ℕ := (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁)
  let S₂ : Finset ℕ := (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂)
  let X : ℝ := (N : ℝ) / (log (N : ℝ)) ^ 2
  let 𝔖 : ℝ := AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1)
  have hNm : N₀ₘ ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNp : N₀ₚ ≤ N := by
    dsimp [N₀] at hN
    omega
  -- Decompose Ω into the prime-power and triple-factor parts.
  have hdecomp := correctedChenOmega_eq_primePower_add_triple N
  -- Bound the triple-factor part by Σ_{p₁,p₂} switchingCount, then apply hTripleMain.
  have htriple' : (correctedChenCandidates N).sum
        (fun p => tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N)) ≤
      cₘ * 𝔖 * X := by
    calc
      (correctedChenCandidates N).sum
          (fun p => tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N))
          ≤ ∑ p₁ ∈ S₁, ∑ p₂ ∈ S₂, (switchingCount N (p₁ * p₂) : ℝ) := by
            have hb := correctedChenOmega_triple_le_switchingCount N
            dsimp [S₁, S₂] at hb ⊢
            simpa [switchingCount] using hb
      _ ≤ cₘ * 𝔖 * X := by
            have hb := hTripleMain N hNm hEven
            dsimp [S₁, S₂, 𝔖, X] at hb ⊢
            have hXeq : cₘ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
                  ((N : ℝ) / (log (N : ℝ)) ^ 2) =
                cₘ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
                  (N : ℝ) / (log (N : ℝ)) ^ 2 := by
              ring
            rwa [hXeq]
  -- Prime-power part: apply hPrimePower.
  have hpow' : (correctedChenCandidates N).sum
        (fun p => primePowerSum (N - p) (correctedChenZ N) (correctedChenY N)) ≤ Cₚ * 𝔖 * X := by
    have hb := hPrimePower N hNp hEven
    dsimp [𝔖, X] at hb ⊢
    have hXeq : Cₚ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          ((N : ℝ) / (log (N : ℝ)) ^ 2) =
        Cₚ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 := by
      ring
    rwa [hXeq]
  have hΩ : correctedChenOmega N ≤ (cₘ + Cₚ) * 𝔖 * X := by
    calc
      correctedChenOmega N
          = (correctedChenCandidates N).sum
                (fun p => primePowerSum (N - p) (correctedChenZ N) (correctedChenY N)) +
            (correctedChenCandidates N).sum
                (fun p => tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N)) := hdecomp
      _ ≤ Cₚ * 𝔖 * X + cₘ * 𝔖 * X := add_le_add hpow' htriple'
      _ = (cₘ + Cₚ) * 𝔖 * X := by
            ring
  -- Target form: cΩ·𝔖_trunc·N/log²N.
  dsimp [X, 𝔖] at hΩ ⊢
  have hXeq : (cₘ + Cₚ) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        ((N : ℝ) / (log (N : ℝ)) ^ 2) =
      (cₘ + Cₚ) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        (N : ℝ) / (log (N : ℝ)) ^ 2 := by
    ring
  rwa [hXeq] at hΩ

/-- **Assembly with the corrected statement**: weighted Pan input and two analytic inputs
(the corrected `hTripleMain` and `hPrimePower`) imply Chen's theorem:
`∃ N₀, ∀ even N ≥ N₀: N = p + q`, with q having at most two prime factors.

The chain is `corrected_chens_theorem_of_inputs` followed by `CorrectedChenOmegaUpperBound_of_analytic_inputs`.
The remaining hypotheses are analytic: the triple-factor `switchingCount` estimate and the uniform prime-power bound. -/
theorem corrected_chens_theorem_of_omega_inputs
    {cₘ Cₚ : ℝ} {N₀ₘ N₀ₚ : ℕ}
    (hPan : ChenWeightedPanInput)
    (hTripleMain : ∀ N : ℕ, N₀ₘ ≤ N → Even N →
      (∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
        ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
          (switchingCount N (p₁ * p₂) : ℝ)) ≤
        cₘ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2)
    (hPrimePower : ∀ N : ℕ, N₀ₚ ≤ N → Even N →
      (correctedChenCandidates N).sum
          (fun p => primePowerSum (N - p) (correctedChenZ N) (correctedChenY N)) ≤
        Cₚ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2)
    (hnum : (10 / 3 : ℝ) > (cₘ + Cₚ) / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧ Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  exact corrected_chens_theorem_of_inputs hPan
    (CorrectedChenOmegaUpperBound_of_analytic_inputs hTripleMain hPrimePower hnum)



/-- Diagnostic direct lower bound for the public good-representation count.
This is stronger than the Jurkat--Richert weighted theorem and is not the
canonical literature contract. -/
def ChenGoodRepresentationLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    c * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) / Real.log N ^ 2 ≤
      ((chenGoodRepresentations N).card : ℝ)


/-- Historical conditional counting bridge for the present `chenW`/`Ω`.

This proposition is retained so the conditional theorem has a stable, explicit
interface, but it is not an open proof obligation: finite evaluation refutes
it for the current definitions (see `CHEN_PROOF_ATLAS.md`).  A future
unconditional development must replace both this statement and, where needed,
the counting objects with a multiplicity-corrected switching bridge. -/
def ChenCountingBridge : Prop :=
  ∀ N : ℕ, Even N → 1000 ≤ N →
    chenW N - chenOmega N / 2 ≤ ((chenGoodRepresentations N).card : ℝ)

/-- The key inequality implies Chen's theorem given the exact counting bridge.

W(N) - Ω/2 > 0 means that there is at least one representation N = p + q,
where p is prime and q = N-p satisfies the sieve conditions, with at most two prime factors. -/
theorem key_inequality_implies_chen
    (h_bridge : ChenCountingBridge)
    (h_key : ∀ N : ℕ, Even N → N ≥ 1000 →
      chenW N - chenOmega N / 2 > 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  -- This implication is formally valid because it consumes
  -- `ChenCountingBridge` verbatim. That premise is externally refuted for the
  -- current historical counts; no symmetry argument is asserted here.
  refine ⟨1000, ?_⟩
  intro N hN_large hN_even
  have hpos : 0 < ((chenGoodRepresentations N).card : ℝ) :=
    lt_of_lt_of_le (h_key N hN_even hN_large) (h_bridge N hN_even hN_large)
  have hcard : 0 < (chenGoodRepresentations N).card := by exact_mod_cast hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hpN, hpprime, hq2, hqalmost⟩ := hp
  refine ⟨p, N - p, hpprime, hq2, hqalmost, ?_⟩
  omega

/-! ## Numerical constants -/

/-- W(N) lower-bound coefficient: 2.6408. -/
noncomputable def chenW_coefficient : ℝ := 2.6408

/-- Ω upper-bound coefficient: 3.9404. -/
noncomputable def chenOmega_coefficient : ℝ := 3.9404

/-- Key difference: W(N) - Ω/2 ≥ (2.6408 - 3.9404/2) 𝔖(N) N/log²N = 0.6706 𝔖(N) N/log²N. -/
noncomputable def chen_difference_coefficient : ℝ :=
  chenW_coefficient - chenOmega_coefficient / 2


/-- Working expression for f(5): 2e^γ · log(5/2) / 5 ≈ 0.6528. -/
noncomputable def sieveF_at_5 : ℝ :=
  2 * exp Real.eulerMascheroniConstant * log (5/2) / 5



/-! ## 6. Historical switching heuristic and its failure -/

/-
**Historical heuristic (not the canonical proof route)**:

1. **Goal**: prove the existence of a prime p and a semiprime q with N = p + q.

2. **First step: a lower bound for W(N)**. Apply the Jurkat-Richert sieve to A = {N-p : p prime}.
   - Sieve out prime factors of N-p that are ≤ N^(1/10).
   - Obtain W(N): N-p has no small prime factor and at most one prime factor in the medium range.
   - W(N) ≥ 2.6408 𝔖(N) N/log²N

3. **Second step: triple-factor cases in W(N)**. A prime p counted by W(N) may correspond to
   N-p = p₁p₂p₃ with exactly three prime factors; these cases must be excluded.
   - The triple-factor case satisfies N^(1/10) < p₁ ≤ N^(1/3) < p₂ < p₃.
   - the historical source claims symmetry gives an `Ω/2` upper bound
   - this step is false for the present definitions: the local multiplicity is
     `1 + 1_[p₁*p₃^2≤N]`, not uniformly two

4. **Third step: an upper bound for Ω**. Apply the Selberg sieve to the switched set B = {N-p₁p₂p₃}.
   - Switch from directly sieving N-p to sieving the variable a in "N-ap₃ is prime".
   - The Selberg sieve gives Ω ≤ 3.9404 𝔖(N) N/log²N.

5. **Historical conclusion**: the displayed conclusion requires the false
   counting bridge and is not used by the canonical endpoint
-/

/-! ## Definition of the switched set B -/

/-- **Switched set B**: `N-p₁p₂p₃`, where
`z ≤ p₁ < y ≤ p₂ ≤ p₃`, `p₁p₂p₃ < N`, `(p₁p₂p₃, N) = 1`。

This is not the triple-factor object used by `tripleFactorCount`: it additionally requires coprimality with `N`
and a product less than `N`, while `p₂ < p₃` excludes repeated factors `p₂ = p₃`. Their exact relationship
remains part of the switching bridge to be formalized. -/
noncomputable def switchedSet (N z y : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n =>
    ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
      z ≤ p₁ ∧ p₁ < y ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
      p₁ < p₂ ∧ p₂ < p₃ ∧
      p₁ * p₂ * p₃ < N ∧
      Nat.gcd (p₁ * p₂ * p₃) N = 1 ∧
      n = N - p₁ * p₂ * p₃)

/-- Sieve function S(B, P, y) on the switched set B. -/
noncomputable def switchedSieveSum (N z y : ℕ) : ℝ :=
  (switchedSet N z y).sum (fun n =>
    if (∀ p : ℕ, p.Prime → p < y → ¬ p ∣ n) then 1 else 0)


/-! ## 8. Audited proof structures -/

/-
**Canonical conditional structure**:

  MathlibNt.ChensTheorem.chens_theorem_of_jurkat_richert_weighted_lower_bound
  ├── ChenJurkatRichertWeightedLowerBound
  │   └── weighted candidates minus half the prime-power penalty
  └── LiuPanWangDingTheorem
      └── canonical upper bound for the triple penalty

**Retained diagnostic structures**:

  chens_theorem_of_good_representation_lower_bound
  └── ChenGoodRepresentationLowerBound
      └── stronger direct good-count premise, not the JR literature theorem

  historical `chens_theorem`
  └── `ChenAnalyticBounds` + `ChenCountingBridge`
      └── refuted current counting premise

  corrected-penalty q¹ endpoint
  ├── valid corrected finite bridge
  └── fixed-level coefficient exceeds the final budget

**Module dependencies**:
  - AnalyticNumberTheory.Sieve.lean: definition and positivity of 𝔖(N).
  - LinearSieve.lean: the Jurkat-Richert theorem and F(s)/f(s).
  - MertensTheorem.lean: asymptotics of V(z) and Mertens' theorem.
  - BombieriVinogradov.lean: distribution conditions and the Pan mean-value theorem.
  - SwitchingPrinciple.lean: historical/corrected counts and canonical external contract
  - SelbergUpperBound.lean: Selberg upper sieve bounds for Ω.
-/

/-- Nonnegativity of the corrected sieve product: every factor `1 - nu p` is positive at a sifting prime. -/
lemma correctedChenSieveProduct_pos_aux (N : ℕ) : 0 ≤ correctedChenSieveProduct N := by
  unfold correctedChenSieveProduct
  exact Finset.prod_nonneg (by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpdvd : p ∣ correctedChenSiftingProduct N :=
      (Nat.mem_primeFactors.mp hp).2.1
    have hpc : p < correctedChenZ N ∧ 2 < p ∧ ¬ p ∣ N :=
      (prime_dvd_correctedChenSiftingProduct hpp).mp hpdvd
    have hinv := correctedChenNu_inv_prime (_N := N) hpp hpc.2.1
    have hpos : 0 < (1 - correctedChenNu p) := by
      have hnum : 0 < ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
        have hcast : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
        have hpm1 : 0 < (p : ℝ) - 1 := by linarith
        have hpm2 : 0 < (p : ℝ) - 2 := by linarith
        exact div_pos hpm1 hpm2
      rw [← hinv] at hnum
      exact inv_pos.mp hnum
    exact le_of_lt hpos)






end MathlibNt.SieveTheory.SwitchingPrinciple

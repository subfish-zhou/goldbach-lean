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
    by_cases hm : m = 0
    · subst m
      simp [switchingSieveNu]
    · by_cases hn : n = 0
      · subst n
        simp [switchingSieveNu]
      · simp [switchingSieveNu, hm, hn]
        field_simp [hm, hn]

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
  induction S using Finset.induction_on with
  | empty => simp [Nat.primeFactors_one]
  | insert p S hpS ih =>
      rw [Finset.prod_insert hpS]
      change (p * S.prod id).primeFactors = insert p S
      have hp' := hS p (Finset.mem_insert_self p S)
      have h0p : p ≠ 0 := hp'.ne_zero
      have h0s : (S.prod id) ≠ 0 := ne_of_gt <| Finset.prod_pos
        (fun q hq => Nat.Prime.pos (hS q (Finset.mem_insert_of_mem hq)))
      rw [Nat.primeFactors_mul h0p h0s, Nat.Prime.primeFactors hp',
        ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))]
      rw [Finset.insert_eq]

/-- The switching sifting product is squarefree, being a product of distinct primes. -/
theorem switchingSiftingProduct_squarefree (z : ℕ) : Squarefree (switchingSiftingProduct z) := by
  unfold switchingSiftingProduct
  let S : Finset ℕ := (Finset.range z).filter Nat.Prime
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  change Squarefree (S.prod id)
  have hmain : ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → Squarefree (S.prod id) := by
    intro S hS
    induction S using Finset.induction_on with
    | empty => simp
    | insert p S hpS ih =>
      have hprim : p.Prime := hS p (Finset.mem_insert_self p S)
      have hsq_p : Squarefree p := by
        unfold Squarefree
        intro b hb
        have hbd : b ∣ p := by
          rcases hb with ⟨k, hk⟩
          refine ⟨b * k, ?_⟩
          calc
            p = b * b * k := hk
            _ = b * (b * k) := by ring
        rcases hprim.eq_one_or_self_of_dvd b hbd with hb1 | hbp
        · rw [hb1]
          simp
        · exfalso
          have hpp : p * p ∣ p := by
            rw [hbp] at hb
            exact hb
          have hp1 : p ∣ 1 := by
            rcases hpp with ⟨k, hk⟩
            have hmain : p * (p * k) = p * 1 := by
              calc
                p * (p * k) = (p * p) * k := by ring
                _ = p := hk.symm
                _ = p * 1 := by ring
            -- p·(p·k) = p ⟹ p·k = 1 (p > 0)
            refine ⟨k, ?_⟩
            exact (Nat.mul_left_cancel (Nat.Prime.pos hprim) hmain).symm
          exact (hprim.ne_one) (Nat.dvd_one.mp hp1)
      have hcop : p.Coprime (S.prod id) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        exact (Nat.coprime_primes hprim (hS q (Finset.mem_insert.mpr (Or.inr hq)))).mpr (by
          intro hpq
          apply hpS
          rwa [hpq])
      rw [Finset.prod_insert hpS]
      exact (Nat.squarefree_mul hcop).mpr ⟨hsq_p, ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))⟩
  exact hmain ((Finset.range z).filter Nat.Prime) hS

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
    simp [hp0]
    exact hp.pos
  nu_lt_one_of_prime := by
    intro p hp hdiv
    unfold switchingSieveNu
    have hp0 : p ≠ 0 := hp.ne_zero
    simp [hp0]
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

/-- **Region restriction for the triple-factor main term**: pairs with `a = p₁p₂ > N/2`
have `switchingCount = 0` by `switchingCount_eq_zero_of_N_lt_two_mul`. Thus the main-term sum
contains only pairs with `2·p₁p₂ ≤ N`, precisely the region where the π upper bound
(`N/a ≥ 2`) and subsequent distribution inputs apply. -/
theorem switchingCount_sum_eq_zero_region (N : ℕ) :
    (∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
      ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
        (switchingCount N (p₁ * p₂) : ℝ)) =
    (∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
      ∑ p₂ ∈ ((Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂)).filter
          (fun p₂ => 2 * (p₁ * p₂) ≤ N),
        (switchingCount N (p₁ * p₂) : ℝ)) := by
  apply Finset.sum_congr rfl
  intro p₁ hp₁
  symm
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂))
    (fun p₂ => 2 * (p₁ * p₂) ≤ N) (fun p₂ => switchingCount N (p₁ * p₂))]
  have hnot : (∑ p₂ ∈ ((Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂)).filter
      (fun p₂ => ¬ 2 * (p₁ * p₂) ≤ N), switchingCount N (p₁ * p₂)) = 0 := by
    apply Finset.sum_eq_zero
    intro p₂ hp₂
    have hp₂' : ¬ 2 * (p₁ * p₂) ≤ N := (Finset.mem_filter.mp hp₂).2
    have hNlt : N < 2 * (p₁ * p₂) := by omega
    exact switchingCount_eq_zero_of_N_lt_two_mul N (p₁ * p₂) hNlt
  rw [hnot]
  simp

/-- **π reduction of the triple-factor main term**: after restricting the region, each pair satisfies
`switchingCount N a ≤ #{p ≤ N/a : p prime}` by `switchingCount_le_pi`. Summing gives
a main term ≤ `Σ_{2p₁p₂ ≤ N} π(N/(p₁p₂))`, the elementary target for the triple-factor estimate. -/
theorem switchingCount_sum_le_pi_sum (N : ℕ) :
    (∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
      ∑ p₂ ∈ ((Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂)).filter
          (fun p₂ => 2 * (p₁ * p₂) ≤ N),
        (switchingCount N (p₁ * p₂) : ℝ)) ≤
    (∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
      ∑ p₂ ∈ ((Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂)).filter
          (fun p₂ => 2 * (p₁ * p₂) ≤ N),
        (((Finset.range (N / (p₁ * p₂) + 1)).filter Nat.Prime).card : ℝ)) := by
  apply Finset.sum_le_sum
  intro p₁ hp₁
  apply Finset.sum_le_sum
  intro p₂ hp₂
  have hp₁2 : 2 ≤ p₁ := (Finset.mem_filter.mp hp₁).2.1.two_le
  have hp₂2 : 2 ≤ p₂ := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₂).1).2.1.two_le
  exact switchingCount_le_pi N (p₁ * p₂) (by nlinarith [hp₁2, hp₂2])

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
  simp [hq0]

/-- **Selberg upper bound for the switching sieve**, an unconditional instance: the switched-set sifted sum satisfies
≤ `totalMass·(Σ selbergTerms)⁻¹ + errSum(Λ²w*)`. -/
theorem switchingSieve_upper_bound (N a : ℕ) :
    ∃ w : ℕ → ℝ, w 1 = 1 ∧
      (switchingSieve N a).siftedSum ≤
        (switchingSieve N a).totalMass *
          (∑ l ∈ (switchingSieve N a).prodPrimes.divisors,
            (switchingSieve N a).selbergTerms l)⁻¹ +
        (switchingSieve N a).errSum (BoundingSieve.lambdaSquared w) :=
  AnalyticNumberTheory.Sieve.selberg_upper_bound_optimal (switchingSieve N a)

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

/-- **Triple-factor part: main-term/error decomposition**, conditional on the stated inputs.
The triple-factor penalty sum is at most the main-term sum plus the error sum, where

  - main term: `Σ_{p₁,p₂} (N/(p₁p₂)+1)·primeProduct(z-1)`;
  - error: `Σ_{p₁,p₂} errSum(Λ²w*)`, with w* the optimal weight.

This is the structural decomposition for a bound of the form `3.9404·𝔖·N/log²N`: the intended main-term inputs
are Mertens estimates and numerical integration (Liu Lemma 4), and the error input is weighted Pan control. See the scale warning below. -/
theorem correctedChenOmega_triple_le_switchingSieveMainErr (N : ℕ) :
    (correctedChenCandidates N).sum
        (fun p => tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N)) ≤
      ∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
        ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
          switchingSieveMainErr N p₁ p₂ := by
  have hfinite := correctedChenOmega_triple_le_switchingCount N
  have hpair : ∀ p₁ ∈ (Finset.range (correctedChenY N)).filter
      (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
      ∀ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
        (switchingCount N (p₁ * p₂) : ℝ) ≤ switchingSieveMainErr N p₁ p₂ := by
    intro p₁ hp₁ p₂ hp₂
    have hsc := switchingCount_le_siftedSum N (p₁ * p₂)
    have hb := switchingSieve_upper_bound_optimal N (p₁ * p₂)
    have hmain := switchingSieve_mainTerm_eq_primeProduct N (p₁ * p₂)
    calc
      (switchingCount N (p₁ * p₂) : ℝ) ≤ (switchingSieve N (p₁ * p₂)).siftedSum := by
            exact_mod_cast hsc
      _ ≤ (switchingSieve N (p₁ * p₂)).totalMass *
              (∑ l ∈ (switchingSieve N (p₁ * p₂)).prodPrimes.divisors,
                (switchingSieve N (p₁ * p₂)).selbergTerms l)⁻¹ +
            (switchingSieve N (p₁ * p₂)).errSum
              (BoundingSieve.lambdaSquared
                (AnalyticNumberTheory.Sieve.optimalSelbergWeight (switchingSieve N (p₁ * p₂)))) := hb
      _ = switchingSieveMainErr N p₁ p₂ := by
            unfold switchingSieveMainErr
            rw [hmain]
  calc
    (correctedChenCandidates N).sum
        (fun p => tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N))
        ≤ ∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
            ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
              (switchingCount N (p₁ * p₂) : ℝ) := by
            simpa [switchingCount] using hfinite
    _ ≤ ∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
            ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
              switchingSieveMainErr N p₁ p₂ := by
            exact Finset.sum_le_sum (fun p₁ hp₁ => Finset.sum_le_sum
              (fun p₂ hp₂ => hpair p₁ hp₁ p₂ hp₂))

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

/-- **Final assembly of Chen's theorem**: weighted Pan input, the corrected `hTripleMain`,
the q¹ distribution bound, and the numerical condition imply Chen's theorem.

`hPrimePower_of_q1Count_bound` reduces the prime-power input to the q¹ bound, and
`properPower_negligible_threshold` discharges the negligible proper-power term.
This leaves only analytic inputs. On the `hPan` side, `ChenWeightedPanInput` is supplied by
`chenPanInput_of_sourceFaithfulSignedInputs`, which uses
`PanTypeICharacterMeanValue`, `PanTypeIICharacterMeanValue`, and
`PanSourceFaithfulSignedMainBound` with explicit `u,v`. The exact signed pointwise split
is proved internally in AnalyticNumberTheory; `PanLogEventuallyLarge` and `δ₁(0)=0` are instantiated.
Once these three analytic inputs and the two analytic bounds (`hTripleMain` and q¹) are supplied,
direct instantiation gives the full proof of `corrected_chens_theorem`. -/
theorem corrected_chens_theorem_of_q1Count_and_triple
    {cₘ Cq : ℝ} {N₀ₘ Nq : ℕ}
    (hPan : ChenWeightedPanInput)
    (hTripleMain : ∀ N : ℕ, N₀ₘ ≤ N → Even N →
      (∑ p₁ ∈ (Finset.range (correctedChenY N)).filter (fun p₁ => p₁.Prime ∧ correctedChenZ N ≤ p₁),
        ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ => p₂.Prime ∧ correctedChenY N ≤ p₂),
          (switchingCount N (p₁ * p₂) : ℝ)) ≤
        cₘ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2)
    (hq1 : ∀ N : ℕ, Nq ≤ N → Even N →
      correctedChenQ1Count N ≤ Cq * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
        (correctedChenZ N - 1) * (N : ℝ) / (log (N : ℝ)) ^ 2)
    (hCq : 0 < Cq)
    (hnum : (10 / 3 : ℝ) > (cₘ + (Cq + 1 / 2)) / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧ Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  rcases properPower_negligible_threshold with ⟨Nn, hneg'⟩
  let Cₚ : ℝ := Cq + 1 / 2
  let N₀ₚ : ℕ := max (max Nq Nn) (2 ^ 110 + 1)
  have hPrimePower' : ∀ N : ℕ, N₀ₚ ≤ N → Even N →
      (correctedChenCandidates N).sum
          (fun p => primePowerSum (N - p) (correctedChenZ N) (correctedChenY N)) ≤
        Cₚ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 := by
    intro N hN hEven
    have hNq : Nq ≤ N := by
      dsimp [N₀ₚ] at hN
      omega
    have hNn : Nn ≤ N := by
      dsimp [N₀ₚ] at hN
      omega
    have hNbig : 2 ^ 110 < N := by
      dsimp [N₀ₚ] at hN
      omega
    let 𝔖 : ℝ := AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1)
    let X : ℝ := (N : ℝ) / (log (N : ℝ)) ^ 2
    have hred := correctedChenPrimePowerSum_le_q1Count_add_negligible N hNbig hEven
    have hq1' : correctedChenQ1Count N ≤ Cq * 𝔖 * X := by
      dsimp [𝔖, X]
      rw [show Cq * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            ((N : ℝ) / (log (N : ℝ)) ^ 2) =
          Cq * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            (N : ℝ) / (log (N : ℝ)) ^ 2 by ring]
      exact hq1 N hNq hEven
    have hneg'' : 60 * (N : ℝ) ^ (9 / 10 : ℝ) ≤ (1 / 2 : ℝ) * 𝔖 * X := by
      dsimp [𝔖, X]
      rw [show (1 / 2 : ℝ) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            ((N : ℝ) / (log (N : ℝ)) ^ 2) =
          (1 / 2 : ℝ) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            (N : ℝ) / (log (N : ℝ)) ^ 2 by ring]
      exact hneg' N hNn hEven
    calc
      (correctedChenCandidates N).sum
          (fun p => primePowerSum (N - p) (correctedChenZ N) (correctedChenY N))
          ≤ correctedChenQ1Count N + 60 * (N : ℝ) ^ (9 / 10 : ℝ) := hred
      _ ≤ Cq * 𝔖 * X + (1 / 2 : ℝ) * 𝔖 * X := add_le_add hq1' hneg''
      _ = (Cq + 1 / 2) * 𝔖 * X := by ring
      _ = Cₚ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            (N : ℝ) / (log (N : ℝ)) ^ 2 := by
            dsimp [Cₚ, 𝔖, X]
            ring
  exact corrected_chens_theorem_of_omega_inputs hPan hTripleMain hPrimePower' hnum

/-- Conditional Chen theorem for the corrected-penalty development.  Its unique
assumption is precisely `CorrectedChenAnalyticPositivity`; the finite bridge and
representation extraction are valid, but the fixed-level q¹ route to this
positivity is numerically obstructed. -/
theorem corrected_chens_theorem (h : CorrectedChenAnalyticPositivity) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q :=
  corrected_key_inequality_implies_chen h

/-- Diagnostic direct lower bound for the public good-representation count.
This is stronger than the Jurkat--Richert weighted theorem and is not the
canonical literature contract. -/
def ChenGoodRepresentationLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    c * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) / Real.log N ^ 2 ≤
      ((chenGoodRepresentations N).card : ℝ)

/-- The diagnostic direct good-representation lower bound has a finite consumer:
positivity of its explicit main term makes the public good fibre nonempty. -/
theorem chens_theorem_of_good_representation_lower_bound
    (hSwitch : ChenGoodRepresentationLowerBound) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  rcases hSwitch with ⟨c, hc, N₀, hbound⟩
  refine ⟨max N₀ 1000, ?_⟩
  intro N hN hEven
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNlarge : 1000 ≤ N := le_trans (le_max_right _ _) hN
  have hNone : 1 < N := lt_of_lt_of_le (by norm_num : 1 < 1000) hNlarge
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hNone)
  have hz : 2 ≤ correctedChenZ N := by
    unfold correctedChenZ
    exact le_max_left _ _
  have hz1 : 1 ≤ correctedChenZ N - 1 := by omega
  have hseries : 0 < AnalyticNumberTheory.Sieve.singularSeriesTruncated N
      (correctedChenZ N - 1) :=
    AnalyticNumberTheory.Sieve.singularSeriesTruncated_pos N
      (correctedChenZ N - 1) hz1
  have hscale : 0 < c *
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N
        (correctedChenZ N - 1) * (N : ℝ) / Real.log N ^ 2 := by
    positivity
  have hcardReal : 0 < ((chenGoodRepresentations N).card : ℝ) :=
    hscale.trans_le (hbound N hN₀ hEven)
  have hcard : 0 < (chenGoodRepresentations N).card := by
    exact_mod_cast hcardReal
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations, Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨p, N - p, hp.2.1, hp.2.2.1, hp.2.2.2, by omega⟩

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

/-- The key difference is positive: 0.6706 > 0. -/
theorem chen_difference_pos : 0 < chen_difference_coefficient := by
  unfold chen_difference_coefficient chenW_coefficient chenOmega_coefficient
  norm_num

/-- Working expression for f(5): 2e^γ · log(5/2) / 5 ≈ 0.6528. -/
noncomputable def sieveF_at_5 : ℝ :=
  2 * exp Real.eulerMascheroniConstant * log (5/2) / 5

/-- Source of the W(N) coefficient: 10 · e^(-γ) · f(5) = 4 · log(5/2) ≈ 3.665...

Note: the full W(N) coefficient 2.6408 comes from the precise evaluation of the Jurkat-Richert sieve function f(5),
which involves explicit formulas for F(s)/f(s), not a simple algebraic simplification.
Here only the cancellation e^γ · e^(-γ) = 1 is verified. -/
theorem chenW_coefficient_simplification :
    sieveF_at_5 * exp (-Real.eulerMascheroniConstant) =
      2 * log (5/2) / 5 := by
  unfold sieveF_at_5
  have h_exp : exp Real.eulerMascheroniConstant * exp (-Real.eulerMascheroniConstant) = 1 := by
    rw [← Real.exp_add]
    have h_sum : Real.eulerMascheroniConstant + (-Real.eulerMascheroniConstant) = 0 := by linarith
    rw [h_sum, Real.exp_zero]
  have h_rearr : (2 * exp Real.eulerMascheroniConstant * log (5/2)) / 5 * exp (-Real.eulerMascheroniConstant) =
        (2 * log (5/2) * (exp Real.eulerMascheroniConstant * exp (-Real.eulerMascheroniConstant))) / 5 := by ring
  rw [h_rearr, h_exp]
  ring

/-- Source of the M₁ coefficient: 8 · 0.49254 = 3.94032. -/
theorem chenOmega_coefficient_derivation :
    (8 : ℝ) * 0.49254 = 3.94032 := by
  -- Lemma 3 gives Σ λ_{d₁} λ_{d₂} / φ([d₁,d₂]) ≈ 8 𝔖(N) / log N.
  -- Lemma 4 gives Σ f(a) / (a log(N/a)) ≤ 0.49254 / log N.
  -- Hence M₁ ≤ 8 · 0.49254 · 𝔖(N) N / log²N = 3.94032 𝔖(N) N / log²N.
  norm_num

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

/-- **Unconditional coarse bound for the switching identity**: the third term equals `(1/2) S(B, P, y) + C`,
where `|C| ≤ N+1`.

The former statement claimed `O(N^(1/3))`, but no switching correspondence between the two current finite-set
definitions has been formalized to justify that sharper error. This records the coarse bound obtained because
both counts are bounded by `range (N+1)`; the cube-root error requires a separate formalization of the switching principle. -/
theorem switching_identity (N z y : ℕ) (_hz : 2 ≤ z) (_hy : y ≤ N) :
    ∃ C : ℝ,
      (1/2 : ℝ) * ((Finset.range (N + 1)).filter (fun n =>
        (∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n) ∧
        ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
          z ≤ p₁ ∧ p₁ < y ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
          p₁ < p₂ ∧ p₂ < p₃ ∧ n = p₁ * p₂ * p₃)).card
      = (1/2 : ℝ) * switchedSieveSum N z y + C ∧
      |C| ≤ (N : ℝ) + 1 := by
  let A : ℝ := (((Finset.range (N + 1)).filter (fun n =>
    (∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n) ∧
    ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
      z ≤ p₁ ∧ p₁ < y ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
      p₁ < p₂ ∧ p₂ < p₃ ∧ n = p₁ * p₂ * p₃)).card : ℝ)
  let S : ℝ := switchedSieveSum N z y
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hAle : A ≤ (N : ℝ) + 1 := by
    dsimp [A]
    have hnat : ((Finset.range (N + 1)).filter (fun n =>
        (∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n) ∧
        ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
          z ≤ p₁ ∧ p₁ < y ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
          p₁ < p₂ ∧ p₂ < p₃ ∧ n = p₁ * p₂ * p₃)).card ≤ N + 1 := by
      calc
        _ ≤ (Finset.range (N + 1)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = N + 1 := Finset.card_range _
    exact_mod_cast hnat
  have hS0 : 0 ≤ S := by
    dsimp [S, switchedSieveSum]
    apply Finset.sum_nonneg
    intro n hn
    split <;> norm_num
  have hSlecard : S ≤ ((switchedSet N z y).card : ℝ) := by
    dsimp [S, switchedSieveSum]
    calc
      (switchedSet N z y).sum (fun n =>
          if (∀ p : ℕ, p.Prime → p < y → ¬ p ∣ n) then 1 else 0) ≤
          (switchedSet N z y).sum (fun _ => (1 : ℝ)) := by
            apply Finset.sum_le_sum
            intro n hn
            split <;> norm_num
      _ = ((switchedSet N z y).card : ℝ) := by simp
  have hScard : ((switchedSet N z y).card : ℝ) ≤ (N : ℝ) + 1 := by
    have hnat : (switchedSet N z y).card ≤ N + 1 := by
      unfold switchedSet
      calc
        _ ≤ (Finset.range (N + 1)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = N + 1 := Finset.card_range _
    exact_mod_cast hnat
  have hSle : S ≤ (N : ℝ) + 1 := hSlecard.trans hScard
  refine ⟨A / 2 - S / 2, ?_, ?_⟩
  · change (1 / 2 : ℝ) * A = (1 / 2 : ℝ) * S + (A / 2 - S / 2)
    ring
  · rw [abs_le]
    constructor <;> nlinarith

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
    have hinv := correctedChenNu_inv_prime (N := N) hpp hpc.2.1
    have hpos : 0 < (1 - correctedChenNu p) := by
      have hnum : 0 < ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
        have hcast : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
        have hpm1 : 0 < (p : ℝ) - 1 := by linarith
        have hpm2 : 0 < (p : ℝ) - 2 := by linarith
        exact div_pos hpm1 hpm2
      rw [← hinv] at hnum
      exact inv_pos.mp hnum
    exact le_of_lt hpos)

/-- Independent instance of the uniform JR lower bound for the corrected Chen sieve:
the ordinary Möbius function is a lower Möbius sequence, and `mainSum mu = V` exactly.
Taking `fs = 1` and `eta0 = 1/2` gives `X*V*(1-1/2) - errSum(1) <= siftedSum`.

This independently applies the `UniformJurkatRichertLowerBound`
interface, with uniform quantifiers `N₀, eta0` preceding `forall N`,
to recover a lower bound of the same form as `correctedChenCandidates_card_ge_X_mul_sieveProduct_sub_errSum`. -/
theorem correctedChenJR_ant_lower_bound :
    AnalyticNumberTheory.Sieve.UniformJurkatRichertLowerBound
      correctedChenBoundingSieve (fun N => (N : ℝ) ^ (1 / 10 : ℝ))
      (fun N => (N : ℝ) ^ (1 / 2 : ℝ)) (fun _ => 1) := by
  let mu : ℕ → ℝ := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)
  refine ⟨2, 1 / 2, by norm_num, ?_⟩
  intro N hN hEven
  refine ⟨mu, ?_, ?_, ?_⟩
  · simpa [mu] using moebius_real_isLowerMoebius
  · intro d
    simpa [mu] using abs_moebius_real_le_one d
  · have hV : AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (correctedChenBoundingSieve N) = correctedChenSieveProduct N := by
      unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors correctedChenSieveProduct
      rfl
    have hmain : (correctedChenBoundingSieve N).mainSum mu =
        correctedChenSieveProduct N := by
      simpa [mu] using mainSum_moebius_eq_correctedChenSieveProduct N
    have hVnonneg : 0 ≤ correctedChenSieveProduct N :=
      correctedChenSieveProduct_pos_aux N
    have hineq : correctedChenSieveProduct N * (1 - 1 / 2) ≤
        correctedChenSieveProduct N := by
      nlinarith
    have hmainterm : AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
          (correctedChenBoundingSieve N) * (1 - 1 / 2) ≤
        (correctedChenBoundingSieve N).mainSum mu := by
      rw [hV, hmain]
      exact hineq
    have hmass : 0 ≤ (correctedChenBoundingSieve N).totalMass := by
      unfold BoundingSieve.totalMass correctedChenBoundingSieve
      exact div_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))
    exact AnalyticNumberTheory.Sieve.siftedSum_lower_bound_of_mainTerm
      (S := correctedChenBoundingSieve N) (fs := fun _ => 1)
      (t := ((N : ℝ) ^ (1 / 2 : ℝ)) / ((N : ℝ) ^ (1 / 10 : ℝ)))
      (η := (1 / 2 : ℝ)) (muMinus := mu) hmass
      (by simpa [mu] using moebius_real_isLowerMoebius)
      (by intro d; simpa [mu] using abs_moebius_real_le_one d)
      hmainterm

/-- **Independent positivity route, without Ω**: the `UniformJurkatRichertLowerBound` instance
with the exact ordinary Möbius main term, together with weighted Pan control of `errSum`,
gives strictly positive corrected-candidate counts for sufficiently large even numbers:

  `0 < card(correctedChenCandidates N)`.

This is parallel to the direct proof using `correctedChenCandidates_card_ge_X_mul_sieveProduct_sub_errSum`.
Here the same lower bound follows through the JR interface, with uniform quantifiers `N₀, eta₀` before `∀ N` and
`X·V·(1-eta₀) - errSum(1) ≤ siftedSum = card`. -/
theorem correctedChenPositivity_via_jr_ant
    (hjr : AnalyticNumberTheory.Sieve.UniformJurkatRichertLowerBound
      correctedChenBoundingSieve (fun N => (N : ℝ) ^ (1 / 10 : ℝ))
      (fun N => (N : ℝ) ^ (1 / 2 : ℝ)) (fun _ => 1))
    (hPan : ChenWeightedPanInput) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      0 < ((correctedChenCandidates N).card : ℝ) := by
  obtain ⟨N₀m, hm⟩ := CorrectedChenMainTermLower_singularSeries_units
  rcases hPan 3 (by norm_num : 0 < (3 : ℝ)) with ⟨C, hC, hbound⟩
  have hErr : ∀ N : ℕ, 1000 ≤ N → Even N →
      (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤ C * (N : ℝ) / (log (N : ℝ)) ^ 3 := by
    intro N hN hEven
    exact le_trans (correctedChenErrSum_le_weightedPanInput N) (by
      simpa [Real.rpow_natCast] using hbound N hN hEven)
  let T : ℝ := 6 * C / 5
  let M : ℕ := Nat.ceil (Real.exp T) + 1
  let N₀ : ℕ := max (max N₀m 1000) (max M 59049)
  refine ⟨N₀, ?_⟩
  intro N hN hEven
  have hNm : N₀m ≤ N := by
    dsimp [N₀] at hN
    omega
  have hN1000 : 1000 ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNM : M ≤ N := by
    dsimp [N₀] at hN
    omega
  have hN59049 : 59049 ≤ N := by
    dsimp [N₀] at hN
    omega
  have hlogN : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hT : T < log (N : ℝ) := by
    have hce : Real.exp T ≤ (Nat.ceil (Real.exp T) : ℝ) := Nat.le_ceil (Real.exp T)
    have hcm : (Nat.ceil (Real.exp T) : ℝ) < (N : ℝ) := by
      have h1 : (Nat.ceil (Real.exp T) + 1 : ℕ) ≤ N := hNM
      have h1r : ((Nat.ceil (Real.exp T) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
      have hlt : (Nat.ceil (Real.exp T) : ℝ) < ((Nat.ceil (Real.exp T) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.lt_succ_self (Nat.ceil (Real.exp T)))
      exact lt_of_lt_of_le hlt h1r
    have hstrict : Real.exp T < (N : ℝ) := lt_of_le_of_lt hce hcm
    have hloglt : Real.log (Real.exp T) < log (N : ℝ) :=
      Real.log_lt_log (Real.exp_pos T) hstrict
    rwa [Real.log_exp] at hloglt
  have hCdiv : C / log (N : ℝ) < (5 / 6 : ℝ) := by
    have hT' : (6 * C) / 5 < log (N : ℝ) := by
      simpa [T] using hT
    have hmul := mul_lt_mul_of_pos_right hT' (by norm_num : 0 < (5 : ℝ))
    have hcross : C * 6 < 5 * log (N : ℝ) := by
      field_simp at hmul ⊢
      nlinarith
    rw [div_lt_iff₀ hlogN]
    nlinarith
  have hz : 2 ≤ correctedChenZ N - 1 := correctedChenZ_sub_one_ge_two_of_large hN59049
  have h𝔖 : (1 / 2 : ℝ) ≤
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) :=
    singularSeriesTruncated_ge_half hz
  have h𝔖pos : 0 < AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) :=
    AnalyticNumberTheory.Sieve.singularSeriesTruncated_pos N (correctedChenZ N - 1) (by omega)
  have hmainN := hm N hNm hEven
  have hErrN := hErr N hN1000 hEven
  -- The JR instance gives X·V·(1/2) - errSum(1) ≤ card.
  rcases hjr with ⟨N₀jr, η₀, hη₀, hjrN⟩
  have hN2 : 2 ≤ N := by omega
  have hjrN' : (correctedChenBoundingSieve N).totalMass *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (correctedChenBoundingSieve N) *
        (1 - 1 / 2) - (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
      (correctedChenBoundingSieve N).siftedSum := by
    have hV' : AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
          (correctedChenBoundingSieve N) = correctedChenSieveProduct N := by
      unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors correctedChenSieveProduct
      rfl
    have hmain' : (correctedChenBoundingSieve N).mainSum
          (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) =
        correctedChenSieveProduct N :=
      mainSum_moebius_eq_correctedChenSieveProduct N
    have hmainterm : AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
          (correctedChenBoundingSieve N) * (1 - 1 / 2) ≤
        (correctedChenBoundingSieve N).mainSum
          (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
      rw [hV', hmain']
      have hVnonneg : 0 ≤ correctedChenSieveProduct N :=
        correctedChenSieveProduct_pos_aux N
      nlinarith
    exact AnalyticNumberTheory.Sieve.siftedSum_lower_bound_of_mainTerm
      (S := correctedChenBoundingSieve N) (fs := fun _ => 1)
      (t := ((N : ℝ) ^ (1 / 2 : ℝ)) / ((N : ℝ) ^ (1 / 10 : ℝ)))
      (η := (1 / 2 : ℝ))
      (muMinus := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
      (by
        unfold BoundingSieve.totalMass correctedChenBoundingSieve
        exact div_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))
          (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))))
      moebius_real_isLowerMoebius abs_moebius_real_le_one hmainterm
  have hlow : (correctedChenBoundingSieve N).totalMass *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (correctedChenBoundingSieve N) *
        (1 - 1 / 2) - (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
      ((correctedChenCandidates N).card : ℝ) := by
    rw [← correctedChenBoundingSieve_siftedSum_eq_card N]
    exact hjrN'
  have hV : AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (correctedChenBoundingSieve N) = correctedChenSieveProduct N := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors correctedChenSieveProduct
    rfl
  have hX : (correctedChenBoundingSieve N).totalMass = (N : ℝ) / log (N : ℝ) := rfl
  have hmaj : (5 / 3 : ℝ) *
        AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        (N : ℝ) / (log (N : ℝ)) ^ 2 ≤
      (correctedChenBoundingSieve N).totalMass *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (correctedChenBoundingSieve N) *
        (1 - 1 / 2) := by
    have hle0 : (5 / 3 : ℝ) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 ≤
        (10 / 3 : ℝ) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 * (1 / 2) := by
      ring_nf
      exact le_rfl
    have hmain2 := le_trans hle0 (mul_le_mul_of_nonneg_right hmainN (by norm_num : 0 ≤ (1 / 2 : ℝ)))
    rw [hX] at hmain2
    rw [hV, hX]
    norm_num at hmain2 ⊢
    simpa [mul_assoc] using hmain2
  have hCsmall : C * (N : ℝ) / (log (N : ℝ)) ^ 3 <
      (5 / 3 : ℝ) *
        AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        (N : ℝ) / (log (N : ℝ)) ^ 2 := by
    have h𝔖56 : (5 / 6 : ℝ) ≤
        (5 / 3 : ℝ) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) := by
      nlinarith [h𝔖, h𝔖pos]
    have hC : C / log (N : ℝ) < (5 / 6 : ℝ) := hCdiv
    have hX3 : 0 < (N : ℝ) / (log (N : ℝ)) ^ 2 := by
      exact div_pos (by positivity : (0 : ℝ) < N) (pow_pos hlogN 2)
    have hmul2 := mul_lt_mul_of_pos_right hC hX3
    have h𝔖N : C / log (N : ℝ) * ((N : ℝ) / (log (N : ℝ)) ^ 2) <
        (5 / 3 : ℝ) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          ((N : ℝ) / (log (N : ℝ)) ^ 2) := by
      exact lt_of_lt_of_le (by simpa using hmul2) (by
        exact mul_le_mul_of_nonneg_right h𝔖56 (le_of_lt hX3))
    have hrewL : C * (N : ℝ) / (log (N : ℝ)) ^ 3 =
        (C / log (N : ℝ)) * ((N : ℝ) / (log (N : ℝ)) ^ 2) := by
      field_simp [hlogN.ne']
    have hrewR : (5 / 3 : ℝ) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 =
        (5 / 3 : ℝ) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          ((N : ℝ) / (log (N : ℝ)) ^ 2) := by
      field_simp [hlogN.ne']
    rwa [hrewL, hrewR]
  have hpos : 0 < (correctedChenBoundingSieve N).totalMass *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (correctedChenBoundingSieve N) *
        (1 - 1 / 2) - (correctedChenBoundingSieve N).errSum (fun _ => 1) := by
    have h1 : C * (N : ℝ) / (log (N : ℝ)) ^ 3 <
        (5 / 3 : ℝ) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 := hCsmall
    have h2 : (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
        C * (N : ℝ) / (log (N : ℝ)) ^ 3 := hErrN
    have h3 : (5 / 3 : ℝ) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 ≤
        (correctedChenBoundingSieve N).totalMass *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (correctedChenBoundingSieve N) *
          (1 - 1 / 2) := hmaj
    linarith
  have hcardpos : 0 < ((correctedChenCandidates N).card : ℝ) := by
    have hhlow : (correctedChenBoundingSieve N).totalMass *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (correctedChenBoundingSieve N) *
          (1 - 1 / 2) - (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
        ((correctedChenCandidates N).card : ℝ) := hlow
    linarith
  exact hcardpos

/-- The canonical JR weighted lower bound reaches Chen's theorem once the
remaining genuine strict-triple penalty has its source-scale upper bound. -/
theorem chensTheorem_of_jurkatRichertWeightedLowerBound_and_triplePenalty
    (hJR : ChenJurkatRichertWeightedLowerBound)
    (hTriple : ChenJurkatRichertTriplePenaltyUpperBound) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  obtain ⟨C, hC, hTripleEvent⟩ := hTriple
  have hJRsmall := hJR (1 / 10 : ℝ) (by norm_num)
  have hrem := eventually_jr_inverseLogRemainder_le_scale
    C (1 / 10 : ℝ) hC (by norm_num)
  have hall : ∀ᶠ N : ℕ in Filter.atTop, Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
    filter_upwards [hJRsmall, hTripleEvent, hrem,
      Filter.eventually_ge_atTop 9] with N hJRN hTN hremN hN
    intro hEven
    let M : ℝ := SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log N ^ (2 : ℕ)
    have hlog : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hM : 0 < M := by
      dsimp [M]
      exact div_pos
        (mul_pos (SingularSeries.liuSingularSeries_pos N)
          (by exact_mod_cast (show 0 < N by omega)))
        (pow_pos hlog 2)
    have hJR' : (2.6408 - 1 / 10 : ℝ) * M ≤
        jurkatRichertWeightedCount N := by
      convert hJRN hEven using 1 <;> dsimp [M] <;> ring
    have hT0 := hTN hEven
    have hR0 := hremN hEven
    have hT : correctedChenTriplePenalty N ≤
        (3.94033 + 1 / 10 : ℝ) * M := by
      calc
        correctedChenTriplePenalty N ≤
            3.94033 * SingularSeries.liuSingularSeries N * (N : ℝ) /
                Real.log N ^ (2 : ℕ) +
              C * (N : ℝ) / Real.log N ^ (3 : ℕ) := hT0
        _ ≤ 3.94033 * M + (1 / 10 : ℝ) * M := by
          apply add_le_add
          · dsimp [M]
            ring_nf
            exact le_rfl
          · dsimp [M]
            have heq :
                (1 / 10 : ℝ) *
                    (SingularSeries.liuSingularSeries N * (N : ℝ) /
                      Real.log N ^ (2 : ℕ)) =
                  (1 / 10 : ℝ) * SingularSeries.liuSingularSeries N *
                    (N : ℝ) / Real.log N ^ (2 : ℕ) := by ring
            rw [heq]
            exact hR0
        _ = (3.94033 + 1 / 10 : ℝ) * M := by ring
    apply corrected_key_inequality_implies_chen_at hN
    rw [correctedChenKeyCount_eq_jurkatRichertWeightedCount_sub_triple]
    nlinarith
  exact Filter.eventually_atTop.1 hall



end MathlibNt.SieveTheory.SwitchingPrinciple

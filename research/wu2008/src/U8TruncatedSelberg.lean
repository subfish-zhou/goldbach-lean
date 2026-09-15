import U8TwoDimensionalDensity
import AnalyticNumberTheory.Sieve.SelbergUpperBound

/-! Truncated Selberg optimization for any positive admissible local density.
Unlike the full-divisor optimizer, the weights here vanish above the free level R. -/
noncomputable section
open Finset
open scoped BigOperators ArithmeticFunction.Moebius
namespace U8Literal.SmallProduct.TruncatedSelberg
open scoped Classical

def C (S : BoundingSieve) (R : ℝ) : Finset ℕ :=
  S.prodPrimes.divisors.filter fun d => (d : ℝ) ≤ R

def G (S : BoundingSieve) (R : ℝ) : ℝ := ∑ d ∈ C S R, S.selbergTerms d

def X (S : BoundingSieve) (R : ℝ) (e : ℕ) : ℝ :=
  if e ∈ C S R then (μ e : ℝ) * S.selbergTerms e / G S R else 0

def weight (S : BoundingSieve) (R : ℝ) (d : ℕ) : ℝ :=
  if d ∣ S.prodPrimes then
    (∑ e ∈ S.prodPrimes.divisors, if d ∣ e then (μ (e/d) : ℝ)*X S R e else 0) / S.nu d
  else 0

theorem G_pos (S : BoundingSieve) {R : ℝ} (hR : 1 ≤ R) : 0 < G S R := by
  apply Finset.sum_pos
  · intro d hd
    exact S.selbergTerms_pos (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
  · exact ⟨1, mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd _, S.prodPrimes_ne_zero⟩,
      by simpa using hR⟩⟩

theorem X_zero (S : BoundingSieve) {R : ℝ} {e : ℕ} (h : R < e) : X S R e = 0 := by
  simp [X, C, not_le.mpr h]

theorem weight_zero (S : BoundingSieve) {R : ℝ} {d : ℕ}
    (h : ¬ d ∣ S.prodPrimes ∨ R < d) : weight S R d = 0 := by
  unfold weight
  split_ifs with hd
  · rcases h with h | h
    · exact (h hd).elim
    · apply (div_eq_zero_iff).mpr
      left
      apply sum_eq_zero
      intro e he
      split_ifs with hde
      · have hde' : (d : ℝ) ≤ e := by
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero
            (ne_zero_of_dvd_ne_zero S.prodPrimes_ne_zero (Nat.mem_divisors.mp he).1)) hde
        rw [X_zero S (h.trans_le hde'), mul_zero]
      · rfl
  · rfl

theorem weight_support (S : BoundingSieve) {R : ℝ} {d : ℕ}
    (h : weight S R d ≠ 0) : d ∈ C S R := by
  apply mem_filter.mpr
  have hd : d ∣ S.prodPrimes := by
    by_contra hn
    exact h (weight_zero S (Or.inl hn))
  refine ⟨Nat.mem_divisors.mpr ⟨hd, S.prodPrimes_ne_zero⟩, ?_⟩
  by_contra hn
  exact h (weight_zero S (Or.inr (lt_of_not_ge hn)))

theorem weight_one (S : BoundingSieve) {R : ℝ} (hR : 1 ≤ R) : weight S R 1 = 1 := by
  rw [weight, if_pos (one_dvd _), S.nu_mult.map_one, div_one]
  simp only [one_dvd, if_true, Nat.div_one]
  have heq : ∀ e ∈ S.prodPrimes.divisors,
      (μ e : ℝ) * X S R e = if e ∈ C S R then S.selbergTerms e / G S R else 0 := by
    intro e he
    have hmu : (μ e : ℝ)^2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (S.squarefree_of_mem_divisors_prodPrimes he)
    unfold X
    split_ifs <;> try simp only [mul_zero]
    calc
      _ = (μ e : ℝ)^2 * S.selbergTerms e / G S R := by ring
      _ = _ := by rw [hmu, one_mul]
  simp_rw [Finset.sum_congr rfl heq]
  rw [← sum_filter]
  have hc : S.prodPrimes.divisors.filter (fun e => e ∈ C S R) = C S R :=
    filter_mem_eq_inter |>.trans (inter_eq_right.mpr (filter_subset _ _))
  rw [hc, ← sum_div]
  exact div_self (G_pos S hR).ne'

private theorem reverse_cancel (S : BoundingSieve) {l e : ℕ}
    (he : e ∈ S.prodPrimes.divisors) :
    (∑ d ∈ S.prodPrimes.divisors,
      if l ∣ d ∧ d ∣ e then (μ (e/d) : ℝ) else 0) =
      if e = l then 1 else 0 := by
  have he0 := ne_zero_of_dvd_ne_zero S.prodPrimes_ne_zero (Nat.mem_divisors.mp he).1
  by_cases hl : l ∣ e
  · have hf : S.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ∣ e) =
        e.divisors.filter fun d => l ∣ d := by
      ext d
      simp only [mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨_,hld,hde⟩
        exact ⟨⟨hde,he0⟩,hld⟩
      · rintro ⟨⟨hde,_⟩,hld⟩
        exact ⟨⟨hde.trans (Nat.mem_divisors.mp he).1,S.prodPrimes_ne_zero⟩,hld,hde⟩
    rw [← sum_filter, hf, sum_filter]
    exact AnalyticNumberTheory.Sieve.sum_moebius_quotient_of_dvd he0 hl
  · have hne : e ≠ l := fun h => hl (h ▸ dvd_refl e)
    rw [if_neg hne]
    apply sum_eq_zero
    intro d _
    exact if_neg (fun h => hl (h.1.trans h.2))

theorem diagonal (S : BoundingSieve) (R : ℝ) {l : ℕ} (hl : l ∣ S.prodPrimes) :
    (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * weight S R d else 0) =
      X S R l := by
  have hw (d : ℕ) (hd : d ∈ S.prodPrimes.divisors) :
      S.nu d * weight S R d =
        ∑ e ∈ S.prodPrimes.divisors, if d ∣ e then (μ (e/d) : ℝ)*X S R e else 0 := by
    rw [weight, if_pos (Nat.mem_divisors.mp hd).1]
    exact mul_div_cancel₀ _ (S.nu_ne_zero (Nat.mem_divisors.mp hd).1)
  have hexp :
      (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * weight S R d else 0) =
      ∑ d ∈ S.prodPrimes.divisors, ∑ e ∈ S.prodPrimes.divisors,
        (if l ∣ d ∧ d ∣ e then (μ (e/d) : ℝ) else 0)*X S R e := by
    apply sum_congr rfl
    intro d hd
    rw [hw d hd]
    by_cases hld : l ∣ d <;> simp [hld, ite_mul]
  rw [hexp, sum_comm]
  simp_rw [← sum_mul]
  have hc := fun (e : ℕ) (he : e ∈ S.prodPrimes.divisors) => reverse_cancel S (l := l) he
  simp_rw [Finset.sum_congr rfl (fun e he => congrArg (fun z : ℝ => z * X S R e) (hc e he))]
  simp only [ite_mul, one_mul, zero_mul]
  exact sum_ite_eq_of_mem' _ l _ (Nat.mem_divisors.mpr ⟨hl,S.prodPrimes_ne_zero⟩)

theorem main_eq (S : BoundingSieve) {R : ℝ} (hR : 1 ≤ R) :
    S.mainSum (BoundingSieve.lambdaSquared (weight S R)) = 1 / G S R := by
  rw [S.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hpoint (l : ℕ) (hl : l ∈ S.prodPrimes.divisors) :
      (S.selbergTerms l)⁻¹ *
        (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * weight S R d else 0)^2 =
      if l ∈ C S R then S.selbergTerms l / (G S R)^2 else 0 := by
    rw [diagonal S R (Nat.mem_divisors.mp hl).1, X]
    split_ifs
    · have hg := (S.selbergTerms_pos (Nat.mem_divisors.mp hl).1).ne'
      have hmu : (μ l : ℝ)^2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (S.squarefree_of_mem_divisors_prodPrimes hl)
      rw [div_pow, mul_pow, hmu, one_mul]
      field_simp
    · simp
  rw [sum_congr rfl hpoint, ← sum_filter]
  have hc : S.prodPrimes.divisors.filter (fun e => e ∈ C S R) = C S R :=
    filter_mem_eq_inter |>.trans (inter_eq_right.mpr (filter_subset _ _))
  rw [hc, ← sum_div]
  change G S R / (G S R)^2 = 1 / G S R
  field_simp [(G_pos S hR).ne']

theorem abs_X (S : BoundingSieve) {R : ℝ} (hR : 1 ≤ R) (e : ℕ) :
    |X S R e| = if e ∈ C S R then S.selbergTerms e / G S R else 0 := by
  unfold X
  split_ifs with he
  · have heQ := (Nat.mem_divisors.mp (mem_filter.mp he).1).1
    have hmu : |(μ e : ℝ)| = 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        (S.squarefree_of_dvd_prodPrimes heQ)
    rw [abs_div, abs_mul, hmu, one_mul,
      abs_of_pos (S.selbergTerms_pos heQ), abs_of_pos (G_pos S hR)]
  · exact abs_zero

theorem sum_abs_X (S : BoundingSieve) {R : ℝ} (hR : 1 ≤ R) :
    (∑ e ∈ S.prodPrimes.divisors, |X S R e|) = 1 := by
  simp_rw [abs_X S hR]
  rw [← sum_filter]
  have hc : S.prodPrimes.divisors.filter (fun e => e ∈ C S R) = C S R :=
    filter_mem_eq_inter |>.trans (inter_eq_right.mpr (filter_subset _ _))
  rw [hc, ← sum_div]
  exact div_self (G_pos S hR).ne'

/-- A polynomially usable coarse bound; no unproved bounded-weight interface. -/
theorem abs_weight_le_inv (S : BoundingSieve) {R : ℝ} (hR : 1 ≤ R)
    {d : ℕ} (hd : d ∣ S.prodPrimes) : |weight S R d| ≤ 1 / S.nu d := by
  rw [weight, if_pos hd, abs_div, abs_of_pos (S.nu_pos_of_dvd_prodPrimes hd)]
  apply div_le_div_of_nonneg_right _ (S.nu_pos_of_dvd_prodPrimes hd).le
  calc
    _ ≤ ∑ e ∈ S.prodPrimes.divisors,
        |if d ∣ e then (μ (e/d) : ℝ)*X S R e else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ S.prodPrimes.divisors, |X S R e| := by
      apply sum_le_sum
      intro e _
      split_ifs
      · rw [abs_mul]
        have hmu : |(μ (e/d) : ℝ)| ≤ 1 := by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := e/d))
        simpa using mul_le_mul_of_nonneg_right hmu (abs_nonneg (X S R e))
      · simp
    _ = 1 := sum_abs_X S hR

end U8Literal.SmallProduct.TruncatedSelberg

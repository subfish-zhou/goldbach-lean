import Wu04BypassTargetBudget
import U8CanonicalMother

noncomputable section
namespace WuTarget.W16
open Finset Real
open scoped Classical

abbrev ordinaryP2 (N : ℕ) : Finset ℕ :=
  MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N

def good (N : ℕ) : Finset ℕ :=
  (ordinaryP2 N).filter fun p => ∃ r q : ℕ,
    (r = 1 ∨ r.Prime) ∧ q.Prime ∧ N = p + r*q ∧
      (r : ℝ) ≤ (q : ℝ) ^ (4469/5000 : ℝ)

def bad (N : ℕ) : Finset ℕ :=
  (ordinaryP2 N).filter fun p => ∃ r q : ℕ,
    r.Prime ∧ q.Prime ∧ r ≤ q ∧ N = p + r*q ∧
      (q : ℝ) ^ (4469/5000 : ℝ) < (r : ℝ)

def units (N : ℕ) : Finset ℕ :=
  (ordinaryP2 N).filter fun p => N-p = 1

def smallBad (N : ℕ) (η : ℝ) : Finset ℕ :=
  (bad N).filter fun p => ((N-p : ℕ) : ℝ) ≤ η*N

def largeBad (N : ℕ) (η : ℝ) : Finset ℕ :=
  (bad N).filter fun p => ¬ ((N-p : ℕ) : ℝ) ≤ η*N

theorem ordinaryP2_literal (N : ℕ) :
    ordinaryP2 N = (Finset.range (N+1)).filter
      (fun p => p.Prime ∧ 0 < N-p ∧ ArithmeticFunction.cardFactors (N-p) ≤ 2) := rfl

theorem factor_cases {n : ℕ} (hn : 0 < n)
    (hΩ : ArithmeticFunction.cardFactors n ≤ 2) :
    n = 1 ∨ n.Prime ∨ ∃ r q : ℕ, r.Prime ∧ q.Prime ∧ r ≤ q ∧ n = r*q := by
  by_cases hn1 : n = 1
  · exact Or.inl hn1
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hn1
  obtain ⟨q, hnq⟩ := hrd
  have hq0 : q ≠ 0 := by intro h; simp [h] at hnq; omega
  have hΩq : ArithmeticFunction.cardFactors q ≤ 1 := by
    rw [hnq, ArithmeticFunction.cardFactors_mul hr.ne_zero hq0,
      ArithmeticFunction.cardFactors_apply_prime hr] at hΩ
    omega
  by_cases hqΩ : ArithmeticFunction.cardFactors q = 0
  · have hq1 := (ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp hqΩ).resolve_left hq0
    exact Or.inr (Or.inl (by simpa [hnq, hq1] using hr))
  have hq : q.Prime := ArithmeticFunction.cardFactors_eq_one_iff_prime.mp (by omega)
  right
  right
  rcases le_total r q with h | h
  · exact ⟨r, q, hr, hq, h, hnq⟩
  · exact ⟨q, r, hq, hr, h, hnq.trans (mul_comm r q)⟩

theorem ordinary_cover (N : ℕ) :
    ordinaryP2 N ⊆ good N ∪ bad N ∪ units N := by
  intro p hp
  have hp' := hp
  rw [ordinaryP2_literal] at hp'
  obtain ⟨hpr, hpprime, hn, hΩ⟩ := Finset.mem_filter.mp hp'
  have hpN : p ≤ N := by have := Finset.mem_range.mp hpr; omega
  have hsum : N = p + (N-p) := by omega
  rcases factor_cases hn hΩ with hu | hprime | ⟨r,q,hr,hq,hrq,hm⟩
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp,hu⟩))
  · apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_filter.mpr
    refine ⟨hp,1,N-p,Or.inl rfl,hprime,by simpa using hsum,?_⟩
    simpa only [Nat.cast_one] using Real.one_le_rpow
      (x := ((N-p : ℕ) : ℝ)) (z := (4469/5000 : ℝ))
      (by exact_mod_cast hprime.one_lt.le) (by norm_num)
  · have hsum' : N = p+r*q := by rw [← hm]; exact hsum
    by_cases hgood : (r : ℝ) ≤ (q : ℝ) ^ (4469/5000 : ℝ)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hp,r,q,Or.inr hr,hq,hsum',hgood⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hp,r,q,hr,hq,hrq,hsum',lt_of_not_ge hgood⟩))))

theorem units_card_le_one (N : ℕ) : (units N).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  omega

theorem bad_split (N : ℕ) (η : ℝ) :
    (smallBad N η).card + (largeBad N η).card = (bad N).card :=
  Finset.card_filter_add_card_filter_not _

theorem finite_subtraction (N : ℕ) (η : ℝ) :
    ((ordinaryP2 N).card : ℝ) - 1 -
      ((smallBad N η).card : ℝ) - ((largeBad N η).card : ℝ) ≤
        ((good N).card : ℝ) := by
  have hcover := Finset.card_le_card (ordinary_cover N)
  have hunion := Finset.card_union_le (good N ∪ bad N) (units N)
  have hpair := Finset.card_union_le (good N) (bad N)
  have hu := units_card_le_one N
  have hs := bad_split N η
  have hnat : (ordinaryP2 N).card ≤
      (good N).card + (smallBad N η).card + (largeBad N η).card + 1 := by omega
  have hreal : ((ordinaryP2 N).card : ℝ) ≤
      ((good N).card : ℝ) + ((smallBad N η).card : ℝ) +
        ((largeBad N η).card : ℝ) + 1 := by exact_mod_cast hnat
  linarith only [hreal]

theorem representation_of_good_nonempty {N : ℕ} (h : (good N).Nonempty) :
    ∃ p r q : ℕ, p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
      N = p+r*q ∧ (r : ℝ) ≤ (q : ℝ) ^ (4469/5000 : ℝ) := by
  obtain ⟨p,hp⟩ := h
  obtain ⟨hp, r,q,hr,hq,hs,hpow⟩ := Finset.mem_filter.mp hp
  rw [ordinaryP2_literal] at hp
  exact ⟨p,r,q,(Finset.mem_filter.mp hp).2.1,hr,hq,hs,hpow⟩

theorem target_lt_safe : (8 * log (5000/4469) : ℝ) < 4491/5000 :=
  Wu04BypassBudget.target_lt_safe

def margin : ℝ := 4491/5000 - 8*log (5000/4469)

theorem margin_pos : 0 < margin := sub_pos.mpr target_lt_safe

theorem same_N_exit {N : ℕ} {c η ε₀ εs εl εu : ℝ}
    (hN : 512 ≤ N) (hc : 4491/5000 ≤ c)
    (hbudget : ε₀ + εs + εl + εu ≤ margin/2)
    (hcount : (c-ε₀)*U8CanonicalMother.M N ≤ ((ordinaryP2 N).card : ℝ))
    (hsmall : ((smallBad N η).card : ℝ) ≤ εs*U8CanonicalMother.M N)
    (hlarge : ((largeBad N η).card : ℝ) ≤
      (8*log (5000/4469)+εl)*U8CanonicalMother.M N)
    (hunit : 1 ≤ εu*U8CanonicalMother.M N) :
    margin/2*U8CanonicalMother.M N ≤ ((good N).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p+r*q ∧ (r : ℝ) ≤ (q : ℝ) ^ (4469/5000 : ℝ) := by
  have hM : 0 < U8CanonicalMother.M N :=
    Wu2008DoubleSieve.HighSixPhase6.original_scale_positive hN
  have hcoef : margin/2 ≤ c-ε₀-εs-(8*log (5000/4469)+εl)-εu := by
    unfold margin at *
    linarith only [hc,hbudget]
  have hmul := mul_le_mul_of_nonneg_right hcoef hM.le
  have hsub := finite_subtraction N η
  have hgood : margin/2*U8CanonicalMother.M N ≤ ((good N).card : ℝ) := by
    nlinarith only [hmul,hcount,hsmall,hlarge,hunit,hsub]
  refine ⟨hgood, representation_of_good_nonempty ?_⟩
  apply Finset.card_pos.mp
  have hpos := (mul_pos (half_pos margin_pos) hM).trans_le hgood
  exact_mod_cast hpos

end WuTarget.W16

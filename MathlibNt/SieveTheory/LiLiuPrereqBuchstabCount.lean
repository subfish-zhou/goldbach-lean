import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Actual rough integers and the finite Buchstab identity

The carrier consists of positive natural numbers bounded by a real number.
The cutoff excludes primes strictly below `z`; in particular the unit is
retained and a prime equal to the cutoff is not excluded.
-/

set_option autoImplicit false

open scoped BigOperators

namespace LiLiuPrereqBuchstab

def Rough (z : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → z ≤ (p : ℝ)

noncomputable def roughNumbers (x z : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊x⌋₊ + 1)).filter
    (fun n => 0 < n ∧ (n : ℝ) ≤ x ∧ Rough z n)

noncomputable def roughCount (x z : ℝ) : ℕ := (roughNumbers x z).card

@[simp] theorem mem_roughNumbers {x z : ℝ} {n : ℕ} :
    n ∈ roughNumbers x z ↔ 0 < n ∧ (n : ℝ) ≤ x ∧ Rough z n := by
  classical
  simp only [roughNumbers, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Nat.lt_succ_iff.mpr (Nat.le_floor h.2.1), h⟩

theorem rough_iff_no_small_prime {z : ℝ} {n : ℕ} :
    Rough z n ↔ ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬p ∣ n := by
  constructor
  · intro h p hp hpz hpn
    exact (not_lt_of_ge (h p hp hpn)) hpz
  · intro h p hp hpn
    exact le_of_not_gt (fun hpz => h p hp hpz hpn)

theorem rough_one (z : ℝ) : Rough z 1 := by
  intro p hp hp1
  exact (hp.ne_one (Nat.dvd_one.mp hp1)).elim

@[simp] theorem one_mem_roughNumbers {x z : ℝ} :
    1 ∈ roughNumbers x z ↔ 1 ≤ x := by
  simp [rough_one]

theorem rough_mono {y z : ℝ} (hyz : y ≤ z) {n : ℕ}
    (hn : Rough z n) : Rough y n :=
  fun p hp hpn => hyz.trans (hn p hp hpn)

theorem roughNumbers_mono {x y z : ℝ} (hyz : y ≤ z) :
    roughNumbers x z ⊆ roughNumbers x y := by
  intro n hn
  obtain ⟨hn, hnx, hr⟩ := mem_roughNumbers.mp hn
  exact mem_roughNumbers.mpr ⟨hn, hnx, rough_mono hyz hr⟩

theorem rough_iff_minFac {z : ℝ} {n : ℕ} (hn : n ≠ 1) :
    Rough z n ↔ z ≤ (n.minFac : ℝ) := by
  constructor
  · intro h
    exact h n.minFac (Nat.minFac_prime hn) (Nat.minFac_dvd n)
  · intro h p hp hpn
    exact h.trans (by exact_mod_cast Nat.minFac_le_of_dvd hp.two_le hpn)

theorem rough_mul_prime {p m : ℕ} (hp : p.Prime) (hm : Rough (p : ℝ) m) :
    Rough (p : ℝ) (p * m) := by
  intro q hq hqpm
  rcases hq.dvd_mul.mp hqpm with hqp | hqm
  · have hqp' : q = p := (Nat.dvd_prime hp).mp hqp |>.resolve_left hq.ne_one
    exact_mod_cast hqp'.ge
  · exact hm q hq hqm

theorem minFac_mul_of_rough {p m : ℕ} (hp : p.Prime)
    (hm : Rough (p : ℝ) m) : (p * m).minFac = p := by
  have hne : p * m ≠ 1 := by
    intro h
    exact hp.ne_one (Nat.eq_one_of_dvd_one (h ▸ dvd_mul_right p m))
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p m)
  · exact_mod_cast (rough_iff_minFac hne).mp (rough_mul_prime hp hm)

theorem rough_div_minFac (n : ℕ) :
    Rough (n.minFac : ℝ) (n / n.minFac) := by
  intro p hp hpd
  have hpn : p ∣ n :=
    dvd_trans hpd (Nat.div_dvd_of_dvd (Nat.minFac_dvd n))
  exact_mod_cast Nat.minFac_le_of_dvd hp.two_le hpn

theorem rough_of_dvd {z : ℝ} {m n : ℕ} (hmn : m ∣ n) (hn : Rough z n) :
    Rough z m :=
  fun p hp hpm => hn p hp (dvd_trans hpm hmn)

/-- Only primes at most `x` can occur as least factors of the removed integers. -/
noncomputable def sievingPrimes (x y z : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊x⌋₊ + 1)).filter
    (fun p => p.Prime ∧ (p : ℝ) ≤ x ∧ y ≤ (p : ℝ) ∧ (p : ℝ) < z)

@[simp] theorem mem_sievingPrimes {x y z : ℝ} {p : ℕ} :
    p ∈ sievingPrimes x y z ↔
      p.Prime ∧ (p : ℝ) ≤ x ∧ y ≤ (p : ℝ) ∧ (p : ℝ) < z := by
  classical
  simp only [sievingPrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Nat.lt_succ_iff.mpr (Nat.le_floor h.2.1), h⟩

theorem removed_ne_one {x y z : ℝ} {n : ℕ}
    (hn : n ∈ roughNumbers x y \ roughNumbers x z) : n ≠ 1 := by
  classical
  obtain ⟨hy, hz⟩ := Finset.mem_sdiff.mp hn
  intro he
  subst n
  exact hz (one_mem_roughNumbers.mpr (one_mem_roughNumbers.mp hy))

theorem minFac_mem_sievingPrimes {x y z : ℝ} {n : ℕ}
    (hn : n ∈ roughNumbers x y \ roughNumbers x z) :
    n.minFac ∈ sievingPrimes x y z := by
  classical
  have hn1 := removed_ne_one hn
  obtain ⟨hy, hz⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hn0, hnx, hry⟩ := mem_roughNumbers.mp hy
  have hminn : (n.minFac : ℝ) ≤ n := by
    exact_mod_cast Nat.le_of_dvd hn0 (Nat.minFac_dvd n)
  have hmin : (n.minFac : ℝ) ≤ x := hminn.trans hnx
  refine mem_sievingPrimes.mpr
    ⟨Nat.minFac_prime hn1, hmin, (rough_iff_minFac hn1).mp hry, ?_⟩
  by_contra h
  exact hz (mem_roughNumbers.mpr
    ⟨hn0, hnx, (rough_iff_minFac hn1).mpr (le_of_not_gt h)⟩)

/-- Multiplication by the least prime factor is an actual finite bijection.
The cofactor may still be divisible by `p`, as required at prime squares. -/
theorem card_leastFactor_fiber {x y z : ℝ} {p : ℕ}
    (hp : p.Prime) (hyp : y ≤ (p : ℝ)) (hpz : (p : ℝ) < z) :
    ((roughNumbers x y \ roughNumbers x z).filter
      (fun n => n.minFac = p)).card = roughCount (x / p) p := by
  classical
  symm
  unfold roughCount
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply Finset.card_bij (fun m _ => p * m)
  · intro m hm
    obtain ⟨hm0, hmx, hrm⟩ := mem_roughNumbers.mp hm
    have hpm0 : 0 < p * m := Nat.mul_pos hp.pos hm0
    have hpmx : ((p * m : ℕ) : ℝ) ≤ x := by
      push_cast
      nlinarith [(le_div_iff₀ hp0).mp hmx]
    refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨?_, ?_⟩,
      minFac_mul_of_rough hp hrm⟩
    · exact mem_roughNumbers.mpr
        ⟨hpm0, hpmx, rough_mono hyp (rough_mul_prime hp hrm)⟩
    · intro hz
      have h := (mem_roughNumbers.mp hz).2.2 p hp (dvd_mul_right p m)
      exact (not_le_of_gt hpz) h
  · intro m₁ _ m₂ _ he
    exact Nat.eq_of_mul_eq_mul_left hp.pos he
  · intro n hn
    obtain ⟨hnmem, hmin⟩ := Finset.mem_filter.mp hn
    have hn1 := removed_ne_one hnmem
    have hpd : p ∣ n := hmin ▸ Nat.minFac_dvd n
    obtain ⟨hn0, hnx, _⟩ :=
      mem_roughNumbers.mp (Finset.mem_sdiff.mp hnmem).1
    have hrn : Rough (p : ℝ) n :=
      (rough_iff_minFac hn1).mpr (by rw [hmin])
    rcases hpd with ⟨m, rfl⟩
    have hm0 : 0 < m := by
      by_contra h
      have : m = 0 := by omega
      simp [this] at hn0
    refine ⟨m, mem_roughNumbers.mpr ⟨hm0, ?_,
      rough_of_dvd (dvd_mul_left m p) hrn⟩, rfl⟩
    apply (le_div_iff₀ hp0).mpr
    simpa only [Nat.cast_mul, mul_comm] using hnx

/-- Exact Buchstab decomposition of the actual positive-integer rough count,
with real upper bounds and the strict small-prime cutoff. -/
theorem roughCount_buchstab {x y z : ℝ} (hyz : y ≤ z) :
    roughCount x y = roughCount x z +
      ∑ p ∈ sievingPrimes x y z, roughCount (x / p) p := by
  classical
  have hf :
      (roughNumbers x y \ roughNumbers x z).card =
        ∑ p ∈ sievingPrimes x y z,
          ((roughNumbers x y \ roughNumbers x z).filter
            (fun n => n.minFac = p)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun _ hn => minFac_mem_sievingPrimes hn)
  have hc := Finset.card_sdiff_add_card_eq_card (roughNumbers_mono (x := x) hyz)
  unfold roughCount
  rw [← hc, hf, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp, _, hyp, hpz⟩ := mem_sievingPrimes.mp hp
  exact card_leastFactor_fiber hp hyp hpz

end LiLiuPrereqBuchstab
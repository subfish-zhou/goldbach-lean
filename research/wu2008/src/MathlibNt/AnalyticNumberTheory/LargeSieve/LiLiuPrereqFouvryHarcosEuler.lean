import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosLPolynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Finite Euler coefficient identities for actual monic polynomials

This is the algebraic, coefficientwise version of the Euler-product argument
in Harcos, §3, Lemma 7 and Theorem 6 (`pages/harcos-lpolynomial-05.png`–`07.png`).
The multiplicities below are those of the actual polynomial factorization.
-/

noncomputable section

open Finset Polynomial UniqueFactorizationMonoid

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {p : ℕ} [Fact p.Prime]

/-- The coefficient obtained by summing a multiplicative weight over actual monics. -/
def harcosEulerCoefficient (η : (ZMod p)[X] →* ℂ) (n : ℕ) : ℂ :=
  ∑ f ∈ harcosMonicPolynomials p n, η f

/-- A coefficient with one marked occurrence of an irreducible factor. -/
def harcosEulerMarked (η : (ZMod p)[X] →* ℂ) (k : (ZMod p)[X]) (n : ℕ) : ℂ :=
  ∑ f ∈ harcosMonicPolynomials p n, ((normalizedFactors f).count k : ℂ) * η f

/-- Every monic irreducible of degree at most the cutoff, with no duplicates. -/
def harcosEulerPrimes (p n : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] := by
  classical
  exact (range (n + 1)).biUnion fun d ↦
    (harcosMonicPolynomials p d).filter Irreducible

theorem mem_harcosEulerPrimes (n : ℕ) (k : (ZMod p)[X]) :
    k ∈ harcosEulerPrimes p n ↔ k.Monic ∧ Irreducible k ∧ k.natDegree ≤ n := by
  classical
  simp only [harcosEulerPrimes, mem_biUnion, mem_range, mem_filter,
    mem_harcosMonicPolynomials]
  constructor
  · rintro ⟨d, hd, ⟨hm, he⟩, hi⟩
    exact ⟨hm, hi, by omega⟩
  · rintro ⟨hm, hi, hd⟩
    exact ⟨k.natDegree, by omega, ⟨hm, rfl⟩, hi⟩

private theorem euler_count_eq_zero_of_not_dvd (k f : (ZMod p)[X]) (h : ¬ k ∣ f) :
    (normalizedFactors f).count k = 0 := by
  classical
  apply Multiset.count_eq_zero.mpr
  intro hm
  exact h (dvd_of_mem_normalizedFactors hm)

private theorem euler_count_mul (k f : (ZMod p)[X]) (hk : k.Monic)
    (hi : Irreducible k) (hf : f.Monic) :
    (normalizedFactors (k * f)).count k = 1 + (normalizedFactors f).count k := by
  classical
  rw [normalizedFactors_mul hk.ne_zero hf.ne_zero,
    normalizedFactors_irreducible hi, hk.normalize_eq_self, Multiset.count_add]
  simp

theorem harcosEulerMarked_eq_zero (η : (ZMod p)[X] →* ℂ)
    (k : (ZMod p)[X]) (n : ℕ) (hn : n < k.natDegree) :
    harcosEulerMarked η k n = 0 := by
  classical
  apply sum_eq_zero
  intro f hf
  obtain ⟨hm, hd⟩ := (mem_harcosMonicPolynomials n f).mp hf
  have hnd : ¬ k ∣ f := by
    intro h
    have := natDegree_le_of_dvd h hm.ne_zero
    omega
  simp [euler_count_eq_zero_of_not_dvd k f hnd]

theorem harcosEulerMarked_add_degree (η : (ZMod p)[X] →* ℂ)
    (k : (ZMod p)[X]) (hk : k.Monic) (hi : Irreducible k) (n : ℕ) :
    harcosEulerMarked η k (k.natDegree + n) =
      η k * (harcosEulerCoefficient η n + harcosEulerMarked η k n) := by
  classical
  unfold harcosEulerMarked harcosEulerCoefficient
  rw [← sum_add_distrib, mul_sum]
  have hfilter :
      (∑ f ∈ harcosMonicPolynomials p (k.natDegree + n),
          ((normalizedFactors f).count k : ℂ) * η f) =
        ∑ f ∈ (harcosMonicPolynomials p (k.natDegree + n)).filter (k ∣ ·),
          ((normalizedFactors f).count k : ℂ) * η f := by
    symm
    apply sum_subset (filter_subset _ _)
    intro f hf hnf
    have hnd : ¬ k ∣ f := by simpa [hf] using hnf
    simp [euler_count_eq_zero_of_not_dvd k f hnd]
  rw [hfilter]
  symm
  apply sum_bij (fun f _ ↦ k * f)
  · intro f hf
    obtain ⟨hm, hd⟩ := (mem_harcosMonicPolynomials n f).mp hf
    exact mem_filter.mpr ⟨(mem_harcosMonicPolynomials _ _).mpr
      ⟨hk.mul hm, by rw [hk.natDegree_mul hm, hd]⟩, dvd_mul_right k f⟩
  · intro f _ g _ he
    exact mul_left_cancel₀ hk.ne_zero he
  · intro f hf
    obtain ⟨hfm, hd⟩ := (mem_harcosMonicPolynomials _ _).mp (mem_filter.mp hf).1
    obtain ⟨g, rfl⟩ := (mem_filter.mp hf).2
    have hg := hk.of_mul_monic_left hfm
    refine ⟨g, (mem_harcosMonicPolynomials _ _).mpr ⟨hg, ?_⟩, rfl⟩
    rw [hk.natDegree_mul hg] at hd
    omega
  · intro f hf
    have hm := ((mem_harcosMonicPolynomials n f).mp hf).1
    rw [euler_count_mul k f hk hi hm, map_mul, Nat.cast_add, Nat.cast_one]
    ring

private theorem euler_degree_sum (f : (ZMod p)[X]) (hf : f.Monic) :
    ((normalizedFactors f).map natDegree).sum = f.natDegree := by
  have hprod : (normalizedFactors f).prod = f := by
    simpa [hf.leadingCoeff] using leadingCoeff_mul_prod_normalizedFactors f
  rw [← natDegree_multiset_prod _ (zero_notMem_normalizedFactors f), hprod]

theorem harcosEuler_degree_marked (η : (ZMod p)[X] →* ℂ) (n : ℕ) :
    (n : ℂ) * harcosEulerCoefficient η n =
      ∑ k ∈ harcosEulerPrimes p n, (k.natDegree : ℂ) * harcosEulerMarked η k n := by
  classical
  unfold harcosEulerCoefficient harcosEulerMarked
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro f hf
  obtain ⟨hm, hd⟩ := (mem_harcosMonicPolynomials n f).mp hf
  have hsub : (normalizedFactors f).toFinset ⊆ harcosEulerPrimes p n := by
    intro k hk
    obtain ⟨hi, hkm, hkd⟩ :=
      (Polynomial.mem_normalizedFactors_iff hm.ne_zero).mp (Multiset.mem_toFinset.mp hk)
    exact (mem_harcosEulerPrimes n k).mpr
      ⟨hkm, hi, hd ▸ natDegree_le_of_dvd hkd hm.ne_zero⟩
  have hs : ∑ k ∈ harcosEulerPrimes p n,
      k.natDegree * (normalizedFactors f).count k = n := by
    have hdeg := euler_degree_sum f hm
    rw [sum_multiset_map_count, hd] at hdeg
    calc
      _ = ∑ k ∈ (normalizedFactors f).toFinset,
          (normalizedFactors f).count k • k.natDegree := by
        simp only [nsmul_eq_mul, mul_comm]
        symm
        apply sum_subset hsub
        intro k _ hk
        simp [Multiset.count_eq_zero.mpr (by simpa using hk)]
      _ = n := hdeg
  have hsc := congrArg (fun x : ℕ ↦ (x : ℂ)) hs
  push_cast at hsc
  rw [← hsc, sum_mul]
  apply sum_congr rfl
  intro k _
  ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

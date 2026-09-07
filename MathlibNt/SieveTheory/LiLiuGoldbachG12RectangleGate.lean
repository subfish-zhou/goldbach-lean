import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFSmall
import MathlibNt.SieveTheory.LiLiuGoldbachG12GateBudget

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open AnalyticNumberTheory.LargeSieve

namespace G12RectangleGate

def linkEmbed (A : Finset (ℕ × ℕ)) : Finset GoldbachG12LinkedAtom :=
  A.image G12RectangleWF.linkedEmbed

/-- All prime factors of the full product, including the short prime. -/
theorem atom_data {N : ℕ} {ε : ℝ} (hN : 2 ≤ N)
    {x : GoldbachG12LinkedAtom} (hx : x ∈ goldbachG12LinkedAtoms N ε) :
    0 < x.1*x.2 ∧ x.1*x.2 < N ∧
    (∀ p ∈ (x.1*x.2).primeFactors, (N : ℝ)^(4/53 : ℝ) ≤ (p : ℝ)) ∧
    (x.1*x.2).primeFactors.card ≤ 20 := by
  obtain ⟨hm,hr⟩ := mem_sigma.mp hx
  have hm0 := (goldbachG12ActiveProductSupport_data hm).1
  have hrp := (mem_filter.mp hr).2.1
  have hpos : 0 < x.1*x.2 := Nat.mul_pos hm0 hrp.pos
  have hle := goldbachG12LinkedPrimeWindow_product_le hm hr
  have hout := goldbachG12LinkedPrimeWindow_output_pos hm hr
  have hlt : x.1*x.2 < N := by rw [mul_comm]; omega
  have hz : (N : ℝ)^(4/53 : ℝ) ≤ (x.2 : ℝ) :=
    ((goldbachG12PiLiEndpoints_bounds hN hm).1.trans_lt (mem_filter.mp hr).2.2.1).le
  have hf : ∀ p ∈ (x.1*x.2).primeFactors, (N : ℝ)^(4/53 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
    rcases hpp.dvd_mul.mp hpd with hpm | hpr
    · exact (goldbachG12ActiveProductSupport_primeFactors hm).1 p
        (Nat.mem_primeFactors.mpr ⟨hpp,hpm,ne_of_gt hm0⟩)
    · have he : p = x.2 := (Nat.dvd_prime hrp).mp hpr |>.resolve_left hpp.ne_one
      simpa only [he] using hz
  refine ⟨hpos,hlt,hf,?_⟩
  have he : (x.1*x.2).primeFactors =
      largePrimeDivisors (x.1*x.2) ((N : ℝ)^(4/53 : ℝ)) :=
    (filter_eq_self.mpr hf).symm
  rw [he]
  exact largePrimeDivisors_card_le_twenty hpos hlt (by norm_num)

/-- Weighted global mass uses the established output-fibre bound, not injectivity. -/
theorem linked_mass_le {N : ℕ} (hN : 2 ≤ N) (ε : ℝ) :
    (∑ x ∈ goldbachG12LinkedAtoms N ε, goldbachG12NormalizedCoefficient N x.1) ≤
      20*(N : ℝ) := by
  have he : goldbachG12LinkedSmallOutputMass N ε (N : ℝ) =
      ∑ x ∈ goldbachG12LinkedAtoms N ε, goldbachG12NormalizedCoefficient N x.1 := by
    rw [G12RectangleWF.linked_small_test]
    apply sum_congr rfl
    intro x hx
    have hd := atom_data hN hx
    have hh : N-x.2*x.1 < N := by rw [mul_comm]; omega
    simp only [Nat.ceil_natCast, if_pos hh]
  simpa only [he, Nat.ceil_natCast] using goldbachG12LinkedSmallOutputMass_le hN ε (N : ℝ)

theorem subset_mass_le {N : ℕ} {ε : ℝ} {A : Finset (ℕ × ℕ)}
    (hN : 2 ≤ N) (hA : linkEmbed A ⊆ goldbachG12LinkedAtoms N ε) :
    (∑ p ∈ A, goldbachG12NormalizedCoefficient N p.1) ≤ 20*(N : ℝ) := by
  calc
    _ = ∑ x ∈ linkEmbed A, goldbachG12NormalizedCoefficient N x.1 := by
      unfold linkEmbed
      rw [sum_image]
      · rfl
      · exact fun _ _ _ _ h => G12RectangleWF.linkedEmbed_injective h
    _ ≤ ∑ x ∈ goldbachG12LinkedAtoms N ε, goldbachG12NormalizedCoefficient N x.1 :=
      sum_le_sum_of_subset_of_nonneg hA
        (fun x _ _ => (goldbachG12NormalizedCoefficient_bounds N x.1).1)
    _ ≤ _ := linked_mass_le hN ε

/-- A nonnegative finite union bound; the signed original gate is untouched. -/
theorem gate_le_mass {N q : ℕ} {A : Finset (ℕ × ℕ)} {Q : Finset ℕ}
    {c : ℕ → ℝ} {z : ℝ} {K : ℕ}
    (hq : q ≤ N) (hz : 0 < z) (hQ : Q ⊆ Icc 1 q)
    (hc : ∀ d ∈ reducedModuli Q (N : ℤ), |c d| ≤ 1)
    (hpos : ∀ p ∈ A, 0 < p.1*p.2)
    (hf : ∀ p ∈ A, ∀ l ∈ (p.1*p.2).primeFactors, z ≤ (l : ℝ))
    (hK : ∀ p ∈ A, (p.1*p.2).primeFactors.card ≤ K) :
    |G12RectangleWF.gate N A Q c| ≤
      ((2*K/z)*conductorHarmonicFactor N^2) *
        ∑ p ∈ A, goldbachG12NormalizedCoefficient N p.1 := by
  let w := goldbachG12NormalizedCoefficient N
  have hw (m : ℕ) : 0 ≤ w m := (goldbachG12NormalizedCoefficient_bounds N m).1
  have hnon (d : ℕ) : 0 ≤ ∑ p ∈ A,
      (if ¬(p.1*p.2).Coprime d then (d.totient : ℝ)⁻¹ else 0)*w p.1 := by
    apply sum_nonneg
    intro p _
    have := hw p.1
    split_ifs <;> positivity
  have he (d : ℕ) :
      (∑ p ∈ A, if ¬(p.1*p.2).Coprime d then w p.1 else 0)/(d.totient : ℝ) =
      ∑ p ∈ A, (if ¬(p.1*p.2).Coprime d then (d.totient : ℝ)⁻¹ else 0)*w p.1 := by
    rw [div_eq_mul_inv, sum_mul]
    apply sum_congr rfl
    intro p _
    split_ifs <;> ring
  calc
    _ ≤ ∑ d ∈ reducedModuli Q (N : ℤ),
        |c d * ((∑ p ∈ A, if ¬(p.1*p.2).Coprime d then w p.1 else 0)/(d.totient : ℝ))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ reducedModuli Q (N : ℤ), ∑ p ∈ A,
        (if ¬(p.1*p.2).Coprime d then (d.totient : ℝ)⁻¹ else 0)*w p.1 := by
      apply sum_le_sum
      intro d hd
      rw [he, abs_mul, abs_of_nonneg (hnon d)]
      exact mul_le_of_le_one_left (hnon d) (hc d hd)
    _ ≤ ∑ d ∈ Icc 1 q, ∑ p ∈ A,
        (if ¬(p.1*p.2).Coprime d then (d.totient : ℝ)⁻¹ else 0)*w p.1 :=
      sum_le_sum_of_subset_of_nonneg
        (fun _ hd => hQ (mem_filter.mp hd).1) (fun d _ _ => hnon d)
    _ = ∑ p ∈ A, (∑ d ∈ Icc 1 q,
        if ¬(p.1*p.2).Coprime d then (d.totient : ℝ)⁻¹ else 0)*w p.1 := by
      rw [sum_comm]
      simp only [sum_mul]
    _ ≤ ∑ p ∈ A, ((2*K/z)*conductorHarmonicFactor N^2)*w p.1 := by
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (G11FiniteGate.bad_inverseTotientMass_le hq (hpos p hp) hz (hf p hp) (hK p hp)) (hw p.1)
    _ = _ := (mul_sum _ _ _).symm

/-- Full-product gcd gate, uniformly for every subset of the original linked atoms. -/
theorem gate_le {N q : ℕ} {ε : ℝ} {A : Finset (ℕ × ℕ)}
    {Q : Finset ℕ} {c : ℕ → ℝ} (hN : 2 ≤ N) (hq : q ≤ N)
    (hA : linkEmbed A ⊆ goldbachG12LinkedAtoms N ε) (hQ : Q ⊆ Icc 1 q)
    (hc : ∀ d ∈ reducedModuli Q (N : ℤ), |c d| ≤ 1) :
    |G12RectangleWF.gate N A Q c| ≤
      (800*N/(N : ℝ)^(4/53 : ℝ))*(1+Real.log (N : ℝ))^2 := by
  have hz : 0 < (N : ℝ)^(4/53 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hd (p : ℕ × ℕ) (hp : p ∈ A) :=
    atom_data hN (hA (mem_image.mpr ⟨p,hp,rfl⟩))
  have hb := gate_le_mass (K := 20) hq hz hQ hc
    (fun p hp => (hd p hp).1) (fun p hp => (hd p hp).2.2.1)
    (fun p hp => (hd p hp).2.2.2)
  calc
    _ ≤ ((2*(20 : ℕ)/(N : ℝ)^(4/53 : ℝ))*conductorHarmonicFactor N^2) *
        ∑ p ∈ A, goldbachG12NormalizedCoefficient N p.1 := hb
    _ ≤ ((2*(20 : ℕ)/(N : ℝ)^(4/53 : ℝ))*conductorHarmonicFactor N^2)*(20*N) :=
      mul_le_mul_of_nonneg_left (subset_mass_le hN hA) (by positivity)
    _ = (800*N/(N : ℝ)^(4/53 : ℝ))*conductorHarmonicFactor N^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (conductorHarmonicFactor_nonneg N) (conductorHarmonicFactor_le N) 2)
      (by positivity)

end G12RectangleGate

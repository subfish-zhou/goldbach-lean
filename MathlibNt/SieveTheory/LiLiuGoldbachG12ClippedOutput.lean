import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedConsumers
import MathlibNt.SieveTheory.LiLiuGoldbachG12RosserFactor

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12ClippedWindow

def atoms (N : ℕ) (L U : ℕ → ℝ) : Finset GoldbachG12LinkedAtom :=
  (goldbachG12ActiveProductSupport N).sigma (window N L U)

def outputSupport (N : ℕ) (L U : ℕ → ℝ) : Finset ℕ :=
  (atoms N L U).image (goldbachG12LinkedOutput N)

/-- All representations of one output retain their actual long weights. -/
def outputWeight (N : ℕ) (g L U : ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ x ∈ (atoms N L U).filter (fun x => goldbachG12LinkedOutput N x = p), g x.1

variable {N : ℕ} {ε : ℝ} {g L U : ℕ → ℝ}

theorem atoms_subset (h : Admissible N ε g L U) :
    atoms N L U ⊆ goldbachG12LinkedAtoms N ε := by
  intro x hx
  obtain ⟨hm,hr⟩ := mem_sigma.mp hx
  exact mem_sigma.mpr ⟨hm,window_subset h hm hr⟩

theorem outputWeight_nonneg (h : Admissible N ε g L U) (p : ℕ) :
    0 ≤ outputWeight N g L U p :=
  sum_nonneg fun x hx => (h x.1 (mem_sigma.mp (mem_filter.mp hx).1).1).1.1

/-- Pointwise domination of whole fibres; no output injection is asserted. -/
theorem outputWeight_le_old (h : Admissible N ε g L U) (p : ℕ) :
    outputWeight N g L U p ≤ goldbachG12LinkedOutputWeight N ε p := by
  calc
    _ ≤ ∑ x ∈ (atoms N L U).filter (fun x => goldbachG12LinkedOutput N x = p),
        goldbachG12NormalizedCoefficient N x.1 :=
      sum_le_sum fun x hx => (h x.1 (mem_sigma.mp (mem_filter.mp hx).1).1).1.2
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (filter_subset_filter _ (atoms_subset h))
      (fun x _ _ => (goldbachG12NormalizedCoefficient_bounds N x.1).1)

theorem outputWeight_le_twenty (hN : 2 ≤ N) (h : Admissible N ε g L U) (p : ℕ) :
    outputWeight N g L U p ≤ 20 :=
  (outputWeight_le_old h p).trans (goldbachG12LinkedOutputWeight_le_twenty hN ε p)

theorem output_pos (h : Admissible N ε g L U) {x : GoldbachG12LinkedAtom}
    (hx : x ∈ atoms N L U) : 0 < goldbachG12LinkedOutput N x := by
  obtain ⟨hm,hr⟩ := mem_sigma.mp (atoms_subset h hx)
  exact goldbachG12LinkedPrimeWindow_output_pos hm hr

theorem zero_not_mem_outputSupport (h : Admissible N ε g L U) :
    0 ∉ outputSupport N L U := by
  rintro hz
  obtain ⟨x,hx,he⟩ := mem_image.mp hz
  have := output_pos h hx
  omega

/-- Exact pushforward for arbitrary output predicates, including divisibility. -/
theorem output_sum (N : ℕ) (g L U : ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ p ∈ (outputSupport N L U).filter P, outputWeight N g L U p) =
    ∑ m ∈ goldbachG12ActiveProductSupport N, g m *
      (((window N L U m).filter (fun r => P (N-r*m))).card : ℝ) := by
  let A := atoms N L U
  let out := goldbachG12LinkedOutput N
  let T := (A.image out).filter P
  have hf := Finset.sum_fiberwise_eq_sum_filter A T out (fun x => g x.1)
  have hfilter : A.filter (fun x => out x ∈ T) = A.filter (fun x => P (out x)) := by
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨hx,hT⟩
      exact ⟨hx,(mem_filter.mp hT).2⟩
    · rintro ⟨hx,hp⟩
      exact ⟨hx,mem_filter.mpr ⟨mem_image.mpr ⟨x,hx,rfl⟩,hp⟩⟩
  rw [hfilter] at hf
  calc
    _ = ∑ x ∈ A.filter (fun x => P (out x)), g x.1 := hf
    _ = _ := by
      rw [sum_filter]
      dsimp [A,atoms]
      rw [sum_sigma]
      apply sum_congr rfl
      intro m _
      change (∑ r ∈ window N L U m, if P (N-r*m) then g m else 0) = _
      rw [← sum_filter]
      simp [mul_comm]

/-- Ungated prime outputs, not the coprime-r subcount. -/
def primeOutput (N : ℕ) (g L U : ℕ → ℝ) : ℝ :=
  400 * ∑ m ∈ goldbachG12ActiveProductSupport N, g m *
    (((window N L U m).filter (fun r => (N-r*m).Prime)).card : ℝ)

def siftedMass (N : ℕ) (g L U : ℕ → ℝ) (Z : ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N, g m *
    (((window N L U m).filter (fun r => (goldbachB10ProdPrimes N Z).Coprime (N-r*m))).card : ℝ)

/-- Only support and weights change; the ordinary prime product and nu do not. -/
def outputSieve (N : ℕ) (hEven : Even N) (g L U : ℕ → ℝ) (ε : ℝ)
    (h : Admissible N ε g L U) (Z X : ℝ) : BoundingSieve :=
  { goldbachB10BoundingSieve N hEven 0 0 0 Z X with
    support := outputSupport N L U
    weights := outputWeight N g L U
    weights_nonneg := outputWeight_nonneg h }

theorem outputSieve_multSum (hEven : Even N) (h : Admissible N ε g L U) (Z X : ℝ) (d : ℕ) :
    (outputSieve N hEven g L U ε h Z X).multSum d =
      ∑ m ∈ goldbachG12ActiveProductSupport N, g m *
        (((window N L U m).filter (fun r => d ∣ N-r*m)).card : ℝ) := by
  unfold BoundingSieve.multSum
  change (∑ p ∈ outputSupport N L U, if d ∣ p then outputWeight N g L U p else 0) = _
  rw [← sum_filter]
  exact output_sum N g L U (fun p => d ∣ p)

theorem outputSieve_siftedSum (hEven : Even N) (h : Admissible N ε g L U) (Z X : ℝ) :
    (outputSieve N hEven g L U ε h Z X).siftedSum = siftedMass N g L U Z := by
  unfold BoundingSieve.siftedSum
  change (∑ p ∈ outputSupport N L U,
    if (goldbachB10ProdPrimes N Z).Coprime p then outputWeight N g L U p else 0) = _
  rw [← sum_filter]
  exact output_sum N g L U (fun p => (goldbachB10ProdPrimes N Z).Coprime p)

theorem outputSieve_rem (hEven : Even N) (h : Admissible N ε g L U) (Z : ℝ)
    {d : ℕ} (hd : d ∣ goldbachB10ProdPrimes N Z) :
    (outputSieve N hEven g L U ε h Z (mass N g L U)).rem d =
      commonResidual N g L U d := by
  have hnu : (outputSieve N hEven g L U ε h Z (mass N g L U)).nu d = 1/(d.totient : ℝ) :=
    goldbachB10BoundingSieve_nu_eq_inv_totient (hEven := hEven)
      (ε := 0) (b := 0) (c := 0) (Z := Z) (X := mass N g L U) hd
  unfold BoundingSieve.rem
  rw [outputSieve_multSum,hnu]
  change _ - (1/(d.totient : ℝ))*mass N g L U = _
  unfold commonResidual
  ring

/-- The actual small-output payment applies to every clipped fibre. -/
theorem primeOutput_le_sifted (hN : 2 ≤ N) (h : Admissible N ε g L U) (Z : ℝ) :
    primeOutput N g L U ≤ 400*siftedMass N g L U Z + 8000*(Nat.ceil Z : ℝ) := by
  have hsmall : (∑ p ∈ (outputSupport N L U).filter (fun p => p < Nat.ceil Z),
      outputWeight N g L U p) ≤ 20*(Nat.ceil Z : ℝ) := by
    calc
      _ ≤ ∑ _p ∈ (outputSupport N L U).filter (fun p => p < Nat.ceil Z), (20 : ℝ) :=
        sum_le_sum fun p _ => outputWeight_le_twenty hN h p
      _ ≤ ∑ _p ∈ range (Nat.ceil Z), (20 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg
          (fun p hp => mem_range.mpr (mem_filter.mp hp).2) (by intros; norm_num)
      _ = _ := by simp [mul_comm]
  have hsplit : (∑ p ∈ (outputSupport N L U).filter Nat.Prime, outputWeight N g L U p) ≤
      (∑ p ∈ (outputSupport N L U).filter (fun p => (goldbachB10ProdPrimes N Z).Coprime p),
        outputWeight N g L U p) +
      ∑ p ∈ (outputSupport N L U).filter (fun p => p < Nat.ceil Z), outputWeight N g L U p := by
    simp only [sum_filter,← sum_add_distrib]
    apply sum_le_sum
    intro p _
    have hw := outputWeight_nonneg h p
    by_cases hp : p.Prime
    · rw [if_pos hp]
      by_cases hc : (goldbachB10ProdPrimes N Z).Coprime p
      · rw [if_pos hc]
        split_ifs <;> linarith
      · have hpd : p ∣ goldbachB10ProdPrimes N Z := by
          by_contra hpd
          exact hc ((hp.coprime_iff_not_dvd.mpr hpd).symm)
        have hs : p < Nat.ceil Z := Nat.lt_ceil.mpr (prime_dvd_goldbachB10ProdPrimes_lt hp hpd)
        simp only [if_neg hc,if_pos hs,zero_add,le_refl]
    · rw [if_neg hp]
      split_ifs <;> linarith
  rw [output_sum,output_sum] at hsplit
  unfold primeOutput siftedMass
  linarith only [hsmall,hsplit]

end G12ClippedWindow

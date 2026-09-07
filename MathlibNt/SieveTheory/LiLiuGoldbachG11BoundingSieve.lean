import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedDivisorDistribution
import MathlibNt.SieveTheory.LiLiuGoldbachB10FibreSieve

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Finset
open scoped BigOperators
noncomputable section

abbrev GoldbachG11LinkedAtom := Σ _m : ℕ, ℕ

def goldbachG11LinkedAtoms (N : ℕ) (ε : ℝ) : Finset GoldbachG11LinkedAtom :=
  (goldbachG11EffectiveProductSupport N ε).sigma (goldbachG11LinkedPrimeWindow N ε)

def goldbachG11LinkedOutput (N : ℕ) (x : GoldbachG11LinkedAtom) : ℕ := N-x.2*x.1

def goldbachG11LinkedOutputSupport (N : ℕ) (ε : ℝ) : Finset ℕ :=
  (goldbachG11LinkedAtoms N ε).image (goldbachG11LinkedOutput N)

/-- Weighted fibres, not a set of distinct outputs with weight one. -/
def goldbachG11LinkedOutputWeight (N : ℕ) (ε : ℝ) (p : ℕ) : ℝ :=
  ∑ x ∈ (goldbachG11LinkedAtoms N ε).filter (fun x => goldbachG11LinkedOutput N x = p),
    goldbachG11EffectiveProductCoefficient N ε x.1

theorem goldbachG11LinkedOutputWeight_nonneg (N : ℕ) (ε : ℝ) (p : ℕ) :
    0 ≤ goldbachG11LinkedOutputWeight N ε p := by
  exact Finset.sum_nonneg (fun x _ => (goldbachG11EffectiveProductCoefficient_bounds N x.1 ε).1)

/-- Reuse the accepted Goldbach prime product and dimension function; replace only
its finite mother and weights by the actual G11 weighted pushforward. -/
def goldbachG11LinkedBoundingSieve (N : ℕ) (hEven : Even N) (ε Z X : ℝ) : BoundingSieve :=
  { goldbachB10BoundingSieve N hEven 0 0 0 Z X with
    support := goldbachG11LinkedOutputSupport N ε
    weights := goldbachG11LinkedOutputWeight N ε
    weights_nonneg := goldbachG11LinkedOutputWeight_nonneg N ε }

theorem goldbachG11LinkedOutput_sum (N : ℕ) (ε : ℝ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ p ∈ (goldbachG11LinkedOutputSupport N ε).filter P,
      goldbachG11LinkedOutputWeight N ε p) =
    ∑ m ∈ goldbachG11EffectiveProductSupport N ε,
      goldbachG11EffectiveProductCoefficient N ε m *
        (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => P (N-r*m))).card : ℝ) := by
  classical
  let A := goldbachG11LinkedAtoms N ε
  let out := goldbachG11LinkedOutput N
  let T := (A.image out).filter P
  have hf := Finset.sum_fiberwise_eq_sum_filter A T out
    (fun x => goldbachG11EffectiveProductCoefficient N ε x.1)
  have hfilter : A.filter (fun x => out x ∈ T) = A.filter (fun x => P (out x)) := by
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨hx, hT⟩
      exact ⟨hx, (mem_filter.mp hT).2⟩
    · rintro ⟨hx, hp⟩
      exact ⟨hx, mem_filter.mpr ⟨mem_image.mpr ⟨x, hx, rfl⟩, hp⟩⟩
  rw [hfilter] at hf
  calc
    _ = ∑ x ∈ A.filter (fun x => P (out x)),
        goldbachG11EffectiveProductCoefficient N ε x.1 := hf
    _ = _ := by
      rw [sum_filter]
      dsimp [A, goldbachG11LinkedAtoms]
      rw [sum_sigma]
      apply sum_congr rfl
      intro m _
      change (∑ r ∈ goldbachG11LinkedPrimeWindow N ε m,
        if P (N-r*m) then goldbachG11EffectiveProductCoefficient N ε m else 0) = _
      rw [← sum_filter]
      simp [mul_comm]

def goldbachG11LinkedSiftedMass (N : ℕ) (ε Z : ℝ) : ℝ :=
  ∑ m ∈ goldbachG11EffectiveProductSupport N ε,
    goldbachG11EffectiveProductCoefficient N ε m *
      (((goldbachG11LinkedPrimeWindow N ε m).filter
        (fun r => (goldbachB10ProdPrimes N Z).Coprime (N-r*m))).card : ℝ)

theorem goldbachG11LinkedBoundingSieve_multSum (N : ℕ) (hEven : Even N)
    (ε Z X : ℝ) (d : ℕ) :
    (goldbachG11LinkedBoundingSieve N hEven ε Z X).multSum d =
      ∑ m ∈ goldbachG11EffectiveProductSupport N ε,
        goldbachG11EffectiveProductCoefficient N ε m *
          (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => d ∣ N-r*m)).card : ℝ) := by
  unfold BoundingSieve.multSum
  change (∑ p ∈ goldbachG11LinkedOutputSupport N ε,
    if d ∣ p then goldbachG11LinkedOutputWeight N ε p else 0) = _
  rw [← sum_filter]
  exact goldbachG11LinkedOutput_sum N ε (fun p => d ∣ p)

theorem goldbachG11LinkedBoundingSieve_siftedSum (N : ℕ) (hEven : Even N) (ε Z X : ℝ) :
    (goldbachG11LinkedBoundingSieve N hEven ε Z X).siftedSum =
      goldbachG11LinkedSiftedMass N ε Z := by
  unfold BoundingSieve.siftedSum
  change (∑ p ∈ goldbachG11LinkedOutputSupport N ε,
    if (goldbachB10ProdPrimes N Z).Coprime p then goldbachG11LinkedOutputWeight N ε p else 0) = _
  rw [← sum_filter]
  exact goldbachG11LinkedOutput_sum N ε (fun p => (goldbachB10ProdPrimes N Z).Coprime p)

theorem goldbachG11LinkedBoundingSieve_nu {N : ℕ} (hEven : Even N) (ε Z X : ℝ)
    {d : ℕ} (hd : d ∣ goldbachB10ProdPrimes N Z) :
    (goldbachG11LinkedBoundingSieve N hEven ε Z X).nu d = (1 : ℝ)/d.totient := by
  exact goldbachB10BoundingSieve_nu_eq_inv_totient (hEven := hEven)
    (ε := 0) (b := 0) (c := 0) (Z := Z) (X := X) hd

theorem goldbachG11LinkedBoundingSieve_rem (N : ℕ) (hEven : Even N) (ε Z X : ℝ)
    {d : ℕ} (hd : d ∣ goldbachB10ProdPrimes N Z) :
    (goldbachG11LinkedBoundingSieve N hEven ε Z X).rem d =
      (∑ m ∈ goldbachG11EffectiveProductSupport N ε,
        goldbachG11EffectiveProductCoefficient N ε m *
          (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => d ∣ N-r*m)).card : ℝ)) -
        X/(d.totient : ℝ) := by
  unfold BoundingSieve.rem
  rw [goldbachG11LinkedBoundingSieve_multSum,
    goldbachG11LinkedBoundingSieve_nu hEven ε Z X hd]
  change _ - (1/(d.totient : ℝ))*X = _
  ring

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
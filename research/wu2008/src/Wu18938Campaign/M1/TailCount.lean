import Wu18938Campaign.M1.TailBuchstab

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical

/-- A strengthened intermediate mother, not the full Wu08 sixth term.
The diagonal in the tail expansion cancels its actual repeated-prime debit. -/
theorem tail_count_exact (N : ℕ) (z w u v V : ℝ)
    (hzw : z ≤ w) (hwu : w ≤ u) (hwv : w ≤ v) (huv : u ≤ v)
    (hu : 0 ≤ u) (hV : V ≤ z * u) (hv : 0 ≤ v) (hNv : (N : ℝ) ≤ v ^ 3)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    ((eleven N z w u v V - upsilon6 N z w u +
      truncatedSixthMass N z w u V + tailPairRaised N z w u V +
      tailTripleRaised N z w u V : ℤ) : ℝ) + quotientAssemblyGains N z w u v =
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (4 * (N : ℝ) / w + 2 * (Real.sqrt N + 1)) +
        (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) +
        (s3RepeatedFirstPrimeMass N (orderedTriples (primeWindow N z w)) : ℝ) +
        (s3RepeatedFirstPrimeMass N
          ((s3SecondRange N z w u).filter (fun t => (t.2.1 : ℝ) * t.2.2 < V)) : ℝ) +
        (s3PairRepeatedBudget N w u : ℝ) := by
  have h := finiteElevenMixed_exact_aggregate N z w u v V
    hzw hwu hwv huv hv hNv hthird
  rw [signed_aggregate_transport N hu hV] at h
  have htail := congrArg (fun x : ℤ => (x : ℝ)) (tail_buchstab_exact N z w u V)
  have hrep := congrArg (fun x : ℤ => (x : ℝ)) (tail_repeated_partition N z w u V)
  have hfull := truncatedSixth_full_sub_kept N z w u V
  rw [truncatedSixth_full_eq_original] at hfull
  change upsilon6 N z w u - truncatedSixthMass N z w u V =
    truncatedSixthOmittedMass N z w u V at hfull
  have hfullR := congrArg (fun x : ℤ => (x : ℝ)) hfull
  push_cast at htail hrep hfullR ⊢
  linarith

theorem target_count_tail_raised {N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (hz : 2 ≤ (N : ℝ) ^ (100 / 1327 : ℝ)) :
    let z := (N : ℝ) ^ (100 / 1327 : ℝ)
    let w := (N : ℝ) ^ (25 / 206 : ℝ)
    let u := (N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ))
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ))
    ((eleven N z w u v V - upsilon6 N z w u +
      truncatedSixthMass N z w u V + tailPairRaised N z w u V +
      tailTripleRaised N z w u V : ℤ) : ℝ) + quotientAssemblyGains N z w u v ≤
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (16 + 2 * (1 / (100 / 1327 : ℝ)) ^ 3 +
          2 * (1 / (25 / 206 : ℝ)) ^ 2) * (N : ℝ) ^ (1 - (100 / 1327 : ℝ)) := by
  let z := (N : ℝ) ^ (100 / 1327 : ℝ)
  let w := (N : ℝ) ^ (25 / 206 : ℝ)
  let u := (N : ℝ) ^ (1 / 2 - 3 * (100 / 1327 : ℝ))
  let V := (N : ℝ) ^ (1 / 2 - 2 * (100 / 1327 : ℝ))
  have h := eleven_count_signed (κ₁ := (100 / 1327 : ℝ)) (κ₂ := (25 / 206 : ℝ))
    hN he (by norm_num) (by norm_num) (by norm_num) (by norm_num) hz
  have htail := congrArg (fun x : ℤ => (x : ℝ)) (tail_buchstab_exact N z w u V)
  have hfull := truncatedSixth_full_sub_kept N z w u V
  rw [truncatedSixth_full_eq_original] at hfull
  change upsilon6 N z w u - truncatedSixthMass N z w u V =
    truncatedSixthOmittedMass N z w u V at hfull
  have hfullR := congrArg (fun x : ℤ => (x : ℝ)) hfull
  have hrep : 0 ≤ (s3RepeatedFirstPrimeMass N (tailTriples N z w u V) : ℝ) := by
    exact_mod_cast (sum_nonneg (s := tailTriples N z w u V)
      (f := fun t => sieveCount N (t.1 * t.2.1 * t.2.2 * t.1) N (t.1 : ℝ))
      (fun _ _ => sieveCount_nonneg _ _ _ _))
  dsimp only at h ⊢
  push_cast at htail hfullR ⊢
  change _ ≤ _ at h
  dsimp only [z, w, u, V] at htail hfullR hrep
  linarith

end Wu18938Campaign.M1

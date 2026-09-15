import Wu18938Campaign.M1.ModulusLoss
import WR2MotherDelta2

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical

noncomputable def positiveModulusMass (N : ℕ) (z v : ℝ) : ℤ :=
  ∑ t ∈ orderedTriples (primeWindow N z v), s3TripleModulusGain N t

theorem positiveModulusMass_nonneg (N : ℕ) (z v : ℝ) :
    0 ≤ positiveModulusMass N z v :=
  sum_nonneg (fun t _ => s3TripleModulusGain_nonneg N t)

theorem thirdModulusLoss_nonneg (N : ℕ) (w u : ℝ) :
    0 ≤ thirdModulusLoss N w u :=
  sum_nonneg (fun t _ =>
    sub_nonneg.mpr (s3_sieveCount_le_mul_modulus N _ N t.1 _))

theorem modulus_loss_antitone (N d a : ℕ) {b c : ℝ}
    (ha : a.Prime) (haN : a.Coprime N) (hab : (a : ℝ) < b) (hbc : b ≤ c) :
    sieveCount N d (N * a) c - sieveCount N d N c ≤
      sieveCount N d (N * a) b - sieveCount N d N b := by
  unfold sieveCount sieveCarrier Sifted
  convert! prime_complement_defect_antitone N d a ha haN hab hbc using 1

theorem thirdModulusLoss_le_positiveModulusMass (N : ℕ) (z w u v : ℝ)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    thirdModulusLoss N w u ≤ positiveModulusMass N z v := by
  calc
    _ ≤ ∑ t ∈ s3ThirdRange N w u, s3TripleModulusGain N t := by
      apply sum_le_sum
      rintro ⟨a, b, c⟩ ht
      obtain ⟨ha, haN, _, _, _, _, _, _, hab, hbc⟩ :=
        mem_s3_ordered_triples.mp (hthird ht)
      exact modulus_loss_antitone N (a * b * c) a ha haN
        (by exact_mod_cast hab) (by exact_mod_cast hbc.le)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hthird
      (fun t _ _ => s3TripleModulusGain_nonneg N t)

theorem delta2_modulus_balance (N : ℕ) (z w u v : ℝ) :
    delta2 N z w u v =
      paperDelta2 N z w u v + positiveModulusMass N z v := by
  unfold delta2 paperDelta2 positiveS4 positiveModulusMass
    s3TripleModulusGain paperTriple
  rw [sum_sub_distrib]
  omega

theorem retained_modulus_balance (N : ℕ) (z w u v : ℝ)
    (hwv : w ≤ v) (huv : u ≤ v)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    s3RetainedTripleMass N z w u v =
      paperRetained N z w u v + positiveModulusMass N z v -
        thirdModulusLoss N w u := by
  have hq := s3_delta2_exact_retained N z w u v hwv huv hthird
  have hp := paper_delta2_exact N z w u v hwv huv hthird
  have hm := delta2_modulus_balance N z w u v
  rw [← delta2_eq_existing] at hq
  omega

noncomputable def paperAssemblyGains (N : ℕ) (z w u v : ℝ) : ℝ :=
  (positiveModulusMass N z v : ℝ) - (thirdModulusLoss N w u : ℝ) +
    (positiveS4 N w u : ℝ) + (s3VariableSlack N w u : ℝ) +
    lowerWeightOuterSlack N w u + lowerWeightOuterSlack N z v

theorem paperAssemblyGains_nonneg {N : ℕ} (hN : 0 < N)
    {z w : ℝ} (hz : 2 ≤ z) (hw : 2 ≤ w) (u v : ℝ)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    0 ≤ paperAssemblyGains N z w u v := by
  have hM := (Int.cast_le (R := ℝ)).mpr
    (thirdModulusLoss_le_positiveModulusMass N z w u v hthird)
  have h4 := Int.cast_nonneg (R := ℝ) (positiveS4_nonneg N w u)
  have hS := Int.cast_nonneg (R := ℝ) (s3VariableSlack_nonneg N w u)
  have hW := lowerWeightOuterSlack_nonneg hN hw u
  have hZ := lowerWeightOuterSlack_nonneg hN hz v
  unfold paperAssemblyGains
  linarith

theorem paper_assembly_balance (N : ℕ) (z w u v : ℝ)
    (hwv : w ≤ v) (huv : u ≤ v)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    quotientAssemblyGains N z w u v =
      (paperRetained N z w u v : ℝ) + paperAssemblyGains N z w u v := by
  have h := congrArg (fun x : ℤ => (x : ℝ))
    (retained_modulus_balance N z w u v hwv huv hthird)
  push_cast at h
  unfold quotientAssemblyGains paperAssemblyGains
  linarith

theorem paper_eleven_exact_count (N : ℕ) (z w u v V : ℝ)
    (hzw : z ≤ w) (hwu : w ≤ u) (hwv : w ≤ v) (huv : u ≤ v)
    (hu : 0 ≤ u) (hV : V ≤ z * u)
    (hv : 0 ≤ v) (hNv : (N : ℝ) ≤ v ^ 3)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    (eleven N z w u v V : ℝ) + (paperRetained N z w u v : ℝ) +
        paperAssemblyGains N z w u v - (quotientExcess N z w u V : ℝ) =
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (4 * (N : ℝ) / w + 2 * (Real.sqrt N + 1)) +
        (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) +
        (s3RepeatedFirstPrimeMass N (orderedTriples (primeWindow N z w)) : ℝ) +
        (s3RepeatedFirstPrimeMass N (s3SecondRange N z w u) : ℝ) +
        (s3PairRepeatedBudget N w u : ℝ) := by
  have h := finiteElevenMixed_exact_aggregate N z w u v V
    hzw hwu hwv huv hv hNv hthird
  rw [signed_aggregate_transport N hu hV,
    paper_assembly_balance N z w u v hwv huv hthird] at h
  linarith

theorem original_count_all_gains {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6)
    (hz : 2 ≤ (N : ℝ) ^ κ₁) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
    (eleven N z w u v V : ℝ) + (paperRetained N z w u v : ℝ) +
        paperAssemblyGains N z w u v - (quotientExcess N z w u V : ℝ) ≤
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (16 + 2 * (1 / κ₁) ^ 3 + 2 * (1 / κ₂) ^ 2) * (N : ℝ) ^ (1 - κ₁) := by
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hwv := Real.rpow_le_rpow_of_exponent_le hbase
    (show κ₂ ≤ 1 / 3 by linarith)
  have huv := Real.rpow_le_rpow_of_exponent_le hbase
    (show 1 / 2 - 3 * κ₁ ≤ 1 / 3 by linarith)
  have hthird := s3ThirdRange_subset_source_triples (by omega : 1 ≤ N) hκ hparam
  have h := eleven_count_signed hN he hκ₁ hκ hupper hparam hz
  dsimp only at h ⊢
  rw [paper_assembly_balance N _ _ _ _ hwv huv hthird] at h
  linarith

end Wu18938Campaign.M1

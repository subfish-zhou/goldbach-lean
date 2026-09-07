import MathlibNt.SieveTheory.LiLiuGoldbachG10BuchstabBridge

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableT16Coverage (P : Prop) : Decidable P :=
  Classical.propDecidable P

private abbrev T16CoverageSourceTriple := Σ _rs : ℕ × ℕ, ℕ

private abbrev T16CoverageTargetTriple := Σ _t : ℕ, Σ _r : ℕ, ℕ

private noncomputable def T16CoverageSourceShapes (N : ℕ) (b c : ℝ) :
    Finset T16CoverageSourceTriple :=
  (goldbachC10Pairs N b c).sigma fun rs =>
    goldbachClosedPrimes N (rs.2 : ℝ) (goldbachC10Cutoff N rs)

private noncomputable def T16CoverageTargetShapes (N : ℕ) (z b u : ℝ) :
    Finset T16CoverageTargetTriple :=
  (goldbachClosedPrimes N z u).sigma fun t =>
    (goldbachClosedPrimes N z (t : ℝ)).sigma fun r =>
      (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter (fun s : ℕ => b < (s : ℝ))

private def T16CoverageEncode (a : T16CoverageSourceTriple) : T16CoverageTargetTriple :=
  ⟨a.2, ⟨a.1.1, a.1.2⟩⟩

private def T16CoverageDecode (a : T16CoverageTargetTriple) : T16CoverageSourceTriple :=
  ⟨(a.2.1, a.2.2), a.1⟩

private theorem T16Coverage_leftInverse :
    Function.LeftInverse T16CoverageDecode T16CoverageEncode := by
  intro a
  cases a
  rfl

private theorem T16Coverage_encode_injective :
    Function.Injective T16CoverageEncode :=
  T16Coverage_leftInverse.injective

private theorem T16Coverage_mem_sourceShapes_iff
    {N : ℕ} {b c : ℝ} {a : T16CoverageSourceTriple} :
    a ∈ T16CoverageSourceShapes N b c ↔
      a.1 ∈ goldbachC10Pairs N b c ∧
        a.2 ∈ goldbachClosedPrimes N (a.1.2 : ℝ) (goldbachC10Cutoff N a.1) := by
  simp [T16CoverageSourceShapes]

private theorem T16Coverage_mem_targetShapes_iff
    {N : ℕ} {z b u : ℝ} {a : T16CoverageTargetTriple} :
    a ∈ T16CoverageTargetShapes N z b u ↔
      a.1 ∈ goldbachClosedPrimes N z u ∧
        a.2.1 ∈ goldbachClosedPrimes N z (a.1 : ℝ) ∧
        a.2.2 ∈
          (goldbachClosedPrimes N (a.2.1 : ℝ) (a.1 : ℝ)).filter
            (fun s : ℕ => b < (s : ℝ)) := by
  simp [T16CoverageTargetShapes]

private theorem T16Coverage_beta_lt_gamma
    {β γ : ℝ}
    (hβγ : β < (1 - 3 * β) / 3)
    (hγ : (1 - 3 * β) / 3 < γ) :
    β < γ :=
  lt_trans hβγ hγ

private theorem T16Coverage_cutoff_lt_cuberoot
    {N : ℕ} {β γ : ℝ} {rs : ℕ × ℕ}
    (hN : 2 ≤ N)
    (_hβγ : β < (1 - 3 * β) / 3)
    (hγ : (1 - 3 * β) / 3 < γ)
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)) :
    goldbachC10Cutoff N rs < (N : ℝ) ^ ((1 : ℝ) / 3) := by
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨hrPrime, hsPrime, _, hbr, _, hcs, _⟩
  have hN1Nat : 1 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN1Nat
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hNpos : (0 : ℝ) < N := by positivity
  let u : ℝ := (N : ℝ) ^ ((1 : ℝ) / 3)
  have huNonneg : 0 ≤ u := by
    dsimp [u]
    exact Real.rpow_nonneg hN0 _
  have hprodPosNat : 0 < goldbachC10Prod rs := by
    simp [goldbachC10Prod, Nat.mul_pos hrPrime.pos hsPrime.pos]
  have hprodPos : 0 < (goldbachC10Prod rs : ℝ) := by
    exact_mod_cast hprodPosNat
  have huSq :
      u ^ 2 = (N : ℝ) ^ ((2 : ℝ) / 3) := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    congr 1
    norm_num
  have hBetaGamma :
      (N : ℝ) ^ (β + γ) = (N : ℝ) ^ β * (N : ℝ) ^ γ :=
    Real.rpow_add hNpos β γ
  have hpowFactor :
      (N : ℝ) ^ (β + γ + (2 : ℝ) / 3) =
        ((N : ℝ) ^ β) * ((N : ℝ) ^ γ) * u ^ 2 := by
    calc
      (N : ℝ) ^ (β + γ + (2 : ℝ) / 3)
          = (N : ℝ) ^ (β + γ) * (N : ℝ) ^ ((2 : ℝ) / 3) := by
              rw [show β + γ + (2 : ℝ) / 3 = (β + γ) + (2 : ℝ) / 3 by ring,
                Real.rpow_add hNpos]
      _ = (((N : ℝ) ^ β) * ((N : ℝ) ^ γ)) * (N : ℝ) ^ ((2 : ℝ) / 3) := by
            rw [hBetaGamma]
      _ = ((N : ℝ) ^ β) * ((N : ℝ) ^ γ) * u ^ 2 := by
            simpa [mul_assoc] using congrArg
              (fun x : ℝ => ((N : ℝ) ^ β) * ((N : ℝ) ^ γ) * x) huSq.symm
  have hexp : (1 : ℝ) < β + γ + (2 : ℝ) / 3 := by
    nlinarith [hγ]
  have hpow :
      (N : ℝ) < ((N : ℝ) ^ β) * ((N : ℝ) ^ γ) * u ^ 2 := by
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by simp
      _ < (N : ℝ) ^ (β + γ + (2 : ℝ) / 3) :=
        Real.rpow_lt_rpow_of_exponent_lt hN1 hexp
      _ = ((N : ℝ) ^ β) * ((N : ℝ) ^ γ) * u ^ 2 := hpowFactor
  have hprodLower :
      ((N : ℝ) ^ β) * ((N : ℝ) ^ γ) ≤ (goldbachC10Prod rs : ℝ) := by
    calc
      ((N : ℝ) ^ β) * ((N : ℝ) ^ γ) ≤ (rs.1 : ℝ) * (rs.2 : ℝ) := by
        gcongr
      _ = (goldbachC10Prod rs : ℝ) := by simp [goldbachC10Prod]
  have hNu :
      (N : ℝ) < (goldbachC10Prod rs : ℝ) * u ^ 2 := by
    exact lt_of_lt_of_le hpow (mul_le_mul_of_nonneg_right hprodLower (sq_nonneg u))
  have hdiv :
      (N : ℝ) / (goldbachC10Prod rs : ℝ) < u ^ 2 := by
    exact (div_lt_iff₀ hprodPos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hNu)
  unfold goldbachC10Cutoff
  refine (Real.sqrt_lt ?_ huNonneg).2 ?_
  · exact div_nonneg (by positivity) hprodPos.le
  · simpa [u] using hdiv

/-- The literal pointwise geometry taking a genuine `T16` label `((r,s),t)` into
the future closed-prime upper-middle carrier. -/
theorem goldbachT16Coverage_pointwise_geometry
    {N : ℕ} {α β γ : ℝ} {rs : ℕ × ℕ} {t : ℕ}
    (hN : 2 ≤ N)
    (hαβ : α ≤ β)
    (_hβ : (1 : ℝ) / 18 < β)
    (hβγ : β < (1 - 3 * β) / 3)
    (hγ : (1 - 3 * β) / 3 < γ)
    (_hγu : γ < (1 : ℝ) / 3)
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ β) ((N : ℝ) ^ γ))
    (ht : t ∈ goldbachClosedPrimes N (rs.2 : ℝ) (goldbachC10Cutoff N rs)) :
    rs.1.Prime ∧ rs.2.Prime ∧ t.Prime ∧
      ¬rs.1 ∣ N ∧ ¬rs.2 ∣ N ∧ ¬t ∣ N ∧
      (N : ℝ) ^ α ≤ (rs.1 : ℝ) ∧
      (N : ℝ) ^ β ≤ (rs.1 : ℝ) ∧
      (rs.1 : ℝ) ≤ (N : ℝ) ^ γ ∧
      (N : ℝ) ^ γ ≤ (rs.2 : ℝ) ∧
      (rs.1 : ℝ) ≤ (rs.2 : ℝ) ∧
      (rs.1 : ℝ) ≤ (t : ℝ) ∧
      (rs.2 : ℝ) ≤ (t : ℝ) ∧
      (N : ℝ) ^ β < (rs.2 : ℝ) ∧
      (t : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3) := by
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨hrPrime, hsPrime, hcop, hbr, hrc, hcs, _⟩
  rcases mem_goldbachClosedPrimes_iff.mp ht with ⟨htPrime, htNotDvd, hst, htCutoff⟩
  have hN1Nat : 1 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN1Nat
  have hzleB : (N : ℝ) ^ α ≤ (N : ℝ) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hN1.le hαβ
  have hzleR : (N : ℝ) ^ α ≤ (rs.1 : ℝ) := le_trans hzleB hbr
  have hrNotDvd : ¬rs.1 ∣ N := by
    have hcopr : Nat.Coprime rs.1 N :=
      hcop.coprime_dvd_left (dvd_mul_of_dvd_left (dvd_refl rs.1) rs.2)
    exact hrPrime.coprime_iff_not_dvd.mp hcopr
  have hsNotDvd : ¬rs.2 ∣ N := by
    have hcops : Nat.Coprime rs.2 N :=
      hcop.coprime_dvd_left (dvd_mul_of_dvd_right (dvd_refl rs.2) rs.1)
    exact hsPrime.coprime_iff_not_dvd.mp hcops
  have hrleS : (rs.1 : ℝ) ≤ (rs.2 : ℝ) := le_trans hrc hcs
  have hrleT : (rs.1 : ℝ) ≤ (t : ℝ) := le_trans hrleS hst
  have hbLtC :
      (N : ℝ) ^ β < (N : ℝ) ^ γ := by
    exact Real.rpow_lt_rpow_of_exponent_lt hN1 (T16Coverage_beta_lt_gamma hβγ hγ)
  have hbLtS : (N : ℝ) ^ β < (rs.2 : ℝ) := lt_of_lt_of_le hbLtC hcs
  have htLtU :
      (t : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3) := by
    exact lt_of_le_of_lt htCutoff (T16Coverage_cutoff_lt_cuberoot hN hβγ hγ hrs)
  exact ⟨hrPrime, hsPrime, htPrime, hrNotDvd, hsNotDvd, htNotDvd,
    hzleR, hbr, hrc, hcs, hrleS, hrleT, hst, hbLtS, htLtU⟩

/-- Actual membership of a `T16` label in the explicit closed-prime target
carrier used later for the upper-middle contribution. -/
theorem goldbachT16Coverage_pointwise_membership
    {N : ℕ} {α β γ : ℝ} {rs : ℕ × ℕ} {t : ℕ}
    (hN : 2 ≤ N)
    (hαβ : α ≤ β)
    (hβ : (1 : ℝ) / 18 < β)
    (hβγ : β < (1 - 3 * β) / 3)
    (hγ : (1 - 3 * β) / 3 < γ)
    (hγu : γ < (1 : ℝ) / 3)
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ β) ((N : ℝ) ^ γ))
    (ht : t ∈ goldbachClosedPrimes N (rs.2 : ℝ) (goldbachC10Cutoff N rs)) :
    t ∈ goldbachClosedPrimes N ((N : ℝ) ^ α) ((N : ℝ) ^ ((1 : ℝ) / 3)) ∧
      rs.1 ∈ goldbachClosedPrimes N ((N : ℝ) ^ α) (t : ℝ) ∧
      rs.2 ∈
        (goldbachClosedPrimes N (rs.1 : ℝ) (t : ℝ)).filter
          (fun s : ℕ => (N : ℝ) ^ β < (s : ℝ)) := by
  rcases goldbachT16Coverage_pointwise_geometry
      hN hαβ hβ hβγ hγ hγu hrs ht with
    ⟨hrPrime, hsPrime, htPrime, hrNotDvd, hsNotDvd, htNotDvd, hzleR, _, _, _,
      hrleS, hrleT, hst, hbLtS, htLtU⟩
  constructor
  · exact mem_goldbachClosedPrimes_iff.mpr ⟨htPrime, htNotDvd, le_trans hzleR hrleT, htLtU.le⟩
  constructor
  · exact mem_goldbachClosedPrimes_iff.mpr ⟨hrPrime, hrNotDvd, hzleR, hrleT⟩
  · refine Finset.mem_filter.mpr ⟨?_, hbLtS⟩
    exact mem_goldbachClosedPrimes_iff.mpr ⟨hsPrime, hsNotDvd, hrleS, hst⟩

private noncomputable def T16CoverageSourceWeight
    (A : Finset ℕ) (N : ℕ) (a : T16CoverageSourceTriple) : ℤ :=
  literalH A (N * a.1.1) (a.1.1 * a.1.2 * a.2) (a.1.2 : ℝ)

private noncomputable def T16CoverageTargetWeight
    (A : Finset ℕ) (N : ℕ) (a : T16CoverageTargetTriple) : ℤ :=
  literalH A (N * a.2.1) (a.2.1 * a.2.2 * a.1) (a.2.2 : ℝ)

private theorem T16Coverage_source_sum_eq
    (A : Finset ℕ) (N : ℕ) (b c : ℝ) :
    goldbachWeightT16 A N b c =
      ∑ a ∈ T16CoverageSourceShapes N b c, T16CoverageSourceWeight A N a := by
  unfold goldbachWeightT16 T16CoverageSourceShapes T16CoverageSourceWeight
  simp_rw [Finset.sum_sigma']

private theorem T16Coverage_target_sum_eq
    (A : Finset ℕ) (N : ℕ) (z b u : ℝ) :
    (∑ a ∈ T16CoverageTargetShapes N z b u, T16CoverageTargetWeight A N a) =
      ∑ t ∈ goldbachClosedPrimes N z u,
        ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
          ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter (fun s : ℕ => b < (s : ℝ)),
            literalH A (N * r) (r * s * t) (s : ℝ) := by
  unfold T16CoverageTargetShapes T16CoverageTargetWeight
  simp_rw [Finset.sum_sigma']

private theorem T16Coverage_image_subset_target
    {N : ℕ} {α β γ : ℝ}
    (hN : 2 ≤ N)
    (hαβ : α ≤ β)
    (hβ : (1 : ℝ) / 18 < β)
    (hβγ : β < (1 - 3 * β) / 3)
    (hγ : (1 - 3 * β) / 3 < γ)
    (hγu : γ < (1 : ℝ) / 3) :
    (T16CoverageSourceShapes N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).image T16CoverageEncode ⊆
      T16CoverageTargetShapes N ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ ((1 : ℝ) / 3)) := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
  rcases T16Coverage_mem_sourceShapes_iff.mp hx with ⟨hrs, ht⟩
  rcases goldbachT16Coverage_pointwise_membership hN hαβ hβ hβγ hγ hγu hrs ht with
    ⟨htMem, hrMem, hsMem⟩
  exact T16Coverage_mem_targetShapes_iff.mpr ⟨htMem, hrMem, hsMem⟩

/-- The genuine `T16` contribution embeds, with label order preserved, into the
explicit closed-prime triple sum that later serves as the upper-middle carrier. -/
theorem goldbachWeightT16_le_explicitClosedPrimeTripleSum
    (A : Finset ℕ) (N : ℕ) {α β γ : ℝ}
    (hN : 2 ≤ N)
    (hαβ : α ≤ β)
    (hβ : (1 : ℝ) / 18 < β)
    (hβγ : β < (1 - 3 * β) / 3)
    (hγ : (1 - 3 * β) / 3 < γ)
    (hγu : γ < (1 : ℝ) / 3) :
    goldbachWeightT16 A N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) ≤
      ∑ t ∈ goldbachClosedPrimes N ((N : ℝ) ^ α) ((N : ℝ) ^ ((1 : ℝ) / 3)),
        ∑ r ∈ goldbachClosedPrimes N ((N : ℝ) ^ α) (t : ℝ),
          ∑ s ∈
            (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
              (fun s : ℕ => (N : ℝ) ^ β < (s : ℝ)),
            literalH A (N * r) (r * s * t) (s : ℝ) := by
  calc
    goldbachWeightT16 A N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
      = ∑ a ∈ T16CoverageSourceShapes N ((N : ℝ) ^ β) ((N : ℝ) ^ γ),
          T16CoverageSourceWeight A N a := T16Coverage_source_sum_eq A N _ _
    _ =
      ∑ a ∈ (T16CoverageSourceShapes N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).image T16CoverageEncode,
        T16CoverageTargetWeight A N a := by
          calc
            ∑ a ∈ T16CoverageSourceShapes N ((N : ℝ) ^ β) ((N : ℝ) ^ γ),
                T16CoverageSourceWeight A N a
              =
                ∑ a ∈ T16CoverageSourceShapes N ((N : ℝ) ^ β) ((N : ℝ) ^ γ),
                  T16CoverageTargetWeight A N (T16CoverageEncode a) := by
                    apply Finset.sum_congr rfl
                    intro a ha
                    simp [T16CoverageSourceWeight, T16CoverageTargetWeight, T16CoverageEncode,
                      Nat.mul_left_comm, Nat.mul_comm]
            _ =
                ∑ a ∈ (T16CoverageSourceShapes N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).image
                    T16CoverageEncode,
                  T16CoverageTargetWeight A N a := by
                    rw [Finset.sum_image]
                    intro a ha b hb hab
                    exact T16Coverage_encode_injective hab
    _ ≤
      ∑ a ∈ T16CoverageTargetShapes N ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ ((1 : ℝ) / 3)),
        T16CoverageTargetWeight A N a := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (T16Coverage_image_subset_target hN hαβ hβ hβγ hγ hγu) ?_
          intro a haTarget haImage
          exact literalH_nonneg A (N * a.2.1) (a.2.1 * a.2.2 * a.1) (a.2.2 : ℝ)
    _ =
      ∑ t ∈ goldbachClosedPrimes N ((N : ℝ) ^ α) ((N : ℝ) ^ ((1 : ℝ) / 3)),
        ∑ r ∈ goldbachClosedPrimes N ((N : ℝ) ^ α) (t : ℝ),
          ∑ s ∈
            (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
              (fun s : ℕ => (N : ℝ) ^ β < (s : ℝ)),
            literalH A (N * r) (r * s * t) (s : ℝ) :=
      T16Coverage_target_sum_eq A N _ _ _

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
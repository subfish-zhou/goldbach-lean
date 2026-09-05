import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimitiveCharacterElementaryPeriodBound
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIActualDyadicDecomposition
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVLowHighConductor

/-!
# Elementary-period Vaughan Type-I bound by row Cauchy

This checker keeps the literal first and middle Vaughan long-row identities.
Inside either lane it uses finite Cauchy--Schwarz on the complete row index;
there is no rowwise triangle inequality.  The sole lane triangle is applied to
`first - middle` after both complete lanes have been bounded.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate

noncomputable section

/-- Exact finite complex Cauchy--Schwarz, with no intervening `norm_sum_le`. -/
theorem finiteComplexCauchy
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * (∑ i ∈ s, ‖b i‖ ^ 2) := by
  let x : EuclideanSpace ℂ ↥s := WithLp.toLp 2 (fun i => conj (a i.1))
  let y : EuclideanSpace ℂ ↥s := WithLp.toLp 2 (fun i => b i.1)
  have hi : inner ℂ x y = ∑ i ∈ s, a i * b i := by
    rw [PiLp.inner_apply]
    simp only [x, y, RCLike.inner_apply]
    rw [Finset.sum_subtype s (fun i => by rfl)]
    apply Finset.sum_congr rfl
    intro i hi
    simp
    ring
  have hx : ‖x‖ ^ 2 = ∑ i ∈ s, ‖a i‖ ^ 2 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
      PiLp.inner_apply (𝕜 := ℂ), map_sum]
    simp only [x]
    rw [Finset.sum_subtype s (fun i => by rfl)]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      RCLike.re (inner ℂ (conj (a i.1)) (conj (a i.1))) =
          ‖conj (a i.1)‖ ^ 2 :=
        (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (conj (a i.1))).symm
      _ = ‖a i.1‖ ^ 2 := by rw [Complex.norm_conj]
  have hy : ‖y‖ ^ 2 = ∑ i ∈ s, ‖b i‖ ^ 2 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
      PiLp.inner_apply (𝕜 := ℂ), map_sum]
    simp only [y]
    rw [Finset.sum_subtype s (fun i => by rfl)]
    apply Finset.sum_congr rfl
    intro i hi
    exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (b i.1)).symm
  have h := norm_inner_le_norm (𝕜 := ℂ) x y
  rw [hi] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg (∑ i ∈ s, a i * b i)) h 2
  rw [mul_pow, hx, hy] at hsq
  exact hsq

private lemma moebius_complex_norm_le_one (d : ℕ) :
    ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]

private lemma shortRange_card_le (y u : ℕ) :
    (vaughanTypeIShortRange y u).card ≤ u := by
  calc
    (vaughanTypeIShortRange y u).card ≤ (Finset.Icc 1 u).card := by
      apply Finset.card_le_card
      intro d hd
      exact Finset.mem_Icc.mpr
        ⟨(mem_vaughanTypeIShortRange.mp hd).1,
          (mem_vaughanTypeIShortRange.mp hd).2.2⟩
    _ ≤ u := by simp [Nat.card_Icc]

private lemma log_div_succ_le_log_succ {y N d : ℕ} (hy : y ≤ N) :
    Real.log (y / d + 1 : ℕ) ≤ Real.log (N + 1 : ℕ) := by
  apply Real.strictMonoOn_log.monotoneOn
  · show (0 : ℝ) < (y / d + 1 : ℕ)
    positivity
  · show (0 : ℝ) < (N + 1 : ℕ)
    positivity
  · exact_mod_cast Nat.succ_le_succ ((Nat.div_le_self y d).trans hy)

private lemma vonMangoldt_le_log_succ {e v : ℕ} (he : 0 < e) (hev : e ≤ v) :
    ArithmeticFunction.vonMangoldt e ≤ Real.log (v + 1 : ℕ) := by
  have hmem : e ∈ e.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, he.ne'⟩
  calc
    ArithmeticFunction.vonMangoldt e ≤
        ∑ r ∈ e.divisors, ArithmeticFunction.vonMangoldt r := by
      exact Finset.single_le_sum
        (s := e.divisors) (f := fun r => ArithmeticFunction.vonMangoldt r)
        (fun r _ => ArithmeticFunction.vonMangoldt_nonneg) hmem
    _ = Real.log (e : ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ ≤ Real.log (v + 1 : ℕ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · show (0 : ℝ) < (e : ℕ)
        positivity
      · show (0 : ℝ) < (v + 1 : ℕ)
        positivity
      · exact_mod_cast hev.trans (Nat.le_succ v)

/-- The complete literal first lane, bounded by Cauchy over the actual `d` rows. -/
theorem norm_vaughanTypeIFirstLong_le_elementaryCauchy
    {N y u q : ℕ} (hy : y ≤ N) (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ‖vaughanTypeIFirstLong (fun _ => 1) y u q χ‖ ≤
      4 * u * q * Real.log (N + 1 : ℕ) := by
  let D := vaughanTypeIShortRange y u
  let A : ℕ → ℂ := fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℂ) * χ.1 (d : ZMod q)
  let B : ℕ → ℂ := fun d =>
    ∑ m ∈ Finset.Icc 1 (y / d),
      (Real.log (m : ℝ) : ℂ) * χ.1 (m : ZMod q)
  have hA : (∑ d ∈ D, ‖A d‖ ^ 2) ≤ (u : ℝ) := by
    calc
      _ ≤ ∑ _d ∈ D, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        apply pow_le_one₀ (norm_nonneg _)
        simp only [A, norm_mul]
        calc
          ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ *
              ‖χ.1 (d : ZMod q)‖ ≤ 1 * 1 :=
            mul_le_mul (moebius_complex_norm_le_one d) (χ.1.norm_le_one _)
              (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      _ = (D.card : ℕ) := by simp
      _ ≤ (u : ℝ) := by exact_mod_cast shortRange_card_le y u
  let L := Real.log (N + 1 : ℕ)
  have hBpoint (d : ℕ) : ‖B d‖ ≤ 4 * q * L := by
    calc
      ‖B d‖ ≤ 4 * q * Real.log (y / d + 1 : ℕ) := by
        simpa [B, Nat.cast_add, Nat.cast_one] using
          (primitiveCharacter_logWeight_Icc_norm_le (M := y / d) hq χ)
      _ ≤ 4 * q * L := by
        apply mul_le_mul_of_nonneg_left (log_div_succ_le_log_succ hy)
        positivity
  have hB : (∑ d ∈ D, ‖B d‖ ^ 2) ≤ (u : ℝ) * (4 * q * L) ^ 2 := by
    calc
      _ ≤ ∑ _d ∈ D, (4 * q * L) ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        exact pow_le_pow_left₀ (norm_nonneg _) (hBpoint d) 2
      _ = (D.card : ℕ) * (4 * q * L) ^ 2 := by simp
      _ ≤ (u : ℝ) * (4 * q * L) ^ 2 := by
        gcongr
        exact_mod_cast shortRange_card_le y u
  have hc := finiteComplexCauchy D A B
  have hid : vaughanTypeIFirstLong (fun _ => 1) y u q χ =
      ∑ d ∈ D, A d * B d := by
    unfold vaughanTypeIFirstLong
    simp only [one_mul, D, A, B]
  rw [← hid] at hc
  have hsquare : ‖vaughanTypeIFirstLong (fun _ => 1) y u q χ‖ ^ 2 ≤
      (4 * u * q * L) ^ 2 := by
    calc
      _ ≤ (∑ d ∈ D, ‖A d‖ ^ 2) * (∑ d ∈ D, ‖B d‖ ^ 2) := hc
      _ ≤ (u : ℝ) * ((u : ℝ) * (4 * q * L) ^ 2) := by gcongr
      _ = (4 * u * q * L) ^ 2 := by ring
  have ht : 0 ≤ 4 * (u : ℝ) * q * L := by
    dsimp [L]
    positivity
  nlinarith [norm_nonneg (vaughanTypeIFirstLong (fun _ => 1) y u q χ)]

/-- The complete literal middle lane, bounded by Cauchy over the actual `(d,e)` rows. -/
theorem norm_vaughanTypeIMiddleLong_le_elementaryCauchy
    {N y u v q : ℕ} (hy : y ≤ N) (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ‖vaughanTypeIMiddleLong (fun _ => 1) y u v q χ‖ ≤
      2 * u * v * q * Real.log (v + 1 : ℕ) := by
  let D := vaughanTypeIShortRange y u
  let E := vaughanTypeIShortRange y v
  let R := D ×ˢ E
  let A : ℕ × ℕ → ℂ := fun de =>
    ((((ArithmeticFunction.moebius de.1 : ℤ) : ℂ) *
      (ArithmeticFunction.vonMangoldt de.2 : ℂ)) *
      χ.1 (de.1 : ZMod q) * χ.1 (de.2 : ZMod q))
  let B : ℕ × ℕ → ℂ := fun de =>
    ∑ m ∈ Finset.Icc 1 (y / (de.1 * de.2)), χ.1 (m : ZMod q)
  let L := Real.log (v + 1 : ℕ)
  have hApoint (de : ℕ × ℕ) (hde : de ∈ R) : ‖A de‖ ≤ L := by
    have he := mem_vaughanTypeIShortRange.mp (Finset.mem_product.mp hde).2
    simp only [A, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := de.2)
    rw [abs_of_nonneg hΛ0]
    calc
      _ ≤ 1 * L * 1 * 1 := by
        gcongr
        · exact moebius_complex_norm_le_one de.1
        · exact vonMangoldt_le_log_succ he.1 he.2.2
        · exact χ.1.norm_le_one _
        · exact χ.1.norm_le_one _
      _ = L := by ring
  have hA : (∑ de ∈ R, ‖A de‖ ^ 2) ≤
      ((u : ℝ) * v) * L ^ 2 := by
    calc
      _ ≤ ∑ _de ∈ R, L ^ 2 := by
        apply Finset.sum_le_sum
        intro de hde
        exact pow_le_pow_left₀ (norm_nonneg _) (hApoint de hde) 2
      _ = (R.card : ℕ) * L ^ 2 := by simp
      _ ≤ ((u : ℝ) * v) * L ^ 2 := by
        gcongr
        have hcard : R.card ≤ u * v := by
          rw [show R.card = D.card * E.card by simp [R]]
          exact Nat.mul_le_mul (shortRange_card_le y u) (shortRange_card_le y v)
        exact_mod_cast hcard
  have hBpoint (de : ℕ × ℕ) : ‖B de‖ ≤ 2 * q := by
    have hset : Finset.Ico 1 (y / (de.1 * de.2) + 1) =
        Finset.Icc 1 (y / (de.1 * de.2)) := by ext m; simp
    change ‖∑ m ∈ Finset.Icc 1 (y / (de.1 * de.2)),
      χ.1 (m : ZMod q)‖ ≤ 2 * q
    rw [← hset]
    exact primitiveCharacter_interval_norm_le_two_mul (A := 1)
      (B := y / (de.1 * de.2) + 1) hq χ
  have hB : (∑ de ∈ R, ‖B de‖ ^ 2) ≤
      ((u : ℝ) * v) * (2 * (q : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ _de ∈ R, (2 * (q : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro de hde
        exact pow_le_pow_left₀ (norm_nonneg _) (hBpoint de) 2
      _ = (R.card : ℕ) * (2 * (q : ℝ)) ^ 2 := by simp
      _ ≤ ((u : ℝ) * v) * (2 * (q : ℝ)) ^ 2 := by
        gcongr
        have hcard : R.card ≤ u * v := by
          rw [show R.card = D.card * E.card by simp [R]]
          exact Nat.mul_le_mul (shortRange_card_le y u) (shortRange_card_le y v)
        exact_mod_cast hcard
  have hc := finiteComplexCauchy R A B
  have hid : vaughanTypeIMiddleLong (fun _ => 1) y u v q χ =
      ∑ de ∈ R, A de * B de := by
    unfold vaughanTypeIMiddleLong
    simp only [one_mul, R, D, E, A, B, Finset.sum_product]
  rw [← hid] at hc
  have hsquare : ‖vaughanTypeIMiddleLong (fun _ => 1) y u v q χ‖ ^ 2 ≤
      (2 * u * v * q * L) ^ 2 := by
    calc
      _ ≤ (∑ de ∈ R, ‖A de‖ ^ 2) * (∑ de ∈ R, ‖B de‖ ^ 2) := hc
      _ ≤ (((u : ℝ) * v) * L ^ 2) * (((u : ℝ) * v) * (2 * q) ^ 2) := by gcongr
      _ = (2 * u * v * q * L) ^ 2 := by ring
  have ht : 0 ≤ 2 * (u : ℝ) * v * q * L := by
    dsimp [L]
    positivity
  nlinarith [norm_nonneg (vaughanTypeIMiddleLong (fun _ => 1) y u v q χ)]

/-- Pointwise primitive Type-I prefix amplitude from the exact phase identity.
The only triangle inequality is between the two already-complete lanes. -/
theorem primitivePrefixAmplitude_vaughanTypeI_le_elementaryCauchy
    (N u v q : ℕ) (hq : 1 < q) (χ : PrimitiveCharacter q) :
    primitivePrefixAmplitude
        (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N q χ ≤
      4 * u * q * Real.log (N + 1 : ℕ) +
        2 * u * v * q * Real.log (v + 1 : ℕ) := by
  let K : ℝ := 4 * u * q * Real.log (N + 1 : ℕ) +
    2 * u * v * q * Real.log (v + 1 : ℕ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  change Real.sqrt (primitiveCharacterPrefixMaxSquare
    (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) 0 N q χ) ≤ K
  rw [← Real.sqrt_sq hK]
  apply Real.sqrt_le_sqrt
  unfold primitiveCharacterPrefixMaxSquare
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := by simpa [Finset.mem_range] using hy
  rw [show vaughanTypeICoeff vaughanUnitIntegerCoeff u v =
    vaughanTypeILongCoeff vaughanUnitIntegerCoeff u v by rfl]
  rw [primitiveCharacterPrefixSquare_typeI_eq_long]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  calc
    ‖vaughanTypeILongPrefix (fun n => vaughanUnitIntegerCoeff n) y u v q χ‖ ≤
        ‖vaughanTypeIFirstLong (fun _ => 1) y u q χ‖ +
          ‖vaughanTypeIMiddleLong (fun _ => 1) y u v q χ‖ := by
      exact norm_sub_le _ _
    _ ≤ K := add_le_add
      (norm_vaughanTypeIFirstLong_le_elementaryCauchy hyN hq χ)
      (norm_vaughanTypeIMiddleLong_le_elementaryCauchy hyN hq χ)

private theorem primitiveCharacter_card_le_totient_elementary
    (q : ℕ) (hq : 0 < q) :
    Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  letI : NeZero q := ⟨hq.ne'⟩
  calc
    Fintype.card (PrimitiveCharacter q) ≤
        Fintype.card (DirichletCharacter ℂ q) := Fintype.card_subtype_le _
    _ = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- AP-normalized Type-I mean on any conductor subset of `Icc 2 Q`. -/
theorem apNormalizedPrimitiveMeanOn_vaughanTypeI_le_elementaryCauchy
    (N Q u v : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 2 Q) :
    apNormalizedPrimitiveMeanOn
        (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N S ≤
      6 * (Q : ℝ) ^ 2 *
        ((u : ℝ) * Real.log (N + 1 : ℕ) +
          (u : ℝ) * v * Real.log (v + 1 : ℕ)) := by
  let X : ℝ := (u : ℝ) * Real.log (N + 1 : ℕ) +
    (u : ℝ) * v * Real.log (v + 1 : ℕ)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  unfold apNormalizedPrimitiveMeanOn
  calc
    _ ≤ ∑ _q ∈ S, 6 * (Q : ℝ) * X := by
      apply Finset.sum_le_sum
      intro q hqS
      have hqI := Finset.mem_Icc.mp (hS hqS)
      have hq0 : 0 < q := by omega
      have hφ : 0 < (q.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hq0
      have hamp (χ : PrimitiveCharacter q) :
          primitivePrefixAmplitude
              (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N q χ ≤
            6 * (q : ℝ) * X := by
        refine (primitivePrefixAmplitude_vaughanTypeI_le_elementaryCauchy
          N u v q (by omega) χ).trans ?_
        dsimp [X]
        have hfirst6 :
            4 * (u : ℝ) * q * Real.log (N + 1 : ℕ) ≤
              6 * q * ((u : ℝ) * Real.log (N + 1 : ℕ)) := by
          calc
            4 * (u : ℝ) * q * Real.log (N + 1 : ℕ) =
                4 * ((u : ℝ) * q * Real.log (N + 1 : ℕ)) := by ring
            _ ≤ 6 * ((u : ℝ) * q * Real.log (N + 1 : ℕ)) :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
            _ = 6 * q * ((u : ℝ) * Real.log (N + 1 : ℕ)) := by ring
        have hmiddle6 :
            2 * (u : ℝ) * v * q * Real.log (v + 1 : ℕ) ≤
              6 * q * ((u : ℝ) * v * Real.log (v + 1 : ℕ)) := by
          calc
            2 * (u : ℝ) * v * q * Real.log (v + 1 : ℕ) =
                2 * ((u : ℝ) * v * q * Real.log (v + 1 : ℕ)) := by ring
            _ ≤ 6 * ((u : ℝ) * v * q * Real.log (v + 1 : ℕ)) :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
            _ = 6 * q * ((u : ℝ) * v * Real.log (v + 1 : ℕ)) := by ring
        calc
          4 * (u : ℝ) * q * Real.log (N + 1 : ℕ) +
              2 * (u : ℝ) * v * q * Real.log (v + 1 : ℕ) ≤
            6 * q * ((u : ℝ) * Real.log (N + 1 : ℕ)) +
              6 * q * ((u : ℝ) * v * Real.log (v + 1 : ℕ)) :=
                add_le_add hfirst6 hmiddle6
          _ = 6 * q * ((u : ℝ) * Real.log (N + 1 : ℕ) +
              (u : ℝ) * v * Real.log (v + 1 : ℕ)) := by ring
      calc
        ((q.totient : ℝ)⁻¹) *
            ∑ χ : PrimitiveCharacter q,
              primitivePrefixAmplitude
                (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N q χ ≤
          ((q.totient : ℝ)⁻¹) *
            ∑ _χ : PrimitiveCharacter q, 6 * (q : ℝ) * X := by
              gcongr with χ
              exact hamp χ
        _ = ((q.totient : ℝ)⁻¹) *
            (Fintype.card (PrimitiveCharacter q) : ℝ) * (6 * q * X) := by simp; ring
        _ ≤ 1 * (6 * q * X) := by
          apply mul_le_mul_of_nonneg_right
          · rw [inv_mul_le_one₀ hφ]
            exact_mod_cast primitiveCharacter_card_le_totient_elementary q hq0
          · positivity
        _ ≤ 6 * Q * X := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by exact_mod_cast hqI.2) (by norm_num)) hX
    _ = (S.card : ℕ) * (6 * (Q : ℝ) * X) := by simp
    _ ≤ (Q : ℝ) * (6 * (Q : ℝ) * X) := by
      gcongr
      exact_mod_cast (Finset.card_le_card hS).trans (by simp [Nat.card_Icc])
    _ = 6 * (Q : ℝ) ^ 2 *
        ((u : ℝ) * Real.log (N + 1 : ℕ) +
          (u : ℝ) * v * Real.log (v + 1 : ℕ)) := by dsimp [X]; ring

/-- The preceding arbitrary-set theorem specialized to the production high-conductor set. -/
theorem highConductorVaughanTypeIMean_le_elementaryCauchy
    (N Q C u v : ℕ) :
    highConductorVaughanTypeIMean N Q C u v ≤
      6 * (Q : ℝ) ^ 2 *
        ((u : ℝ) * Real.log (N + 1 : ℕ) +
          (u : ℝ) * v * Real.log (v + 1 : ℕ)) := by
  unfold highConductorVaughanTypeIMean
  apply apNormalizedPrimitiveMeanOn_vaughanTypeI_le_elementaryCauchy
  intro q hq
  exact (Finset.mem_filter.mp hq).1

end
end AnalyticNumberTheory.LargeSieve

import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedCaseIEndpoint

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- The supported prime carrier cut out by a strict real cutoff. -/
noncomputable def suzukiSupportedBelowPowerReal
    (S : BoundingSieve) (x : ℝ) : Finset ℕ :=
  S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < x)

/-- The source outer carrier with its strict upper cutoff expressed in `ℝ`. -/
noncomputable def suzukiSourceOuterCarrierPowerReal
    (n D : ℕ) (x : ℝ) (P : Finset ℕ) : Finset ℕ :=
  (P.filter (fun p : ℕ => (p : ℝ) < x)).filter fun p =>
    D ≤ p ^ (n + 2) ∧ (Odd n → p ^ 3 < D)

/-- Naturals below a positive real cutoff are exactly naturals below its natural
ceiling.  The positivity hypothesis records the power-cutoff use case. -/
theorem nat_lt_natCeil_iff_lt_real
    {x : ℝ} {z p : ℕ} (_hx : 0 < x) (hz : z = ⌈x⌉₊) :
    p < z ↔ (p : ℝ) < x := by
  rw [hz, Nat.lt_ceil]

/-- Exact carrier transport from an arbitrary positive real cutoff to its
natural ceiling. -/
theorem suzukiSupportedBelow_natCeil_eq_powerReal
    (S : BoundingSieve) {x : ℝ} {z : ℕ} (hx : 0 < x)
    (hz : z = ⌈x⌉₊) :
    suzukiSupportedBelow S z = suzukiSupportedBelowPowerReal S x := by
  ext p
  simp only [suzukiSupportedBelow, suzukiSupportedBelowPowerReal, mem_filter]
  rw [nat_lt_natCeil_iff_lt_real hx hz]

/-- Carrier transport remains exact after any additional recurrence filter. -/
theorem suzukiSupportedBelow_filter_natCeil_eq_powerReal
    (S : BoundingSieve) (P : ℕ → Prop) [DecidablePred P]
    {x : ℝ} {z : ℕ} (hx : 0 < x) (hz : z = ⌈x⌉₊) :
    (suzukiSupportedBelow S z).filter P =
      (suzukiSupportedBelowPowerReal S x).filter P := by
  rw [suzukiSupportedBelow_natCeil_eq_powerReal S hx hz]

/-- In particular, the terminal filter in the base source layer is unchanged. -/
theorem suzukiSourceBaseCarrier_natCeil_eq_powerReal
    (S : BoundingSieve) (D : ℕ) {x : ℝ} {z : ℕ}
    (hx : 0 < x) (hz : z = ⌈x⌉₊) :
    (suzukiSupportedBelow S z).filter (fun p => D ≤ p ^ 3) =
      (suzukiSupportedBelowPowerReal S x).filter (fun p => D ≤ p ^ 3) := by
  exact suzukiSupportedBelow_filter_natCeil_eq_powerReal S _ hx hz

/-- The complete source-recurrence outer carrier is unchanged by replacing a
positive real cutoff by its natural ceiling. -/
theorem suzukiSourceOuterCarrier_natCeil_eq_powerReal
    (n D : ℕ) (P : Finset ℕ) {x : ℝ} {z : ℕ}
    (hx : 0 < x) (hz : z = ⌈x⌉₊) :
    suzukiSourceOuterCarrier n D z P =
      suzukiSourceOuterCarrierPowerReal n D x P := by
  ext p
  simp only [suzukiSourceOuterCarrier, suzukiSourceOuterCarrierPowerReal,
    mem_filter]
  rw [nat_lt_natCeil_iff_lt_real hx hz]

/-- Exact successor recurrence with an arbitrary positive real power cutoff. -/
theorem suzukiSourceV_succ_natCeil_eq_powerReal
    (S : BoundingSieve) {n D z : ℕ} {x : ℝ}
    (hn : 0 < n) (hx : 0 < x) (hz : z = ⌈x⌉₊) :
    suzukiSourceV S (n + 1) D z =
      ∑ p ∈ suzukiSourceOuterCarrierPowerReal
          (n + 1) D x S.prodPrimes.primeFactors,
        S.nu p * suzukiSourceV S n (D ⌈/⌉ p) p := by
  rw [suzukiSourceV_succ_of_pos S hn]
  rw [suzukiSourceOuterCarrier_natCeil_eq_powerReal _ _ _ hx hz]

/-- Suzuki's finite Euler product is literally invariant under natural-ceiling
transport of any positive real cutoff. -/
theorem suzukiVProduct_natCeil_eq_power
    (S : BoundingSieve) {x : ℝ} {z : ℕ} (hx : 0 < x)
    (hz : z = ⌈x⌉₊) :
    suzukiVProduct S (z : ℝ) = suzukiVProduct S x := by
  classical
  unfold suzukiVProduct
  congr 1
  ext p
  simp only [mem_filter]
  rw [Nat.cast_lt, nat_lt_natCeil_iff_lt_real hx hz]

/-- Every Euler suffix carrier is exactly invariant under natural-ceiling
transport. -/
theorem suzukiSuffixCarrier_natCeil_eq_power
    (S : BoundingSieve) (p : ℕ) {x : ℝ} {z : ℕ}
    (hx : 0 < x) (hz : z = ⌈x⌉₊) :
    S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < (z : ℝ)) =
      S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < x) := by
  ext q
  simp only [mem_filter]
  rw [Nat.cast_lt, nat_lt_natCeil_iff_lt_real hx hz]

/-- Consequently every inverse Euler suffix product is exactly invariant. -/
theorem suzukiSuffixProduct_natCeil_eq_power
    (S : BoundingSieve) (p : ℕ) {x : ℝ} {z : ℕ}
    (hx : 0 < x) (hz : z = ⌈x⌉₊) :
    (∏ q ∈ S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < (z : ℝ)), (1 - S.nu q)⁻¹) =
      ∏ q ∈ S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < x), (1 - S.nu q)⁻¹ := by
  rw [suzukiSuffixCarrier_natCeil_eq_power S p hx hz]

/-- A positive natural base has a positive real `1/s` power cutoff, for every
real power parameter `s`. -/
theorem natCast_rpow_one_div_pos {D : ℕ} (hD : 0 < D) (s : ℝ) :
    0 < (D : ℝ) ^ (1 / s) := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hD) _

/-- Convenient exact supported-carrier specialization to `D^(1/s)`. -/
theorem suzukiSupportedBelow_natCeil_rpow_eq
    (S : BoundingSieve) {D z : ℕ} {s : ℝ} (hD : 0 < D)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    suzukiSupportedBelow S z =
      suzukiSupportedBelowPowerReal S ((D : ℝ) ^ (1 / s)) :=
  suzukiSupportedBelow_natCeil_eq_powerReal S
    (natCast_rpow_one_div_pos hD s) hz

/-- Convenient exact Euler-product specialization to `D^(1/s)`. -/
theorem suzukiVProduct_natCeil_rpow_eq
    (S : BoundingSieve) {D z : ℕ} {s : ℝ} (hD : 0 < D)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    suzukiVProduct S (z : ℝ) =
      suzukiVProduct S ((D : ℝ) ^ (1 / s)) :=
  suzukiVProduct_natCeil_eq_power S (natCast_rpow_one_div_pos hD s) hz

/-- Convenient exact source-successor recurrence specialization to
`D^(1/s)`. -/
theorem suzukiSourceV_succ_natCeil_rpow_eq
    (S : BoundingSieve) {n D z : ℕ} {s : ℝ}
    (hn : 0 < n) (hD : 0 < D)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    suzukiSourceV S (n + 1) D z =
      ∑ p ∈ suzukiSourceOuterCarrierPowerReal
          (n + 1) D ((D : ℝ) ^ (1 / s)) S.prodPrimes.primeFactors,
        S.nu p * suzukiSourceV S n (D ⌈/⌉ p) p :=
  suzukiSourceV_succ_natCeil_eq_powerReal S hn
    (natCast_rpow_one_div_pos hD s) hz

/-- Convenient exact inverse-suffix specialization to `D^(1/s)`. -/
theorem suzukiSuffixProduct_natCeil_rpow_eq
    (S : BoundingSieve) (p : ℕ) {D z : ℕ} {s : ℝ} (hD : 0 < D)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    (∏ q ∈ S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < (z : ℝ)), (1 - S.nu q)⁻¹) =
      ∏ q ∈ S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < (D : ℝ) ^ (1 / s)),
          (1 - S.nu q)⁻¹ :=
  suzukiSuffixProduct_natCeil_eq_power S p
    (natCast_rpow_one_div_pos hD s) hz

/-- For a base at least one, decreasing the positive power parameter increases
`D^(1/s)`. -/
theorem rpow_one_div_mono_of_le
    {D s t : ℝ} (hD : 1 ≤ D) (hs : 0 < s) (hst : s ≤ t) :
    D ^ (1 / t) ≤ D ^ (1 / s) := by
  apply Real.rpow_le_rpow_of_exponent_le hD
  exact one_div_le_one_div_of_le hs hst

/-- Natural ceilings preserve the preceding power-cutoff order. -/
theorem natCeil_rpow_one_div_mono_of_le
    {D s t : ℝ} (hD : 1 ≤ D) (hs : 0 < s) (hst : s ≤ t) :
    ⌈D ^ (1 / t)⌉₊ ≤ ⌈D ^ (1 / s)⌉₊ :=
  Nat.ceil_mono (rpow_one_div_mono_of_le hD hs hst)

/-- The cubic natural cutoff lies below every `s`-power natural cutoff with
`0 < s ≤ 3`. -/
theorem natCeil_cuberoot_le_natCeil_power
    {D s : ℝ} (hD : 1 ≤ D) (hs : 0 < s) (hs3 : s ≤ 3) :
    ⌈D ^ (1 / 3 : ℝ)⌉₊ ≤ ⌈D ^ (1 / s)⌉₊ := by
  exact natCeil_rpow_one_div_mono_of_le hD hs hs3

/-- Named `y ≤ z` bridge used by the cubic/source Case-II assembly. -/
theorem caseII_hyz_of_natCeil_powerCutoffs
    {D : ℕ} {s : ℝ} {y z : ℕ} (hD : 1 ≤ D)
    (hs : 0 < s) (hs3 : s ≤ 3)
    (hy : y = ⌈(D : ℝ) ^ (1 / 3 : ℝ)⌉₊)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    y ≤ z := by
  rw [hy, hz]
  apply natCeil_cuberoot_le_natCeil_power
  · exact_mod_cast hD
  · exact hs
  · exact hs3

/-- Every supported prime below the cubic natural ceiling satisfies Suzuki's
strict cubic source cutoff. -/
theorem supported_cube_lt_of_eq_natCeil_cuberoot
    (S : BoundingSieve) {D y : ℕ} (hD : 0 < D)
    (hy : y = ⌈(D : ℝ) ^ (1 / 3 : ℝ)⌉₊) :
    ∀ p ∈ suzukiSupportedBelow S y, p ^ 3 < D := by
  intro p hp
  have hpP : p ∈ S.prodPrimes.primeFactors := (mem_filter.mp hp).1
  have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hpP).pos
  have hroot0 : 0 < (D : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have hplt : (p : ℝ) < (D : ℝ) ^ (1 / 3 : ℝ) :=
    (nat_lt_natCeil_iff_lt_real hroot0 hy).1 (mem_filter.mp hp).2
  have hr := Real.lt_rpow_inv_iff_of_pos
    (x := (p : ℝ)) (y := (D : ℝ)) (z := (3 : ℝ))
    (by positivity) (by positivity) (by norm_num)
  norm_num [one_div] at hr
  have hcubeR : (p : ℝ) ^ (3 : ℕ) < (D : ℝ) := hr.mp hplt
  exact_mod_cast hcubeR

/-- One packet supplies both Case-II cutoff obligations: cubic support at `y`
and the natural-cutoff order `y ≤ z`. -/
theorem cubicSupport_and_caseII_hyz_of_natCeil_powerCutoffs
    (S : BoundingSieve) {D : ℕ} {s : ℝ} {y z : ℕ}
    (hD : 1 ≤ D) (hs : 0 < s) (hs3 : s ≤ 3)
    (hy : y = ⌈(D : ℝ) ^ (1 / 3 : ℝ)⌉₊)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    (∀ p ∈ suzukiSupportedBelow S y, p ^ 3 < D) ∧ y ≤ z := by
  exact ⟨supported_cube_lt_of_eq_natCeil_cuberoot S (by omega) hy,
    caseII_hyz_of_natCeil_powerCutoffs hD hs hs3 hy hz⟩

end MathlibNt.SieveTheory

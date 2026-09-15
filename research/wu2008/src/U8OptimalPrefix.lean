import U8PairGeometry
import AnalyticNumberTheory.Mertens.PartialSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Prime reciprocal mass, not an integer harmonic relaxation. -/
noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal.SmallProduct
open AnalyticNumberTheory.Mertens TwoDimensional

/-- One Mertens interval constant works simultaneously for every exponent and N. -/
theorem prime_window_mass_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (N : ℕ) (a : ℝ), 0 < a → a ≤ 1 → 1 < N →
      3 ≤ (N : ℝ)^a → ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ (N : ℝ)^a ≤ p ∧ p ≤ N) →
      (∑ p ∈ S, 1/(p : ℝ)) ≤ Real.log (1/a)+E := by
  classical
  obtain ⟨E,hE,hbound⟩ := primeReciprocalSum_range_le
  refine ⟨E,hE,?_⟩
  intro N a ha ha1 hN hNa S hS
  let A : ℕ := ⌈(N : ℝ)^a⌉₊
  have hceil : (N : ℝ)^a ≤ A := Nat.le_ceil _
  have hA3 : 3 ≤ A := by exact_mod_cast hNa.trans hceil
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos hN'
  have hlogA : 0 < Real.log A := Real.log_pos (by exact_mod_cast (by omega : 1 < A))
  have hloglower : a * Real.log N ≤ Real.log A := by
    rw [← Real.log_rpow (by positivity)]
    exact Real.log_le_log (by positivity) hceil
  have hAN : A ≤ N := Nat.ceil_le.mpr (by
    simpa using Real.rpow_le_rpow_of_exponent_le hN'.le ha1)
  have hsub : S ⊆ (range (N+1)).filter (fun p => p.Prime ∧ A ≤ p) := by
    intro p hp
    have hd := hS p hp
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hd.1, Nat.ceil_le.mpr hd.2.1⟩
  have hratio : Real.log N / Real.log A ≤ 1/a := by
    apply (div_le_div_iff₀ hlogA ha).mpr
    nlinarith [hloglower]
  have hlogratio := Real.log_le_log (div_pos hlogN hlogA) hratio
  calc
    _ ≤ ∑ p ∈ (range (N+1)).filter (fun p => p.Prime ∧ A ≤ p), 1/(p : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = primeReciprocalSum N - primeReciprocalSum (A-1) :=
      primeReciprocalSum_range_eq A N (by omega) hAN
    _ ≤ Real.log (Real.log N / Real.log A)+E := hbound A N hA3 hAN
    _ ≤ _ := add_le_add hlogratio le_rfl

/-- The two prime windows retain their separate lower exponents. No integer
harmonic sum is used in this bound. The constant is independent of e and N. -/
theorem pair_reciprocal_mass_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (e : ℝ), 1 < N →
      3 ≤ (N : ℝ)^originalAlpha →
      (∑ t ∈ pairs N e, 1/((t.1 : ℝ)*t.2)) ≤ C := by
  classical
  obtain ⟨E,hE,hbound⟩ := prime_window_mass_bound
  let A := Real.log (1/originalAlpha)+E
  let B := Real.log (1/(1/3 : ℝ))+E
  have hA : 0 < A := add_pos_of_nonneg_of_pos
    (Real.log_nonneg (by norm_num [originalAlpha])) hE
  have hB : 0 < B := add_pos_of_nonneg_of_pos
    (Real.log_nonneg (by norm_num)) hE
  refine ⟨A*B,mul_pos hA hB,?_⟩
  intro N e hN hNa
  let S := (pairs N e).image Prod.fst
  let T := (pairs N e).image Prod.snd
  have hS : ∀ p ∈ S, p.Prime ∧ (N : ℝ)^originalAlpha ≤ p ∧ p ≤ N := by
    intro p hp
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hp
    have hd := pairs_data ht
    have hbox := mem_product.mp (pairs_subset_box N e ht)
    exact ⟨hd.1,hd.2.2.2.1,by have := mem_range.mp hbox.1; omega⟩
  have hT : ∀ p ∈ T, p.Prime ∧ (N : ℝ)^(1/3 : ℝ) ≤ p ∧ p ≤ N := by
    intro p hp
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hp
    have hd := pairs_data ht
    have hbox := mem_product.mp (pairs_subset_box N e ht)
    exact ⟨hd.2.1,hd.2.2.2.2.2.1,by have := mem_range.mp hbox.2; omega⟩
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hNb : 3 ≤ (N : ℝ)^(1/3 : ℝ) := hNa.trans
    (Real.rpow_le_rpow_of_exponent_le hN' (by norm_num [originalAlpha]))
  have hsumS : (∑ p ∈ S, 1/(p : ℝ)) ≤ A :=
    hbound N originalAlpha (by norm_num [originalAlpha]) (by norm_num [originalAlpha]) hN hNa S hS
  have hsumT : (∑ p ∈ T, 1/(p : ℝ)) ≤ B :=
    hbound N (1/3) (by norm_num) (by norm_num) hN hNb T hT
  calc
    _ ≤ ∑ t ∈ S ×ˢ T, 1/((t.1 : ℝ)*t.2) :=
      sum_le_sum_of_subset_of_nonneg (fun t ht => mem_product.mpr
        ⟨mem_image.mpr ⟨t,ht,rfl⟩,mem_image.mpr ⟨t,ht,rfl⟩⟩)
        (fun _ _ _ => by positivity)
    _ = (∑ p ∈ S, 1/(p : ℝ))*(∑ p ∈ T, 1/(p : ℝ)) := by
      rw [sum_product, primeReciprocal_doubleSum_eq]
    _ ≤ A*B := mul_le_mul hsumS hsumT (sum_nonneg (fun _ _ => by positivity)) hA.le

/-- An actual small-prefix upper bound with constructed weights entirely eliminated.
Only the true dimension-two denominator remains; no logarithmic lower bound is assumed. -/
theorem smallPrefix_optimal_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), Even N → 4 ≤ N →
      3 ≤ (N : ℝ)^originalAlpha → ∀ (e R : ℝ), 0 ≤ e → e ≤ 1/2 →
      1 ≤ R → R < (N : ℝ)^originalAlpha →
      ((smallPrefix N e).card : ℝ) ≤
        C*e*(N : ℝ)/denominator N ((N : ℝ)^(1/3 : ℝ)) R +
        8*(N : ℝ)^(3/5 : ℝ)*(R+1)^2*R^4 := by
  obtain ⟨C,hC,hmass⟩ := pair_reciprocal_mass_bounded
  refine ⟨C,hC,?_⟩
  intro N hNe hN hNa e R he0 he hR hRa
  have hden : 0 < denominator N ((N : ℝ)^(1/3 : ℝ)) R := by
    rw [← denominator_eq N hNe]
    exact TruncatedSelberg.G_pos _ hR
  have hlength : (∑ t ∈ pairs N e, ((interval N e t).card : ℝ)) ≤ C*e*N := by
    calc
      _ ≤ ∑ t ∈ pairs N e, e*(N : ℝ)/((t.1 : ℝ)*t.2) :=
        sum_le_sum fun _ ht => interval_card_le_cutoff ht he0
      _ = e*(N : ℝ)*(∑ t ∈ pairs N e, 1/((t.1 : ℝ)*t.2)) := by
        rw [mul_sum]
        exact sum_congr rfl (fun _ _ => by ring)
      _ ≤ e*(N : ℝ)*C := mul_le_mul_of_nonneg_left (hmass N e (by omega) hNa) (by positivity)
      _ = _ := by ring
  apply (smallPrefix_optimal_card_bound N hNe e R hN he hR hRa).trans
  apply add_le_add (div_le_div_of_nonneg_right hlength hden.le)
  calc
    _ ≤ (4*(N : ℝ)^(3/5 : ℝ))*(2*(R+1)^2*R^4) :=
      mul_le_mul_of_nonneg_right (pairs_card_le_three_fifths (by omega : 1 ≤ N)
        (by linarith : e ≤ 1)) (by positivity)
    _ = _ := by ring

/-- Every fixed legal positive exponent can be inserted into the actual bound;
the small-product parameter stays independent of N. -/
theorem smallPrefix_optimal_power_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ), 0 < β → β < originalAlpha →
      ∀ (N : ℕ), Even N → 4 ≤ N → 3 ≤ (N : ℝ)^originalAlpha →
      ∀ e : ℝ, 0 ≤ e → e ≤ 1/2 →
      ((smallPrefix N e).card : ℝ) ≤
        C*e*(N : ℝ)/denominator N ((N : ℝ)^(1/3 : ℝ)) ((N : ℝ)^β) +
        8*(N : ℝ)^(3/5 : ℝ)*((N : ℝ)^β+1)^2*((N : ℝ)^β)^4 := by
  obtain ⟨C,hC,hbound⟩ := smallPrefix_optimal_upper
  refine ⟨C,hC,?_⟩
  intro β hβ hβα N hNe hN hNa e he0 he
  have hlegal := power_cutoff_legal (by omega : 1 < N) hβ hβα
  exact hbound N hNe hN hNa e ((N : ℝ)^β) he0 he hlegal.1 hlegal.2.1

open Filter in
/-- A threshold-free eventual interface for every fixed e and fixed legal beta. -/
theorem smallPrefix_optimal_eventually_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ (e β : ℝ), 0 ≤ e → e ≤ 1/2 →
      0 < β → β < originalAlpha → ∀ᶠ N : ℕ in atTop, Even N →
      ((smallPrefix N e).card : ℝ) ≤
        C*e*(N : ℝ)/denominator N ((N : ℝ)^(1/3 : ℝ)) ((N : ℝ)^β) +
        8*(N : ℝ)^(3/5 : ℝ)*((N : ℝ)^β+1)^2*((N : ℝ)^β)^4 := by
  obtain ⟨C,hC,hbound⟩ := smallPrefix_optimal_power_upper
  refine ⟨C,hC,?_⟩
  intro e β he0 he hβ hβα
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop (by norm_num [originalAlpha] : 0 < originalAlpha)).comp hcast
  have hlarge : ∀ᶠ N : ℕ in atTop, 3 ≤ (N : ℝ)^originalAlpha :=
    hpow.eventually_ge_atTop 3
  filter_upwards [hlarge, eventually_ge_atTop 4] with N hNa hN
  intro hNe
  exact hbound β hβ hβα N hNe hN hNa e he0 he

open Filter Asymptotics in
/-- A universal exponent gap pays the polynomial error on the N/log² N scale.
No choice of e as a function of N is involved, and no bound for G is used. -/
theorem polynomial_remainder_littleO {β : ℝ} (hβ : 0 < β) (hsmall : β < 1/15) :
    (fun N : ℕ => 8*(N : ℝ)^(3/5 : ℝ)*((N : ℝ)^β+1)^2*((N : ℝ)^β)^4)
      =o[atTop] (fun N : ℕ => (N : ℝ)/(Real.log N)^2) := by
  let q : ℝ := 3/5+6*β
  have hq : 0 < 1-q := by dsimp [q]; linarith
  have hlog : Tendsto (fun N : ℕ => (Real.log N)^2 / (N : ℝ)^(1-q)) atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hq).tendsto_div_nhds_zero
    have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hh := h.comp hcast
    apply hh.congr'
    filter_upwards [] with N
    exact Real.rpow_two (Real.log N) ▸ rfl
  refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hN' : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hn : (N : ℝ)/(Real.log N)^2 ≠ 0 :=
      div_ne_zero (by positivity) (pow_ne_zero _ (Real.log_pos hN').ne')
    exact fun h => (hn h).elim
  apply squeeze_zero' ?_ ?_ (by simpa using hlog.const_mul 32)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    positivity
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hNb : 1 ≤ (N : ℝ)^β := Real.one_le_rpow hN1 hβ.le
    have hp : (N : ℝ)^(3/5 : ℝ)*((N : ℝ)^β)^2*((N : ℝ)^β)^4 = (N : ℝ)^q := by
      rw [mul_assoc, ← pow_add, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
        ← Real.rpow_add hN0]
      congr 1
      dsimp [q]
      ring
    have herr : 8*(N : ℝ)^(3/5 : ℝ)*((N : ℝ)^β+1)^2*((N : ℝ)^β)^4 ≤ 32*(N : ℝ)^q := by
      calc
        _ ≤ 8*(N : ℝ)^(3/5 : ℝ)*(2*(N : ℝ)^β)^2*((N : ℝ)^β)^4 := by
          gcongr
          linarith
        _ = 32*((N : ℝ)^(3/5 : ℝ)*((N : ℝ)^β)^2*((N : ℝ)^β)^4) := by ring
        _ = _ := by rw [hp]
    have heq : (N : ℝ)^q / ((N : ℝ)/(Real.log N)^2) =
        (Real.log N)^2 / (N : ℝ)^(1-q) := by
      rw [Real.rpow_sub hN0, Real.rpow_one]
      field_simp
    calc
      _ ≤ (32*(N : ℝ)^q) / ((N : ℝ)/(Real.log N)^2) :=
        div_le_div_of_nonneg_right herr (by positivity)
      _ = 32*((Real.log N)^2/(N : ℝ)^(1-q)) := by rw [mul_div_assoc, heq]

end U8Literal.SmallProduct

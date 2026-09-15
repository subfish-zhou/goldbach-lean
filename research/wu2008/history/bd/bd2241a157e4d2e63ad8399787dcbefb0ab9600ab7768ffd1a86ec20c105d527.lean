import MathlibNt.Wu2008DoubleSieve.Gamma6GainMain

/-! # Actual Gamma7/8 selected-prime-cutoff counts

The Boolean index is true for Gamma7 and false for Gamma8.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology Interval

noncomputable def gamma78GainLower (tri : Bool) : ℝ :=
  if tri then gamma5MassA else gamma6BaseB

noncomputable def gamma78GainUpper (tri : Bool) : ℝ :=
  if tri then gamma6BaseB else gamma5ClassicalB

noncomputable def gamma78GainStart (tri : Bool) (t : ℝ) : ℝ :=
  if tri then t else gamma6BaseB

noncomputable def gamma78GainLabels {i : ℕ} (tri : Bool) (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : Finset Gamma5ClassicalLabel :=
  (gamma5ClassicalLabels N δ W).filter (fun x =>
    (x.2.1 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma6BaseB ∧
    (if tri then True else
      ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma6BaseB ≤ (x.2.2 : ℝ)) ∧
    (x.2.2 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma78GainUpper tri)

noncomputable def gamma78GainCount {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (X : Finset Gamma5ClassicalLabel) : ℝ :=
  ∑ x ∈ X, (convolutionCoeff W x.1 : ℝ) *
    (sourceSieveCount N (gamma5ClassicalProduct x) (x.1 * N) (x.2.1 : ℝ) : ℝ)

theorem gamma78Gain_count_eq_nat {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (X : Finset Gamma5ClassicalLabel) :
    gamma78GainCount N W X =
      ((∑ x ∈ X, convolutionCoeff W x.1 *
        (sourceSieveCarrier N (x.1 * x.2.1 * x.2.2) (x.1 * N) (x.2.1 : ℝ)).card : ℕ) : ℝ) := by
  simp only [gamma78GainCount, sourceSieveCount, gamma5ClassicalProduct, Nat.cast_sum, Nat.cast_mul,
    Int.cast_natCast]

theorem gamma78Gain_count_partition {α : Type*} [Fintype α] {i : ℕ}
    (N : ℕ) (W : Fin i → Finset ℕ)
    (L : Finset Gamma5ClassicalLabel) (P : α → Finset Gamma5ClassicalLabel)
    (hd : Pairwise (fun j l => Disjoint (P j) (P l))) (hs : ∀ j, P j ⊆ L) :
    gamma78GainCount N W L = gamma78GainCount N W (L \ univ.biUnion P) +
      ∑ j, gamma78GainCount N W (P j) :=
  gamma5Gain_partition_sum L P hd hs _

theorem gamma78Gain_count_le_classical {i N : ℕ} {δ : ℝ} {W : Fin i → Finset ℕ}
    {X : Finset Gamma5ClassicalLabel} (hX : X ⊆ gamma5ClassicalLabels N δ W) :
    gamma78GainCount N W X ≤ gamma5ClassicalCount N δ W X := by
  apply sum_le_sum
  intro x hx
  have hp := (mem_filter.mp (hX hx)).2.2.2.2.2.1
  exact mul_le_mul_of_nonneg_left (gamma5Classical_source_count_antitone _ _ _ hp) (Nat.cast_nonneg _)

theorem gamma78Gain_constants (tri : Bool) :
    gamma5MassA < gamma6BaseB ∧ gamma6BaseB < gamma5ClassicalB ∧
      gamma5MassA ≤ gamma78GainLower tri ∧
      gamma78GainLower tri < gamma78GainUpper tri ∧
      gamma6BaseB ≤ gamma78GainUpper tri ∧ gamma78GainUpper tri ≤ gamma5ClassicalB := by
  cases tri <;> norm_num [gamma78GainLower, gamma78GainUpper, gamma5MassA,
    gamma6BaseB, gamma5ClassicalB, gamma5ClassicalS]

theorem gamma78Gain_mem_labels_iff {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (tri : Bool) (x : Gamma5ClassicalLabel) :
    x ∈ gamma78GainLabels tri N δ (convolutionWuWindows N Δ V) ↔
      x.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) ∧
      x.2.1.Prime ∧ x.2.2.Prime ∧ x.2.1.Coprime N ∧ x.2.2.Coprime N ∧
      wuLocalCutoff N δ x.1 gamma5ClassicalS ≤ (x.2.1 : ℝ) ∧ x.2.1 < x.2.2 ∧
      (x.2.1 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma6BaseB ∧
      (if tri then True else
        ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma6BaseB ≤ (x.2.2 : ℝ)) ∧
      (x.2.2 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma78GainUpper tri := by
  constructor
  · intro hx
    obtain ⟨hx,hp,hq,hqu⟩ := mem_filter.mp hx
    obtain ⟨hd,hpp,hqq,hpN,hqN,hz,hpq,_⟩ :=
      (gamma5Classical_mem_labels_iff hN hδ hδhi hb x).mp hx
    exact ⟨hd,hpp,hqq,hpN,hqN,hz,hpq,hp,hq,hqu⟩
  · rintro ⟨hd,hp,hq,hpN,hqN,hz,hpq,hpu,hql,hqu⟩
    have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
    have hu := rpow_le_rpow_of_exponent_le hR.le (gamma78Gain_constants tri).2.2.2.2.2
    exact mem_filter.mpr ⟨(gamma5Classical_mem_labels_iff hN hδ hδhi hb x).mpr
      ⟨hd,hp,hq,hpN,hqN,hz,hpq,hqu.trans_le hu⟩,hpu,hql,hqu⟩

noncomputable def gamma78GainV (t u : ℝ) : ℝ := (1 - t - u) / t

def gamma78GainRegion (tri : Bool) : Set (ℝ × ℝ) :=
  {v | v.1 ∈ Icc gamma5MassA gamma6BaseB ∧
    v.2 ∈ Icc (gamma78GainStart tri v.1) (gamma78GainUpper tri)}

theorem gamma78Gain_region_bounds {tri : Bool} {v : ℝ × ℝ} (hv : v ∈ gamma78GainRegion tri) :
    gamma5GainTriangle v ∧ v.1 ≤ gamma6BaseB ∧
      0 < v.1 ∧ 0 < v.2 ∧ v.1 < 1 ∧ v.2 < 1 ∧
      2 * v.2 < 1 ∧ v.2 + 2 * v.1 < 1 ∧
      1 < gamma78GainV v.1 v.2 ∧ gamma78GainV v.1 v.2 < 3 := by
  have ha : (0 : ℝ) < gamma5MassA := by norm_num [gamma5MassA, gamma5ClassicalS]
  have ht := hv.1
  have hu := hv.2
  have htu : v.1 ≤ v.2 := by
    cases tri <;> simp only [gamma78GainStart, Bool.false_eq_true, if_false, if_true] at hu
    · exact ht.2.trans hu.1
    · exact hu.1
  have huc : v.2 ≤ gamma5ClassicalB := hu.2.trans (gamma78Gain_constants tri).2.2.2.2.2
  have ht0 := ha.trans_le ht.1
  have hu0 := ht0.trans_le htu
  refine ⟨⟨ht.1,htu,huc⟩,ht.2,ht0,hu0,?_,?_,?_,?_,?_,?_⟩
  all_goals
    norm_num [gamma5MassA, gamma5ClassicalS, gamma6BaseB, gamma5ClassicalB] at ht huc
  · linarith [ht.2]
  · linarith
  · linarith
  · linarith [ht.2]
  · apply (lt_div_iff₀ ht0).mpr
    linarith [ht.2]
  · apply (div_lt_iff₀ ht0).mpr
    linarith [ht.1]

theorem gamma78Gain_V_antitone {A C t u : ℝ} (hA : 0 < A) (hAt : A ≤ t)
    (hCu : C ≤ u) (hu : u ≤ 1) :
    gamma78GainV t u ≤ gamma78GainV A C := by
  have ht : 0 < t := hA.trans_le hAt
  have he (x y : ℝ) (hx : x ≠ 0) : gamma78GainV x y = (1-y)/x-1 := by
    unfold gamma78GainV
    field_simp
    ring
  rw [he _ _ ht.ne', he _ _ hA.ne']
  apply sub_le_sub_right
  exact (div_le_div_of_nonneg_left (by linarith) hA hAt).trans
    (div_le_div_of_nonneg_right (by linarith) hA.le)

end Wu2008DoubleSieve

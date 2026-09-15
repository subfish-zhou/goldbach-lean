import MathlibNt.Wu2008DoubleSieve.TruncatedFourGeometry
import MathlibNt.Wu2008DoubleSieve.NinthProductProfile
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledR1Layers
import MathlibNt.Wu2008DoubleSieve.Omega3Multiplicity

/-! The fourth prime varies; the rough residual remains an arbitrary integer.
The support is independent of the output prime and of every AP modulus. -/
namespace Wu2008DoubleSieve.LastPrimeFour
open Finset Real
open scoped Classical

abbrev Index := ℕ × ℕ × ℕ × ℕ

def cofactor (t : Index) : ℕ := t.1 * t.2.1 * t.2.2.1 * t.2.2.2
noncomputable def z (N : ℕ) : ℝ := (N : ℝ)^truncatedSixthLowerAlpha
noncomputable def w (N : ℕ) : ℝ := (N : ℝ)^truncatedSixthLowerBeta
noncomputable def v (N : ℕ) : ℝ := (N : ℝ)^truncatedSixthLowerLambda

/-- `true` is the original eleventh family, `false` the tenth. -/
noncomputable def lower (N : ℕ) (eleven : Bool) (t : Index) : ℝ :=
  if eleven then max (t.2.2.1 : ℝ) ((⌈w N⌉ : ℤ) - 1 : ℝ) else t.2.2.1
noncomputable def cap (N : ℕ) (eleven : Bool) (t : Index) : ℝ :=
  if eleven then v N / t.2.2.1 else w N
noncomputable def upper (N : ℕ) (eleven : Bool) (t : Index) : ℝ :=
  min (((⌈cap N eleven t⌉ : ℤ) : ℝ) - 1) (ninthProfileUpper N (cofactor t))

noncomputable def base (N : ℕ) : Finset Index :=
  ((range (N+1)) ×ˢ (range (N+1)) ×ˢ (range (N+1)) ×ˢ (range (N+1))).filter
    fun t => t.1.Prime ∧ t.1.Coprime N ∧ z N ≤ t.1 ∧
      t.2.1.Prime ∧ t.2.1.Coprime N ∧ t.2.2.1.Prime ∧ t.2.2.1.Coprime N ∧
      t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧ (t.2.2.1 : ℝ) < w N ∧
      1 < t.2.2.2 ∧ LiLiuPrereqBuchstab.Rough (t.2.1 : ℝ) t.2.2.2

noncomputable def labels (N : ℕ) (eleven : Bool) : Finset Index :=
  (base N).filter fun t =>
    (omega3ProfilePrimes N (lower N eleven t) (upper N eleven t)).Nonempty

/-- Exact integer rounding, valid also when the real cutoff is an integer. -/
theorem strict_ceiling (x : ℝ) (d : ℕ) :
    (d : ℝ) ≤ (⌈x⌉ : ℤ) - 1 ↔ (d : ℝ) < x := by
  have h : (d : ℤ) ≤ ⌈x⌉ - 1 ↔ (d : ℤ) < ⌈x⌉ := by omega
  have hc : (d : ℝ) ≤ (⌈x⌉ : ℤ) - 1 ↔ (d : ℤ) ≤ ⌈x⌉ - 1 := by
    constructor <;> intro hh <;> exact_mod_cast hh
  rw [hc, h, Int.lt_ceil]
  norm_cast

theorem closed_ceiling (x : ℝ) (d : ℕ) :
    ((⌈x⌉ : ℤ) : ℝ) - 1 < d ↔ x ≤ (d : ℝ) := by
  have h : ⌈x⌉ - 1 < (d : ℤ) ↔ ⌈x⌉ ≤ (d : ℤ) := by omega
  have hc : ((⌈x⌉ : ℤ) : ℝ) - 1 < d ↔ ⌈x⌉ - 1 < (d : ℤ) := by
    constructor <;> intro hh <;> exact_mod_cast hh
  rw [hc, h, Int.ceil_le]
  norm_cast

theorem lower_iff (N d : ℕ) (e : Bool) (t : Index) :
    lower N e t < (d : ℝ) ↔ t.2.2.1 < d ∧ (e = true → w N ≤ d) := by
  cases e <;> simp [lower, closed_ceiling]

theorem upper_iff {N : ℕ} (hN : 0 < N) (e : Bool) (t : Index)
    (hm : 0 < cofactor t) (d : ℕ) :
    (d : ℝ) ≤ upper N e t ↔ (d : ℝ) < cap N e t ∧ cofactor t*d < N := by
  simp only [upper, le_min_iff, strict_ceiling, ninthProfileUpper_nat_iff hN hm]

theorem base_data {N : ℕ} {t : Index} (ht : t ∈ base N) :
    t.1.Prime ∧ t.1.Coprime N ∧ z N ≤ t.1 ∧
      t.2.1.Prime ∧ t.2.1.Coprime N ∧ t.2.2.1.Prime ∧ t.2.2.1.Coprime N ∧
      t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧ (t.2.2.1 : ℝ) < w N ∧
      1 < t.2.2.2 ∧ LiLiuPrereqBuchstab.Rough (t.2.1 : ℝ) t.2.2.2 :=
  (mem_filter.mp ht).2

theorem base_pos {N : ℕ} {t : Index} (ht : t ∈ base N) : 0 < cofactor t := by
  obtain ⟨ha,_,_,hb,_,hc,_,_,_,_,hn,_⟩ := base_data ht
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha.pos hb.pos) hc.pos) (by omega)

theorem labels_base {N : ℕ} {e : Bool} {t : Index} (ht : t ∈ labels N e) :
    t ∈ base N := (mem_filter.mp ht).1

/-- Nonempty support is a proved restriction, not an assumption on all windows. -/
theorem omitted_empty {N : ℕ} {e : Bool} {t : Index} (ht : t ∈ base N)
    (hn : t ∉ labels N e) :
    omega3ProfilePrimes N (lower N e t) (upper N e t) = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  intro hp
  exact hn (mem_filter.mpr ⟨ht,hp⟩)

theorem label_geometry {N : ℕ} {e : Bool} {t : Index} (ht : t ∈ labels N e) :
    0 < cofactor t ∧ 2 ≤ lower N e t ∧ lower N e t ≤ upper N e t ∧
      (cofactor t : ℝ) * upper N e t ≤ N := by
  have hb := labels_base ht
  obtain ⟨ha,_,_,hp,_,hc,_⟩ := base_data hb
  have hm := base_pos hb
  obtain ⟨d,hd⟩ := (mem_filter.mp ht).2
  obtain ⟨_,_,hlo,hup⟩ := mem_filter.mp hd
  have hc2 : (2 : ℝ) ≤ t.2.2.1 := by exact_mod_cast hc.two_le
  have hmR : (0 : ℝ) < cofactor t := by exact_mod_cast hm
  refine ⟨hm, ?_, hlo.le.trans hup, ?_⟩
  · cases e
    · exact hc2
    · exact hc2.trans (le_max_left _ _)
  · calc
      _ ≤ (cofactor t : ℝ) * ninthProfileUpper N (cofactor t) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hmR.le
      _ = (N : ℝ)-1 := by rw [ninthProfileUpper, mul_div_cancel₀ _ hmR.ne']
      _ ≤ N := by linarith

theorem label_balanced {N : ℕ} (hN : 1 < N) {e : Bool} {t : Index}
    (ht : t ∈ labels N e) :
    (N : ℝ)^truncatedSixthLowerAlpha ≤ cofactor t ∧
      (cofactor t : ℝ) ≤ (N : ℝ)^(1-truncatedSixthLowerAlpha) := by
  have hb := labels_base ht
  obtain ⟨ha,_,hza,hbP,_,hc,_,hab,hbc,_,hn,_⟩ := base_data hb
  have hm := base_pos hb
  have hmR : (0 : ℝ) ≤ cofactor t := Nat.cast_nonneg _
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨d,hd⟩ := (mem_filter.mp ht).2
  obtain ⟨_,_,hlo,hup⟩ := mem_filter.mp hd
  have hcd := ((lower_iff N d e t).mp hlo).1
  have hs := ((upper_iff (by omega) e t hm d).mp hup).2
  have ham : t.1 ≤ cofactor t := by
    unfold cofactor
    exact (Nat.le_mul_of_pos_right _ hbP.pos).trans
      ((Nat.le_mul_of_pos_right _ hc.pos).trans (Nat.le_mul_of_pos_right _ (by omega)))
  refine ⟨hza.trans (by exact_mod_cast ham), ?_⟩
  have had : (t.1 : ℝ) ≤ d := by exact_mod_cast (hab.le.trans (hbc.le.trans hcd.le))
  have hsR : (cofactor t : ℝ)*(d : ℝ) ≤ N := by exact_mod_cast hs.le
  have hmul := (mul_le_mul_of_nonneg_left (hza.trans had) hmR).trans hsR
  rw [rpow_sub hNR, rpow_one]
  exact (le_div_iff₀ (rpow_pos_of_pos hNR _)).mpr hmul

theorem label_le_N {N : ℕ} {e : Bool} {t : Index} (ht : t ∈ labels N e) :
    cofactor t ≤ N := by
  obtain ⟨_,h2,hlu,hmu⟩ := label_geometry ht
  have hm1 : (cofactor t : ℝ) ≤ (cofactor t : ℝ)*upper N e t :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
  exact_mod_cast hm1.trans hmu

noncomputable def family (N : ℕ) (e : Bool) : LabelledPhysical.Family Index N where
  labels := labels N e
  weight := fun _ => 1
  cofactor := cofactor
  lower := lower N e
  upper := upper N e
  weight_nonneg := by intro t _; norm_num
  geometry := fun _ ht => label_geometry ht

end Wu2008DoubleSieve.LastPrimeFour

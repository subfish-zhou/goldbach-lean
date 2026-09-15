import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFactorConvolution

/-!
# Canonical extraction of a divisor from two positive factors

Fouvry (1987), p. 627, §III.5, the finite identity immediately before (3.12).
Here the extracted divisor is called `D`; in that identity it is `δ δ₂`,
not the three-factor phase modulus `δ δ₁ δ₂`.
The split is determined by `Δ' = gcd D s`, using gcd cancellation only.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Coordinates `((Δ, Δ'), (r', s'))`. -/
abbrev FactorExtractionTuple := (ℕ × ℕ) × (ℕ × ℕ)

def factorExtraction (D r s : ℕ) : FactorExtractionTuple :=
  let Δ' := D.gcd s
  let Δ := D / Δ'
  ((Δ, Δ'), (r / Δ, s / Δ'))

def FactorExtractionValid (D r s : ℕ) (e : FactorExtractionTuple) : Prop :=
  0 < e.1.1 ∧ 0 < e.1.2 ∧ 0 < e.2.1 ∧ 0 < e.2.2 ∧
    D = e.1.1 * e.1.2 ∧ r = e.1.1 * e.2.1 ∧ s = e.1.2 * e.2.2 ∧
    e.2.2.Coprime e.1.1

theorem factorExtraction_valid {D r s : ℕ}
    (hD : 0 < D) (hr : 0 < r) (hs : 0 < s) (hd : D ∣ r * s) :
    FactorExtractionValid D r s (factorExtraction D r s) := by
  let g := D.gcd s
  have hg : 0 < g := Nat.gcd_pos_of_pos_left s hD
  have hgD : g ∣ D := Nat.gcd_dvd_left D s
  have hgs : g ∣ s := Nat.gcd_dvd_right D s
  have hΔ : 0 < D / g := Nat.div_pos (Nat.le_of_dvd hD hgD) hg
  have hc : (D / g).Coprime (s / g) :=
    Nat.gcd_div_gcd_div_gcd_of_pos_left hD
  have hd' : D / g ∣ r * (s / g) := by
    apply Nat.dvd_of_mul_dvd_mul_left hg
    calc
      g * (D / g) = D := Nat.mul_div_cancel' hgD
      _ ∣ r * s := hd
      _ = g * (r * (s / g)) := by
        rw [mul_left_comm, Nat.mul_div_cancel' hgs]
  have hΔr : D / g ∣ r := hc.dvd_mul_right.mp hd'
  refine ⟨hΔ, hg, Nat.div_pos (Nat.le_of_dvd hr hΔr) hΔ,
    Nat.div_pos (Nat.le_of_dvd hs hgs) hg, ?_, ?_, ?_, hc.symm⟩
  · exact (Nat.div_mul_cancel hgD).symm
  · exact (Nat.mul_div_cancel' hΔr).symm
  · exact (Nat.mul_div_cancel' hgs).symm

/-- Reconstruction and the single coprimality condition force all four
coordinates, so the change of variables has no multiplicity. -/
theorem factorExtraction_unique {D r s : ℕ} {e : FactorExtractionTuple}
    (he : FactorExtractionValid D r s e) : e = factorExtraction D r s := by
  obtain ⟨hΔ, hΔ', _, _, hD, hr, hs, hc⟩ := he
  have hg : D.gcd s = e.1.2 := by
    rw [hD, hs, mul_comm e.1.1 e.1.2, Nat.gcd_mul_left,
      hc.symm.gcd_eq_one, mul_one]
  have hquot : D / D.gcd s = e.1.1 := by
    rw [hg, hD, Nat.mul_div_cancel _ hΔ']
  have hrquot : r / (D / D.gcd s) = e.2.1 := by
    rw [hquot, hr, Nat.mul_div_right _ hΔ]
  have hsquot : s / D.gcd s = e.2.2 := by
    rw [hg, hs, Nat.mul_div_right _ hΔ']
  exact Prod.ext (Prod.ext hquot.symm hg.symm) (Prod.ext hrquot.symm hsquot.symm)

theorem factorExtraction_existsUnique {D r s : ℕ}
    (hD : 0 < D) (hr : 0 < r) (hs : 0 < s) (hd : D ∣ r * s) :
    ∃! e : FactorExtractionTuple, FactorExtractionValid D r s e :=
  ⟨factorExtraction D r s, factorExtraction_valid hD hr hs hd,
    fun _ he => factorExtraction_unique he⟩

def factorExtractionSource {ι : Type*} (R S : ℕ) (U : Finset ι)
    (P : ℕ → ℕ → ι → Prop) : Finset ((ℕ × ℕ) × ι) :=
  (((Ioc 0 R) ×ˢ (Ioc 0 S)) ×ˢ U).filter (fun z => P z.1.1 z.1.2 z.2)

def factorExtractionReconstruct {ι : Type*} (z : FactorExtractionTuple × ι) :
    (ℕ × ℕ) × ι :=
  ((z.1.1.1 * z.1.2.1, z.1.1.2 * z.1.2.2), z.2)

/-- An explicit broad four-dimensional box with the original support and
mask, the divisor equation, and the primitive condition as exact filters.
In particular this is not defined as the image of the old index set. -/
def factorExtractionTarget {ι : Type*} (R S : ℕ) (U : Finset ι)
    (D : ℕ → ℕ → ι → ℕ) (P : ℕ → ℕ → ι → Prop) :
    Finset (FactorExtractionTuple × ι) :=
  ((((Ioc 0 R) ×ˢ (Ioc 0 S)) ×ˢ ((Ioc 0 R) ×ˢ (Ioc 0 S))) ×ˢ U).filter
    (fun z =>
      let r := z.1.1.1 * z.1.2.1
      let s := z.1.1.2 * z.1.2.2
      r ≤ R ∧ s ≤ S ∧ P r s z.2 ∧
        D r s z.2 = z.1.1.1 * z.1.1.2 ∧ z.1.2.2.Coprime z.1.1.1)

private theorem source_mem {ι : Type*} {R S : ℕ} {U : Finset ι}
    {P : ℕ → ℕ → ι → Prop} {z : (ℕ × ℕ) × ι} :
    z ∈ factorExtractionSource R S U P ↔
      (0 < z.1.1 ∧ z.1.1 ≤ R) ∧ (0 < z.1.2 ∧ z.1.2 ≤ S) ∧
        z.2 ∈ U ∧ P z.1.1 z.1.2 z.2 := by
  simp only [factorExtractionSource, mem_filter, mem_product, mem_Ioc]
  tauto

private theorem target_mem {ι : Type*} {R S : ℕ} {U : Finset ι}
    {D : ℕ → ℕ → ι → ℕ} {P : ℕ → ℕ → ι → Prop}
    {z : FactorExtractionTuple × ι} :
    z ∈ factorExtractionTarget R S U D P ↔
      (0 < z.1.1.1 ∧ z.1.1.1 ≤ R) ∧ (0 < z.1.1.2 ∧ z.1.1.2 ≤ S) ∧
      (0 < z.1.2.1 ∧ z.1.2.1 ≤ R) ∧ (0 < z.1.2.2 ∧ z.1.2.2 ≤ S) ∧
      z.2 ∈ U ∧ z.1.1.1 * z.1.2.1 ≤ R ∧ z.1.1.2 * z.1.2.2 ≤ S ∧
      P (z.1.1.1 * z.1.2.1) (z.1.1.2 * z.1.2.2) z.2 ∧
      D (z.1.1.1 * z.1.2.1) (z.1.1.2 * z.1.2.2) z.2 =
        z.1.1.1 * z.1.1.2 ∧ z.1.2.2.Coprime z.1.1.1 := by
  simp only [factorExtractionTarget, mem_filter, mem_product, mem_Ioc]
  tauto

/-- A finite bijection for a divisor which may depend on the reconstructed
factors and every surviving auxiliary variable. All original masks remain. -/
theorem sum_factorExtraction {ι A : Type*} [AddCommMonoid A]
    (R S : ℕ) (U : Finset ι) (D : ℕ → ℕ → ι → ℕ)
    (P : ℕ → ℕ → ι → Prop)
    (hD : ∀ z ∈ factorExtractionSource R S U P,
      0 < D z.1.1 z.1.2 z.2 ∧ D z.1.1 z.1.2 z.2 ∣ z.1.1 * z.1.2)
    (F : (ℕ × ℕ) × ι → A) :
    (∑ z ∈ factorExtractionSource R S U P, F z) =
      ∑ z ∈ factorExtractionTarget R S U D P, F (factorExtractionReconstruct z) := by
  have hv (z : FactorExtractionTuple × ι)
      (hz : z ∈ factorExtractionTarget R S U D P) :
      FactorExtractionValid
        (D (factorExtractionReconstruct z).1.1 (factorExtractionReconstruct z).1.2 z.2)
        (factorExtractionReconstruct z).1.1 (factorExtractionReconstruct z).1.2 z.1 := by
    obtain ⟨hΔ, hΔ', hr, hs, _, _, _, _, he, hc⟩ := target_mem.mp hz
    exact ⟨hΔ.1, hΔ'.1, hr.1, hs.1, he, rfl, rfl, hc⟩
  symm
  refine sum_bij (fun z _ => factorExtractionReconstruct z) ?_ ?_ ?_ ?_
  · intro z hz
    obtain ⟨hΔ, hΔ', hr, hs, hu, hR, hS, hP, _, _⟩ := target_mem.mp hz
    exact source_mem.mpr
      ⟨⟨Nat.mul_pos hΔ.1 hr.1, hR⟩, ⟨Nat.mul_pos hΔ'.1 hs.1, hS⟩, hu, hP⟩
  · intro z hz y hy he
    have hzv := factorExtraction_unique (hv z hz)
    have hyv := factorExtraction_unique (hv y hy)
    have hu : z.2 = y.2 := congrArg (fun v : (ℕ × ℕ) × ι => v.2) he
    apply Prod.ext _ hu
    rw [hzv, hyv, he, hu]
  · intro z hz
    obtain ⟨hr, hs, hu, hP⟩ := source_mem.mp hz
    obtain ⟨hpos, hdvd⟩ := hD z hz
    let e := factorExtraction (D z.1.1 z.1.2 z.2) z.1.1 z.1.2
    have hev : FactorExtractionValid (D z.1.1 z.1.2 z.2) z.1.1 z.1.2 e :=
      factorExtraction_valid hpos hr.1 hs.1 hdvd
    obtain ⟨hΔ, hΔ', hr', hs', heD, her, hes, hec⟩ := hev
    have hΔR : e.1.1 ≤ R := (Nat.le_of_dvd hr.1 ⟨e.2.1, her⟩).trans hr.2
    have hΔ'S : e.1.2 ≤ S := (Nat.le_of_dvd hs.1 ⟨e.2.2, hes⟩).trans hs.2
    have hr'R : e.2.1 ≤ R := (Nat.le_of_dvd hr.1
      ⟨e.1.1, her.trans (mul_comm _ _)⟩).trans hr.2
    have hs'S : e.2.2 ≤ S := (Nat.le_of_dvd hs.1
      ⟨e.1.2, hes.trans (mul_comm _ _)⟩).trans hs.2
    refine ⟨(e, z.2), target_mem.mpr ?_, ?_⟩
    · exact ⟨⟨hΔ, hΔR⟩, ⟨hΔ', hΔ'S⟩, ⟨hr', hr'R⟩, ⟨hs', hs'S⟩, hu,
        her ▸ hr.2, hes ▸ hs.2, her ▸ hes ▸ hP, her ▸ hes ▸ heD, hec⟩
    · exact Prod.ext (Prod.ext her.symm hes.symm) rfl
  · intro _ _
    rfl

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

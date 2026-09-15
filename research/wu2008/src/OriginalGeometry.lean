import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9LongCoefficient
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9IntervalEndpoints
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9ScaleLevel
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9ModulusSupport

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace OriginalU8

/-- Ordered long labels, retaining the diagonal and no coprimality on r. -/
def labels (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (fouvryG9LongLabels N ρ k).filter fun z => z.1 ≤ z.2

def products (L : Finset (ℕ × ℕ)) : Finset ℕ := L.image fun z => z.1*z.2

def alpha (L : Finset (ℕ × ℕ)) (m : ℕ) : ℝ :=
  ((L.filter fun z => z.1*z.2=m).card : ℝ)

theorem alpha_nonneg (L : Finset (ℕ × ℕ)) (m : ℕ) : 0 ≤ alpha L m := by
  unfold alpha; positivity

/-- Generic ordered-label interface; no primality, uniqueness, or omitted diagonal. -/
theorem alpha_order_two (L : Finset (ℕ × ℕ))
    (hL : ∀ z ∈ L, 0 < z.1 ∧ 0 < z.2) (m : ℕ) :
    |alpha L m| ≤ (fouvryTau 2 m : ℝ) := by
  rw [abs_of_nonneg (alpha_nonneg L m), fouvryTau_two]
  apply Nat.cast_le.mpr
  apply card_le_card_of_injOn (fun z => z.1)
  · intro z hz
    obtain ⟨hz,he⟩ := mem_filter.mp hz
    exact Nat.mem_divisors.mpr ⟨he ▸ dvd_mul_right z.1 z.2,
      he ▸ Nat.ne_of_gt (Nat.mul_pos (hL z hz).1 (hL z hz).2)⟩
  · intro x hx y hy he
    obtain ⟨hx,hxm⟩ := mem_filter.mp hx
    obtain ⟨_,hym⟩ := mem_filter.mp hy
    apply Prod.ext he
    apply Nat.eq_of_mul_eq_mul_left (hL x hx).1
    change x.1 = y.1 at he
    calc
      x.1*x.2 = m := hxm
      _ = y.1*y.2 := hym.symm
      _ = x.1*y.2 := by rw [he]

theorem alpha_sum (L : Finset (ℕ × ℕ)) (F : ℕ → ℝ) :
    (∑ z ∈ L, F (z.1*z.2)) = ∑ m ∈ products L, alpha L m * F m := by
  have h := sum_fiberwise_of_maps_to (s := L) (t := products L)
    (g := fun z : ℕ × ℕ => z.1*z.2)
    (fun z hz => mem_image_of_mem _ hz) (fun z => F (z.1*z.2))
  rw [← h]
  apply sum_congr rfl
  intro m _
  calc
    _ = ∑ _z ∈ L.filter (fun z => z.1*z.2=m), F m := by
      apply sum_congr rfl
      intro z hz
      rw [(mem_filter.mp hz).2]
    _ = _ := by simp only [sum_const, nsmul_eq_mul, alpha]

theorem labels_positive (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) :
    ∀ z ∈ labels N ρ k, 0 < z.1 ∧ 0 < z.2 := by
  intro z hz
  have h := (mem_filter.mp (mem_filter.mp hz).1).2
  exact ⟨h.1.pos,h.2.1.pos⟩

theorem products_bounds {N : ℕ} {ρ : ℝ} (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    {k : ℕ × ℕ × ℕ} {m : ℕ} (hm : m ∈ products (labels N ρ k)) :
    ρ^(k.2.1+k.2.2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2*ρ^(k.2.1+k.2.2) := by
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hm
  have hm := mem_image_of_mem (fun z : ℕ × ℕ => z.1*z.2) (mem_filter.mp hz).1
  exact ⟨(fouvryG9LongProducts_bounds hρ hm).1,fouvryG9LongProducts_le_two hρ hρu hm⟩

theorem labels_mem (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (p r : ℕ) :
    (p,r) ∈ labels N ρ k ↔
      p ≤ N ∧ r ≤ N ∧ p.Prime ∧ r.Prime ∧ p.Coprime N ∧
        (N : ℝ)^(1/3 : ℝ) ≤ p ∧
        ρ^k.2.1 ≤ p ∧ (p : ℝ) < ρ^(k.2.1+1) ∧
        ρ^k.2.2 ≤ r ∧ (r : ℝ) < ρ^(k.2.2+1) ∧ p ≤ r := by
  simp [labels,fouvryG9LongLabels,and_assoc,and_left_comm,and_comm]

theorem alpha_firstIndex (N : ℕ) (ρ : ℝ) (i i' j l m : ℕ) :
    alpha (labels N ρ (i,j,l)) m = alpha (labels N ρ (i',j,l)) m := rfl

def shortLower (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) : ℝ :=
  max (ρ^k.1) ((N : ℝ)^(100/1327 : ℝ))
def shortUpper (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) : ℝ :=
  min (ρ^(k.1+1)) ((N : ℝ)^(1/10 : ℝ))

/-- Literal original-alpha occupied separated box; not a C2 hypothesis. -/
def Occupied (N : ℕ) (e ρ : ℝ) (k : ℕ × ℕ × ℕ) : Prop :=
  ∃ n : ℕ, ∃ z ∈ labels N ρ k, n.Prime ∧ n.Coprime N ∧
    shortLower N ρ k ≤ n ∧ (n : ℝ) < shortUpper N ρ k ∧
    e*N < (n : ℝ)*(z.1*z.2 : ℕ) ∧ (n : ℝ)*(z.1*z.2 : ℕ) < N

theorem endpoints {N : ℕ} {e ρ : ℝ} {k : ℕ × ℕ × ℕ}
    (h : Occupied N e ρ k) : shortLower N ρ k ≤ shortUpper N ρ k := by
  obtain ⟨n,z,hz,hp,hc,hl,hu,hw⟩ := h
  exact hl.trans hu.le

def interval {N : ℕ} {e ρ : ℝ} (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (k : ℕ × ℕ × ℕ) (hbig : 3 ≤ ρ^k.1) (h : Occupied N e ρ k) : PrimeC2Interval :=
  g9PrimeHalfOpenInterval (ρ^k.1) (shortLower N ρ k) (shortUpper N ρ k)
    hbig (le_max_left _ _) (endpoints h) (by
      apply (min_le_left _ _).trans
      rw [pow_succ]
      nlinarith [pow_pos (by linarith : 0 < ρ) k.1])

theorem interval_mem {N : ℕ} {e ρ : ℝ} (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (k : ℕ × ℕ × ℕ) (hbig : 3 ≤ ρ^k.1) (h : Occupied N e ρ k) (n : ℕ) :
    let z := interval hρ hρu k hbig h
    n ∈ primeSWInterval z.lower z.upper ↔
      shortLower N ρ k ≤ n ∧ (n : ℝ) < shortUpper N ρ k :=
  mem_g9PrimeHalfOpenInterval _ _ _ _ _ _ _ n

/-- Uniform buffered scale geometry from an actual prime-triple witness. -/
theorem geometry {N : ℕ} {e ρ : ℝ} (he : 0 < e) (hρ : 1 < ρ)
    (hρu : ρ ≤ 5/4) {k : ℕ × ℕ × ℕ} (h : Occupied N e ρ k) :
    let T := (2/3 : ℝ)*ρ^k.1
    let M := ρ^(k.2.1+k.2.2)
    1 ≤ M ∧ (N : ℝ)/(2/e) ≤ 4*M*T ∧ 4*M*T ≤ 4*N ∧
      (N : ℝ)^(100/1327 : ℝ)/2 ≤ T ∧ T ≤ (N : ℝ)^(1/10 : ℝ) := by
  dsimp only
  obtain ⟨n,z,hz,hp,_,hl,hu,hlo,hhi⟩ := h
  obtain ⟨hnl,hna⟩ := max_le_iff.mp hl
  obtain ⟨hnu,hnb⟩ := lt_min_iff.mp hu
  have hprod := mem_image_of_mem (fun z : ℕ × ℕ => z.1*z.2) hz
  obtain ⟨hml,hmu⟩ := products_bounds hρ hρu hprod
  have ht0 : 0 < ρ^k.1 := pow_pos (by linarith) _
  have hm0 : 0 < ρ^(k.2.1+k.2.2) := pow_pos (by linarith) _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hp.pos
  have hb := mul_le_mul hnl hml hm0.le (Nat.cast_nonneg n)
  have hnu' : (n : ℝ) < (5/4 : ℝ)*ρ^k.1 := by
    rw [pow_succ] at hnu
    exact hnu.trans_le (by nlinarith)
  have hb' := mul_le_mul hnu'.le hmu (by positivity : (0 : ℝ) ≤ (z.1*z.2 : ℕ))
    (by positivity : (0 : ℝ) ≤ (5/4 : ℝ)*ρ^k.1)
  have hquot : (N : ℝ)/(2/e) = e*N/2 := by field_simp
  refine ⟨one_le_pow₀ hρ.le,?_,?_,?_,?_⟩
  · rw [hquot]; nlinarith [mul_pos ht0 hm0]
  · nlinarith
  · nlinarith
  · nlinarith

end OriginalU8

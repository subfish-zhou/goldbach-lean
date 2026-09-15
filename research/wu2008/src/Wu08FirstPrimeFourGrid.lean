import Wu08FirstPrimeFourC2
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9GridIndex
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9IntervalEndpoints
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9ScaleLevel

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace Wu08FirstPrimeFour
abbrev Key := ℕ × ℕ

def key (ρ : ℝ) (x : Physical) : Key :=
  (fouvryG9GridIndex ρ (shortPart x), fouvryG9GridIndex ρ (longProduct (longPart x)))
def positivePart (N : ℕ) (e : Bool) (ξ : ℝ) : Finset Physical :=
  (small N e).filter fun x => ξ*N < (longProduct (longPart x)*shortPart x : ℕ)
def smallPrefix (N : ℕ) (e : Bool) (ξ : ℝ) : Finset Physical :=
  (small N e).filter fun x => ¬ξ*N < (longProduct (longPart x)*shortPart x : ℕ)
def occupied (N : ℕ) (e : Bool) (ξ ρ : ℝ) : Finset Key :=
  (positivePart N e ξ).image (key ρ)

/-- A first-index-dependent but first-PRIME-independent long coefficient.
It retains the a<b and product faces at the outer box endpoints. -/
def longCell (N : ℕ) (e : Bool) (ξ ρ : ℝ) (k : Key) : Finset Long :=
  (longLabels N e).filter fun t =>
    ρ^k.2 ≤ (longProduct t : ℝ) ∧ (longProduct t : ℝ) < ρ^(k.2+1) ∧
    LastPrimeFour.z N ≤ t.1 ∧ ρ^k.1 < (t.1 : ℝ) ∧
    ρ^k.1*(longProduct t : ℝ) < N ∧ ξ*N < ρ^(k.1+1)*(longProduct t : ℝ)
def shortCell (ρ : ℝ) (k : Key) : Finset ℕ :=
  primeSWInterval ((⌈ρ^k.1⌉ : ℝ)-1) ((⌈ρ^(k.1+1)⌉ : ℝ)-1)
def level (N : ℕ) (ρ δ : ℝ) (k : Key) : ℝ :=
  (N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))

theorem small_card_smallPrefix (N : ℕ) (e : Bool) (ξ : ℝ) :
    (positivePart N e ξ).card+(smallPrefix N e ξ).card=(small N e).card :=
  card_filter_add_card_filter_not _

theorem positive_data {N : ℕ} {e : Bool} {ξ : ℝ} {x : Physical}
    (hx : x ∈ positivePart N e ξ) :
    x ∈ LastPrimeFour.original N e ∧ (shortPart x).Prime ∧
    LastPrimeFour.z N ≤ shortPart x ∧ (shortPart x : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) ∧
    0 < longProduct (longPart x) ∧
    ξ*N < (longProduct (longPart x)*shortPart x : ℕ) ∧
    longProduct (longPart x)*shortPart x < N := by
  obtain ⟨hx,hlo⟩ := mem_filter.mp hx
  obtain ⟨hx,hhi⟩ := mem_filter.mp hx
  rcases x with ⟨⟨a,b,c,d⟩,n⟩
  obtain ⟨ha,_,hza,hb,_,hc,_,_,_,_,hn,_,hd,_,_,_,_,hs,_⟩ := LastPrimeFour.original_data hx
  have hb0 := hb.pos
  have hc0 := hc.pos
  have hd0 := hd.pos
  have hn0 : 0 < n := by omega
  refine ⟨hx,ha,hza,hhi,?_,hlo,?_⟩
  · dsimp only [longPart,longProduct]
    positivity
  · change b*c*d*n*a < N
    change a*b*c*n*d < N at hs
    nlinarith only [hs]

theorem grid_bounds {N : ℕ} {e : Bool} {ξ ρ : ℝ} (hρ : 1 < ρ)
    {x : Physical} (hx : x ∈ positivePart N e ξ) :
    ρ^(key ρ x).1 ≤ (shortPart x : ℝ) ∧ (shortPart x : ℝ) < ρ^((key ρ x).1+1) ∧
    ρ^(key ρ x).2 ≤ (longProduct (longPart x) : ℝ) ∧
      (longProduct (longPart x) : ℝ) < ρ^((key ρ x).2+1) := by
  obtain ⟨_,ha,_,_,hm,_⟩ := positive_data hx
  exact ⟨(fouvryG9GridIndex_bounds hρ (by exact_mod_cast ha.one_le)).1,
    (fouvryG9GridIndex_bounds hρ (by exact_mod_cast ha.one_le)).2,
    fouvryG9GridIndex_bounds hρ (by exact_mod_cast hm)⟩

/-- Original physical witnesses supply the local/global scale hypotheses.
The small-prime endpoint a=N^(1/10) is included without a zero-measure deletion. -/
theorem occupied_geometry {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hξ : 0 < ξ) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    {k : Key} (hk : k ∈ occupied N e ξ ρ) :
    let T := (2/3 : ℝ)*ρ^k.1
    let M := ρ^k.2
    1 ≤ M ∧ (N : ℝ)/(2/ξ) ≤ 4*M*T ∧ 4*M*T ≤ 4*N ∧
      (N : ℝ)^truncatedSixthLowerAlpha/2 ≤ T ∧ T ≤ (N : ℝ)^(1/10 : ℝ) := by
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hk
  obtain ⟨_,_,hza,haSmall,hm,hlo,hhi⟩ := positive_data hx
  obtain ⟨hal,hau,hml,hmu⟩ := grid_bounds hρ hx
  have hP : 0 < ρ^(key ρ x).1 := pow_pos (by linarith) _
  have hM : 0 < ρ^(key ρ x).2 := pow_pos (by linarith) _
  have ha0 : 0 ≤ (shortPart x : ℝ) := Nat.cast_nonneg _
  have hm0 : 0 ≤ (longProduct (longPart x) : ℝ) := Nat.cast_nonneg _
  have haU : (shortPart x : ℝ) ≤ (5/4 : ℝ)*ρ^(key ρ x).1 := by
    rw [pow_succ] at hau
    nlinarith
  have hmU : (longProduct (longPart x) : ℝ) ≤ (5/4 : ℝ)*ρ^(key ρ x).2 := by
    rw [pow_succ] at hmu
    nlinarith
  have hp := mul_le_mul hal hml hM.le ha0
  have hp' := mul_le_mul haU hmU hm0 (by positivity : (0 : ℝ) ≤ (5/4)*ρ^(key ρ x).1)
  have hhi' : (shortPart x : ℝ)*(longProduct (longPart x) : ℝ) ≤ N := by
    exact_mod_cast (show shortPart x*longProduct (longPart x) ≤ N by nlinarith only [hhi])
  have hlo' : ξ*N < (shortPart x : ℝ)*(longProduct (longPart x) : ℝ) := by
    simpa only [Nat.cast_mul,mul_comm] using hlo
  have he : (N : ℝ)/(2/ξ)=ξ*N/2 := by field_simp
  dsimp only
  refine ⟨one_le_pow₀ hρ.le,?_,?_,?_,?_⟩
  · rw [he]
    nlinarith only [hp',hlo',mul_pos hP hM]
  · nlinarith only [hp,hhi']
  · change (N : ℝ)^truncatedSixthLowerAlpha ≤ shortPart x at hza
    linarith
  · nlinarith only [hal,haSmall,hP]

def cellInterval {ρ : ℝ} (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (k : Key) (hbig : 3 ≤ ρ^k.1) : PrimeC2Interval :=
  g9PrimeHalfOpenInterval (ρ^k.1) (ρ^k.1) (ρ^(k.1+1)) hbig le_rfl
    (by rw [pow_succ]; nlinarith [pow_pos (by linarith : 0 < ρ) k.1])
    (by rw [pow_succ]; nlinarith [pow_pos (by linarith : 0 < ρ) k.1])

theorem shortCell_mem {ρ : ℝ} (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (k : Key) (hbig : 3 ≤ ρ^k.1) (a : ℕ) :
    a ∈ shortCell ρ k ↔ ρ^k.1 ≤ (a : ℝ) ∧ (a : ℝ) < ρ^(k.1+1) :=
  mem_g9PrimeHalfOpenInterval _ _ _ hbig le_rfl
    (by rw [pow_succ]; nlinarith [pow_pos (by linarith : 0 < ρ) k.1])
    (by rw [pow_succ]; nlinarith [pow_pos (by linarith : 0 < ρ) k.1]) a

theorem longCell_bounds {N : ℕ} {e : Bool} {ξ ρ : ℝ} (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    {k : Key} {t : Long} (ht : t ∈ longCell N e ξ ρ k) :
    ρ^k.2 ≤ (longProduct t : ℝ) ∧ (longProduct t : ℝ) ≤ 2*ρ^k.2 := by
  obtain ⟨_,hl,hu,_⟩ := mem_filter.mp ht
  refine ⟨hl,?_⟩
  rw [pow_succ] at hu
  nlinarith [pow_pos (by linarith : 0 < ρ) k.2]

/-- All original atoms are present in their actual first-prime rectangle. -/
theorem positive_mem_box {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) {x : Physical}
    (hx : x ∈ positivePart N e ξ) (hbig : 3 ≤ ρ^(key ρ x).1) :
    x ∈ box N e (longCell N e ξ ρ (key ρ x)) (shortCell ρ (key ρ x)) := by
  obtain ⟨horig,_,_,_,hm,hlo,hhi⟩ := positive_data hx
  obtain ⟨hal,hau,hml,hmu⟩ := grid_bounds hρ hx
  apply mem_filter.mpr
  refine ⟨horig,?_,(shortCell_mem hρ hρu _ hbig _).mpr ⟨hal,hau⟩⟩
  apply mem_filter.mpr
  refine ⟨original_long_mem horig,hml,hmu,?_,?_,?_,?_⟩
  · rcases x with ⟨⟨a,b,c,d⟩,n⟩
    obtain ⟨_,_,hza,_,_,_,_,hab,_⟩ := LastPrimeFour.original_data horig
    exact hza.trans (by exact_mod_cast hab.le)
  · rcases x with ⟨⟨a,b,c,d⟩,n⟩
    have hab := (LastPrimeFour.original_data horig).2.2.2.2.2.2.2.1
    exact hal.trans_lt (by exact_mod_cast hab)
  · have hh : (shortPart x : ℝ)*(longProduct (longPart x) : ℝ) < N := by
      simpa only [Nat.cast_mul,mul_comm] using (show (longProduct (longPart x)*shortPart x : ℝ) < N by exact_mod_cast hhi)
    exact (mul_le_mul_of_nonneg_right hal (Nat.cast_nonneg _)).trans_lt hh
  · have hh : ξ*N < (shortPart x : ℝ)*(longProduct (longPart x) : ℝ) := by
      simpa only [Nat.cast_mul,mul_comm] using hlo
    exact hh.trans (mul_lt_mul_of_pos_right hau (by exact_mod_cast hm))

#print axioms occupied_geometry
#print axioms positive_mem_box
end Wu08FirstPrimeFour

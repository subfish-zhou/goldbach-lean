#!/usr/bin/env python3
"""Reproduce the 1024 rational sixth-source panel certificates and their assembly.

All arithmetic uses Fraction. The original payment table is reproduced byte for byte, retaining its 10^-12
rounding. A shared analytic soundness lemma eliminates the intermediate rounded
density/profile proofs; Lean directly checks the exact rational product on each
32-cell block and the original integer total.
"""
import argparse
from pathlib import Path
from fractions import Fraction as F
alpha,beta=F(100,1327),F(25,206)
end=(F(1,2)-alpha-beta)/alpha
q=[F(11133,500000),F(21591,10**6),F(20159,10**6),F(563,31250),F(3939,250000),F(6447,500000),F(9961,10**6),F(3841,500000),F(7139,10**6)]
q += [F(v,10**10) for v in [61150104,51820373,43726568,36703695,30615051,25346254,20800762,16896457,13563001,10739764,8374182,6420445,4833811,3565810,2565457,1783875,1174988,695497,310497]]
def loglower(t):
 z=(t-1)/(t+1)
 return 2*sum(z**k/k for k in [1,3,5,7])
def node(i):return 2+F(i,10)
def L(z):return max(alpha,z-F(1,4))
def U(z):return min(beta,z-beta)
def density(a,b):
 za,zb=F(1,2)-alpha*a,F(1,2)-alpha*b
 r=U(zb)*(zb-L(zb))/(L(za)*(za-U(za)))
 return loglower(max(F(1),r))/(b*(1-2*alpha*a))
scale=10**12
fmt=lambda x:f'({x.numerator}/{x.denominator}:ℝ)'
def floor(v):return v.numerator*scale//v.denominator
def data(i,n=1024):
 a=2+(end-2)*F(i,n);b=2+(end-2)*F(i+1,n)
 k=next(k for k in range(2,12) if b-1<=node(k))
 p=floor(q[k-2]*loglower(node(k)/(b-1))+F(tails[k],scale))
 d=floor(density(a,b));c=floor(8*(b-a)*F(d,scale)*F(p,scale))
 return a,b,k,p,d,c

tails={k:sum(floor(q[i-2]*loglower(node(i)/node(i-1)))
             for i in range(k+1,30)) for k in range(2,12)}
pay=[data(i)[-1] for i in range(1024)]
assert sum(pay) == 56646110394
outputs={}
s='import WR2XiSixthUniformGrid\nnoncomputable section\nnamespace WuPaper.R2Xi.SixthContinuous\nopen Finset\n'
for b in range(32):
 s+=f'def paymentBlock{b:02d} : ℕ → ℕ\n'
 for j in range(32):s+=f'  | {j} => {pay[32*b+j]}\n'
 s+='  | _ => 0\n\n'
s+='def paymentNumerator (i : ℕ) : ℕ :=\n  match i/32 with\n'
for b in range(32):s+=f'  | {b} => paymentBlock{b:02d} (i%32)\n'
s+='  | _ => 0\n\ndef payment (i : ℕ) : ℝ := (paymentNumerator i:ℝ)/1000000000000\n\n'
s+='''set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem payment_sum : (∑ i ∈ range 1024, paymentNumerator i) = 56646110394 := by
  decide +kernel

theorem payment_total : (283:ℝ)/5000 ≤ ∑ i ∈ range 1024, payment i := by
  simp only [payment,← Finset.sum_div,← Nat.cast_sum,payment_sum]
  norm_num

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.payment_total
'''
outputs['WR2XiSixthPayments.lean'] = s
for b in range(32):
 s=f'''import WR2XiSixthDirectCheck
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem direct_block_{b:02d} : ∀ j : Fin 32,
    DirectCheck.condition (32*{b}+j.val) := by
  decide +kernel

theorem grid_block_{b:02d} (j : Fin 32) : payment (32*{b}+j.val) ≤ panelBound (32*{b}+j.val) :=
  DirectCheck.condition_sound (direct_block_{b:02d} j)

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_{b:02d}
'''
 outputs[f'WR2XiSixthGridBlock{b:02d}.lean'] = s
s=''.join(f'import WR2XiSixthGridBlock{b:02d}\n' for b in range(32))
s+='''import WR2XiSourceFinalBudget
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous

theorem all_panels_paid (i : ℕ) (hi : i < 1024) : payment i ≤ panelBound i := by
  have hj : i%32 < 32 := Nat.mod_lt _ (by norm_num)
  have hb : i/32 < 32 := by omega
  have hh (b : Fin 32) : payment (32*b.val+i%32) ≤ panelBound (32*b.val+i%32) := by
    fin_cases b
'''
for b in range(32):s+=f'    · exact grid_block_{b:02d} ⟨i%32,hj⟩\n'
s+='''  have he : 32*(i/32)+i%32=i := by omega
  simpa only [he] using hh ⟨i/32,hb⟩

theorem sixth_gain_lower : (283:ℝ)/5000 ≤ SourceSixth.amount :=
  uniform_certificate all_panels_paid payment_total

theorem one894_of_classical
    (hc : (17401:ℝ)/20000 ≤ SourceContinuousCount.classicalPart) :
    ∃ T ≥ 512, ∀ N ≥ T, Even N → ∃ p r q : ℕ,
      p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧ N=p+r*q ∧ r^500≤q^447 :=
  SourceContinuousCount.one894_of_integral_bounds hc sixth_gain_lower

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.sixth_gain_lower
#print axioms WuPaper.R2Xi.SixthContinuous.one894_of_classical
'''
outputs['WR2XiSixthCertificate.lean'] = s

parser=argparse.ArgumentParser(description=__doc__)
group=parser.add_mutually_exclusive_group(required=True)
group.add_argument('--check',type=Path,metavar='SOURCE_DIR')
group.add_argument('--write',type=Path,metavar='SOURCE_DIR')
args=parser.parse_args()
destination=args.check or args.write
if args.write:
    destination.mkdir(parents=True,exist_ok=True)
for name,content in outputs.items():
    path=destination/name
    if args.check:
        if not path.exists() or path.read_text()!=content:
            raise SystemExit(f'Generated source differs: {path}')
    else:
        path.write_text(content)
print(f'{"Verified" if args.check else "Wrote"} {len(outputs)} generated sources')

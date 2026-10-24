"""Exact rational Xi2 rectangle diagnostics, not formal integral certificates.

Each original indicator interval is clipped to one node cell and subdivided.
Logarithm arguments use their lower endpoint bound; the positive denominator
uses its interval maximum. The final decreasing log uses the right endpoint.
The common sigma contribution uses W06SigmaV2's rational mass lower bounds.
Gamma5 is paid with the proved rowDebit/2 budget. This Python computation is
not a Lean certificate; analytic proofs and kernel checks are tracked separately.
"""
from fractions import Fraction as F
from first_feedback_candidate import low as base_low, mass


def low(x):
    """Four-factor refinement represented by WR2XiLogRefinement.cellLogLower."""
    return base_low((1+x)/2)+base_low(2*x/(1+x))

rows=[list(map(F,p)) for p in [('2.2','4.54','3.53','2.90','2.44'),('2.3','4.50','3.54','2.88','2.43'),('2.4','4.46','3.57','2.87','2.40'),('2.5','4.12','3.56','2.91','2.50')]]
target=[[154,26,26,26,27,27,27,28,28],[152,25,26,26,26,27,27,27,27],[151,25,25,25,26,26,26,27,27],[154,23,24,25,25,26,26,26,27]]
debit=list(map(F,['1/1500','1/1000','9/8000','1/2000']))
def pieces(p):
 """The nine original supports and their lower logarithm arguments."""
 s,S,k1,k2,k3=p
 a1,a2,a3,a4,a5,a6,a7,a8,a9=[k1-2,S-2,S-S/s-1,S-S/k2-1,S-S/k3-1,S-2*S/k2,S-S/k1-S/k3,S-S/k1-S/k2,k1-k1/k2-1]
 return [(a2,F(3),lambda a,b:sum(low((a+1)/(q-1)) for q in p),False),
 (a9,a1,lambda a,b:low((a+1)/((k2-1)*(k1-1-a))),False),
 (a5,a2,lambda a,b:low((a+1)/((k3-1)*(S-1-a))),False),
 (a3,a2,lambda a,b:low((a+1)/((s-1)*(S-1-a))),False),
 (a1,a2,lambda a,b:low((a+1)/(k1-1))+low((a+1)/(k2-1)),False),
 (a7,a5,lambda a,b:low(S*S/((k1*S-S-k1*a)*(k3*S-S-k3*a))),True),
 (a5,a8,lambda a,b:low(S*(S-1-a)/(k1*S-S-k1*a)),True),
 (a6,a8,lambda a,b:low(S/(k2*S-S-k2*a)),True),
 (a8,a2,lambda a,b:low(S-1-b),True)]
def panel_payments(p,k,n):
 """Yield (piece index, exact rational payment) for every nonempty panel."""
 S=p[1]
 lo=F(1) if k==0 else F(21+k,10);hi=F(22+k,10)
 for piece,(l,r,f,quad) in enumerate(pieces(p)):
  l,r=max(l,lo),min(r,hi)
  if l>=r:continue
  for j in range(n):
   a,b=l+(r-l)*F(j,n),l+(r-l)*F(j+1,n)
   den=max(a*(1-a/S),b*(1-b/S),S/4 if a<=S/2<=b else 0) if quad else b
   yield piece,(b-a)*f(a,b)/(5*den)

def sigma_payment(p,k):
 return mass[k]/(1-F(858467,5000000))*sum(low(4/(q-1)) for q in p)/5

def row(p,k,n):
 return sigma_payment(p,k)+sum(value for _,value in panel_payments(p,k,n))
if __name__ == '__main__':
 for n in [128,512]:
  for i,p in enumerate(rows):
   margins=[row(p,k,n)-F(target[i][k],1000)-(debit[i] if k==0 else 0) for k in range(9)]
   if n == 512:
    assert all(v > 0 for v in margins)
   print(n,i,[round(float(x),8) for x in margins],flush=True)

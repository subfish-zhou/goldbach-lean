import sympy as s
x=s.symbols('x')
lo=(x-1)*(s.Rational(1,30)+x*(-s.Rational(37,210)+x*(s.Rational(169,42)+x*(s.Rational(327,14)+x*(s.Rational(2213,42)+x*(s.Rational(11093,210)+x*(s.Rational(1649,70)+x*s.Rational(155,42))))))))/(x**2*(x+1)**4*(x*x+8*x+1))
up=(21*x*(x-1)*(x*x+10*x+1)*(x+1)**3+168*x*x*(x-1)*(x+1)**3+56*x*x*(x-1)**3*(x+1)-3*(x-1)**7)/(210*x*x*(x+1)**4)

z=s.symbols('z')
p=2*z*(1+z*z/3+z**4/5+z**6/7)
u=p+2*z**9/(9*(1-z*z))
sl=lo.subs(x,(x+1)/2)+lo.subs(x,2*x/(x+1))
su=up.subs(x,(x+1)/2)+up.subs(x,2*x/(x+1))
y=(1+z)/(1-z)
checks={
 'lower_difference':s.factor(p-lo.subs(x,y)),
 'upper_difference':s.factor(up.subs(x,y)-u),
 'split_upper_difference':s.factor(su.subs(x,y)-u),
 'unsplit_lower_counterexample':s.factor((p.subs(z,(x-1)/(x+1))-sl).subs(x,s.Rational(5,4))),
}
assert checks['unsplit_lower_counterexample']<0
for k,v in checks.items():print(k, '=',v)
print('SymPy operation counts (not Lean DAG-node counts):', {n:int(s.count_ops(e)) for n,e in [('old lower',lo),('old upper',up),('P7',p),('U7',u)]})

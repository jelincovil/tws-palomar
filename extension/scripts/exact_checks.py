#!/usr/bin/env python3
from fractions import Fraction as F
from collections import defaultdict
p={-3:-1,-1:9,0:16,1:9,3:-1}
k=p.copy();count=0
for j in range(5):
 scale=32**(j+1);r=3*(2**(j+1)-1)
 assert sum(k.values())==scale
 taps={a:F(v,scale) for a,v in k.items()}
 for n in (1,2,3,5):
  x=[F((i*7)%11-5,3) for i in range(n)];M=n+2*r
  def at(t):return x[max(0,min(t,n-1))]
  direct=[sum(v*at(i-a) for a,v in taps.items()) for i in range(n)]
  padded=[at(t-r) for t in range(M)]
  folded=defaultdict(F)
  for a,v in taps.items():folded[a%M]+=v
  periodic=[sum(v*padded[(r+i-a)%M] for a,v in folded.items()) for i in range(n)]
  assert direct==periodic
  assert all(sum(taps.values())*F(7,3)==F(7,3) for i in range(n))
  count+=1
 nxt=defaultdict(int);s=2**(j+1)
 for a,v in k.items():
  for shift,w in ((0,16),(s,9),(-s,9),(3*s,-1),(-3*s,-1)):nxt[a+shift]+=v*w
 k=dict(nxt)
# Strict upper and inclusive lower endpoint conventions.
for tau in (F(-1),F(0),F(1)):
 for m in (F(0),F(1,3),F(2)):
  for y in (tau-m,tau,tau+m,tau+m+1,tau-m-1):
   for x in (y-m,y,y+m):
    assert not(y>tau+m) or x>tau
    assert not(y<=tau-m) or x<=tau
    assert ((y>tau)==(x>tau)) or tau-m<y<=tau+m
print('PASS:',count,'rational direct/padded cases; signed masses j=0..4; threshold boundaries. Not a universal proof.')

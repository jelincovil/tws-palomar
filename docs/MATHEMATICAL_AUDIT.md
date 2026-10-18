# Mathematical audit of the proposed statements

## 1. Norms and quantifiers

For a finite abelian group G, the source and target of convolutionOperator
are the full real function space G -> R. Mathlib's finite Pi norm is
max_x |f(x)|. The norm on ContinuousLinearMap is its induced operator norm.
The definition does not assert or assume any value for that norm.

The group is nonempty because it contains zero. Empty stencils are allowed
in the general folding theorem. Their operator is zero; the sign witness
still has unit input norm and zero output norm.

For the db2 specialization, N and d are natural numbers, NeZero N supplies
finiteness of ZMod N, and the theorem additionally requires 7 <= N. The
NeZero hypothesis is mathematically redundant under that inequality but
convenient for Lean's typeclass elaboration. No parity or power-of-two
condition is needed for the explicitly defined circular convolution.
This does not assert that an external wavelet software API accepts every N.

## 2. General operator norm

Triangle inequality gives, for every x,

    |sum_y k(y) f(x-y)| <= (sum_y |k(y)|) ||f||_infinity.

Taking the maximum gives the upper bound. Define f(z)=1 if k(-z)>=0 and
f(z)=-1 otherwise. Then ||f||=1 and

    (C_k f)(0) = sum_y k(y) f(-y) = sum_y |k(y)|.

This is a matching lower bound. It is a real signal, not an abstract
existence assumption. The same construction covers k=0. The proof uses
the standard operator norm bounds in Mathlib to connect the calculation
to the actual continuous linear map.

## 3. Periodization

For a finite set I of stencil indices, foldKernel a q x is the sum of all
a_i whose offset q_i is x. All collisions are summed before absolute values
are taken. Therefore

    sum_x |sum_{i:q_i=x} a_i| <= sum_i |a_i|.

If q is injective, every fiber has at most one element and equality follows.
Injectivity is only a sufficient condition. Collisions among coefficients
of the same sign can preserve the mass. Opposite-sign collisions can reduce
it; the independent exact matrix check gives norm 1 for db2 at period N=4,
although its unperiodized l1 mass is 9/8.

## 4. Tensorization

For K(x_1,...,x_d)=product_j k(x_j), distributivity over a finite product gives

    sum_x |K(x)| = (sum_y |k(y)|)^d.

The domain group for convolution is now (Fin d -> G). Apply the general norm
identity on that group. For d=0, both sides equal one: the empty tensor
product is the unit kernel on the singleton group.

## 5. db2 identification and no collision

The low-pass filter is c times

    [1+sqrt(3), 3+sqrt(3), 3-sqrt(3), 1-sqrt(3)], c=1/(4 sqrt(2)).

Its autocorrelations at nonnegative lags 0,1,2,3 are 1,9/16,0,-1/16.
One half of the symmetric autocorrelation is

    [-1,0,9,16,9,0,-1]/32.

Its l1 mass is 36/32=9/8. The centered modular offsets are i-3 for
0 <= i < 7. If two such offsets agree modulo N, cancel the common shift
and compare the canonical residues of i and j. For N>=7, both are below N,
so i=j. This supplies the injectivity hypothesis of the folding theorem.

Tensorization gives (9/8)^d. The general sign witness supplies attainment,
and linearity supplies the two-signal perturbation inequality.

## 6. Conditional propagation

Let `P` be a continuous linear map and let `landscape` send its output to an
additive group. Suppose an auxiliary function `lInf` satisfies

    lInf (landscape u - landscape v) <= L * ||u - v||

and a second function `lTwo` satisfies `lTwo w <= sqrt(mu) * lInf w`, with
`L >= 0` and `mu >= 0`. The operator bound and these two hypotheses give

    lTwo (landscape (P f) - landscape (P g))
      <= L * ||P|| * sqrt(mu) * ||f - g||.

For the level-one db2 operator and `N >= 7`, `||P||` may be replaced by
`(9/8)^d`. Any constant `C` such that `||P f|| <= C ||f||` for every `f`
satisfies `(9/8)^d <= C`. If instead the summary is valued in a normed group
and already obeys

    ||landscape u - landscape v|| <= L * sqrt(mu) * ||u - v||,

the reverse triangle inequality for that norm yields

    | ||landscape (P f)||^2 - ||landscape (P g)||^2 |
      <= (L * (9/8)^d * sqrt(mu) * ||f - g||)
         * (||landscape (P f)|| + ||landscape (P g)||).

None of these four statements constructs a persistence diagram or proves that
a landscape is non-expansive. A proof of bottleneck stability would be a
different project.

## 7. Audit boundaries

- A norm equality for smoothing is not a sharpness theorem for persistence
  landscapes or any other nonlinear summary.
- The new code does not import or rebrand the earlier empty-diagram skeleton.
- The filter-to-kernel identification is included, but a particular
  floating-point implementation is not verified.
- The convolution, folding, and tensor arguments in sections 2--4 are
  standard finite-dimensional analysis. The cascade identity in section 8
  depends on the sign analysis written out in `docs/CASCADE_THEOREM.md`.
  That improvement over the product bound `(9/8)^{(j+1)d}` is not, by
  itself, a priority claim. The editorial threshold remains a separate
  question, and `docs/RELATED_WORK.md` leaves originality unresolved.
- This mathematical proof account does not establish that the supplied Lean
  scripts elaborate. That check is recorded separately in `docs/VERIFICATION.md`.

## 8. Exact cascade levels 1, 2 and 3

Let `k_0` be the seven-tap kernel above. The undecimated cascade sets
`k_{j+1} = k_j ∗ (↑_{2^{j+1}} k_0)`. Clearing the denominator
`2^{5(j+1)}` gives an integer sequence. The step from level `j` to level
`j+1` is the five-tap stencil with coefficients `16` at `0`, `9` at `±s`
and `-1` at `±3s`, where `s = 2^{j+1}`.

Summing absolute values of that integer sequence gives three exact l1 masses:

- level 1, nineteen taps: `299/256`
- level 2, forty-three taps: `9663/8192`
- level 3, ninety-one taps: `309991/262144`

The support lengths are 19, 43 and 91. For a period at least that long, the
centered offsets are injective, so folding does not cancel and the periodic
operator norm is the corresponding power `(mass)^d`, including `d = 0`.
At dimension 2 the squares are `89401/65536`, `93373569/67108864` and
`96094420081/68719476736`. Manuscript equation (10) prints the rounded
decimals `1.364151`, `1.391375` and `1.398358`.

The same recurrence has a closed form at every level. Let
`L = 1651/1395` and

```
c_j = L - (4/63) 4^{-j} + (1/180) 16^{-j} - (1/1736) 32^{-j}.
```

The free kernel has l1 mass `c_j`. Whenever `N >= S_j = 6 * 2^{j+1} - 5`,
folding does not cancel and the periodic operator norm is `c_j^d`. For every
`N >= 1`, the folded norm is at most `L^d`; aliasing can only decrease the
l1 mass. `L^d` is the least constant that works for all levels and all
positive periods simultaneously. The witnessing periods may grow with `j`.
The free mass `c_j` is strictly increasing and converges to `L`, with
`0 < L - c_j <= (4/63) 4^{-j}`. The free mass does not depend on `N`.
At dimension zero every operator norm equals 1. The least-constant
statement at dimension zero concludes `1 ≤ B` and does not conclude
`B = 1`. The condition `N >= S_j` is sufficient, not necessary.
The conditional propagation in section 6 still takes bottleneck stability
and landscape non-expansiveness as hypotheses. The full argument, with the
Lean names of the lemmas that carry it, is `docs/CASCADE_THEOREM.md`.
`docs/RELATED_WORK.md` records the literature comparison and does not
claim that the formula is absent from the wavelet literature.

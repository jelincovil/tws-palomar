# Related work for the db2 cascade norm

Checked on 2026-10-18. This note records what was actually read and what
remains unread. It does not treat a failed search for the fraction
`1651/1395` as evidence that the formula is new.

The object under comparison is the one proved in `docs/CASCADE_THEOREM.md`:
the free ℓ¹ mass of the undecimated cascade whose first stage is

```
k_0 = [−1, 0, 9, 16, 9, 0, −1] / 32,
```

the induced supremum-operator norm of its periodization on `(ℤ/Nℤ)^d`, and
the least constant `L^d` with `L = 1651/1395` that bounds every level and
every positive period. The index `j = 0` is already this seven-tap stage.

## 1. Amat and Moncayo, 2008

S. Amat and M. Moncayo, “ℓ∞-stability for linear multiresolution algorithms:
a new explicit approach. Part I: the basic rules and the Daubechies case,”
*Applied Mathematics and Computation* **206** (2008), no. 1, 74–91.
DOI: [10.1016/j.amc.2008.08.047](https://doi.org/10.1016/j.amc.2008.08.047).
Bibliographic record:
<https://portalinvestigacion.upct.es/documentos/61860a058a2f583ff09b0d60>.

**Access.** Abstract and bibliographic record only. No public full text was
found on the authors’ institutional portal, and the publisher copy was not
opened. The review summary on the MaRDI item
<https://portal.mardi4nfdi.de/wiki/Item:Q2379027> was also read. Page-level
comparison is therefore not available.

**What the abstract supports.** The paper studies ℓ∞ stability of Mallat’s
multiresolution transform for orthogonal wavelet filters, by rewriting
successive convolutions and assuming a contraction. Decomposition uses a
different normalization from reconstruction. The Daubechies filters are the
worked case. The stated output is an explicit error bound that can be turned
into a compression level for a prescribed reconstruction tolerance.

**Relation.** Successive convolution and an ℓ∞ bound for a Daubechies filter
are the points of contact. The transform in view is Mallat’s, hence
decimated, and the filter is the orthogonal low-pass filter rather than the
half-autocorrelation `k_0`. Nothing in the abstract states a closed form in
the cascade level, a constant `1651/1395`, or a periodic convolution norm on
`(ℤ/Nℤ)^d`. Those absences are absences from the abstract, not from the
paper. Parts II and III of the same series (DOI
[10.1016/j.amc.2008.08.048](https://doi.org/10.1016/j.amc.2008.08.048) and
[10.1016/j.amc.2008.08.058](https://doi.org/10.1016/j.amc.2008.08.058))
extend the framework to other filter families and to two dimensions. Their
abstracts were read on the same portal. They were not used as substitutes
for Part I.

## 2. Amat and Moncayo, 2009

S. Amat and M. Moncayo, “Exact error bounds for the reconstruction processes
using interpolating wavelets,” *Mathematics and Computers in Simulation*
**79** (2009), no. 12, 3547–3555.
DOI: [10.1016/j.matcom.2009.04.005](https://doi.org/10.1016/j.matcom.2009.04.005).
Publisher link:
<https://www.sciencedirect.com/science/article/pii/S0378475409001049>.
Institutional record:
<https://portalinvestigacion.upct.es/documentos/61860a3a8a2f583ff09b1131>.

**Access.** Abstract only. The full text is marked as subscriber access, and
no institutional open copy was found.

**What the abstract supports.** The paper gives explicit error bounds for
reconstruction by the interpolating wavelets of Donoho. It says that the
stability constants of the interpolatory wavelets built from Daubechies
filters, which the abstract also calls Deslauriers–Dubuc wavelets, are
tabulated, and that those constants approximate the true constants more
closely than an earlier contraction argument. “Tabulated” and “better
approximated” describe numerical constants for a reconstruction operator.
They do not say that a closed form in the number of stages was proved.

**Relation.** This is the closest announced computation: exact or sharpened
ℓ∞ constants for the Daubechies interpolatory scheme. Our kernel `k_0` is
half of the usual four-point Deslauriers–Dubuc mask, whose center coefficient
is `1` rather than `1/2` (see §4). A table of reconstruction constants is
not, on the strength of the abstract, the same quantity as `c_j` or as
`L^d`. The table itself was not seen, so equality is not ruled out and is
not asserted.

## 3. Saito and Beylkin on autocorrelation wavelets

The published coauthor is Gregory Beylkin. The surname Belkin does not
appear on these papers.

Three public versions were located from
<https://www.math.ucdavis.edu/~saito/contrib/> and the publication list
linked there.

1. N. Saito and G. Beylkin, “Multiresolution representations using the
   autocorrelation functions of compactly supported wavelets,” *IEEE
   Transactions on Signal Processing* **41** (1993), no. 12, 3584–3590.
   DOI: [10.1109/78.258102](https://doi.org/10.1109/78.258102).
   Erratum: vol. 45 (1997), no. 3, p. 768, DOI
   [10.1109/TSP.1997.558499](https://doi.org/10.1109/TSP.1997.558499).
   Author copy:
   <https://www.math.ucdavis.edu/~saito/publications/saito_acs.pdf>.
   **Access.** The file was downloaded. Its text encoding does not extract
   to readable characters with `pypdf` or `pdfplumber`, so the body of this
   copy was not used. The author abstract on
   <https://www.math.ucdavis.edu/~saito/publications/acs.html> was read.

2. G. Beylkin and N. Saito, “Wavelets, their autocorrelation functions, and
   multiresolution representations of signals,” *Proc. SPIE* **1826**
   (1992), 39–50.
   DOI: [10.1117/12.131585](https://doi.org/10.1117/12.131585).
   Author copy:
   <https://www.math.ucdavis.edu/~saito/publications/saito_acs_spie.pdf>.
   **Access.** Full text of the author copy, 13 pages. This is the version
   from which the formulae below are quoted. It is a proceedings account,
   not a line-by-line substitute for the 1993 journal article.

3. N. Saito and G. Beylkin, *Proc. ICASSP-92*, vol. 4, pp. 381–384.
   DOI: [10.1109/ICASSP.1992.226356](https://doi.org/10.1109/ICASSP.1992.226356).
   **Access.** Citation and author abstract page only.

**Operator and normalization, as read in the SPIE copy.** Let `φ` be the
Daubechies scaling function and `Φ(x) = ∫ φ(y) φ(y − x) dy` its
autocorrelation. For the quadrature-mirror filter of length `L = 4` (two
vanishing moments), the autocorrelation coefficients in their normalization
are `a_1 = 9/8` and `a_3 = −1/8`. Equation (1.6) defines
`a_k = 2 ∑_l h_l h_{l+k}`. Our autocorrelation, without that factor `2`,
is `R(1) = 9/16` and `R(3) = −1/16`, so `a_k = 2 R(k)`. The two-scale
relation (1.9) specializes to

```
Φ(x) = Φ(2x) + (9/16) (Φ(2x−1) + Φ(2x+1)) − (1/16) (Φ(2x−3) + Φ(2x+3)).
```

Equation (1.26) says `Φ(k/2) = a_k / 2`. The paper identifies `Φ` with the
fundamental function of the Deslauriers–Dubuc iterative interpolation
scheme, and equation (1.18) quotes Dubuc’s four-point insertion rule

```
f(x) = (9/16) (f(x−h) + f(x+h)) − (1/16) (f(x−3h) + f(x+3h)).
```

**Norm, domain, and level.** The SPIE text does not compute an ℓ¹ mass of
a discrete cascade, does not state a supremum-operator norm on a cyclic
group, and does not give a constant depending on the number of iterations.
Its conclusions are symmetry of `Φ`, the interpolation identity, shift
invariance of the autocorrelation shell, and reconstruction from
zero-crossings. The domain of `Φ` is the real line. Our `m_j` is a finite
sum of absolute values of a discrete kernel.

**Relation.** The taps match, up to the factor-two convention in `a_k`.
The half-autocorrelation `k_0` is the discrete mask whose symbol is built
from `R`, with center coefficient `1/2`. The interpolatory mask written
out from (1.18), keeping old samples, has center coefficient `1` and is
`2 k_0`. Convolving with `k_0` and subdividing by the interpolatory mask
are different operators. The paper supplies the identification of the mask.
It does not supply `c_j` or `L`.

## 4. Deslauriers–Dubuc and the four-point scheme

G. Deslauriers and S. Dubuc, “Symmetric iterative interpolation processes,”
*Constructive Approximation* **5** (1989), 49–68.
DOI: [10.1007/BF01889598](https://doi.org/10.1007/BF01889598).

S. Dubuc, “Interpolation through an iterative scheme,” *Journal of
Mathematical Analysis and Applications* **114** (1986), 185–204.

**Access.** The 1989 abstract on the publisher page, and the four-point
formula as quoted by Beylkin–Saito (equation (1.18) above). The 1989
article itself was not opened. An erratum, *Constr. Approx.* **8** (1992),
125–126, corrects the proof of their Theorem 6.4 on the continuous
extension of the fundamental function. That erratum was seen as a publisher
PDF and concerns continuity of `F`, not an ℓ¹ cascade.

**What is safely attributed.** The four-point symmetric insertion rule is
Dubuc’s. Deslauriers–Dubuc extend it to an even number of knots and prove
that the fundamental function is continuous and positive definite, with
derivative regularity described by Lipschitz classes. The mask of the
binary four-point scheme, written so that old values are kept, is

```
[−1, 0, 9, 16, 9, 0, −1] / 16.
```

Its center entry is `1`, so the scheme reproduces constants and existing
samples. Our `k_0` is that mask divided by `2`.

**A different published norm.** C. Deng, K. Hormann, and Z. Zhang, “On the
norms of the Dubuc–Deslauriers subdivision schemes,” *Computer Aided
Geometric Design* **30** (2013), 672–674, give the ℓ∞ operator norm of the
single subdivision step as the number of taps `2n` grows. Their Theorem 1
bounds that norm between `1 + (1/4) log n` and `3/2 + (1/2) log n`. The
parameter is the mask order `n`, not the cascade level `j` of the fixed
four-point mask. The author PDF
<https://www.inf.usi.ch/hormann/papers/Deng.2013.OTN.pdf> was read. This
result does not decide the value of `m_j`.

## 5. What is not identified

No source read here states

```
c_j = 1651/1395 − (4/63) 4^{−j} + (1/180) 16^{−j} − (1/1736) 32^{−j},
```

or the least uniform constant `(1651/1395)^d` for the periodic operators
`C_{j,N,d}`. A web search for the fraction `1651/1395` on 2026-10-18
returned no wavelet source containing it. That search does not show that
no equivalent formula exists under another normalization.

The following correspondences were not established, and are not assumed.

- Mallat’s decimated orthogonal filter bank is not the undecimated
  convolution by `k_j`.
- The interpolatory subdivision operator with center `1` is not convolution
  by `k_0`. Passing from one ℓ¹ mass to the other would require a proved
  factor of `2` at each stage and the same pattern of upsampling. That
  factor is visible on the masks. It has not been checked against a
  published cascade formula, because no such formula was in the texts read.
- The ℓ∞ norm of one subdivision step, as a function of the mask order, is
  not the norm of the `j`-fold cascade.
- The supremum norm of a discrete periodic convolution is not the L¹ norm
  of the limit function `Φ` on the line, and neither has been shown here
  to equal a reconstruction-error constant from a multiresolution transform.

## 6. Conclusion

**C. The originality of the closed form remains unresolved, because the
evidence and the access are incomplete.**

The concrete comparison still missing is a reading of the full texts of
Amat–Moncayo 2008 and Amat–Moncayo 2009, checking three points in each:

1. the filter (orthogonal Daubechies taps, or the interpolatory mask with
   center `1`, or the half-autocorrelation `k_0`);
2. the operator (decimated analysis or reconstruction, interpolatory
   subdivision, or undecimated periodic convolution) and the norm (a
   reconstruction factor in ℓ∞, or `∑ |k|` on `ℤ/Nℤ`);
3. whether any stated constant or table entry equals `9/8`, `299/256`,
   `9663/8192`, `309991/262144`, or `1651/1395`, for one level or for
   every level.

Until that reading is done, this repository does not claim that the formula
is absent from the literature, and it does not claim that formalizing it
meets an editorial threshold. The proved gain inside the repository is
narrower and is not a priority claim: the exact mass is bounded by the
constant `L`, whereas the triangle inequality only gives the growing
product `(9/8)^{j+1}`.

If a later reading finds the same formula, or the same formula for the
mask `2 k_0`, the appropriate action is attribution. The Lean development
would then be a formalization of a known identity, which is a different
contribution from a first proof. If that reading finds only coarser bounds,
the present note should be updated to say which bound is improved and under
which identification of operators. Either outcome can be recorded by editing
this file. It does not require a new theorem.

One adjacent paper was seen at abstract level only and is not part of the
missing comparison above. M. Moncayo and S. Amat, “Error bounds for a class
of subdivision schemes based on the two-scale refinement equation,”
*Journal of Computational and Applied Mathematics* **236** (2011), 265–278,
DOI [10.1016/j.cam.2011.06.031](https://doi.org/10.1016/j.cam.2011.06.031),
estimate the distance from a control polygon to the limit curve, including
schemes built from Daubechies filters. That is a geometric subdivision
error, not the periodic convolution norm proved here. Turning that
estimate into a comparison with `L` would be a separate project. It is
left as future work and is not attempted in this revision.

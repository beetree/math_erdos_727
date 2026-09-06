# Candidate proof for the cases k = 2 and k = 3 of Erdős Problem 727

**Date:** 6 September 2026.

**Status.** This document presents a candidate unconditional proof for the two stated cases. The argument has undergone internal mathematical checks, but has not received independent expert verification or formal certification. It makes no claim to settle the original question for every fixed $k\geq 2$, and no priority claim is made.

The proof establishes the $k=3$ assertion directly; the $k=2$ assertion follows by divisibility of factorials. Its external analytic input is the classical prime number theorem in arithmetic progressions with a fixed modulus. The necessary consequences of that theorem, the lifting argument, the quadratic exponential-sum estimate, and the uniformity needed when summing over primes are given explicitly below. No prime-tuples conjecture or smoothness conjecture is assumed.

## 1. Statement and notation

Put

$$
f(t)=210t^2+391t+179.
$$

**Theorem.** There exist fixed integers $Q\geq 1$, $0\leq t_0<Q$, and $X_0\geq 1$ such that, for every integer $X\geq X_0$, at least $X/100$ integers $v\in[X,2X)$ satisfy

$$
\bigl((f(t_0+Qv)+3)!\bigr)^2\mid \bigl(2f(t_0+Qv)\bigr)!.
\tag{1.1}
$$

In particular, there are infinitely many positive integers $n$ such that

$$
((n+3)!)^2\mid(2n)!.
\tag{1.2}
$$

There is also a fixed constant $c_*>0$ such that the number of such $n\leq Z$ is at least $c_*\sqrt Z$ for every sufficiently large $Z$.

**Corollary.** There are infinitely many positive integers $n$ such that

$$
((n+2)!)^2\mid(2n)!.
\tag{1.3}
$$

Throughout, $p$ denotes a prime, $v_p(m)$ is the exponent of $p$ in the positive integer $m$, $\{x\}=x-\lfloor x\rfloor$, and $\log$ is the natural logarithm. Write $e(x)=\exp(2\pi i x)$, and let $\|x\|$ be the distance from $x$ to the nearest integer.

Let $\pi(z)$ count primes at most $z$, and let $\pi(z;d,a)$ count those congruent to $a$ modulo $d$. Write $\varphi(d)$ for Euler's totient function and $\operatorname{Li}(z)=\int_2^z du/\log u$ for $z\geq2$.

All arithmetic progressions and all constants are fixed before $X\to\infty$. Implicit constants may depend on these fixed choices. In particular, the progression modulus $Q$ is allowed to be enormous; it does not depend on $X$.

## 2. Factorial divisibility and carries

Define

$$
B(n)=\binom{2n}{n},\qquad
A(n)=(n+1)(n+2)(n+3).
$$

Since $(n+3)!=n!A(n)$, assertion (1.2) is equivalent to

$$
A(n)^2\mid B(n).
\tag{2.1}
$$

Legendre's formula, obtained by counting multiples of $p,p^2,\ldots$ in a factorial, gives

$$
v_p(B(n))
=\sum_{h\geq1}\left(
\left\lfloor\frac{2n}{p^h}\right\rfloor
-2\left\lfloor\frac n{p^h}\right\rfloor\right)
=\sum_{h\geq1}\mathbf 1_{\{n/p^h\}\geq1/2}.
\tag{2.2}
$$

Set

$$
c_p(n)=v_p(B(n)).
$$

Each summand in (2.2) is the carry out of the lowest $h$ digits when $n$ is doubled in base $p$. Thus the required inequalities are

$$
c_p(n)\geq 2v_p(A(n))\qquad\text{for every prime }p.
\tag{2.3}
$$

Only primes dividing $A(n)$ require attention.

## 3. Six linear factors

The chosen polynomial satisfies

$$
\begin{aligned}
f(t)+1&=(35t+36)(6t+5),\\
f(t)+2&=(t+1)(210t+181),\\
f(t)+3&=(15t+14)(14t+13).
\end{aligned}
\tag{3.1}
$$

Denote these six linear forms, in the displayed order, by $L_i(t)=a_i t+b_i$, and let $j_i$ be the associated shift. The following table also records the derivative at a root of $L_i$:

| $i$ | $L_i(t)$ | $j_i$ | $c_i$, where $f'(t)\equiv c_i$ if $L_i(t)\equiv0\pmod p$ |
|---:|---|---:|---:|
| 1 | $35t+36$ | 1 | $-41$ |
| 2 | $6t+5$ | 1 | $41$ |
| 3 | $t+1$ | 2 | $-29$ |
| 4 | $210t+181$ | 2 | $29$ |
| 5 | $15t+14$ | 3 | $-1$ |
| 6 | $14t+13$ | 3 | $1$ |

The derivative statements hold whenever $p\nmid a_i$, by substituting $t\equiv-b_i/a_i$ into $f'(t)=420t+391$.

Every $L_i$ is primitive: $\gcd(a_i,b_i)=1$. The prime divisors of their slopes lie in $\{2,3,5,7\}$. The within-pair resultants are, up to sign, $41,29,1$. A prime dividing factors belonging to different pairs must divide a difference of two members of $f+1,f+2,f+3$, and is therefore at most $2$.

Consequently, any prime $p>1000$ divides at most one of the six factors at a given integer $t$, and the derivative in its root class is nonzero modulo $p$.

## 4. One progression handles every prime at most 1000

Fix

$$
Y=1000,\qquad
G(t)=\prod_{i=1}^6L_i(t)=A(f(t)).
$$

At $t=0$,

$$
G(0)=180\cdot181\cdot182,
$$

whose prime support is

$$
S=\{2,3,5,7,13,181\}.
$$

For each prime $p\leq Y$ outside $S$, impose $t\equiv0\pmod p$. Then $p\nmid G(t)$.

For $p\in S$, put

$$
e_p=\sum_{j=1}^3v_p(179+j),
$$

and use the following fixed choices:

| $p$ | $e_p$ | $b_p$ | $b_p+2e_p$ |
|---:|---:|---:|---:|
| 2 | 3 | 3 | 9 |
| 3 | 2 | 3 | 7 |
| 5 | 1 | 2 | 4 |
| 7 | 1 | 2 | 4 |
| 13 | 1 | 2 | 4 |
| 181 | 1 | 2 | 4 |

Each $b_p$ exceeds every individual valuation $v_p(179+j)$. Let $r_p$ be the least nonnegative residue of $179$ modulo $p^{b_p}$, and prescribe

$$
f(t)\equiv r_p+p^{b_p}(p^{2e_p}-1)
\pmod {p^{b_p+2e_p}},\qquad t\equiv0\pmod p.
\tag{4.1}
$$

This congruence has a unique lift of $t=0\pmod p$, because $f'(0)=391=17\cdot23$ is coprime to every $p\in S$.

For completeness, the lifting fact used here is elementary. If $f'(u)\not\equiv0\pmod p$, then

$$
f(u+zp^r)\equiv f(u)+zp^rf'(u)\pmod {p^{r+1}}.
$$

As $z$ runs through the residues modulo $p$, this realizes each possible next digit of the target exactly once. Induction proves the lifting assertion.

Condition (4.1) preserves $f(t)\equiv179\pmod {p^{b_p}}$, so each valuation $v_p(f(t)+j)$ remains equal to $v_p(179+j)$. It also prescribes a block of $2e_p$ consecutive digits equal to $p-1$ in the base-$p$ expansion of $f(t)$, at positions $b_p$ through $b_p+2e_p-1$. Every such digit produces a carry when doubled, regardless of the incoming carry. Therefore

$$
c_p(f(t))\geq2e_p=2v_p(G(t)).
\tag{4.2}
$$

Apply the Chinese remainder theorem to these finitely many congruences. Let

$$
Q=\prod_{p\in S}p^{b_p+2e_p}
\prod_{\substack{p\leq Y\\p\notin S}}p,
$$

and choose the resulting residue $t_0$ with $0\leq t_0<Q$. On the progression

$$
t=t_0+Qv,
\tag{4.3}
$$

inequality (2.3) holds for every prime $p\leq Y$.

From now on write

$$
F(v)=f(t_0+Qv),\qquad
\mathcal L_i(v)=L_i(t_0+Qv).
$$

For $v\in[X,2X)$ there is a fixed $C\geq1$ such that all $\mathcal L_i(v)$ are positive and at most $CX$. Also $F(v)\asymp X^2$. For $p>Y$, the slope $a_iQ$ is invertible modulo $p^r$ for every $r\geq1$.

## 5. Repeated prime factors and the remaining failure events

Discard parameters $v\in[X,2X)$ for which $p^2\mid\mathcal L_i(v)$ for some $i$ and some $p>Y$. Since this is one residue class modulo $p^2$, their number is at most

$$
6X\sum_{p>Y}\frac1{p^2}+6\pi(\sqrt{CX})
\leq\frac{6X}{Y}+o(X)
=0.006X+o(X).
\tag{5.1}
$$

Here $\sum_{m>Y}m^{-2}\leq1/Y$, and even the elementary estimate $\pi(z)\leq z$ makes the endpoint error $o(X)$.

For every undiscarded parameter, each prime $p>Y$ dividing $G(t)$ has exponent exactly one, by Section 3. If $p\mid\mathcal L_i(v)$, then

$$
F(v)\equiv-j_i\pmod p.
$$

Since $p>Y>6$, this gives the carry at level $p$. Therefore an undiscarded parameter can fail (2.3) only if, for some $i$ and $p>Y$,

$$
p\mid\mathcal L_i(v),\qquad
\{F(v)/p^h\}<1/2\quad\text{for every }h\geq2.
\tag{5.2}
$$

We bound the union of these events. No independence between primes or between linear factors will be assumed.

## 6. Prime harmonic sums used below

The classical prime number theorem in arithmetic progressions, for fixed $d$ and $\gcd(a,d)=1$, gives

$$
\pi(x;d,a)=\frac{\operatorname{Li}(x)}{\varphi(d)}
+O_d\bigl(x\exp(-c_d\sqrt{\log x})\bigr)
\tag{6.1}
$$

for some $c_d>0$. Only fixed moduli are used. This standard unconditional theorem is recorded, for example, in [NIST DLMF, equation 27.12.8](https://dlmf.nist.gov/27.12.E8); the ordinary version is [equation 27.12.5](https://dlmf.nist.gov/27.12.E5).

Partial summation of (6.1) gives

$$
\sum_{\substack{p\leq z\\p\equiv a\pmod d}}\frac1p
=\frac1{\varphi(d)}\log\log z+B_{d,a}+o(1).
\tag{6.2}
$$

Indeed, partial summation writes the left side as $\pi(z;d,a)/z+\int_2^z\pi(u;d,a)u^{-2}\,du$. The main term gives $(\log\log z)/\varphi(d)$ plus a constant. The error integral converges at infinity, since

$$
\int_2^\infty\exp(-c_d\sqrt{\log u})\,\frac{du}{u}<\infty.
$$

In particular, for fixed $0<a<b$,

$$
\sum_{X^a<p\leq X^b}\frac1p=\log\frac ba+o(1).
\tag{6.3}
$$

If $R$ is a fixed set of reduced residue classes modulo $d$, and $C>0$ is fixed, then

$$
\sum_{\substack{X^a<p\leq CX^b\\p\bmod d\in R}}\frac1p
=\frac{|R|}{\varphi(d)}\log\frac ba+o(1).
\tag{6.4}
$$

We also need the weighted limit, for fixed $P>1$, $c>0$ and $\delta>0$,

$$
\lim_{X\to\infty}
\sum_{P<p\leq X^\delta}\frac1p
\exp\left(-\frac{c\log X}{\log p}\right)
=\int_0^\delta e^{-c/y}\frac{dy}{y}
=E_1(c/\delta),
\tag{6.5}
$$

where $E_1(z)=\int_z^\infty e^{-w}\,dw/w$.

To justify the lower endpoint in (6.5), write the ordinary case of (6.2) as

$$
\sum_{p\leq z}\frac1p=\log\log z+B+R(z),\qquad R(z)\to0.
$$

Integrate $g_X(z)=\exp(-c\log X/\log z)$ against this identity in the Stieltjes sense. The main term becomes the integral in (6.5), initially starting at $\log P/\log X$; its missing lower tail tends to zero. The constant term contributes nothing. For the error, split at a fixed $Z>P$. The part below $Z$ tends to zero. Since $g_X$ is increasing, partial summation bounds the part above $Z$ by $2\sup_{z\geq Z}|R(z)|g_X(X^\delta)$, apart from terms tending to zero. First let $X\to\infty$, then $Z\to\infty$. This proves (6.5).

## 7. Very small primes

Fix

$$
\delta=\frac1{20},\qquad
\rho=\frac{Y+1}{2Y}=\frac{1001}{2000},\qquad
c=\frac12\log(1/\rho).
$$

For $Y<p\leq X^\delta$, put

$$
\ell=\left\lfloor\frac{\log X}{2\log p}\right\rfloor.
$$

Then $\ell\geq10$ and $p^\ell\leq\sqrt X$.

Fix $i$ and the unique root class of $\mathcal L_i(v)$ modulo $p$. On that class,

$$
F'(v)\equiv Qc_i\not\equiv0\pmod p.
$$

The lifting argument in Section 4 shows that $v\mapsto F(v)$ is a bijection from this root class modulo $p^\ell$ onto the residues congruent to $-j_i$ modulo $p$.

The units digit of the latter residues is $p-j_i$, and its doubling produces a carry. To avoid every additional carry at levels $2,\ldots,\ell$, the next digit has $(p-1)/2$ choices; every subsequent digit has $(p+1)/2$ choices. Thus the number of permitted residues modulo $p^\ell$ is

$$
\frac{p-1}{2}\left(\frac{p+1}{2}\right)^{\ell-2}
\leq p^{\ell-1}\rho^{\ell-1}.
$$

The number of corresponding parameters $v\in[X,2X)$ is at most

$$
\left(\frac Xp+p^{\ell-1}\right)\rho^{\ell-1}.
\tag{7.1}
$$

The sum of the second terms over all these primes and the six forms is

$$
O\left(\sqrt X\sum_{p\leq X^\delta}\frac1p\right)
=O(\sqrt X\log\log X)=o(X).
\tag{7.2}
$$

Also

$$
\ell-1\geq\frac{\log X}{2\log p}-2,
\qquad
\rho^{\ell-1}\leq\rho^{-2}
\exp\left(-\frac{c\log X}{\log p}\right).
$$

Let $E_{\mathrm{small}}(X)$ count the union of events (5.2) in this prime range. Equations (6.5), (7.1) and (7.2) give

$$
\limsup_{X\to\infty}\frac{E_{\mathrm{small}}(X)}X
\leq6\rho^{-2}E_1(c/\delta).
\tag{7.3}
$$

Since $\rho^{-2}<4$, $c/\delta=10\log(2000/1001)>6$, and $E_1(z)\leq e^{-z}/z$,

$$
6\rho^{-2}E_1(c/\delta)
<\frac{24e^{-6}}6
=4e^{-6}<0.01.
\tag{7.4}
$$

These strict numerical comparisons need no numerical approximation to an integral. For example, $\log x\geq2(x-1)/(x+1)$ for $x\geq1$ gives $\log(2000/1001)>3/5$, while $e^3>\sum_{r=0}^8 3^r/r!>20$ gives $e^6>400$.

## 8. A uniform quadratic exponential-sum estimate

**Lemma.** Let $q\geq3$ be odd, let $a\in\mathbb Z$ satisfy $\gcd(a,q)=1$, and let $I$ be an interval of $L$ consecutive integers. Uniformly in $a,q,I$ and every real $\theta$,

$$
\left|\sum_{r\in I}e\left(\frac{ar^2}{q}+\theta r\right)\right|
\ll\left(\frac L{\sqrt q}+\sqrt q\right)\log(2q).
\tag{8.1}
$$

**Proof.** First suppose $L\leq q$. Translate the interval to $0\leq r<L$; this changes only the linear coefficient and a constant phase. For $b\bmod q$, let

$$
G_b=\sum_{s\bmod q}e\left(\frac{as^2-bs}{q}\right).
$$

Squaring the absolute value and setting the difference between the two summation variables equal to $h$ gives

$$
|G_b|^2
=\sum_{h\bmod q}e\left(\frac{ah^2-bh}{q}\right)
\sum_{s\bmod q}e\left(\frac{2ahs}{q}\right)
=q,
$$

because $2a$ is invertible modulo $q$. Fourier inversion now gives

$$
\sum_{r=0}^{L-1}e\left(\frac{ar^2}{q}+\theta r\right)
=\frac1q\sum_{b\bmod q}G_b
\sum_{r=0}^{L-1}e\bigl((\theta+b/q)r\bigr).
$$

The geometric-sum bound is

$$
\left|\sum_{r=0}^{L-1}e(ur)\right|
\leq\min\left(L,\frac1{2\|u\|}\right),
$$

with the second quantity interpreted as infinity when $u$ is integral. Uniformly in $\theta$, the sum of these bounds over $b\bmod q$ is $O(q\log(2q))$: at each distance scale $m/q$ from an integer there are only a bounded number of frequencies, and the resulting harmonic sum is $O(q\sum_{m\leq q}1/m)$, together with $O(q)$ for the closest frequencies. Since $|G_b|=\sqrt q$, this proves the bound $O(\sqrt q\log(2q))$ for $L\leq q$.

For general $L$, divide $I$ into at most $L/q+1$ consecutive intervals of length at most $q$ and apply this bound to each. This proves (8.1). $\square$

The uniformity in an arbitrary real linear coefficient is essential in the next section.

## 9. Uniform distribution for medium primes

Fix

$$
\eta=10^{-6},\qquad a_j=\frac2j\quad(4\leq j\leq40).
$$

For $J\in\{4,\ldots,39\}$, consider the band

$$
X^{a_{J+1}+\eta}<p\leq X^{a_J-\eta}.
\tag{9.1}
$$

Each band is nonempty as an exponent interval: its gap before removing the two margins is at least $1/780>2\eta$.

Fix $i$, and let $v_0$ be the least nonnegative root of $\mathcal L_i$ modulo $p$. Conditional on $p\mid\mathcal L_i(v)$, write

$$
v=v_0+pz.
$$

The allowed $z$ form an interval of

$$
L=\frac Xp+O(1)
$$

consecutive integers. As $F$ has leading coefficient $D=210Q^2$,

$$
F(v_0+pz)=Dp^2z^2+pF'(v_0)z+F(v_0).
\tag{9.2}
$$

We claim that, uniformly over the primes in (9.1), the vectors

$$
\left(\{F(v)/p^2\},\ldots,\{F(v)/p^J\}\right)
\tag{9.3}
$$

are asymptotically uniformly distributed in the $(J-1)$-dimensional unit cube, as $v$ ranges over the conditioned parameters.

Fix a nonzero integer Fourier frequency $(h_2,\ldots,h_J)$, and let $H$ be its highest nonzero index. The phase is

$$
\sum_{r=2}^J h_r\frac{F(v_0+pz)}{p^r}.
$$

If $H\geq3$, its quadratic coefficient has reduced denominator exactly

$$
q=p^{H-2}
$$

for all sufficiently large $X$ for this fixed frequency. Indeed, after using the common denominator $p^{H-2}$, the numerator is congruent to $Dh_H\not\equiv0\pmod p$; every prime divisor of the fixed nonzero integer $Dh_H$ is eventually smaller than the lower endpoint of (9.1). The linear coefficient may be any real number, which is permitted in (8.1).

After division by $L$, the resulting bound is

$$
O\left(\left(p^{-(H-2)/2}+\frac{p^{H/2}}X\right)\log X\right)=o(1)
\tag{9.4}
$$

uniformly over the band. Here $p\geq X^\delta$, $H\leq J$, and

$$
\frac{p^{H/2}}X\leq\frac{p^{J/2}}X\leq X^{-\eta J/2}.
$$

If $H=2$, the quadratic coefficient is the integer $Dh_2$. The remaining nonconstant phase is

$$
\frac{h_2F'(v_0)}p\,z.
$$

Because $F'(v_0)\equiv Qc_i\pmod p$, this coefficient is congruent modulo one to $h_2Qc_i/p$, with fixed nonzero numerator. For all sufficiently large $p$ the geometric sum is $O(p)$, and its normalized size is

$$
O(p/L)=O(p^2/X)=o(1)
\tag{9.5}
$$

uniformly, since (9.1) implies $p\leq X^{1/2-\eta}$.

Equations (9.4) and (9.5) prove uniform cancellation for every fixed nonzero Fourier frequency. To pass to a box indicator, approximate it from above and below by continuous periodic functions with arbitrarily close integrals, then approximate these functions uniformly by finite trigonometric polynomials. At each approximation stage there are only finitely many frequencies, so cancellation is uniform simultaneously for all of them. Take $X\to\infty$ first, then refine the approximations. This proves the claimed uniform distribution, including for boxes whose boundaries have measure zero.

In particular, the proportion of conditioned parameters with no carry at levels $2,\ldots,J$ is

$$
2^{1-J}+o(1),
\tag{9.6}
$$

uniformly in (9.1): the relevant box is $[0,1/2)^{J-1}$.

Let $E_{\mathrm{medium}}(X)$ be the union count of (5.2) over the medium bands. For each band, sum (9.6) times $X/p+O(1)$. The errors sum to $o(X)$: the reciprocal-prime sum over a fixed band is bounded, its distribution error is uniform, and the sum of the $O(1)$ terms is $O(\pi(X^{1/2-\eta}))=o(X)$. Summing the six forms and the finitely many bands gives

$$
\begin{aligned}
\limsup_{X\to\infty}\frac{E_{\mathrm{medium}}(X)}X
&\leq6\sum_{J=4}^{39}2^{1-J}\log\frac{J+1}{J}\\
&\leq6\sum_{J=4}^{\infty}2^{1-J}\log\left(1+\frac1J\right)\\
&\leq6\cdot\frac14\sum_{J=4}^{\infty}2^{1-J}
=\frac38.
\end{aligned}
\tag{9.7}
$$

We used $\log(1+1/J)\leq1/J\leq1/4$ and $\sum_{J\geq4}2^{1-J}=1/4$.

## 10. Boundary strips

The prime exponents between $\delta=1/20$ and $1/2+\eta$ that are not covered by (9.1) lie in one of the 37 strips

$$
X^{a_j-\eta}\leq p\leq X^{a_j+\eta},\qquad 4\leq j\leq40.
\tag{10.1}
$$

Count all divisibility events $p\mid\mathcal L_i(v)$ in these strips, irrespective of carries. Equation (6.3) and the bound $X/p+O(1)$ give an upper limiting proportion at most

$$
6\sum_{j=4}^{40}\log\frac{a_j+\eta}{a_j-\eta}.
\tag{10.2}
$$

All endpoint errors are $o(X)$, since the primes involved are at most $X^{1/2+\eta}$.

Using $\log(1+u)\leq u$ and $\sum_{j=4}^{40}j=814$,

$$
\begin{aligned}
6\sum_{j=4}^{40}\log\frac{a_j+\eta}{a_j-\eta}
&\leq12\eta\sum_{j=4}^{40}\frac1{a_j-\eta}\\
&\leq\frac{6\eta\cdot814}{1-20\eta}
<0.004885<0.01.
\end{aligned}
\tag{10.3}
$$

Overlaps between these strips and the other prime ranges are harmless, since all counts are upper bounds for unions.

## 11. Large primes and a finite residue calculation

It remains to consider $p>X^{1/2+\eta}$ dividing a factor $\mathcal L_i(v)$. Write

$$
L_i(t)=pm,\qquad t=t_0+Qv.
$$

Then $m$ is a positive integer and

$$
\frac mp\leq\frac{CX}{p^2}=O(X^{-2\eta})=o(1)
\tag{11.1}
$$

uniformly throughout the range.

The exact identities

$$
f(t)=\alpha_iL_i(t)^2+\beta_iL_i(t)-j_i
\tag{11.2}
$$

have the following coefficients:

| $i$ | $L_i(t)$ | $\alpha_i$ | $\beta_i$ | Reduced denominator $d_i$ of $\alpha_i$ |
|---:|---|---:|---:|---:|
| 1 | $35t+36$ | $6/35$ | $-41/35$ | 35 |
| 2 | $6t+5$ | $35/6$ | $41/6$ | 6 |
| 3 | $t+1$ | $210$ | $-29$ | 1 |
| 4 | $210t+181$ | $1/210$ | $29/210$ | 210 |
| 5 | $15t+14$ | $14/15$ | $-1/15$ | 15 |
| 6 | $14t+13$ | $15/14$ | $1/14$ | 14 |

Hence

$$
\frac{f(t)}{p^2}
=\alpha_i m^2+\beta_i\frac mp-\frac{j_i}{p^2}.
\tag{11.3}
$$

For $i\neq3$, $d_i\mid a_i$ and $\gcd(b_i,d_i)=1$. Reducing $L_i(t)=pm$ modulo $d_i$ gives

$$
m\equiv b_ip^{-1}\pmod {d_i}.
\tag{11.4}
$$

Thus, as the reduced residue class of $p$ modulo $d_i$ varies, the corresponding class of $m$ runs bijectively through the unit group modulo $d_i$. This uses the original $a_i,b_i$; imposing the progression (4.3) does not alter (11.4).

The distinct possible fractional parts of $\alpha_i m^2$, for unit residues $m$, are:

| $i$ | Possible fractional parts | Proportion $\theta_i$ below $1/2$ |
|---:|---|---:|
| 1 | $6/35,19/35,24/35,26/35,31/35,34/35$ | $1/6$ |
| 2 | $5/6$ | $0$ |
| 4 | $1/210,79/210,109/210,121/210,151/210,169/210$ | $1/3$ |
| 5 | $11/15,14/15$ | $0$ |
| 6 | $1/14,9/14,11/14$ | $1/3$ |

Each listed fractional part has the same number of preimages: squaring on a finite abelian group is a homomorphism with equal-sized fibers on its image, and multiplication by the numerator of $\alpha_i$ permutes residues modulo $d_i$. No displayed fraction equals $0$ or $1/2$.

By (11.1), the correction in (11.3) tends to zero uniformly. Since the displayed sets are finite, every fractional part above $1/2$ gives the $p^2$-level carry for all sufficiently large $X$. Failures are therefore confined to fixed reduced residue classes of $p$, occupying proportion $\theta_i$ of the unit group.

The factor $i=3$ is favorable for a separate reason. Here

$$
\frac{f(t)}{p^2}=210m^2-\frac{29m}{p}-\frac2{p^2}.
\tag{11.5}
$$

The correction is strictly negative and tends uniformly to zero. For large $X$ it lies in $(-1/2,0)$, so the fractional part in (11.5) lies in $(1/2,1)$. This always supplies the second carry. Set $\theta_3=0$.

For each $i\neq3$, let $R_i$ be the fixed bad set of prime residue classes just described. The union count $E_{\mathrm{large}}(X)$ is bounded by

$$
\sum_{i\neq3}\;
\sum_{\substack{X^{1/2+\eta}<p\leq CX\\p\bmod d_i\in R_i}}
\left(\frac Xp+O(1)\right).
\tag{11.6}
$$

The summed endpoint error is $O(\pi(CX))=o(X)$. This remains true for the fixed, possibly very large constant $C$.

By (6.4), and since

$$
\sum_{i=1}^6\theta_i=\frac16+\frac13+\frac13=\frac56,
$$

we obtain

$$
\limsup_{X\to\infty}\frac{E_{\mathrm{large}}(X)}X
\leq\frac56\log\frac1{1/2+\eta}
<\frac56\log2<\frac7{12}.
\tag{11.7}
$$

The final strict inequality follows from $\log2<7/10$; for instance, the first four terms of the exponential series already give $e^{7/10}>2$.

## 12. Completion of the proof and the case k = 2

Every relevant prime is covered:

1. All primes $p\leq Y$ satisfy (2.3) throughout the fixed progression.
2. Primes $Y<p\leq X^\delta$ are counted in Section 7.
3. Medium bands and boundary strips cover $X^\delta<p\leq X^{1/2+\eta}$.
4. Larger primes are counted in Section 11, and no prime divisor of any $\mathcal L_i(v)$ exceeds $CX$.

After the repeated-factor exclusions in Section 5, every failure is included in one of the no-extra-carry events (5.2). Therefore the upper limiting proportion of unsuccessful parameters is strictly below

$$
0.006+0.01+\frac38+0.01+\frac7{12}
=\frac{2953}{3000}
<\frac{99}{100}.
\tag{12.1}
$$

All constants, the progression, the band dimensions, and the exponent margins have already been fixed. The Fourier approximations used to prove (9.6) are fixed before each asymptotic limit and then refined. Thus every $o(X)$ error above is valid simultaneously for the finitely many ranges and forms used in (12.1).

It follows that, for every sufficiently large integer $X$, at most $99X/100$ of the $X$ integers in $[X,2X)$ fail. At least $X/100$ succeed. This proves (1.1).

The map $v\mapsto F(v)$ is strictly increasing for positive $v$ and has positive quadratic leading coefficient. Hence successful parameters yield infinitely many distinct integers $n$ satisfying (1.2). Moreover $F(v)\leq C_2v^2$ for some fixed $C_2$ and all sufficiently large $v$. For large $Z$, take

$$
X=\left\lfloor\frac12\sqrt{Z/C_2}\right\rfloor.
$$

Then all $v\in[X,2X)$ give $F(v)\leq Z$, and at least $X/100\gg\sqrt Z$ of these values succeed. This gives the stated counting lower bound.

Finally,

$$
((n+3)!)^2=(n+3)^2((n+2)!)^2.
$$

Every integer $n$ supplied by (1.2) therefore also satisfies (1.3), proving the $k=2$ corollary. $\square$

## 13. Exact finite checks

The infinitude argument does not use computation. The following checks are supplied to make the algebra and residue tables reproducible and to give an exact example of the factorial criterion.

For $t=61$,

$$
n=f(61)=805440,
$$

and the six factors are

$$
2171,\quad371,\quad62,\quad12991,\quad929,\quad867.
$$

The complete valuation certificate is:

| Prime $p$ dividing $A(n)$ | $c_p(n)$ | Required $2v_p(A(n))$ |
|---:|---:|---:|
| 2 | 6 | 2 |
| 3 | 9 | 2 |
| 7 | 5 | 2 |
| 11 | 2 | 2 |
| 13 | 3 | 2 |
| 17 | 5 | 4 |
| 31 | 2 | 2 |
| 53 | 2 | 2 |
| 167 | 2 | 2 |
| 929 | 2 | 2 |
| 1181 | 2 | 2 |

This finite example need not belong to the specially chosen progression in Section 4. It independently illustrates the conclusion and checks the valuation implementation. There are 1,612 successful parameters among $t=1,\ldots,10000$ in the unrestricted polynomial family.

The following Python code uses only the standard library. Polynomial identities and residue proportions are checked exactly with rational arithmetic; the factorial criterion is checked through prime valuations.

```python
from collections import Counter
from fractions import Fraction as R
from math import gcd


# (a_i, b_i, j_i, alpha_i, beta_i, derivative at root)
DATA = [
    (35, 36, 1, R(6, 35), R(-41, 35), -41),
    (6, 5, 1, R(35, 6), R(41, 6), 41),
    (1, 1, 2, R(210), R(-29), -29),
    (210, 181, 2, R(1, 210), R(29, 210), 29),
    (15, 14, 3, R(14, 15), R(-1, 15), -1),
    (14, 13, 3, R(15, 14), R(1, 14), 1),
]


def check_algebra_and_residues():
    bad_proportions = []
    for a, b, j, alpha, beta, derivative in DATA:
        assert gcd(a, b) == 1
        assert alpha*a*a == 210
        assert 2*alpha*a*b + beta*a == 391
        assert alpha*b*b + beta*b - j == 179
        assert 420*R(-b, a) + 391 == derivative
        d = alpha.denominator
        if d == 1:
            assert beta < 0
            bad_proportions.append(R(0))
            continue
        assert a % d == 0 and gcd(b, d) == 1
        counts = Counter()
        for m in range(d):
            if gcd(m, d) == 1:
                counts[(alpha*m*m) % 1] += 1
        assert len(set(counts.values())) == 1
        assert R(0) not in counts and R(1, 2) not in counts
        bad = sum(count for x, count in counts.items() if x < R(1, 2))
        bad_proportions.append(R(bad, sum(counts.values())))
    assert bad_proportions == [R(1, 6), R(0), R(0), R(1, 3), R(0), R(1, 3)]
    assert sum(bad_proportions) == R(5, 6)


def factor(n):
    out = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def carries(n, p):
    total, q = 0, p
    while q <= 2*n:
        total += (2*n)//q - 2*(n//q)
        q *= p
    return total


def check_parameter(t):
    assert t >= 1
    n = 210*t*t + 391*t + 179
    factors = [a*t+b for a, b, *_ in DATA]
    for j in range(1, 4):
        assert factors[2*j-2]*factors[2*j-1] == n+j
    valuations = {}
    for value in factors:
        for p, exponent in factor(value).items():
            valuations[p] = valuations.get(p, 0) + exponent
    rows = [(p, carries(n, p), 2*exponent)
            for p, exponent in sorted(valuations.items())]
    return n, all(actual >= needed for p, actual, needed in rows), rows


if __name__ == '__main__':
    check_algebra_and_residues()
    print(check_parameter(61))
    print(sum(check_parameter(t)[1] for t in range(1, 10001)))
```

The final line prints `1612`.

## 14. References and scope

1. P. Erdős, R. L. Graham, I. Z. Ruzsa and E. G. Straus, *On the prime factors of* $\binom{2n}{n}$, Mathematics of Computation **29** (1975), 83–92. The factorial-divisibility question appears on p. 90. [Original paper](https://www.renyi.hu/~p_erdos/1975-27.pdf).
2. NIST Digital Library of Mathematical Functions, §27.12, *Asymptotic Formulas: Primes*, especially equations 27.12.5 and 27.12.8. These supply the classical prime-distribution input in Section 6. [Reference](https://dlmf.nist.gov/27.12).

The claimed conclusions of this document are precisely (1.1), (1.2), their counting consequence, and the corollary (1.3). The general case of Erdős Problem 727 is not proved here. The candidate status stated at the beginning applies to the entire argument.

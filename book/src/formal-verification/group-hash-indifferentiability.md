# Group-Hash Indifferentiability

The Zcash security arguments model the Pasta group hashes as random oracles into
the curve groups. This page explains what justifies that modelling, and what the
formalization does and does not establish. It is written for a reader who has
not seen an indifferentiability proof before; no prior acquaintance with the
notion is assumed.

The counting that the argument rests on lives in
[CompElliptic](https://github.com/daira/CompElliptic) ([`Hashing/TwoTermUniformity.lean`](https://github.com/daira/CompElliptic/blob/main/CompElliptic/Hashing/TwoTermUniformity.lean),
[`Hashing/PastaSSWU.lean`](https://github.com/daira/CompElliptic/blob/main/CompElliptic/Hashing/PastaSSWU.lean)); the probabilistic argument on this page lives under
`Zcash/Security/GroupHash/`.

## The deployed hash

Let $\Group$ be an elliptic curve group, $\Field$ its field of definition
(base field), and $\Domain$ a convenient input domain. The deployed group hash
$H \typecolon \Domain \to \Group$ is

$$H(m) = f(u_0) + f(u_1), \qquad (u_0, u_1) = \mathsf{hash\_to\_field}(m, 2),$$

where $f = \mathsf{mapToCurve} \typecolon \Field \to \Group$ sends a field element
to a curve point, and the sum is the group law.

We model $\mathsf{hash\_to\_field}(\argument, 2) \typecolon \Domain \to \Field \times \Field$
as a random oracle: an idealized hash whose output on each new input is a fresh
uniform pair. The question is whether $H$ itself may then be modelled as a random
oracle into the group $\Group$. But first, we'll try to explain why a simpler
construction does not suffice.

## Mapping to a curve

How can we map from a field to an elliptic curve group? In the case of short
Weierstrass curves, each non-identity point has coordinates
$(x, y) \typecolon \Field \times \Field$ satisfying the curve equation:

$$y^2 = x^3 + a \mul x + b$$

An obvious candidate for a map from a field element $u$ to a curve element
would be to choose one of the points with $x = u$ using a deterministic square
root function $\possqrt{\argument}$, i.e. $(u, \possqrt{u^3 + a \mul u + b})$.

Sapling used twisted Edwards curves which have a different equation, but that
is essentially what it did — pick one of the coordinates, and then the equation
in the other is quadratic. It's easy to construct a hash into the field with
low bias using a conventional hash function with a large enough output size, by
taking its output as an integer modulo the field size. Then the mapping above
is bijective, so its output points will be approximately evenly distributed,
although only among *half* of the curve points — the half chosen by the
deterministic $\possqrt{\argument}$.

The problem is that then not all $x$-coordinates, and therefore not all inputs
to the hash, map to a point. For each $x$-coordinate, we have 0, 1, or 2
solutions for $y$ depending on the number of square roots of $x^3 + a \mul x + b$.
Heuristically, roughly half of the $x$-coordinates should have no solutions
for $y$, roughly half of them should have two solutions, and a negligible
proportion (only the case
<span style="white-space: nowrap">$y^2 = 0 = x^3 + a \mul x + b$</span>, which
may not happen at all for a particular curve) have one solution. That is in fact
what happens in practice. If the curve has $N$ points, and
$N$ is odd —as it is for Pallas and Vesta— then the number of
$x$-coordinates that correspond to a point on the curve is exactly $(N - 1)/2$.
The *proportion* that correspond to a point is $(N - 1)/(2 \mul \FieldSize)$,
writing $\FieldSize$ for the number of elements of $\Field$.
The [Hasse bound](https://en.wikipedia.org/wiki/Hasse%27s_theorem_on_elliptic_curves),
$|N - (\FieldSize + 1)| \leq 2\sqrt{\FieldSize}$, makes the
heuristic precise: $(N - 1)/(2 \mul \FieldSize)$ is within
$1/\sqrt{\FieldSize}$ of $\fraction{1}{2}$.

For fixed generators, having a group hash that is not a total function is not
so much of a problem: we can extend it to a total function by repeated hashing with
an index. Since there are only a fixed set of generators and they are found off-line,
non-constant timing due to the variable number of iterations is not an issue.
But Sapling had introduced *diversified addresses*, which require on-line use
of the group hash in order to derive an address from a diversifier. We avoided
timing attacks in Sapling by not doing repeated hashing, and accepting that
only half of all diversifiers would be valid. But we had encountered complications
in the application protocol ([ZIP 32](https://zips.z.cash/zip-0032) and its usage)
due to this abstraction leak from the underlying cryptography. We wanted to avoid
that when designing Orchard.

Fortunately, an Informational RFC for deterministic, constant-time Hashing to
Elliptic Curves was close enough to ready (it was in a
[late draft](https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-10.html),
and in fact did not change significantly before the final version,
[RFC 9380](https://www.rfc-editor.org/rfc/rfc9380.html)). The scheme we analyse
here is that standard, specialized to Pallas and Vesta.

## What 𝑓 looks like

So how does $f$, or as RFC 9380 calls it `map_to_curve`, work? A naive approach
would be to try to "fill in" the other half of the curve points that were missed
by the deterministic square root, using the other half of the $x$-coordinates.
But there is no known way of doing so (in fact, if there were then it would
indicate undesired structure and potential cryptographic weaknesses in the curve).

The basic idea of having two different cases depending on whether a given input
yields solutions for a square root, however, is exactly what RFC 9380's
"[Simplified SWU](https://www.rfc-editor.org/rfc/rfc9380.html#name-simplified-shallue-van-de-w)"
construction does. For now we will ignore a complication that arises for short
Weierstrass curves with $a = 0$, like Pallas and Vesta; we'll get to that in
[its own section](#the-detour-through-an-isogenous-curve). Then, ignoring
negligible cases we have:

$$f(u) = \begin{cases}
  f_1(u),&\textsf{for half of the } u \\
  f_2(u),&\textsf{for the other half.}
\end{cases}$$

The Simplified SWU construction arranges that the two candidate curve-equation
values differ by a nonsquare factor, so exactly one of the two branches is
available for each input $u$. The precise formulas —including how $u$ is
transformed before it becomes an $x$-coordinate— are in CompElliptic's
[`Hashing/SimplifiedSWU.lean`](https://github.com/daira/CompElliptic/blob/main/CompElliptic/Hashing/SimplifiedSWU.lean),
the formalization of the construction.

The actual construction also fixes the sign at the end: the output's
$y$-coordinate is negated if necessary so that its sign matches the sign of the
input, in the convention that RFC 9380 calls `sgn0`. This makes $f$ *odd*, that
is, $f(-u) = -f(u)$ for $u \neq 0$. Oddness carries weight below: it is what
splits an input pair $\{u, -u\}$ across a point and its negation, and the
character-sum analysis relies on it too.

The images of $f_1$ and $f_2$ are not disjoint; for Simplified SWU they in fact
coincide, apart from a negligible proportion of exceptional points. To see why,
fix a target point $P$. Whether any input reaches $P$ via $f_1$ comes down to a
quadratic equation in $t = Z \mul u^2$; the equation depends only on the
$x$-coordinate of $P$, which $P$ shares with $-P$. A solution $t$ yields inputs
precisely when $t/Z$ is a square —that is, when $t$ really is $Z \mul u^2$ for
some input $u$— and then, since $f$ is odd, the input pair $\{u, -u\}$ has one
member mapping to $P$ and the other to $-P$. So each realizable solution
contributes exactly one preimage of $P$. Reaching $P$ via $f_2$ comes down to a
second quadratic in $t$, in the same way. Now, two facts connect the branches:

- $t$ solves the $f_1$-equation exactly when $1/t$ solves the $f_2$-equation;
- $t/Z$ is a square iff $(1/t)/Z$ is, because their product is the square $1/Z^2$.

So input $u$ reaching $P$ via $f_1$ corresponds to the inputs $\pm 1/(Z \mul u)$
reaching $P$ via $f_2$ and vice versa. Hence $P$ is reached via $f_1$ iff it is
reached via $f_2$.

This coexists with the exact halves above because those partition the *inputs*,
not the outputs. The correspondence $u \mapsto \pm 1/(Z \mul u)$ carries the
$f_1$-half of the inputs into the $f_2$-half and back, preserving the point reached.
About $\fraction{3}{8}$ of the output space is reached
—with 2 or 4 preimages per reached point excluding exceptional cases— and
the remaining $\fraction{5}{8}$ by neither map. (These proportions are heuristic;
we confirmed them by
[exact computation on small curves](https://github.com/daira/CompElliptic/blob/main/scripts/check_sswu_small_curves.sage),
and they can be proven
with error $O(1/\sqrt{\FieldSize})$ by counting points on the branch varieties —
Lang–Weil, "Number of Points of Varieties in Finite Fields",
*Amer. J. Math.* 76(4), 1954, [doi:10.2307/2372655](https://doi.org/10.2307/2372655).
A modern exposition of that paper is Tao,
[The Lang-Weil bound](https://terrytao.wordpress.com/2012/08/31/the-lang-weil-bound/),
2012.)

```admonish info title="Where the ⅜ comes from"
Fix a target point and consider the quadratic in $t$ deciding whether it is
reached — the branch-$f_1$ one, say. (The branch-$f_2$ one behaves identically
under $t \mapsto 1/t$.) Two coin flips decide the outcome.

- The quadratic has two roots when its discriminant is a square: probability
  about $\fraction{1}{2}$.
- Given a split, each root $t_i$ yields an input pair $\pm u_i$ exactly when
  $t_i/Z$ is a square. These two events are perfectly correlated, because the
  product $t_1 \mul t_2$ is fixed by the quadratic's coefficients: writing the
  quadratic character $\chi(\argument)$ as $+1$ on nonzero squares and $-1$ on
  nonsquares, we have $\chi(t_1/Z) \mul \chi(t_2/Z) = \chi(t_1 \mul t_2)$.
  That sign is $-1$ about half the time, in which case exactly one root yields
  inputs. It is $+1$ otherwise — then both roots yield inputs or neither does,
  each about half the time.

By oddness, each input pair $\pm u$ contributes one preimage to the target point
and one to its negation. So the point is reached from $2$ preimages (one per
branch) with probability $\fraction{1}{2} \mul \fraction{1}{2} = \fraction{1}{4}$,
and from $4$ preimages (two per branch) with probability
$\fraction{1}{2} \mul \fraction{1}{2} \mul \fraction{1}{2} = \fraction{1}{8}$;
otherwise it is unreached. The reach probability is
$\fraction{1}{4} + \fraction{1}{8} = \fraction{3}{8}$, and reached points have
$\fraction{8}{3}$ preimages on average.
```

It turns out, for the Pasta curves, that we cannot do much better than this
$\fraction{3}{8}$ coverage by mapping directly from a single field element (or
at least, trying to do so would not lead to a less complicated scheme overall,
given other constraints like the desire for a constant-time group hash).

Particular application protocols might actually be perfectly fine with this
kind of non-uniform mapping. However, it can easily be distinguished from a
uniform one, and each of our security arguments would then need to take the
non-uniformity into account separately. That need does not go away entirely;
what we can do is pay for it once, with a concrete figure. So we would like
a mapping that, applied to $\mathsf{hash\_to\_field}$ outputs, can be
distinguished from a uniform mapping onto the whole group only with a
concretely bounded advantage. As we will see, modelling
$\mathsf{hash\_to\_field}$ as a random oracle, that advantage is at most
$q/2^{120}$ after $q$ queries for the mapping we chose.

## The detour through an isogenous curve

Now for the complication we deferred. The formulas of Simplified SWU require
the curve coefficients to satisfy $a \neq 0$ and $b \neq 0$. Pallas and Vesta
both have the curve equation $y^2 = x^3 + 5$, i.e. $a = 0$. This is not by
coincidence; the same Complex Multiplication structure that allows us to
find a cycle of curves is what blocks Simplified SWU from working.

```admonish info title="One symmetry, two effects"
The short Weierstrass form with $a = 0$ corresponds to curves with
$j$-invariant $0$, that is, with Complex Multiplication by $\mathbb{Z}[\zeta_3]$
and an automorphism group of order $6$: there are exactly six invertible mappings
from the curve to itself that preserve the group structure, namely
$(x, y) \mapsto (\zeta_3^k \mul x, \pm y)$. (These stay on the curve because
$x$ appears only cubed, and $(\zeta_3^k)^3 = 1$.)

Daira-Emma Hopwood's ZK Study Club talk
"Optimizing Halo and Constructing Graphs of Elliptic Curves"
([part 1](https://www.youtube.com/watch?v=q7bAYgxkHUE),
[bonus session](https://www.youtube.com/watch?v=IQVGIqcdxL4),
[slides](https://raw.githubusercontent.com/daira/halographs/master/halographs.pdf))
explains why the Pasta curves have this form: the two curves of a 2-cycle
necessarily share their CM discriminant, and with known methods a cycle can only
feasibly be found when that discriminant is tiny (the Pasta search fixed the
smallest, $D = -3$, which is exactly the case $j = 0$). Slides 8 and 9 give a
nice visual form of the argument.

Simplified SWU, for its part, obtains its branch pair by *solving for the
$x$-coordinate* at which the scaling defect

$$g(\lambda x) - \lambda^3 g(x) = a \lambda (1 - \lambda^2) \mul x + b (1 - \lambda^3)$$

vanishes, where $\lambda = Z \mul u^2$. The $x$-coefficient is proportional
to $a$, so on a $j = 0$ curve there is nothing to solve for: every
$x$-scaling is an isomorphism onto a sextic twist, making the defect
constant in $x$, and it vanishes only when the scaling is one of the extra
automorphisms — which $\lambda$, a nonsquare, never is.
```

RFC 9380 (section 6.6.3) resolves this with a detour: run Simplified SWU on
an auxiliary curve with $a \neq 0$ that is *isogenous* to the target. An
isogeny is a mapping from one curve to another, given by rational maps on
the coordinates, that preserves the identity point. In general it need not
be invertible; over the algebraic closure, a degree-$3$ isogeny is
$3$-to-$1$. For Pallas and Vesta, the auxiliary curves are the ones that
the protocol specification and the `pasta_curves` crate call iso-Pallas
and iso-Vesta respectively. Having used Simplified SWU to obtain a point
on the auxiliary curve, we apply the isogeny (here of degree 3; the Pasta
curves were chosen to make the degree as low as possible), in order to land
on the intended curve.

For the analysis on this page the detour is short, at least conceptually.
An isogeny is always a group homomorphism, and for these particular curve
pairs it is a bijection on the rational points. (Isogenous curves have
equally many rational points, and the kernels of these particular isogenies
contain no rational point other than the identity.) A bijective relabelling
of the outputs neither merges nor splits fibres, so the branch structure,
the preimage counts, and the oddness that the character-sum analysis below
relies on, all transport across unchanged. The formalization defines $f$
(`mapToCurve`) as the composition and states the counting theorems directly
on that mapping.

Because the isogeny is a homomorphism, there are two equivalent ways to
compute <span style="white-space: nowrap">$f(u_0) + f(u_1)$:</span>
either by adding the two Simplified SWU outputs on the auxiliary curve and
applying the isogeny once, or by mapping each point across the isogeny and
then adding. The former method is used by RFC 9380 and `hashtocurve.sage`;
the latter by `pasta_curves`. The two orders agree exactly
(`mapHashOutputsToCurve_eq`), so nothing depends on the choice.

Although a correctly constructed isogeny is *always* a homomorphism
(Silverman, *The Arithmetic of Elliptic Curves*, Theorem III.4.8), Mathlib
does not prove that or have the necessary machinery to do so in general.
Instead we prove that the particular rational maps given in the protocol
specification ([§5.4.9.8](https://zips.z.cash/protocol/protocol.pdf#concretegrouphashpallasandvesta))
and `hashtocurve.sage` are bijective (`iso_map_bijective`) and are
homomorphisms (`iso_map_add`). The latter turns out to be quite involved,
requiring a careful choice of coordinates to make it feasible to prove the
necessary identities using Mathlib's `linear_combination` tactic. The
details are explained in `Homomorphism.lean`.

We've now described the deployed construction in full, and established the
motivation for using $H(m) = f(u_0) + f(u_1)$ instead of a mapping from a
single field element. The rest of this page is about why that construction
works, specifically why it can reasonably be modelled as a random oracle.

## Uniformity is not enough

A first guess is that it would suffice for $H$'s outputs to be close to uniform
on $\Group$. We will see from the [regularity](#the-first-ingredient-regularity)
analysis below that this holds. It does not suffice, because $H$ is not a black
box. The function $\mathsf{hash\_to\_field}$ is public: anyone can compute the
intermediate pair $(u_0, u_1)$ and check that $H(m)$ really equals
$f(u_0) + f(u_1)$. A security argument that replaces $H$ by an ideal random
oracle $R$ must survive an adversary that does exactly that. So the question is
not "do $H$'s outputs look uniform?" but "can the *pair* of oracles
$(\mathsf{hash\_to\_field}, H)$ be faked consistently, given only $R$ ?".

## Indifferentiability

Indifferentiability (Maurer–Renner–Holenstein,
[Indifferentiability, Impossibility Results on Reductions, and Applications to the Random Oracle Methodology](https://eprint.iacr.org/2003/161))
makes that question precise. A *simulator* $\Sim$ is given oracle access to the
ideal random oracle $R$, and must answer $\mathsf{hash\_to\_field}$ queries.
A *distinguisher* $\Dist$ talks to two oracles and tries to tell which of two
worlds it is in:

- the **real world** $(\mathsf{hash\_to\_field}, H)$ — the genuine intermediate
  oracle and the genuine construction built on top of it;
- the **ideal world** $(\Sim^R, R)$ — the ideal random oracle $R$ into the
  group, and the simulator faking the intermediate hash consistently with it.

The construction is $(q, \eps)$-**indifferentiable** if some simulator makes
every distinguisher's advantage at most $\eps$ after $q$ queries. The point
of establishing this is the Maurer–Renner–Holenstein composition theorem:
any<sup>†</sup> protocol proven secure with an ideal $R$ in place of the
group hash stays secure with the real $H$ — provided one is content to model
$\mathsf{hash\_to\_field}$ as a random oracle. So indifferentiability is what
lets the rest of the security development treat the group hash as a random
oracle without having to reason about $\mathsf{hash\_to\_field}$ again.

```admonish note title="A heuristic, not an assumption"
Modelling $\mathsf{hash\_to\_field}$ as a random oracle is a *heuristic*, not a
falsifiable hardness assumption. Non-instantiability results (Canetti–Goldreich–Halevi,
[The Random Oracle Methodology, Revisited](https://eprint.iacr.org/1998/011))
show that a scheme can be provably secure in the random-oracle model yet insecure
under every concrete instantiation. So an indifferentiability proof does not
guarantee real-world security on its own; it restricts attention to adversaries
that treat $\mathsf{hash\_to\_field}$ as a black box, which is where analytical
effort is most useful to spend. The [Security Models](security-models.md) page
develops this framing.

<span id="dagger-note"></span>† The "any" has a shape requirement: the
protocol's security game —challenger, adversary, and win condition
together— must fold into a single
distinguisher talking to the two oracles, as the games in this development
do. Composition can genuinely fail for definitions that restrict the state
shared between the stages of an adversary (Ristenpart–Shacham–Shrimpton,
[Careful with Composition: Limitations of Indifferentiability and Universal Composability](https://eprint.iacr.org/2011/339)).
The boundary is made precise, as a restriction on the memory available to
the simulator, in Demay–Gaži–Hirt–Maurer,
[Resource-Restricted Indifferentiability](https://eprint.iacr.org/2012/613).
```

## The simulator is forced

The consistency check above pins down what the simulator must do. On a query $m$
it learns $Q = R(m)$, a uniform group element, and it must return a pair
$(u_0, u_1)$ with

$$f(u_0) + f(u_1) = Q,$$

because the distinguisher can and will check that equation. Moreover the pair
must *look* like a fresh $\mathsf{hash\_to\_field}$ output, i.e. uniform — so the
simulator must return a preimage of $Q$ that is close enough to uniform under the
two-term sum. Following the proof of Theorem 1 of Brier–Coron–Icart–Madore–Randriam–Tibouchi
([Efficient Indifferentiable Hashing into Ordinary Elliptic Curves](https://eprint.iacr.org/2009/340)),
specialized to this construction, two ingredients make this possible.

### The first ingredient: regularity

For uniform $(u_0, u_1)$, the distribution of $f(u_0) + f(u_1)$ is close to
uniform on $\Group$. CompElliptic's `TwoTermUniformity` proves this from a
Weil bound on the character sums of $f$.

A *character* of $\Group$ is a homomorphism $\psi \typecolon \Group \to \Cmul$
into the nonzero complex numbers: it turns the group operation into ordinary
multiplication, $\psi(P + Q) = \psi(P) \mul \psi(Q)$, and its values lie on the unit
circle. The *character sum* of $f$ at $\psi$ is

$$S(\psi) = \sum_{u \in \Field} \psi(f(u)),$$

the character added up over all outputs of $f$. The trivial character
$\psi \equiv 1$ gives $S(\psi) = \FieldSize$; a *Weil bound* bounds the
absolute value $|S(\psi)|$ at the nontrivial characters, from which such
character-sum bounds follow. The name "Weil bound" is from André Weil's
proof of the Riemann hypothesis for algebraic curves over finite fields
([Sur les courbes algébriques et les variétés qui s'en déduisent](http://denise.vella.chemla.free.fr/Weil-courbes-varietes.pdf), 1948).
A modern presentation of the elliptic-curve case is Kohel–Shparlinski,
[On Exponential Sums and Group Generators for Elliptic Curves over Finite Fields](https://www.i2m.univ-amu.fr/perso/david.kohel/pub/character.pdf), *ANTS-IV*, *LNCS* 1838, 2000.

Character sums measure uniformity because a distribution on $\Group$ is uniform
exactly when all its nontrivial character sums vanish — so small nontrivial
character sums mean close to uniform. That is what lets a Weil bound control
the *regularity distance*

$$\sum_{Q} \left| \frac{\mathsf{pairCount}\, f\, Q}{(\FieldSize)^2} - \frac{1}{\GroupSize} \right| \le \beta,$$

where $\mathsf{pairCount}\, f\, Q$ counts the pairs $(u_0, u_1)$ with
$f(u_0) + f(u_1) = Q$ — the size of the *fibre* of $Q$. Dividing by
$(\FieldSize)^2$ turns the count into the probability that the two-term sum lands
on $Q$, so the sum is the $L^1$ distance between that output distribution and the
uniform distribution on $\Group$. The *$L^1$ distance* between two distributions
$\mu$ and $\nu$ on a finite set is $\sum_x |\mu(x) - \nu(x)|$, the total of the
absolute differences of the probabilities they assign. $\beta$ will be calculated
in the next section.

```admonish info title="Characters, for readers who know the DFT"
The DFT analyses a signal on $\mathbb{Z}/N$ against the reference waves
$a \mapsto e^{2\pi i \mul ka/N}$, one per frequency $k$. What makes those
waves work is not anything analytic about the exponential — it is the
identity
$e^{2\pi i \mul k(a+b)/N} = e^{2\pi i \mul ka/N} \mul e^{2\pi i \mul kb/N}$,
which turns addition of signal positions into multiplication of wave values.
A character keeps exactly that property and discards the rest. For
$\mathbb{Z}/N$ the characters are precisely the $N$ reference waves of the
DFT; for a general finite abelian group there are exactly as many characters
as group elements, and they support the same Fourier toolkit — in particular
*orthogonality* (a nontrivial wave sums to zero over a full period) and
*Parseval* (total energy is the same in the signal and frequency domains).
Curve points under point addition are a finite abelian group, so all of this
applies to them directly; no geometry enters.

The regularity proof is then the standard DFT pipeline for a convolution:
the distribution of $f(u_0) + f(u_1)$ for independent uniform $u_0, u_1$ is
the convolution of two copies of the distribution of $f(u)$, and convolution
in the signal domain is multiplication in the frequency domain, so the
transform of $\mathsf{pairCount}\, f$ at frequency $\psi$ is the *square*
$S(\psi)^2$ — just as convolving a signal with itself squares its spectrum.
The Weil bound says every nontrivial frequency is small; squaring, Parseval,
and <span style="white-space: nowrap">Cauchy–Schwarz</span> then yield the
regularity distance.
```

#### Calculating the Weil constant

The regularity distance is proved relative to the named hypothesis `WeilBounded`.
That hypothesis is parameterized: it asserts a constant $C$ with every nontrivial
character sum of the zero-repaired mapping at most $C \mul \sqrt{\FieldSize}$,
and the final advantage scales with $C^2$.

The formalization
([`sum_abs_prob_dev_le`](https://github.com/daira/CompElliptic/blob/main/CompElliptic/Hashing/TwoTermUniformity.lean))
bounds the regularity distance of the previous section by any budget
$\beta$ whose square dominates
<span style="white-space: nowrap">$\frac{(\GroupSize - 1) \mul C^4}{(\FieldSize)^2}$ —</span>
that is, any $\beta$ just above $\frac{C^2 \mul \sqrt{\GroupSize}}{\FieldSize}$.

That expression is the
[aside](#admonition-characters-for-readers-who-know-the-dft)'s pipeline,
made quantitative. The two-term
spectrum at $\psi$ is $S(\psi)^2$, so each of the $\GroupSize - 1$ nontrivial
frequencies has spectral energy at most $(C^2 \mul \FieldSize)^2$. Parseval
turns total spectral energy into the summed squared deviation of the pair
counts, divided by $\GroupSize$; <span style="white-space: nowrap">Cauchy–Schwarz</span>
bounds the square of an $L^1$ sum by $\GroupSize$ times the sum of squares,
cancelling the $\GroupSize$ quotient; and normalizing counts to probabilities
divides by $(\FieldSize)^4$ — leaving
$\frac{(\GroupSize - 1) \mul C^4}{(\FieldSize)^2}$.

At the deployed sizes $\FieldSize \approx \GroupSize \approx 2^{254}$ and
$C = 21/2$ (see below), yielding $\beta \approx 2^{-120}$.

The Weil bound places a bound on character sums along covering curves of the
encoding, once $C$ is calculated via a per-encoding genus computation. Proving
this result in general requires machinery that is not yet in Mathlib, which is
why the hypothesis is named rather than discharged; that is where the deep
number theory lives.

The calculation of the constant $C$ for a specific encoding and curves, on the
other hand, is relatively straightforward. For example,
[Farashahi–Fouque–Shparlinski–Tibouchi–Voloch](https://eprint.iacr.org/2010/539)
carry out this calculation for a sibling of the deployed encoding —simplified SWU
with $Z = -1$, over fields of size $\equiv 3 \pmod 4$, with a quadratic-residue
sign rule— and obtain $|S(\chi)| \le 52 \mul \sqrt{\FieldSize} + 151$ from genus-8
coverings.

The deployed variant differs in all three parameters. The Weil bound for both
Pallas and Vesta has been calculated as $|S(\chi)| \le 10\sqrt{\FieldSize} + 1$
from genus-6 coverings (see zcash/pasta's
[`weilbound.sage`](https://github.com/zcash/pasta/blob/master/weilbound.sage)).
This is where the deployed $C = 21/2$ comes from: the hypothesis wants
$|S(\chi)| \le C \mul \sqrt{\FieldSize}$, and the extra half over the $10$
absorbs the trailing $+ 1$. In square-root-free form this is
$(10\sqrt{\FieldSize} + 1)^2 \le (21/2)^2 \mul \FieldSize$, which holds at the
deployed sizes with margin about $2^{126}$.

The calculation of $C$ is proven on paper in CompElliptic's
[`design/weil-constant-derivation.md`](https://github.com/daira/CompElliptic/blob/main/design/weil-constant-derivation.md),
modulo results cited as established mathematics. It is also formalized,
down to Weil's theorem at the two branch covers, in CompElliptic's
[`Hashing/BranchCovers.lean`](https://github.com/daira/CompElliptic/blob/main/CompElliptic/Hashing/BranchCovers.lean)
and [`Hashing/WeilInstance.lean`](https://github.com/daira/CompElliptic/blob/main/CompElliptic/Hashing/WeilInstance.lean).
The per-cover inputs are
$|S_{C_j}(\chi)| \le (2 \mul 6 - 2) \mul \sqrt{\FieldSize}$ — the analogous
sums over the rational points of the two branch coverings, stated in
square-root-free form. Everything between those inputs and the deployed
`WeilBounded` instances is machine-checked. The paper proof's own checkable
inputs are also machine-checked (CompElliptic's
[`Hashing/WeilSupport.lean`](https://github.com/daira/CompElliptic/blob/main/CompElliptic/Hashing/WeilSupport.lean)),
and the design doc cites each proven fact at its point of use, with CI
keeping the references exact. Weil's theorem itself stays the cited input:
even stating it needs vocabulary (genus, places, covers of curves) that
Mathlib does not yet have. That vocabulary is tracked at
[CompElliptic#30](https://github.com/daira/CompElliptic/issues/30).

### The second ingredient: preimage sampling

For each $Q$, the simulator must sample a pair uniformly from the fibre
$\{(u_0, u_1) \mid f(u_0) + f(u_1) = Q\}$. Sampling one coordinate is easy: draw
$u_0$ uniformly. Then the second coordinate must satisfy $f(u_1) = Q - f(u_0)$,
so $u_1$ ranges over the preimages of $Q - f(u_0)$ under the single map $f$.
That single-term fibre has at most a constant number of elements — we saw in
the "[Where the ⅜ comes from](#admonition-where-the-⅜-comes-from)" note above
that each point has at most $4$ nonzero preimages under $f$, and
CompElliptic's `card_mapToCurve_fibre_le` proves the weaker but sufficient
bound of $10$, again counting nonzero preimages.

Care is needed to make the *pair* uniform on the fibre. Drawing $u_1$
uniformly from the preimages of $Q - f(u_0)$ would over-weight the pairs
whose preimage set is small: the pair's probability would be
$\frac{1}{\FieldSize \mul c}$ with $c$ the size of its preimage set,
and $c$ varies across the fibre. So the simulator instead fixes a bound
$d$ on the preimage counts and draws a slot index $0 \leq j < d$ uniformly,
alongside $u_0$. If the preimage set of $Q - f(u_0)$ has an element with
index $j$, the round accepts the pair $(u_0, u_1)$ with $u_1$ that element;
otherwise it rejects, and the simulator redraws both $u_0$ and $j$. In
particular an empty preimage set always rejects. Now every pair of the
fibre consistent with $u_0$ is accepted in a round with the same
probability $\frac{1}{\FieldSize \mul d}$, whatever the size of its
preimage set, so conditional on acceptance the pair is exactly uniform on
the fibre. The bound $d$ also controls the cost: a round accepts with
probability $\frac{\mathsf{pairCount}\, f\, Q}{\FieldSize \mul d}$, about
$1/d$ for typical $Q$, so few rounds are needed. This is the rejection
sampler whose costs and output law `Simulator.lean` proves, instantiated
at the deployed mappings at the constant `deployedFibreBound = 11` — the
bound of $10$ for nonzero preimages, plus one for the input $0$.

## The single-query bias, in detail

This is the part the formalization currently establishes, in
`Zcash/Security/GroupHash/Sampler.lean`, and it is the technical heart of the
argument. It compares the two worlds on a *single* fresh query, before worrying
about how queries compose.

### Two per-query laws

On a fresh query, the distinguisher observes a pair in
$\Field \times \Field$ (from which the group element is a fixed
function). Each world draws that pair from a distribution:

- **real**: the pair is uniform on $\Field \times \Field$ — this is
  $\mathsf{hash\_to\_field}$ answering honestly (`PMF.uniformOfFintype`);
- **ideal**: draw a uniform group element $Q$, then draw a pair uniformly from
  the fibre of $Q$ (`idealLaw`, the `bind` of the uniform law on $\Group$
  with the fibre sampler).

### The fibre sampler and its fallback

`fibreSampler f Q` samples a pair uniformly from the fibre of $Q$. One subtlety:
the two-term sum need not be surjective, so some $Q$ have an *empty* fibre, with
no pair to return. On those, the sampler falls back to a uniform pair on
$\Field \times \Field$, which keeps it a genuine distribution. The fallback's
only effect is on the bias, where it is accounted for exactly.

### The bias reduces to the regularity distance

The claim, in each direction, is that the law in each world *overshoots* that
of the other world by at most $\beta$: for every test $w$ valued in $\closedrange{0}{1}$,
$\sum_x \mu(x)\, w(x) \le \sum_x \nu(x)\, w(x) + \beta$. This one-sided form
(`PMFWeightedBiasLE`) is what the query-composition step needs.

To bound it, regroup the per-pair difference by the group element
$Q = f(u_0) + f(u_1)$. Take a nonempty fibre of $Q$, with
$k = \mathsf{pairCount}\, f\, Q \ge 1$ pairs. Every pair in it looks identical
in both worlds:

- the ideal world puts $\frac{1}{\GroupSize \mul k}$ on each pair — it spreads
  the $\frac{1}{\GroupSize}$ that $R$ gives to $Q$ uniformly over the $k$ pairs;
- the real world puts $\frac{1}{(\FieldSize)^2}$ on each pair.

So the absolute difference is one constant across all $k$ pairs of the fibre,
and summed over the fibre it is

$$k \mul \left| \frac{1}{\GroupSize \mul k} - \frac{1}{(\FieldSize)^2} \right| = \left| \frac{1}{\GroupSize} - \frac{k}{(\FieldSize)^2} \right|,$$

a single term of the regularity distance. The $k$ cancels inside the first
fraction. The fibre size enters only as $\mathsf{pairCount}\, f\, Q$ in that
term, which is identical for every nonempty fibre — the ideal-world law is
uniform *within* the fibre whatever its size, so all $k$ pairs share one
probability. Summing over the nonempty fibres gives the part of the regularity
distance with $\mathsf{pairCount}\, f\, Q > 0$.

### Why both directions come out at the same $\beta$

The empty fibres require our attention in one direction only.

When the **real** law overshoots the ideal one, the fallback only *raises* the
ideal law's probabilities, which shrinks $\text{real} - \text{ideal}$. So this
direction is bounded by the nonempty part of the regularity distance alone.

When the **ideal** law overshoots the real one, the fallback contributes a
*fallback mass* $\frac{e}{\GroupSize}$, spread over all pairs, where $e$ is the
number of group elements the two-term sum misses — the mass $R$ sends to those
missed elements. That mass is exactly the empty-fibre part of the *same*
regularity distance: an empty fibre has $\mathsf{pairCount}\, f\, Q = 0$, so
its term is $\left| 0 - \frac{1}{\GroupSize} \right| = \frac{1}{\GroupSize}$, and
there are $e$ of them, totalling $\frac{e}{\GroupSize}$. So the nonempty part
and the fallback mass together are the *whole* regularity distance
$\sum_Q \left| \frac{\mathsf{pairCount}\, f\, Q}{(\FieldSize)^2} - \frac{1}{\GroupSize} \right| \le \beta$.
The fallback fills in the terms the nonempty part left out, and the bound stays
at $\beta$.

## From one query to many

A single-query bound does not immediately bound a distinguisher that makes many
adaptive queries — later queries may depend on earlier answers. The adaptive
hybrid `runFreshPMF_eventBiasLE` (in `Zcash/Common/Oracle/`) bridges the
gap: it charges the one-squeeze bias once per query node, so a $q$-query tree
turns a single-query bias $\beta$ into an overall bias of at most $q \mul \beta$,
even when the query tree is fully adaptive. Repeated queries to the same point
are first collapsed by `dedup`, so a point asked twice keeps one answer rather
than drawing a fresh one.

## What is proved, and what is modelled

It's important to be precise about the status of each part.

- **Formalized and machine-checked.** The regularity distance
  (`TwoTermUniformity`, conditional on the Weil bound), the single-term fibre
  bound (`card_mapToCurve_fibre_le`), the single-query bias in both
  directions (`Sampler.lean`), its composition into the full
  distinguisher-advantage bound at the deployed mappings (`Indiff.lean`),
  the collapse of the two-oracle game onto that one-oracle form
  (`TwoOracle.lean`), and the rejection-sampling simulator — its round-count
  laws, its output law's distance to the fibre sampler, and the composition
  with the simulator as the exhibited ideal-world witness (`Simulator.lean`
  and the capped section of `Indiff.lean`).
- **An unformalized mathematical input.** The regularity distance rests on
  Weil's theorem at the two branch covers — the `CharSumBounded` inputs
  discussed in [Calculating the Weil constant](#calculating-the-weil-constant).
  The bound calculation between those inputs and the endpoints is
  machine-checked; the inputs themselves are cited — stating them needs
  function-field vocabulary that Mathlib does not yet have
  ([CompElliptic#30](https://github.com/daira/CompElliptic/issues/30)).
- **A modelling choice, not a theorem.** That $\mathsf{hash\_to\_field}$ behaves
  like a random oracle is a heuristic (see
  [the note above](#admonition-a-heuristic-not-an-assumption)). The
  indifferentiability argument is what makes that heuristic transfer from
  $\mathsf{hash\_to\_field}$ to the group hash $H$; it does not remove it.

## Conclusion

The question this page set out to answer is: "can we formally justify modelling
the deployed group hash as a random oracle into the curve group, given that
$\mathsf{hash\_to\_field}$ is so modelled?" The formalization now carries
the whole argument, machine-checked at the deployed Pallas and Vesta
instances.

A distinguisher that makes $q$ queries, and sees both the field-element
hash and the group hash built from it, can tell the real construction from
a random oracle with advantage at most $q/2^{120}$
(`pallas_indiffFromRO`, `vesta_indiffFromRO`, via the two-oracle collapse
`twoOracleIndiffFromRO`). The only unformalized mathematical input is
Weil's theorem at the two branch covers, discussed above. The $2^{-120}$
budget absorbs the regularity distance, about $2^{-120.2}$ (the arithmetic
is at the end of
[the regularity section](#the-first-ingredient-regularity)), and the
zero-repair transport $4/\FieldSize$, roughly $2^{-252}$.

The ideal world in that statement is played by a simulator, and the
simulator is a real algorithm, not just a distribution: it hashes once,
then rejection-samples a preimage pair, giving up after $K$ rounds. Its
cost is pinned down exactly — the chance that it is still running after
$k$ rounds decays geometrically. The answers it returns differ from the
idealized ones by at most $(1 - \mathsf{acceptProb})^K$ per query, where
$\mathsf{acceptProb}$ is a round's chance of accepting, so the cap $K$
makes that difference as small as desired. The indifferentiability
statement holds with this algorithmic simulator in place of the idealized
one, at the cost of that same per-query term
(`pallas_indiffFromROCapped`, `vesta_indiffFromROCapped`), conditional
on the Weil bound hypothesis.

Two things remain, both tracked in issues:

* The Weil bound rests on a cited input: Weil's theorem at the two branch
  covers. The calculation from that input to the deployed constant is
  formalized, and so are the paper proof's supporting facts
  (CompElliptic's [`Hashing/WeilSupport.lean`](https://github.com/daira/CompElliptic/blob/main/CompElliptic/Hashing/WeilSupport.lean)) — the delivered scope of
  [CompElliptic#28](https://github.com/daira/CompElliptic/issues/28).
  The input's own statement needs function-field vocabulary (genus,
  places, covers) that Mathlib does not yet have, tracked at
  [CompElliptic#30](https://github.com/daira/CompElliptic/issues/30).
* The security games that want to use this result need the group hash
  added to their adversary's interface first
  ([#188](https://github.com/zcash/ironwood/issues/188)). The composition
  requirement for multi-stage games (the [† note above](#dagger-note))
  applies at each consumption site.

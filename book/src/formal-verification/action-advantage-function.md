# Reading the Security Bound

> **Bottom line:** within the formal model, breaking the knowledge soundness of the
> deployed Action verifier is —up to a small statistical error— at least as hard as
> solving Vesta discrete log: the reduction turns every covered attack into a DLOG
> solver with comparable resources. The benchmark therefore remains Vesta DLOG, whose
> best known classical attacks have an expected-work scale of about $2^{126}$ group
> operations. This is conventionally summarized as a 126-bit headline security level
> for Vesta DLOG. At the certified profile, the constructed solver uses less than
> twice the attacker's group-work budget, giving this claim a conservative 125-bit
> computational-work headline; the advantage function below is the precise statement.

Here “knowledge soundness” means that whoever produced an accepted proof must know a
valid *witness*: the private data that justifies the proved statement. The extractor
computes the witness from the prover's declared group-element representations, not
from the proof alone. “Covered” means inside
the theorem's scope: an adversary that stays within the resource budgets below, supplies
a representation for every group element it outputs, and faces Fiat–Shamir challenges
modelled as a random oracle. The game also samples the verifier's fixed bases; the
deployed, baked-in list inherits the result through the fixed-bases argument in
[Security Models](security-models.md#fixed-bases-the-group-hash-and-the-reference-string).

## For experts

For a bundle containing $n$ Actions and an adversary $A$ making at most $q$
random-oracle queries and performing at most $g$ Vesta group operations, the reduction
gives

$$
\Prob{\text{verifier accepts but extraction fails}}
\;\le\;
\operatorname{Adv}_{\mathrm{DLOG}}
  \bigl(q+22,\,g+R(n)\bigr)
+ \varepsilon_{\mathrm{stat}}(q,n).
$$

**$\operatorname{Adv}_{\mathrm{DLOG}}(q,g)$ is the advantage function**: for query budget
$q$ and group-operation budget $g$, the externally supplied upper bound on the success probability
of a Vesta DLOG solver.

**$\varepsilon_{\mathrm{stat}}(q,n)$ is the statistical soundness error**: it collects
the non-DLOG statistical terms, including exceptional random challenges that prevent
extraction and the random-URS binding term, for an adversary making at most $q$ oracle
queries against a bundle containing $n$ Actions.

**Direction of the reduction:**

> Action attacker $A$ using $q$ queries and $g$ group operations
> $\longrightarrow$ reduction adds 22 queries and $R(n)$ group operations
> $\longrightarrow$ Vesta DLOG solver using $q+22$ queries and $g+R(n)$ group operations.

The reduction constructs the DLOG solver by running the Action attacker and processing
its output. $R(n)$ is the extra Vesta group work it performs for a bundle containing $n$
Actions — reduction overhead, not attacker work or a probability loss. For the deployed
Action specialization, the reduction also makes 22 oracle queries beyond those made by
the attacker.

For the certified consensus profile, $q\le 2^{123}$, $g\le 2^{125}$,
$R(n)\le 2^{123}$, and $\varepsilon_{\mathrm{stat}}(q,n)\le 2^{-83}$. The exact bound is

$$
\Prob{\text{failure}}
\;\le\;
\operatorname{Adv}_{\mathrm{DLOG}}
  \bigl(2^{123}+22,\,2^{125}+2^{123}\bigr)
+2^{-83}.
$$

Rounding the solver budgets up to powers of two gives the simpler endpoint

$$
\Prob{\text{failure}}
\;\le\;
\operatorname{Adv}_{\mathrm{DLOG}}
  \bigl(2^{124},\,2^{126}\bigr)
+2^{-83}.
$$

Here $2^{125}$ is the covered Action-attacker work budget. The reduction turns it into at
most $2^{125}+2^{123}\approx 2^{125.32}$ solver work, giving Action a conservative 125-bit
computational-work headline. The $2^{126}$ in the endpoint is only its rounded ceiling.
Separately, Vesta itself has a [headline 126-bit DLOG security level](https://electriccoin.co/blog/the-pasta-curves-for-halo-2-and-beyond/);
the matching number has a different origin. [Security Models](security-models.md) gives
the full coverage-parameter interpretation.

## In plain language

Outside the statistical soundness error, a covered knowledge-soundness attack would
imply a DLOG break with the resources shown above. No easier protocol-specific computational term
remains in the bound.

The advantage function says more than any single “security-bit target” could: for any
query and work budgets, it tells experts exactly where to evaluate their preferred Vesta
DLOG estimate.

## Reading the work curve

Choose an amount of Action-attacker group work on the horizontal axis, trace upward to the
orange curve, and then read the corresponding computational-success scale on the vertical
axis. The curve shifts the idealized Vesta DLOG reference by the reduction's conservative
one-bit work loss. Its marked scale is therefore the headline for this claim: about $2^{125}$
group operations, derived from Vesta's 126-bit DLOG headline.

The graph shows only group work. The oracle-query budget $q$ remains a separate input in
the equation above, and the statistical term is not plotted. The exact advantage function,
not this illustration, is the security claim.

<figure class="advantage-figure">
<svg class="advantage-chart" viewBox="0 0 840 500" role="img" aria-labelledby="advantage-chart-title advantage-chart-desc">
  <title id="advantage-chart-title">Reduction-adjusted computational work scale for Action</title>
  <desc id="advantage-chart-desc">A log-log illustration obtained by shifting the idealized Vesta discrete-log work curve by the reduction's conservative one-bit work loss. The marked Action computational-work headline is near two to the 125 group operations. This illustration is not a proved upper bound on the advantage function.</desc>
  <g class="advantage-grid">
    <line x1="92" y1="42" x2="780" y2="42" />
    <line x1="92" y1="123" x2="780" y2="123" />
    <line x1="92" y1="204" x2="780" y2="204" />
    <line x1="92" y1="285" x2="780" y2="285" />
    <line x1="92" y1="366" x2="780" y2="366" />
    <line x1="92" y1="432" x2="780" y2="432" />
    <line x1="92" y1="42" x2="92" y2="432" />
    <line x1="242" y1="42" x2="242" y2="432" />
    <line x1="391" y1="42" x2="391" y2="432" />
    <line x1="541" y1="42" x2="541" y2="432" />
    <line x1="690" y1="42" x2="690" y2="432" />
    <line x1="780" y1="42" x2="780" y2="432" />
  </g>
  <g class="advantage-axes">
    <line x1="92" y1="42" x2="92" y2="432" />
    <line x1="92" y1="432" x2="780" y2="432" />
  </g>
  <g class="advantage-labels">
    <text x="80" y="46" text-anchor="end">1</text>
    <text x="80" y="127" text-anchor="end">2⁻²⁰</text>
    <text x="80" y="208" text-anchor="end">2⁻⁴⁰</text>
    <text x="80" y="289" text-anchor="end">2⁻⁶⁰</text>
    <text x="80" y="370" text-anchor="end">2⁻⁸⁰</text>
    <text x="80" y="436" text-anchor="end">2⁻⁹⁶</text>
    <text x="92" y="454" text-anchor="middle">2⁸⁰</text>
    <text x="242" y="454" text-anchor="middle">2⁹⁰</text>
    <text x="391" y="454" text-anchor="middle">2¹⁰⁰</text>
    <text x="541" y="454" text-anchor="middle">2¹¹⁰</text>
    <text x="690" y="454" text-anchor="middle">2¹²⁰</text>
    <text x="780" y="454" text-anchor="middle">2¹²⁶</text>
    <text x="436" y="486" text-anchor="middle">Action attacker group operations</text>
    <text transform="translate(20 237) rotate(-90)" text-anchor="middle">computational success scale</text>
  </g>
  <polyline class="advantage-rho" points="92,409 242,328 391,247 481,198 541,166 690,84 735,60 765,46 780,43" />
  <circle class="advantage-break-point" cx="765" cy="46" r="6" />
  <line class="advantage-break-callout" x1="759" y1="55" x2="706" y2="238" />
  <text class="advantage-break-label" x="700" y="256" text-anchor="end">Action knowledge-soundness security</text>
  <text class="advantage-break-label" x="700" y="275" text-anchor="end">≈ 2¹²⁵ work</text>
</svg>
<figcaption>The orange line is the idealized Vesta DLOG work curve shifted by the reduction's conservative one-bit work loss. It illustrates the claim's 125-bit computational-work headline; it is not a proved upper bound on <code>Adv_DLOG</code>. The equations above are the precise claim.</figcaption>
</figure>

Lean proves the adversary-to-DLOG reduction, its resource transformation, and the
statistical soundness error. The numerical DLOG estimate comes from external
cryptanalysis.

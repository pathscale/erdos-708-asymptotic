#set page(
  paper: "us-letter",
  margin: (left: 0.95in, right: 0.95in, top: 0.9in, bottom: 0.9in),
  numbering: "1",
)
#set document(
  title: "Whole-Cofactor Peeling, Extreme-Point LP Rank Rounding, and Shifted-Interval Hinge Duality for Erdős Problem 708",
  author: "C. Bergström",
)

#set text(font: "Libertinus Serif", size: 10.3pt, hyphenate: false)
#set par(justify: true, leading: 0.62em, spacing: 0.8em)
#set heading(numbering: "1.")
#show heading: set block(above: 1.2em, below: 0.6em, sticky: true)
#show raw.where(block: false): it => text(size: 9.4pt, font: "DejaVu Sans Mono", it.text.replace("_", "_\u{200b}"))

#let pmod(m) = $space ("mod" #m)$
#let ZZ = $bb(Z)$
#let RR = $bb(R)$
#let prod = math.product
#let lcm = math.op("lcm")

#align(center)[
  #set par(justify: false)
  #text(size: 14pt, weight: "bold")[
    Whole-Cofactor Peeling, Extreme-Point LP Rank Rounding, and \
    Shifted-Interval Hinge Duality for Erdős Problem 708
  ]
  #v(0.5em)
  #text(size: 11pt, weight: "semibold")[C. Bergström]
  #v(0.15em)
  #text(size: 9.8pt)[24x AI Research]
  #v(0.14em)
  #text(size: 9pt)[ORCID: `0009-0008-7153-1817`]
  #v(0.18em)
  #text(size: 9.5pt)[November 2026]
]

#v(0.65em)
#pad(x: 1.8em)[
  #text(weight: "bold")[Abstract.]
  Let $A subset.eq ZZ_(>= 2)$ be a set of $n$ integers with maximum $M$. Let $g(n)$ be the smallest integer such that every interval of length $M$ contains a subset $B$ of size at most $g(n)$ whose product is divisible by the product of all elements in $A$. Erdős and Surányi proved that $g(n)$ is at least $(2 - o(1)) n$ in 1959. Erdős later posed the question of whether $g(n) <= (2 + o(1)) n$. Previous methods, such as those by Chen, established bounds of $g(n) <= 11 n$, but these methods incur a $+2 n$ large-prime rounding surcharge in the intermediate interval regime. We eliminate this surcharge by combining whole-cofactor cumulative-GCD peeling, smooth extreme-point linear-programming rounding, and shifted-interval hinge inequalities. We establish an unconditional bound of $g(n) <= (56501 / 6400 + o(1)) n approx 8.83 n$ (and $g(n) <= 10 n$ for all $n >= 1","446$), reducing the asymptotic upper bound by approximately 20% compared to previous work, alongside a self-contained $tau(A, I) <= 3 n$ bound for $M >= 9 n^2$ and a universal vertex-saving bound for semiprime multigraphs.
]

= Introduction and Reduction Architecture

For a finite set $A = {a_1 < dots < a_n} subset.eq ZZ_(>= 2)$ with $M = a_n$ and an interval $I = {x + 1, dots, x + M}$ ($x in ZZ_(>= 0)$), write $D_p (A) := sum_(a in A) v_p (a)$. Define the product-cover number and its fractional relaxation by
$ tau(A, I) := min { |B| : B subset.eq I, space prod_(a in A) a divides prod_(b in B) b }, quad g(n) := sup_(|A| = n, space x >= 0) tau(A, I), $
and
$ tau^*(A, I) := min { sum_(b in I) x_b : x in [0, 1]^I, space forall p <= M, space sum_(b in I) v_p (b) x_b >= D_p (A) }. $

Erdős and Surányi @erdossuranyi59 proved $g(3) = 4$ and $g(n) >= (2 - o(1)) n$ via semiprime cliques $A = {p_i p_j : 1 <= i < j <= ell}$ at $M asymp n ln^2 n$. In @erdos92c @erdos95, Erdős asked whether $g(n) <= (2 + o(1)) n$ (Problem 708 in @bloom708). A companion preprint @bergstrom26small resolves the exact small-$n$ values $g(4) = 5$, $g(5) = 6$, and $g(6) = 8$, and establishes $g(7) >= 9$ and $g(8) >= 11$. For general $n$, Chen @chen26 proved $tau(A, I) <= 2 n$ for $M >= 8 n^3$ ($3 n$ for $M >= 9 n^2$), and established for every $M >= 1$, shifted interval $I = {x + 1, dots, x + M}$ ($x >= 0$), and prime-weight vector $w = (w_p)_(p <= M) in [0, 1]^({p <= M})$ (writing $X_w (m) := sum_(p <= M) v_p (m) w_p$) the unconditional shifted-interval hinge inequality
$ sum_(m = 1)^M (X_w (m) - c)_+ <= sum_(b in I) (X_w (b) - 1)_+ $
at $c = 56501 / 6400$ (implying $g(n) <= 11 n$) and, formalized end to end in Lean 4, at $c = 97 / 10$ (implying $g(n) <= 12 n$), while noting two obstacles.

1. _Large-prime rounding surcharge ($4 n$ barrier)._ Vertex rounding on all of $A$ for $M < 9 n^2$ incurs up to $|P(A)| <= n + pi(3 n)$ fractional variables from primes $> M^(1 / 2)$ and primes $<= 3 n$. That route gives $g(n) <= ceil(c n) + 2 n$ (and $(c + 1 + o(1)) n$ asymptotically) and cannot drop below $4 n$ because $(H_c)$ fails whenever $c < 2$.
2. _Cross-scale coupling below $M = 8 n^3$._ Uncoupled prime-tier splitting $tau(A, I) <= tau(D|_(T_1), I) + tau(D|_(T_2), I)$ exceeds $2 n$ across $M < n^3$. Remark 7 exhibits a cross-tier family $A = {r_k p_k q_i}$ where uncoupled splitting costs $(7 / 3 - o(1)) n$.

Whole-cofactor peeling and smooth vertex rounding remove the first obstacle across $2 n < M <= c^2 n^2$ by keeping $|P(A_"sm")| <= pi(Q_n - 1) = o(n)$ and peeling $A_"hi"$ in $<= 2 |A_"hi"| - 1$ picks. Removing the $+2 n$ surcharge lowers $g(n)$ unconditionally to $(56501 / 6400 + o(1)) n$ ($g(n) <= 10 n$ for $n >= 1","446$) and reduces $M <= 4 n^2$ directly to $(H_2)$. Sections 2 and 4 resolve the $q > M^(1 / 2)$ and semiprime-multigraph cases of the second obstacle.

*Proposition 1 (Short-interval closure $M <= 2 n$).* For every $n$-set $A subset.eq ZZ_(>= 2)$ with $M = max(A) <= 2 n$ and every $I = {x + 1, dots, x + M}$ ($x >= 0$), $tau(A, I) <= M <= 2 n$.

_Proof._ Because $binom(x + M, M) = (prod_(b in I) b) / M! in ZZ$ @hardywright08 and $prod_(a in A) a divides M!$, the full interval $B = I$ covers $A$ with $|B| = M <= 2 n$. $square$

= Whole-Cofactor Peeling via Incremental Cumulative-GCD

This section peels every element carrying a prime factor $q >= Q$ together with its smooth cofactor at $< 2$ picks per element.

*Lemma 2 (Incremental Cumulative-GCD Extension).* Let $I$ be an interval of $M$ consecutive positive integers, let $B_0 subset.eq I$ satisfy $H_0 divides prod_(u in B_0) u$ for some integer $H_0 >= 1$, and let $h in {1, dots, M}$. If $gcd(H_0, h) <= floor(M / (|B_0| + 1))$, then there exists $b in I without B_0$ such that $H_0 h divides b prod_(u in B_0) u$.

_Proof._ Since $1 <= h <= M$, the interval $I$ contains at least one multiple $m$ of $h$. If $m in.not B_0$, take $b = m$. Otherwise every multiple of $h$ in $I$ lies in $B_0$, so $h divides prod_(u in B_0) u$. Because $H_0 divides prod_(u in B_0) u$ as well, the least common multiple $lcm(H_0, h) = (H_0 h) / g^*$ divides $prod_(u in B_0) u$, where $g^* := gcd(H_0, h) <= floor(M / (|B_0| + 1))$. Since $|I inter g^* ZZ| >= floor(M / g^*) >= |B_0| + 1$, pigeonhole yields $b in I without B_0$ divisible by $g^*$, whence $H_0 h = g^* lcm(H_0, h) divides b prod_(u in B_0) u$. $square$

*Theorem 3 (Whole-Cofactor Peeling Reduction).* Let $A subset.eq ZZ_(>= 2)$ have $|A| = n$ and $M = max(A)$, and let $I$ be an interval of $M$ consecutive positive integers. For an integer $Q >= 2$, partition $A = A_"sm" union.sq A_"hi"$ into $A_"sm" := {a in A : p_"max" (a) < Q}$ and $A_"hi" := {a in A : p_"max" (a) >= Q}$. Let $B_"sm" subset.eq I$ cover $A_"sm"$ (with $B_"sm" = emptyset$ if $A_"sm" = emptyset$), and set $L := |B_"sm"| + 2 |A_"hi"| >= 1$. Suppose $Q^2 > M$ and every $a in A_"hi"$ satisfies $a / p_"max" (a) <= floor(M / L)$ (in particular, whenever $Q^2 > M$ and $Q >= L$). When $A_"hi" != emptyset$, the cover $B_"sm"$ extends to a cover $B subset.eq I$ of $A$ of size $|B| <= |B_"sm"| + 2 |A_"hi"| - r <= L - 1$, where $r >= 1$ counts the distinct primes $>= Q$ dividing $prod_(a in A_"hi") a$. Two regimes follow for any target budget $L_0 >= L$.

1. _Regime 1 ($2 n < M <= L_0^2 + 2 L_0$)._ Setting $Q := L_0 + 1$ gives $Q^2 = (L_0 + 1)^2 > M$ and $Q > L_0 >= L$, so $a / p_"max" (a) <= floor(M / Q) <= floor(M / L)$. For $L_0 = 2 n$ and $|B_"sm"| <= 2 |A_"sm"|$, this reduces $2 n < M <= 4 n^2 + 4 n$ to $2 n$-smooth sets.
2. _Regime 2 ($M >= L_0^2$)._ Setting $Q := floor(M^(1 / 2)) + 1$ gives $Q^2 > M$, and $k := floor(M^(1 / 2)) >= L_0$ implies $M >= k^2 >= L_0 k$, so $floor(M / L_0) >= k$. Every $a in A_"hi"$ then has $a / p_"max" (a) < M^(1 / 2)$ and hence $a / p_"max" (a) <= k <= floor(M / L_0) <= floor(M / L)$, reducing $M >= 4 n^2$ (at $L_0 = 2 n$) to $floor(M^(1 / 2))$-smooth sets.

_Proof._ Assume $A_"hi" != emptyset$. Because $Q^2 > M$, each $a in A_"hi"$ has a unique prime factor $q = p_"max" (a) >= Q$, with $v_q (a) = 1$ and cofactor $c(a) := a / q <= floor(M / L)$ satisfying $p_"max" (c(a)) < Q$. Group $A_"hi" = union.sq_(t = 1)^r G_t$ by $q_t$, writing $G_t = {q_t c_(t, 1) < dots < q_t c_(t, m_t)}$ with $m_t >= 1$ and $sum_(t = 1)^r m_t = |A_"hi"|$.

1. _First element of each $q_t$-group._ Start from $B_"cur" = B_"sm"$ and $H_"cur" = prod_(a in A_"sm") a$, and apply Lemma 2 sequentially for $t = 1, dots, r$ to $h_t := q_t c_(t, 1) <= M$. Because $q_t >= Q$ divides neither $prod_(a in A_"sm") a$ nor any earlier $h_s$ ($s < t$), the divisor bound $gcd(H_"cur", q_t c_(t, 1)) = gcd(H_"cur", c_(t, 1)) <= c_(t, 1) <= floor(M / L) <= floor(M / (|B_"cur"| + 1))$ holds. Adding these $r$ elements covers $H_1 := (prod_(a in A_"sm") a) prod_(t = 1)^r (q_t c_(t, 1))$.
2. _Remaining prime copies $q_t^(m_t - 1)$._ For each $t$ with $m_t >= 2$, put $u_t := v_(q_t) (prod_(b in B_"cur") b) >= 1$. When $u_t < m_t$, the interval $I$ contains $>= floor(M / q_t) >= c_(t, m_t) >= m_t$ multiples of $q_t$, and at most $u_t$ lie in $B_"cur"$. Choose $m_t - u_t$ untouched multiples of $q_t$ in $I without B_"cur"$. Their union across $t = 1, dots, r$ adds at most $sum_(t = 1)^r (m_t - 1) = |A_"hi"| - r$ elements and covers $H_2 := (prod_(a in A_"sm") a) prod_(t = 1)^r (q_t^(m_t) c_(t, 1))$.
3. _Remaining cofactors $c_(t, j)$ ($2 <= j <= m_t$)._ Exactly $|A_"hi"| - r$ cofactors remain, each $<= floor(M / L)$. Across $|A_"hi"| - r$ applications of Lemma 2, the size bound $|B_"cur"| + 1 <= |B_"sm"| + r + 2 (|A_"hi"| - r) = |B_"sm"| + 2 |A_"hi"| - r <= L$ holds, so $gcd(H_"cur", c_(t, j)) <= c_(t, j) <= floor(M / (|B_"cur"| + 1))$. Thus $B_"cur"$ covers $A$ in size $<= |B_"sm"| + 2 |A_"hi"| - r$. $square$

*Corollary 4 (Self-contained quadratic-interval bound $M >= 9 n^2$).* Every $n$-set $A subset.eq ZZ_(>= 2)$ with $M = max(A) >= 9 n^2$ and every interval $I$ of length $M$ satisfy $tau(A, I) <= 3 |A_"sm"| + 2 |A_"hi"| <= 3 n$ at $Q = floor(M^(1 / 2)) + 1$.

_Proof._ Set $k := floor(M^(1 / 2)) >= 3 n$, so $M >= k^2 >= 3 n k$ gives $floor(M / (3 n)) >= k$. For each $a in A_"sm"$ ($p_"max" (a) <= k$), let $b_1 <= M^(1 / 2)$ be a maximal subproduct of prime factors of $a$ with multiplicity, so $b_1 <= k$. When $b_1 < a$, pick any prime $p^* divides (a / b_1)$ and put $b_2 := p^* <= k$. Maximality of $b_1$ forces $b_1 p^* > M^(1 / 2)$, whence $b_3 := a / (b_1 p^*) < M / M^(1 / 2) = M^(1 / 2)$ and $b_3 <= k$. Sequential extension via Lemma 2 across those $<= 3 |A_"sm"|$ factors in ${1, dots, k}$ covers $A_"sm"$ in size $<= 3 |A_"sm"|$. Theorem 3 ($L_0 = 3 n$) then extends that cover to $A$ in size $<= 3 |A_"sm"| + 2 |A_"hi"| <= 3 n$. $square$

= Smooth Extreme-Point LP Rank Rounding and Global Bounds

This section restricts linear-programming vertex rounding to smooth subsets so the rounding error drops from $+2 n$ to $o(n)$.

*Theorem 5 (Extreme-Point LP Rank Rounding, Hinge Equivalence, and Surcharge Elimination).*

1. _(Support-rank rounding)._ Any finite nonempty set $A_"sm" subset.eq ZZ_(>= 2)$ with active primes $P(A_"sm")$ below $Q$ and any interval $I$ of length $M >= max(A_"sm")$ satisfy
   $ tau(A_"sm", I) <= floor(tau^*(A_"sm", I)) + |P(A_"sm")| <= floor(tau^*(A_"sm", I)) + pi(Q - 1). $
2. _(Hinge equivalence)._ Given $w = (w_p)_(p <= M) in RR_(>= 0)^(pi(M))$, put $X_w (m) := sum_(p <= M) v_p (m) w_p$. Across each $M >= 1$, interval $I = {x + 1, dots, x + M}$ ($x >= 0$), and $c >= 1$, two statements are equivalent.
   - _(Fractional bound)._ Every nonempty subset $A subset.eq {1, dots, M}$ satisfies $tau^*(A, I) <= c |A|$.
   - _(Shifted-interval hinge inequality $(H_c)$)._ All weight vectors $w in [0, 1]^({p <= M})$ satisfy
     $ sum_(m = 1)^M (X_w (m) - c)_+ <= sum_(b in I) (X_w (b) - 1)_+. $
3. _(Surcharge elimination)._ Suppose $(H_c)$ holds for all $(M, I)$ at some $c >= 2$, and let $Q_n$ be the least integer $>= floor(c n) + pi(Q_n - 1) + 1$ (so $Q_n = c n + (1 + o(1)) c n / ln n > c n$). Each $n$-set $A$ with $M = max(A) <= Q_n^2 - 1$ (including all $M <= c^2 n^2$) obeys $tau(A, I) <= floor(c n) + pi(Q_n - 1) = (c + o(1)) n$. Two consequences follow immediately.
   - Combining $c >= 3$ with Corollary 4 ($M >= 9 n^2 <= c^2 n^2$) gives $g(n) <= floor(c n) + pi(Q_n - 1) = (c + o(1)) n$ across all $M >= 2$. Invoking Chen's unconditional inequality $(H_(56501 / 6400))$ @chen26 yields $g(n) <= (56501 / 6400 + o(1)) n < (8.8283 + o(1)) n$, with $g(n) <= 10 n$ for $n >= 1","446$ ($g(n) <= 9 n$ for $n >= 4.11 times 10^(27)$). Meanwhile the Lean-4-formalized inequality $(H_(97 / 10))$ @chen26 yields $g(n) <= (9.7 + o(1)) n$, with $g(n) <= 11 n$ for $n >= 1","254$.
   - At $c = 2$, the hinge bound $(H_2)$ implies $tau(A, I) <= 2 n + (2 + o(1)) n / ln n = (2 + o(1)) n$ across $M <= 4 n^2$.

_Proof._ (1) The polytope $cal(P) = {x in [0, 1]^I : forall p in P(A_"sm"), space sum_(b in I) v_p (b) x_b >= D_p (A_"sm")}$ is nonempty ($x_b = 1$ is feasible by Legendre majorization) and compact. Thus $sum_(b in I) x_b$ attains its minimum $tau^*(A_"sm", I)$ at an extreme point $x^* in cal(P)$. Set $F := {b in I : 0 < x^*_b < 1}$. Because $x^*$ is an extreme point, the columns $(v_p (b))_(p in T, b in F)$ of the tight demand rows $T subset.eq P(A_"sm")$ are linearly independent, giving $|F| <= |T| <= |P(A_"sm")|$. If $|F| = 0$, the point $x^*$ is integral and $tau(A_"sm", I) = tau^*(A_"sm", I)$. When $|F| >= 1$, rounding $hat(x)_b := ceil(x^*_b) in {0, 1}$ preserves demand feasibility and gives $sum_(b in I) hat(x)_b = |{b : x^*_b = 1}| + |F| < sum_(b in I) x^*_b + |F| <= tau^*(A_"sm", I) + |P(A_"sm")|$. Integrality of $sum hat(x)_b$ yields $tau(A_"sm", I) <= floor(tau^*(A_"sm", I)) + |P(A_"sm")|$.

(2) Linear-programming strong duality on $0 <= x_b <= 1$ (with dual weights $w_p >= 0$ and upper-bound multipliers $z_b = (X_w (b) - 1)_+$) gives
$ tau^*(A, I) = max_(w >= 0) [ sum_(a in A) X_w (a) - sum_(b in I) (X_w (b) - 1)_+ ]. $
Consider _Legendre clipping_ to $[0, 1]^({p <= M})$. If $w_(p_0) = 1 + delta > 1$, lowering $w_(p_0)$ to $1$ reduces $sum_(a in A) X_w (a)$ by $delta D_(p_0) (A)$. Meanwhile every $b in I$ divisible by $p_0$ retains $X_(w') (b) >= v_(p_0) (b) >= 1$, so $sum_(b in I) (X_w (b) - 1)_+$ drops by $delta sum_(b in I) v_(p_0) (b) >= delta sum_(r >= 1) floor(M / p_0^r) >= delta D_(p_0) (A)$. Hence the dual maximum is attained on $[0, 1]^({p <= M})$. Next, $tau^*(A, I) <= c |A|$ holds for all nonempty $A subset.eq {1, dots, M}$ (and for $A = emptyset$) if and only if every $w in [0, 1]^({p <= M})$ obeys $max_(A subset.eq {1, dots, M}) (sum_(a in A) X_w (a) - c |A|) <= sum_(b in I) (X_w (b) - 1)_+$. The left-hand maximum is attained at $A = {1 <= m <= M : X_w (m) > c}$ and equals $sum_(m = 1)^M (X_w (m) - c)_+$.

(3) Because $Q - pi(Q - 1)$ is nondecreasing and rises by $1$ at every composite $Q - 1$, the threshold $Q_n$ exists and satisfies $Q_n = c n + (1 + o(1)) c n / ln n > c n$. For $M <= Q_n^2 - 1$, split $A = A_"sm" union.sq A_"hi"$ at $Q_n$. Parts (1) and (2) yield a cover $B_"sm" subset.eq I$ of $A_"sm"$ with $|B_"sm"| <= floor(c |A_"sm"|) + pi(Q_n - 1)$ (or $0$ if $A_"sm" = emptyset$). Since $c >= 2$ and $2 |A_"hi"| in ZZ$, the floor identity gives $floor(c |A_"sm"|) + 2 |A_"hi"| = floor(c |A_"sm"| + 2 |A_"hi"|) <= floor(c n)$. Thus $L := |B_"sm"| + 2 |A_"hi"| <= floor(c n) + pi(Q_n - 1) =: L_0 <= Q_n - 1$, giving $Q_n >= L_0 + 1$ and $Q_n^2 > M$. Theorem 3 extends $B_"sm"$ to $A$ in size $<= L <= floor(c n) + pi(Q_n - 1)$. When $c >= 3$, Corollary 4 covers all $M >= Q_n^2 > c^2 n^2 >= 9 n^2$ in size $<= 3 n <= c n$. Testing $Q = 10 n + 1$ at $c = 56501 / 6400$ (and $Q = 11 n + 1$ at $c = 97 / 10$) with Rosser and Schoenfeld's bound $pi(x) < 1.25506 x / ln x$ ($x > 1$) @rosserschoenfeld62 gives $floor(c n) + pi(Q - 1) <= Q - 1$, hence $Q_n <= Q$, for $n >= 4","486$ (and $n >= 3","722$). Direct finite evaluation of $Q_n$ across $1","446 <= n <= 4","485$ and $1","254 <= n <= 3","721$ (verified computationally via our accompanying verification suite @bergstrom26code) completes both bounds. $square$

= Universal Semiprime Multigraph Saving and Cross-Tier Obstructions

This section proves an unconditional vertex-saving bound for arbitrary semiprime multigraphs without prime-size restrictions.

*Theorem 6 (Universal Semiprime Multigraph Saving Bound).* Fix $M >= 2$ and $I = {x + 1, dots, x + M}$ ($x >= 0$). Let $G = (V, E)$ be a loopless multigraph on primes $V$ with $|E| = m$ edges, $u_e w_e <= M$ for all $e = {u_e, w_e} in E$ ($u_e != w_e$), and $deg_E (v) <= |I inter v ZZ|$ for all $v in V$.

1. _General multigraphs._ The cover number obeys $tau(G, I) := tau({u_e w_e : e in E}, I) <= 2 m - ceil(|V_"non-iso"| / 2)$.
2. _Bipartite multigraphs._ When $G = (P union.sq Q, E)$ is bipartite, $tau(G, I) <= 2 m - max(|P_"non-iso"|, |Q_"non-iso"|)$.

_Proof._ For each edge $e = {u_e, w_e} in E$, pick a multiple $b_e in I$ of $u_e w_e <= M$, and put $B_"init" := {b_e : e in E} subset.eq I$ with $t := |B_"init"| >= 1$. Define $V(b) := union_(e in E : b_e = b) {u_e, w_e} subset.eq V$ for each $b in B_"init"$, so $|V(b)| >= 2$ and $prod_(v in V(b)) v divides b$. For $v in V$, set $c_v := |{b in B_"init" : v in V(b)}|$ and $tilde(c)_v := |{b in B_"init" : v divides b}| >= c_v$. Then $v^(tilde(c)_v)$ divides $prod_(b in B_"init") b$. Whenever $tilde(c)_v < deg_E (v)$, adjoin $deg_E (v) - tilde(c)_v$ untouched multiples of $v$ from $I without B_"init"$. Taking the union over $v in V$ covers $G$ in size $|B| <= t + sum_(v in V) (deg_E (v) - c_v) = 2 m + t - sum_(b in B_"init") |V(b)|$. Since $|V(b)| >= 2$ for all $b in B_"init"$ and $sum_(b in B_"init") |V(b)| >= |union_(b in B_"init") V(b)| = |V_"non-iso"|$, this gives $|B| <= min(2 m - t, 2 m + t - |V_"non-iso"|) <= 2 m - ceil(|V_"non-iso"| / 2)$. When $G = (P union.sq Q, E)$ is bipartite, $|V(b) inter P| >= 1$ gives $|V(b)| - 1 >= |V(b) inter Q|$. Summing over $b in B_"init"$ yields $sum_b (|V(b)| - 1) >= |Q_"non-iso"|$, and symmetry gives $>= |P_"non-iso"|$. $square$

*Remark 7 (Cross-tier obstruction below $M = n^3$).* Choose $4 n^2 <= M < n^(2.9)$ with $n / 3$ primes $q_i approx M^(0.505)$, three primes $p_k approx M^(0.33)$, and three primes $r_k approx M^(0.165)$, forming $A = {r_k p_k q_i : 1 <= k <= 3, space 1 <= i <= n / 3}$. Because $|I inter p_k^2 ZZ| = O(M^(0.34)) = o(n)$ and $|I inter r_k^4 ZZ| = O(M^(0.34)) = o(n)$, uncoupled tier splitting gives $tau(D|_(> M^(1 / 2)), I) + tau(D|_([2, M^(1 / 2)]), I) = (7 / 3 - o(1)) n > 2 n$. Theorem 3 (Regime 2) instead covers $A$ in $<= 5 n / 3$ picks. Even if $q_i approx M^(0.495) < M^(1 / 2)$, Theorem 6(2) covers $E = {p_k q_i}$ ($p_k q_i <= M / 2$) in $<= 5 n / 3$ picks plus $n / 3$ picks for ${r_1, r_2, r_3}$, totaling $<= 2 n$.

= Maximal-Proper-Divisor Matching and Telescoping Structure of $(H_2)$

This section records two reductions of $(H_2)$ and identifies the parity obstruction to pointwise level-set dominance.

*Proposition 8 (Maximal-Proper-Divisor Matching Criterion and Single-Prime Telescoping).* Let $M >= 1$ and $I = {x + 1, dots, x + M}$ ($x >= 0$).

1. _(Combinatorial matching sufficiency)._ Set $cal(M)_(>= 3) := {1 <= m <= M : Omega(m) >= 3}$. An injection $pi : cal(M)_(>= 3) arrow.hook I$ satisfying $(m / p) divides pi(m)$ for at least one prime $p divides m$ at each $m in cal(M)_(>= 3)$ implies $(H_2)$ for $(M, I)$ across all $w in [0, 1]^({p <= M})$ simultaneously.
2. _(Prime-by-prime telescoping identity)._ Fix any ordering $p_1, dots, p_K$ of the primes $<= M$, and put $Y_j (n) := sum_(i < j) v_(p_i) (n) w_(p_i)$. Then $(H_2)$ is equivalent to
   $ sum_(j = 1)^K sum_(r >= 1) sum_(k = 1)^(floor(M / p_j^r)) integral_(1 - r w_(p_j))^(1 - (r - 1) w_(p_j)) bold(1)_(Y_j (k) > s + 1) dif s <= sum_(j = 1)^K sum_(r >= 1) sum_(b' in I_(j, r)) integral_(1 - r w_(p_j))^(1 - (r - 1) w_(p_j)) bold(1)_(Y_j (b') > s) dif s, $
   where $I_(j, r) := {floor(x / p_j^r) + 1, dots, floor((x + M) / p_j^r)}$ has cardinality $|I_(j, r)| in {floor(M / p_j^r), floor(M / p_j^r) + 1}$.

_Proof._ (1) For $w in [0, 1]^({p <= M})$, every $m in {1, dots, M} without cal(M)_(>= 3)$ has $Omega(m) <= 2$, so $X_w (m) <= 2$ and $(X_w (m) - 2)_+ = 0$. When $m in cal(M)_(>= 3)$ satisfies $(m / p) divides pi(m)$, the valuation inequality $X_w (pi(m)) >= X_w (m / p) = X_w (m) - w_p >= X_w (m) - 1$ gives $(X_w (pi(m)) - 1)_+ >= (X_w (m) - 2)_+$. Summing over the injective image $pi(cal(M)_(>= 3)) subset.eq I$ yields $(H_2)$.

(2) Since $gcd(p_i, p_j) = 1$ for $i < j$, the prefix sum obeys $Y_j (p_j^r k) = Y_j (k)$ for all $r >= 1$ and $k >= 1$. Summing $(Y_j (n) + v_(p_j) (n) w_(p_j) - c)_+ - (Y_j (n) - c)_+$ over $j = 1, dots, K$ telescopes to $(X_w (n) - c)_+$. Expand each $j$-th step over $1 <= r <= v_(p_j) (n)$ via $(u - a)_+ - (u - b)_+ = integral_a^b bold(1)_(u > t) dif t$ at $a = c - r w_(p_j) <= c - (r - 1) w_(p_j) = b$. Substituting $t = s + 1$ at $c = 2$ on ${1, dots, M}$ and $t = s$ at $c = 1$ on $I$ yields both sides identically. $square$

*Remark 9 (Computational verification and the Hensley–Richards $s = 0$ barrier).* Three computational and analytic observations (verified via our accompanying verification suite @bergstrom26code) clarify Proposition 8.

1. Hopcroft–Karp bipartite matching constructs $pi : cal(M)_(>= 3) arrow.hook I$ across all $x in [0, 1000]$ for $M in {12, 24, dots, 120}$ ($10","010$ windows), as well as across both adversarial Chinese Remainder configurations ($x equiv 0 pmod(lcm(1, dots, M))$ and centered prime-power alignment $x + floor(M / 2) + 1 equiv p pmod(p^(e_p))$ for $p^(e_p) > M$) up to $M = 15","120$ ($9","457$ of $9","457$ matched). Restricting Proposition 8(1) to $p = p_"max" (m)$ alone fails at $M = 2","520$ ($1","431$ of $1","434$ matched), whereas allowing any prime $p divides m$ succeeds universally.
2. Sliding-window evaluations ($18","037$ primary and $360","000","000$ extended window checks) confirm $max (sum_(m = 1)^M (X_w (m) - 2)_+ - sum_(b in I) (X_w (b) - 1)_+) = 0$. Testing sub-critical $c = 1.8 < 2$ fails on the $32$-prime Erdős–Surányi clique on $[503, 709]$ at $M = 497","009$ ($"LHS" = 105.4 > "RHS" = 93.0$).
3. Pointwise dominance $|{k <= L : Y(k) > s + 1}| <= |{b' in I' : Y(b') > s}|$ at $s = 0$ fails for Proposition 8(2). Setting $w_q = 1$ on all primes $q <= L$ at $s = 0$ gives $pi(x + L) - pi(x) <= pi(L) + 1$, the Second Hardy–Littlewood inequality, which fails for $L >= e^(100)$ by $Theta(L / ln^2 L)$ @hensleyrichards74. Proving $(H_2)$ (or its $(2 + epsilon)$-analogue on $(2 + epsilon) n$-smooth weights) therefore requires averaging across $s$.

#set heading(numbering: none)

= Data and Code Availability

All computational checks for Theorem 3, Corollary 4, the finite cutoffs of Theorem 5(3), Theorem 6, and Proposition 8 (up to $M = 15","120$) are deterministically reproducible via the standalone Rust and independent arbitrary-precision verification suites archived at Zenodo @bergstrom26code (`https://doi.org/10.5281/zenodo.24342717`), with source SHA-256 digests `312e8fb7a27ce66ab4b72a6d758138da5cb3926218f8464b38636e670655b52c` and `be0b65d47711340b70bf281caaf4734ba2be1f28e52fa587f1898532fa7cc17c`.

= Acknowledgments and Declaration of Generative AI

During the preparation of this work, the author used internal research automation (Karen, 24x AI Research) and large language model assistance (Google Gemini) for proof exploration, computational stress-testing, and manuscript editing. After using these tools, the author reviewed, verified, and edited the content as needed and takes full responsibility for the mathematical correctness and content of the publication.

#bibliography("references.bib", title: "References")

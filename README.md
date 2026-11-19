# Erdős Problem #708 — Whole-Cofactor Peeling, Extreme-Point LP Rank Rounding, and Shifted-Interval Hinge Duality

**HOLD — DO NOT PUBLISH UNTIL FULL $(2 + o(1))n$ PROGRAMME IS READY FOR JOINT RELEASE.**

Companion manuscript and zero-dependency verification repository (`https://doi.org/10.5281/zenodo.24342717`; companion small-$n$ manuscript `https://doi.org/10.5281/zenodo.24366897`) on the asymptotic Erdős–Surányi problem ([Erdős Problem #708](https://www.erdosproblems.com/708)).

## Summary of Unconditional Results vs. Remaining Analytic Frontier

### Proved Unconditionally in This Paper
1. **Whole-Cofactor Peeling (`Theorem 3`) & Self-Contained Quadratic-Interval Bound (`Corollary 4`):**
   - Via an Incremental Cumulative-GCD Extension (`Lemma 2`), peeling primes $q \ge Q$ together with their cofactors in $\le 2|A_{\mathrm{hi}}| - 1$ picks reduces $2n < M \le 4n^2 + 4n$ to $2n$-smooth sets ($Q = 2n + 1$) and reduces $M \ge 4n^2$ to $\lfloor M^{1/2} \rfloor$-smooth sets ($Q = \lfloor M^{1/2} \rfloor + 1$).
   - Yields a self-contained proof that $\tau(A, I) \le 3|A_{\mathrm{sm}}| + 2|A_{\mathrm{hi}}| \le 3n$ for **all $M \ge 9n^2$** and $n \ge 1$.
2. **Smooth Extreme-Point LP Rank Rounding, Hinge Equivalence, and $+2n$ Surcharge Elimination (`Theorem 5`):**
   - On any $Q_n$-smooth subset $A_{\mathrm{sm}}$, basic-feasible-solution support rounding gives $\tau(A_{\mathrm{sm}}, I) \le \lfloor \tau^*(A_{\mathrm{sm}}, I) \rfloor + \pi(Q_n - 1)$, avoiding the $|P(A)| \le n + \pi(3n)$ large-prime LP rounding surcharge ($\lceil cn \rceil + 2n$, which imposed a $4n$ floor at $c = 2$).
   - Combined with `Theorem 3` and `Corollary 4`, any global shifted-interval hinge bound $(H_c)$ ($c \ge 3$) yields $g(n) \le \lfloor cn \rfloor + \pi(Q_n - 1) = (c + o(1))n$ across **all $M \ge 2$**:
     - Invoking Chen's (`https://doi.org/10.5281/zenodo.22660853`, v14) $(H_{56501/6400})$ unconditionally improves $g(n)$ to **$g(n) \le (56501/6400 + o(1))n < (8.8283 + o(1))n$**, with **$g(n) \le 10n$ for every $n \ge 1{,}446$** (and $g(n) \le 9n$ for $n \ge 4.11 \times 10^{27}$).
     - Invoking Chen's Lean-4-formalized $(H_{97/10})$ unconditionally yields **$g(n) \le (9.7 + o(1))n$**, with **$g(n) \le 11n$ for every $n \ge 1{,}254$**.
   - Breaks the $4n$ rounding barrier at $c = 2$: the critical hinge inequality $(H_2)$ directly implies $\tau(A, I) \le 2n + (2 + o(1)) n / \ln n = (2 + o(1))n$ across the entire polynomial window **$M \le 4n^2$**.
3. **Universal Semiprime Multigraph Saving Bound (`Theorem 6`):**
   - For every $M \ge 2$, $x \ge 0$, and loopless semiprime multigraph $G = (V, E)$ with $u_e w_e \le M$ and $\deg_E(v) \le |I \cap v\mathbb{Z}|$, $\tau(G, I) \le 2|E| - \lceil |V_{\mathrm{non\text{-}iso}}| / 2 \rceil$ (and $\le 2|E| - \max(|P_{\mathrm{non\text{-}iso}}|, |Q_{\mathrm{non\text{-}iso}}|)$ when bipartite), resolving the cross-tier $\{r_k p_k q_i\}$ $\frac{7}{3}n$ uncoupled-tier obstruction (`Remark 7`).
4. **Maximal-Proper-Divisor Matching & Single-Prime Telescoping (`Proposition 8`, `Remark 9`):**
   - Any injection $\pi : \mathcal{M}_{\ge 3} \hookrightarrow I$ with $(m / p) \mid \pi(m)$ for some prime $p \mid m$ implies $(H_2)$ simultaneously for all weight vectors $w \in [0, 1]^{\{p \le M\}}$ (`9,457 / 9,457` matched at $M = 15{,}120$).
   - Identifies the Hensley–Richards (1974) Second Hardy–Littlewood parity obstruction to naive $s = 0$ level-set dominance in the prime-by-prime telescoping identity.

### Open Analytic Frontier for $g(n) \le (2 + o(1))n$
- Proving $(H_2)$ (or its $(2 + \varepsilon)$-relaxed analogue on $(2 + \varepsilon)n$-smooth weights) closes $M \le 4n^2$ via `Theorem 5(3)`, leaving only the intermediate single-large-prime coupling window $q \in (M^{1/3}, M^{1/2}]$ on $4n^2 < M < 8n^3$.

## Contents & Build Instructions

- `paper/erdos708-asymptotic.pdf` (`paper/erdos708-asymptotic.typ`, `paper/erdos708-asymptotic.tex`, `paper/references.bib`): Manuscript (`typst compile paper/erdos708-asymptotic.typ paper/erdos708-asymptotic.pdf`).
- `scripts/verify_asymptotic_708.rs` (SHA-256 `312e8fb7a27ce66ab4b72a6d758138da5cb3926218f8464b38636e670655b52c`): Zero-dependency Rust 2021 verifier:
  - Build: `rustc -O --edition 2021 -D warnings scripts/verify_asymptotic_708.rs -o verify_asymptotic_708`
  - Fast suite (`18,037` sliding windows + CRT spikes up to $M = 15{,}120$): `./verify_asymptotic_708`
  - Extended suite (`360,000,000` sliding-window evaluations): `./verify_asymptotic_708 --extended`
  - Negative tamper checks: `./verify_asymptotic_708 --tamper-hinge-c 1.8` and `./verify_asymptotic_708 --tamper-pmax-only`
- `scripts/check708-asymptotic-independent.ts` (SHA-256 `be0b65d47711340b70bf281caaf4734ba2be1f28e52fa587f1898532fa7cc17c`): Independent TypeScript/Bun `BigInt` CRT verifier (`bun scripts/check708-asymptotic-independent.ts`).
- `scripts/validate-all.sh`: End-to-end SHA-256 manifest check, Rust + Bun positive verification up to $M = 15{,}120$, and negative tamper/soundness checks.

## Quick Verification

```sh
./scripts/validate-all.sh
```

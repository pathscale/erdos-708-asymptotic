//! Deterministic zero-dependency standalone verifier for:
//! "Whole-Cofactor Peeling, Extreme-Point LP Rank Rounding, and
//!  Shifted-Interval Hinge Duality for Erdos Problem 708"
//!
//! Compile and run:
//!   rustc -O --edition 2021 scripts/verify_asymptotic_708.rs -o verify_asymptotic_708
//!   ./verify_asymptotic_708

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::env;
use std::process;

fn sieve_primes(limit: usize) -> Vec<usize> {
    let mut is_p = vec![true; limit + 1];
    is_p[0] = false;
    if limit >= 1 {
        is_p[1] = false;
    }
    let mut p = 2;
    while p * p <= limit {
        if is_p[p] {
            let mut mult = p * p;
            while mult <= limit {
                is_p[mult] = false;
                mult += p;
            }
        }
        p += 1;
    }
    (2..=limit).filter(|&x| is_p[x]).collect()
}

fn factorize_map(mut n: u64) -> BTreeMap<u64, u32> {
    let mut out = BTreeMap::new();
    let mut d = 2u64;
    while d * d <= n {
        while n % d == 0 {
            *out.entry(d).or_insert(0) += 1;
            n /= d;
        }
        d += 1;
    }
    if n > 1 {
        *out.entry(n).or_insert(0) += 1;
    }
    out
}

fn p_max(n: u64) -> u64 {
    factorize_map(n).keys().next_back().copied().unwrap_or(1)
}

fn add_factors(acc: &mut BTreeMap<u64, u32>, n: u64) {
    for (p, e) in factorize_map(n) {
        *acc.entry(p).or_insert(0) += e;
    }
}

fn divides_val(demand: &BTreeMap<u64, u32>, supply: &BTreeMap<u64, u32>) -> bool {
    demand
        .iter()
        .all(|(p, &e)| supply.get(p).copied().unwrap_or(0) >= e)
}

fn gcd_with_val_map(h_cur: &BTreeMap<u64, u32>, h: u64) -> u64 {
    let fh = factorize_map(h);
    let mut g = 1u64;
    for (p, eh) in fh {
        let ec = h_cur.get(&p).copied().unwrap_or(0).min(eh);
        for _ in 0..ec {
            g *= p;
        }
    }
    g
}

/// Constructive implementation of Lemma 2 (Incremental Cumulative-GCD Extension).
fn lemma2_extend(
    x: u64,
    m: u64,
    b_set: &mut BTreeSet<u64>,
    b_supply: &mut BTreeMap<u64, u32>,
    h_cur: &mut BTreeMap<u64, u32>,
    h: u64,
) {
    assert!(h >= 1 && h <= m, "Lemma 2 requires 1 <= h <= M");
    let g_star = gcd_with_val_map(h_cur, h);
    let limit = m / ((b_set.len() as u64) + 1);
    assert!(
        g_star <= limit,
        "Lemma 2 precondition violated: gcd={} > floor(M/(|B|+1))={}",
        g_star,
        limit
    );

    // Check if an untouched multiple of h exists in I = [x+1, x+M].
    let first_h = ((x / h) + 1) * h;
    let mut mult = first_h;
    while mult <= x + m {
        if !b_set.contains(&mult) {
            b_set.insert(mult);
            add_factors(b_supply, mult);
            add_factors(h_cur, h);
            assert!(divides_val(h_cur, b_supply));
            return;
        }
        mult += h;
    }

    // Otherwise all multiples of h in I are in B_0; pick an untouched multiple of g_star.
    let first_g = ((x / g_star) + 1) * g_star;
    let mut mult_g = first_g;
    while mult_g <= x + m {
        if !b_set.contains(&mult_g) {
            b_set.insert(mult_g);
            add_factors(b_supply, mult_g);
            add_factors(h_cur, h);
            assert!(divides_val(h_cur, b_supply));
            return;
        }
        mult_g += g_star;
    }
    panic!("Lemma 2 pigeonhole failed unexpectedly");
}

/// Constructive implementation of Theorem 3 (Whole-Cofactor Peeling).
fn theorem3_peel(
    a_hi: &[u64],
    q_thresh: u64,
    x: u64,
    m: u64,
    l_budget: u64,
    b_set: &mut BTreeSet<u64>,
    b_supply: &mut BTreeMap<u64, u32>,
    h_cur: &mut BTreeMap<u64, u32>,
) -> usize {
    if a_hi.is_empty() {
        return 0;
    }
    assert!(
        (q_thresh as u128) * (q_thresh as u128) > (m as u128),
        "Theorem 3 requires Q^2 > M"
    );
    let mut groups: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for &a in a_hi {
        let q = p_max(a);
        assert!(q >= q_thresh);
        let c = a / q;
        assert!(c <= m / l_budget);
        groups.entry(q).or_default().push(c);
    }
    for cs in groups.values_mut() {
        cs.sort_unstable();
    }
    let r = groups.len();

    // Step 1: First element q_t * c_{t,1} of each q_t-group via Lemma 2.
    for (&q, cs) in &groups {
        let h_t = q * cs[0];
        lemma2_extend(x, m, b_set, b_supply, h_cur, h_t);
    }

    // Step 2: Remaining prime copies q_t^{m_t - 1}.
    for (&q, cs) in &groups {
        let m_t = cs.len() as u32;
        if m_t >= 2 {
            let u_t = b_supply.get(&q).copied().unwrap_or(0);
            assert!(u_t >= 1);
            if u_t < m_t {
                let mut need = m_t - u_t;
                let mut mult = ((x / q) + 1) * q;
                while mult <= x + m && need > 0 {
                    if !b_set.contains(&mult) {
                        b_set.insert(mult);
                        add_factors(b_supply, mult);
                        need -= 1;
                    }
                    mult += q;
                }
                assert_eq!(need, 0, "Insufficient multiples of q in I");
            }
            *h_cur.entry(q).or_insert(0) += m_t - 1;
            assert!(divides_val(h_cur, b_supply));
        }
    }

    // Step 3: Remaining cofactors c_{t,j} (j >= 2) via Lemma 2.
    for cs in groups.values() {
        for &c in cs.iter().skip(1) {
            lemma2_extend(x, m, b_set, b_supply, h_cur, c);
        }
    }
    r
}

fn isqrt_u64(n: u64) -> u64 {
    let mut r = (n as f64).sqrt() as u64;
    while (r + 1).saturating_mul(r + 1) <= n {
        r += 1;
    }
    while r.saturating_mul(r) > n {
        r -= 1;
    }
    r
}

fn verify_part1_peeling_and_cor4() -> (usize, usize) {
    let mut state = 0x7080_2026_1118_u64;
    let mut next_u64 = || -> u64 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };

    // 1A: Verify Regime I (2n < M <= 4n^2 + 4n, Q = 2n + 1).
    let mut regime1_ok = 0usize;
    for trial in 0..500usize {
        let n = 3 + (trial % 14);
        let m_min = (2 * n + 1) as u64;
        let m_max = (4 * n * n + 4 * n) as u64;
        let m = m_min + (next_u64() % (m_max - m_min + 1));
        let x = next_u64() % 50_000;
        let q_thresh = (2 * n + 1) as u64;

        let mut set_a = BTreeSet::new();
        set_a.insert(m);
        // Force several elements with p_max >= Q when primes >= Q exist <= M.
        let primes = sieve_primes(m as usize);
        let hi_primes: Vec<u64> = primes
            .iter()
            .copied()
            .map(|p| p as u64)
            .filter(|&p| p >= q_thresh)
            .collect();
        if !hi_primes.is_empty() {
            for _ in 0..(n / 2) {
                let q = hi_primes[(next_u64() as usize) % hi_primes.len()];
                let max_c = (m / q).max(1);
                let c = 1 + (next_u64() % max_c);
                if q * c >= 2 && q * c <= m {
                    set_a.insert(q * c);
                }
            }
        }
        let mut guard = 0usize;
        while set_a.len() < n && guard < 10_000 {
            let cand = 2 + (next_u64() % (m - 1));
            set_a.insert(cand);
            guard += 1;
        }
        if set_a.len() < n {
            continue;
        }
        let a_vec: Vec<u64> = set_a.into_iter().collect();
        let (a_sm, a_hi): (Vec<u64>, Vec<u64>) =
            a_vec.iter().copied().partition(|&a| p_max(a) < q_thresh);

        // Cover A_sm greedily (or via <= 2|A_sm| picks when small-smooth cover exists).
        let mut b_set = BTreeSet::new();
        let mut b_supply = BTreeMap::new();
        let mut h_cur = BTreeMap::new();
        for &a in &a_sm {
            add_factors(&mut h_cur, a);
        }
        // Greedy supply pick for A_sm: pick elements maximizing uncovered demand.
        while !divides_val(&h_cur, &b_supply) {
            let mut best_b = x + 1;
            let mut best_gain = 0u32;
            for b in (x + 1)..=(x + m) {
                if b_set.contains(&b) {
                    continue;
                }
                let fb = factorize_map(b);
                let mut gain = 0u32;
                for (p, &need) in &h_cur {
                    let have = b_supply.get(p).copied().unwrap_or(0);
                    if have < need {
                        gain += fb.get(p).copied().unwrap_or(0).min(need - have);
                    }
                }
                if gain > best_gain {
                    best_gain = gain;
                    best_b = b;
                }
            }
            assert!(best_gain > 0);
            b_set.insert(best_b);
            add_factors(&mut b_supply, best_b);
        }
        let sm_size = b_set.len();
        if sm_size <= 2 * a_sm.len() && !a_hi.is_empty() {
            let l_budget = (sm_size + 2 * a_hi.len()) as u64;
            let r = theorem3_peel(
                &a_hi,
                q_thresh,
                x,
                m,
                l_budget,
                &mut b_set,
                &mut b_supply,
                &mut h_cur,
            );
            let mut full_demand = BTreeMap::new();
            for &a in &a_vec {
                add_factors(&mut full_demand, a);
            }
            assert!(divides_val(&full_demand, &b_supply));
            assert!(b_set.len() <= sm_size + 2 * a_hi.len() - r);
            assert!(b_set.len() <= 2 * n - 1);
            regime1_ok += 1;
        } else if a_hi.is_empty() {
            regime1_ok += 1;
        }
    }

    // 1B: Verify Corollary 4 (M >= 9n^2 => tau(A, I) <= 3|A_sm| + 2|A_hi| <= 3n).
    let mut cor4_ok = 0usize;
    for trial in 0..500usize {
        let n = 1 + (trial % 20);
        let m_base = (9 * n * n) as u64;
        let m = if trial < 40 {
            // Exact boundary M = 9n^2 and 9n^2 + 1.
            m_base + (trial as u64 % 2)
        } else {
            m_base + (next_u64() % (4 * m_base + 1))
        };
        let x = next_u64() % 100_000;
        let k = isqrt_u64(m);
        assert!(k >= (3 * n) as u64);
        assert!(m / (3 * n as u64) >= k);
        let q_thresh = k + 1;

        let mut set_a = BTreeSet::new();
        set_a.insert(m);
        while set_a.len() < n {
            set_a.insert(2 + (next_u64() % (m - 1)));
        }
        let a_vec: Vec<u64> = set_a.into_iter().collect();
        let (a_sm, a_hi): (Vec<u64>, Vec<u64>) =
            a_vec.iter().copied().partition(|&a| p_max(a) < q_thresh);

        let mut b_set = BTreeSet::new();
        let mut b_supply = BTreeMap::new();
        let mut h_cur = BTreeMap::new();

        // Decompose each a in A_sm into <= 3 factors <= k and apply Lemma 2.
        for &a in &a_sm {
            let mut prime_multiset = Vec::new();
            for (p, e) in factorize_map(a) {
                assert!(p <= k);
                for _ in 0..e {
                    prime_multiset.push(p);
                }
            }
            let mut b1 = 1u64;
            let mut rem = Vec::new();
            for p in prime_multiset {
                if b1 * p <= k {
                    b1 *= p;
                } else {
                    rem.push(p);
                }
            }
            let mut chunks = vec![b1];
            if !rem.is_empty() {
                let p_star = rem[0];
                assert!(b1 * p_star > k);
                let b2 = p_star;
                let b3 = a / (b1 * p_star);
                assert!(b2 <= k && b3 <= k);
                chunks.push(b2);
                if b3 > 1 {
                    chunks.push(b3);
                }
            }
            assert!(chunks.len() <= 3);
            for h in chunks {
                if h >= 1 {
                    lemma2_extend(x, m, &mut b_set, &mut b_supply, &mut h_cur, h);
                }
            }
        }
        assert!(b_set.len() <= 3 * a_sm.len());

        let l_budget = (b_set.len() + 2 * a_hi.len()).max(1) as u64;
        assert!(l_budget <= (3 * n) as u64);
        let r = theorem3_peel(
            &a_hi,
            q_thresh,
            x,
            m,
            l_budget,
            &mut b_set,
            &mut b_supply,
            &mut h_cur,
        );
        let mut full_demand = BTreeMap::new();
        for &a in &a_vec {
            add_factors(&mut full_demand, a);
        }
        assert!(divides_val(&full_demand, &b_supply));
        if !a_hi.is_empty() {
            assert!(r >= 1);
            assert!(b_set.len() <= 3 * a_sm.len() + 2 * a_hi.len() - r);
        }
        assert!(b_set.len() <= 3 * n);
        cor4_ok += 1;
    }
    (regime1_ok, cor4_ok)
}

fn verify_part2_hinge_duality(c_test: f64) -> Result<(usize, f64, f64), String> {
    // 2A: Verify Legendre clipping: clipping w_p > 1 down to 1 never decreases dual objective.
    let primes_60 = sieve_primes(60);
    for trial in 0..200usize {
        let m = 20 + (trial % 41);
        let x = (trial * 37) % 500;
        let ps: Vec<usize> = primes_60.iter().copied().filter(|&p| p <= m).collect();
        let mut w_raw = vec![0.0f64; ps.len()];
        for (idx, &p) in ps.iter().enumerate() {
            w_raw[idx] = 0.4 + (((trial * 13 + p * 7) % 19) as f64) * 0.1;
        }
        let w_clip: Vec<f64> = w_raw.iter().map(|&v| v.min(1.0)).collect();
        let a_set: Vec<usize> = (2..=m).step_by(2).collect();

        let eval_dual = |w: &[f64]| -> f64 {
            let xw = |mut num: usize| -> f64 {
                let mut acc = 0.0;
                for (i, &p) in ps.iter().enumerate() {
                    while num % p == 0 {
                        acc += w[i];
                        num /= p;
                    }
                }
                acc
            };
            let lhs: f64 = a_set.iter().map(|&a| xw(a)).sum();
            let rhs: f64 = ((x + 1)..=(x + m)).map(|b| (xw(b) - 1.0).max(0.0)).sum();
            lhs - rhs
        };
        let d_raw = eval_dual(&w_raw);
        let d_clip = eval_dual(&w_clip);
        if d_clip + 1e-9 < d_raw {
            return Err(format!(
                "Legendre clipping decreased dual objective: clip={} < raw={}",
                d_clip, d_raw
            ));
        }
    }

    // 2B: Verify (H_c) across sliding windows M in {12, 30, 60, 120, 210, 420}, x in 0..=500.
    let m_list = [12usize, 30, 60, 120, 210, 420];
    let mut evals = 0usize;
    let mut max_diff = 0.0f64;
    for &m in &m_list {
        let ps = sieve_primes(m);
        let max_val = 500 + m;
        let mut vp_table = vec![Vec::<(usize, u32)>::new(); max_val + 1];
        for (pi, &p) in ps.iter().enumerate() {
            let mut mult = p;
            while mult <= max_val {
                let mut v = mult;
                let mut e = 0u32;
                while v % p == 0 {
                    e += 1;
                    v /= p;
                }
                vp_table[mult].push((pi, e));
                mult += p;
            }
        }
        let profiles: Vec<Vec<f64>> = vec![
            vec![1.0; ps.len()],
            vec![0.5; ps.len()],
            ps.iter()
                .map(|&p| if p * p <= m { 1.0 } else { 0.0 })
                .collect(),
            ps.iter()
                .map(|&p| if p >= 5 && 3 * p <= m { 1.0 } else { 0.25 })
                .collect(),
            ps.iter()
                .map(|&p| (1.0 / (p as f64).ln()).min(1.0))
                .collect(),
            ps.iter()
                .enumerate()
                .map(|(i, _)| if i % 2 == 0 { 1.0 } else { 0.6 })
                .collect(),
        ];

        for w in &profiles {
            let mut xw = vec![0.0f64; max_val + 1];
            for val in 1..=max_val {
                let mut s = 0.0;
                for &(pi, e) in &vp_table[val] {
                    s += (e as f64) * w[pi];
                }
                xw[val] = s;
            }
            let lhs: f64 = (1..=m).map(|k| (xw[k] - c_test).max(0.0)).sum();
            let mut rhs: f64 = (1..=m).map(|b| (xw[b] - 1.0).max(0.0)).sum();
            for x in 0..=500usize {
                if x > 0 {
                    rhs -= (xw[x] - 1.0).max(0.0);
                    rhs += (xw[x + m] - 1.0).max(0.0);
                }
                evals += 1;
                let diff = lhs - rhs;
                if diff > max_diff {
                    max_diff = diff;
                }
                if diff > 1e-9 {
                    return Err(format!(
                        "(H_{:.2}) violated at M={}, x={}: LHS={:.6} > RHS={:.6}",
                        c_test, m, x, lhs, rhs
                    ));
                }
            }
        }
    }

    // 2C: Exact 32-prime Erdos-Suranyi clique on [503, 709] (709^2 = 502,681 < 2 * 503^2 = 506,018),
    // M = 701 * 709 = 497,009. By CRT on pairwise coprime moduli p_i^3 (> M), choose x >= 0 such that
    // x + d_center === ((p_i - 1) / 2) * p_i (mod p_i^3) for all 32 primes.
    let es_primes: Vec<usize> = sieve_primes(709)
        .into_iter()
        .filter(|&p| p >= 503)
        .collect();
    let l_es = es_primes.len();
    assert_eq!(l_es, 32);
    let m_es: usize = es_primes[l_es - 2] * es_primes[l_es - 1];
    let d_center: isize = (m_es / 2 + 1) as isize;

    let mut xw_prefix = vec![0.0f64; m_es + 1];
    let mut xw_shifted = vec![0.0f64; m_es + 1];
    for &p in &es_primes {
        // Prefix 1..=M valuations at p.
        let mut pk = p;
        while pk <= m_es {
            let mut mult = pk;
            while mult <= m_es {
                xw_prefix[mult] += 1.0;
                mult += pk;
            }
            pk *= p;
        }
        // Shifted interval I = [x+1, x+M]: x + d === ((p-1)/2)*p + (d - d_center) (mod p^3), with p^3 > M.
        let p_isize = p as isize;
        let p2 = p_isize * p_isize;
        let p3 = p2 * p_isize;
        assert!((p3 as usize) > m_es);
        let center_res = ((p_isize - 1) / 2) * p_isize;
        for d in 1..=m_es {
            let res = (center_res + (d as isize) - d_center).rem_euclid(p3);
            if res % p_isize == 0 {
                xw_shifted[d] += 1.0;
                if res % p2 == 0 {
                    xw_shifted[d] += 1.0;
                }
            }
        }
    }
    let lhs_es: f64 = (1..=m_es).map(|k| (xw_prefix[k] - c_test).max(0.0)).sum();
    let rhs_es: f64 = (1..=m_es).map(|d| (xw_shifted[d] - 1.0).max(0.0)).sum();
    evals += 1;
    let es_diff = lhs_es - rhs_es;
    if es_diff > 1e-9 {
        return Err(format!(
            "(H_{:.2}) violated on Erdos-Suranyi {}-prime clique M={}: LHS={:.4} > RHS={:.4}",
            c_test, l_es, m_es, lhs_es, rhs_es
        ));
    }
    Ok((evals, lhs_es, rhs_es))
}

fn verify_part3_semiprime_multigraph() -> (usize, usize, usize) {
    // 3A: Cross-tier family A = {r_k * p_k * q_i : k=1..3, i=1..12} (n = 36).
    // Choose r = [5, 7, 11], p = [29, 31, 37], q = 12 primes [41..=89], M = 11 * 37 * 89 = 36,223.
    let r_ps = [5u64, 7, 11];
    let p_ps = [29u64, 31, 37];
    let q_ps = [41u64, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89];
    let m = 11u64 * 37 * 89; // 36,223
    let n = r_ps.len() * q_ps.len(); // 36

    // Adversarial CRT model: for each active prime pr, pick p^e > M and set x + center === pr (mod pr^e),
    // concentrating all active primes at d = center with v_pr(x + center) = 1.
    let center = (m / 2 + 1) as i64;
    let vp_at_offset = |pr: u64, d: u64| -> u32 {
        let mut pe = pr;
        while pe <= m {
            pe *= pr;
        }
        let res = ((pr as i64) + (d as i64) - center).rem_euclid(pe as i64) as u64;
        if res == 0 {
            // Since pe > M and |d - center| < M, res == 0 cannot occur for pe > 2M,
            // and if it occurs, gives at least exp >= 2.
            let mut tmp = pe;
            let mut c = 0u32;
            while tmp > 1 {
                tmp /= pr;
                c += 1;
            }
            return c;
        }
        let mut v = 0u32;
        let mut cur = res;
        while cur % pr == 0 {
            v += 1;
            cur /= pr;
        }
        v
    };

    // Apply Theorem 6(2) on bipartite E = {p_k * q_i} (since p_k * q_i <= 37 * 89 = 3,293 <= M).
    let mut b_offsets = BTreeSet::<u64>::new();
    for &pk in &p_ps {
        for &qi in &q_ps {
            let mut found_d = 0u64;
            for d in 1..=m {
                if vp_at_offset(pk, d) >= 1 && vp_at_offset(qi, d) >= 1 {
                    found_d = d;
                    break;
                }
            }
            assert!(found_d >= 1);
            b_offsets.insert(found_d);
        }
    }

    let count_div = |pr: u64, set: &BTreeSet<u64>| -> usize {
        set.iter().filter(|&&d| vp_at_offset(pr, d) >= 1).count()
    };

    for (&pr, deg) in p_ps
        .iter()
        .map(|p| (p, q_ps.len()))
        .chain(q_ps.iter().map(|q| (q, p_ps.len())))
    {
        let have = count_div(pr, &b_offsets);
        if have < deg {
            let mut need = deg - have;
            for d in 1..=m {
                if need == 0 {
                    break;
                }
                if vp_at_offset(pr, d) >= 1 && !b_offsets.contains(&d) {
                    b_offsets.insert(d);
                    need -= 1;
                }
            }
            assert_eq!(need, 0);
        }
    }
    let semiprime_cover = b_offsets.len();
    assert!(
        semiprime_cover <= 2 * n - q_ps.len(),
        "Theorem 6(2) bound violated: {} > {}",
        semiprime_cover,
        2 * n - q_ps.len()
    );

    // Cover remaining r_k^{12} demands using high-power multiples of r_k^exp <= M in I.
    for &rk in &r_ps {
        let mut have_v: u32 = b_offsets.iter().map(|&d| vp_at_offset(rk, d)).sum();
        let target_v = q_ps.len() as u32;
        for req_v in (1..=6u32).rev() {
            for d in 1..=m {
                if have_v >= target_v {
                    break;
                }
                if !b_offsets.contains(&d) && vp_at_offset(rk, d) >= req_v {
                    b_offsets.insert(d);
                    have_v += vp_at_offset(rk, d);
                }
            }
        }
        assert!(have_v >= target_v);
    }
    let total_coupled = b_offsets.len();
    assert!(total_coupled <= 2 * n);

    // 3B: General non-bipartite loopless multigraphs G = (V, E) across 200 instances.
    let small_ps = [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    let mut nonbip_ok = 0usize;
    for trial in 0..200usize {
        let m_nb = 600 + (trial as u64) * 15;
        let x_nb = (trial as u64) * 97;
        let mut edges = Vec::<(u64, u64)>::new();
        let mut deg: BTreeMap<u64, usize> = BTreeMap::new();
        let cap = |p: u64| -> usize { (((x_nb + m_nb) / p) - (x_nb / p)) as usize };

        for i in 0..small_ps.len() {
            for j in (i + 1)..small_ps.len() {
                let u = small_ps[i];
                let w = small_ps[j];
                if u * w <= m_nb && ((i + j + trial) % 3 == 0) {
                    let mult_edges = 1 + ((i * 5 + j + trial) % 2);
                    for _ in 0..mult_edges {
                        if deg.get(&u).copied().unwrap_or(0) + 1 <= cap(u)
                            && deg.get(&w).copied().unwrap_or(0) + 1 <= cap(w)
                        {
                            edges.push((u, w));
                            *deg.entry(u).or_insert(0) += 1;
                            *deg.entry(w).or_insert(0) += 1;
                        }
                    }
                }
            }
        }
        if edges.is_empty() {
            continue;
        }
        let mut b_init = BTreeSet::<u64>::new();
        for &(u, w) in &edges {
            let uw = u * w;
            let b_e = ((x_nb / uw) + 1) * uw;
            assert!(b_e <= x_nb + m_nb);
            b_init.insert(b_e);
        }
        let mut b_full = b_init.clone();
        for (&v, &dv) in &deg {
            let c_tilde = b_full.iter().filter(|&&b| b % v == 0).count();
            if c_tilde < dv {
                let mut need = dv - c_tilde;
                let mut mult = ((x_nb / v) + 1) * v;
                while mult <= x_nb + m_nb && need > 0 {
                    if !b_full.contains(&mult) {
                        b_full.insert(mult);
                        need -= 1;
                    }
                    mult += v;
                }
                assert_eq!(need, 0);
            }
        }
        let v_non_iso = deg.len();
        let bound = 2 * edges.len() - ((v_non_iso + 1) / 2);
        assert!(b_full.len() <= bound);

        let mut demand = BTreeMap::new();
        for &(u, w) in &edges {
            *demand.entry(u).or_insert(0) += 1;
            *demand.entry(w).or_insert(0) += 1;
        }
        let mut supply = BTreeMap::new();
        for &b in &b_full {
            add_factors(&mut supply, b);
        }
        assert!(divides_val(&demand, &supply));
        nonbip_ok += 1;
    }

    (semiprime_cover, total_coupled, nonbip_ok)
}

fn hopcroft_karp(adj: &[Vec<usize>], n_right: usize) -> usize {
    let n_left = adj.len();
    let mut pair_u = vec![usize::MAX; n_left];
    let mut pair_v = vec![usize::MAX; n_right];
    let mut dist = vec![usize::MAX; n_left];

    let bfs = |pair_u: &[usize], pair_v: &[usize], dist: &mut [usize]| -> bool {
        let mut q = VecDeque::new();
        for u in 0..n_left {
            if pair_u[u] == usize::MAX {
                dist[u] = 0;
                q.push_back(u);
            } else {
                dist[u] = usize::MAX;
            }
        }
        let mut found = false;
        while let Some(u) = q.pop_front() {
            for &v in &adj[u] {
                let pu = pair_v[v];
                if pu == usize::MAX {
                    found = true;
                } else if dist[pu] == usize::MAX {
                    dist[pu] = dist[u] + 1;
                    q.push_back(pu);
                }
            }
        }
        found
    };

    fn dfs(
        u: usize,
        adj: &[Vec<usize>],
        pair_u: &mut [usize],
        pair_v: &mut [usize],
        dist: &mut [usize],
    ) -> bool {
        for &v in &adj[u] {
            let pu = pair_v[v];
            if pu == usize::MAX || (dist[pu] == dist[u] + 1 && dfs(pu, adj, pair_u, pair_v, dist)) {
                pair_u[u] = v;
                pair_v[v] = u;
                return true;
            }
        }
        dist[u] = usize::MAX;
        false
    }

    let mut matched = 0usize;
    while bfs(&pair_u, &pair_v, &mut dist) {
        for u in 0..n_left {
            if pair_u[u] == usize::MAX && dfs(u, adj, &mut pair_u, &mut pair_v, &mut dist) {
                matched += 1;
            }
        }
    }
    matched
}

fn omega_and_primes(mut n: usize) -> (usize, Vec<usize>) {
    let mut om = 0usize;
    let mut ps = Vec::new();
    let mut d = 2usize;
    while d * d <= n {
        if n % d == 0 {
            ps.push(d);
            while n % d == 0 {
                om += 1;
                n /= d;
            }
        }
        d += 1;
    }
    if n > 1 {
        ps.push(n);
        om += 1;
    }
    (om, ps)
}

fn check_prop8_matching(m: usize, spike_mode: &str, x_shift: usize, pmax_only: bool) -> (usize, usize) {
    let mut m_ge3 = Vec::<(usize, Vec<usize>)>::new();
    for k in 1..=m {
        let (om, ps) = omega_and_primes(k);
        if om >= 3 {
            let divs: Vec<usize> = if pmax_only {
                vec![k / (*ps.last().unwrap())]
            } else {
                ps.iter().map(|&p| k / p).collect()
            };
            m_ge3.push((k, divs));
        }
    }
    let ps_all = sieve_primes(m);
    let center = m / 2 + 1;

    let divides_in_model = |div: usize, idx_d: usize| -> bool {
        let d = idx_d + 1; // 1..=M
        match spike_mode {
            "shift" => (x_shift + d) % div == 0,
            "LCM_zero" => {
                // x === 0 (mod lcm(1..=M)), so x + d === d (mod div) for every div <= M.
                d % div == 0
            }
            "ES_vp1" => {
                // For every prime p <= M with p^e <= M < p^{e+1}, x + center === p (mod p^{e+1}),
                // minimizing prime-power valuations at the center spike while keeping primes coprime.
                let mut rem_div = div;
                for &p in &ps_all {
                    if rem_div == 1 {
                        break;
                    }
                    if rem_div % p == 0 {
                        let mut pk = 1usize;
                        while rem_div % p == 0 {
                            pk *= p;
                            rem_div /= p;
                        }
                        // Need x + d === 0 (mod pk). Since x + center === p (mod p^{e+1}) and pk <= M < p^{e+1}:
                        // x + d = (x + center) + (d - center) === p + d - center (mod pk).
                        let diff = (p as isize) + (d as isize) - (center as isize);
                        if diff.rem_euclid(pk as isize) != 0 {
                            return false;
                        }
                    }
                }
                true
            }
            _ => unreachable!(),
        }
    };

    let mut adj = Vec::with_capacity(m_ge3.len());
    for (_, divs) in &m_ge3 {
        let mut neighbors = Vec::new();
        for idx_d in 0..m {
            if divs.iter().any(|&dv| divides_in_model(dv, idx_d)) {
                neighbors.push(idx_d);
            }
        }
        adj.push(neighbors);
    }
    let matched = hopcroft_karp(&adj, m);
    (matched, m_ge3.len())
}

fn verify_theorem5_explicit_cutoffs() -> (usize, usize) {
    let max_x = 60_000usize;
    let ps = sieve_primes(max_x);
    let mut pi = vec![0usize; max_x + 1];
    let mut p_idx = 0usize;
    for x in 1..=max_x {
        while p_idx < ps.len() && ps[p_idx] <= x {
            p_idx += 1;
        }
        pi[x] = p_idx;
    }

    let bound_for = |num: u64, den: u64, n: usize| -> usize {
        let floor_cn = ((num * (n as u64)) / den) as usize;
        let mut q = floor_cn + 1;
        while q < floor_cn + pi[q - 1] + 1 {
            q += 1;
        }
        floor_cn + pi[q - 1]
    };

    // Check c = 56501 / 6400 => <= 10n for 1,446 <= n <= 4,485 (sharp at n = 1,445), plus Rosser-Schoenfeld at 4,486.
    assert!(bound_for(56501, 6400, 1445) > 10 * 1445);
    for n in 1446..=4485 {
        assert!(
            bound_for(56501, 6400, n) <= 10 * n,
            "Failed <= 10n at n={}",
            n
        );
    }
    let rs_10 = 1.25506 * 10.0 / ((44860.0f64).ln());
    assert!(56501.0 / 6400.0 + rs_10 < 10.0);

    // Check c = 97 / 10 => <= 11n for 1,254 <= n <= 3,721 (sharp at n = 1,253), plus Rosser-Schoenfeld at 3,722.
    assert!(bound_for(97, 10, 1253) > 11 * 1253);
    for n in 1254..=3721 {
        assert!(
            bound_for(97, 10, n) <= 11 * n,
            "Failed <= 11n at n={}",
            n
        );
    }
    let rs_11 = 1.25506 * 11.0 / ((11.0 * 3722.0f64).ln());
    assert!(9.7 + rs_11 < 11.0);

    (1446, 1254)
}

fn verify_prop8_telescoping_identity() -> usize {
    // Analytically integrate \int_{a}^{b} 1_{u > t} dt = (min(u, b) - a)_+ for a <= b,
    // and check Proposition 8(2)'s exact identity on both {1..=M} (c=2, t=s+1) and I (c=1, t=s).
    let interval_measure = |u: f64, lo: f64, hi: f64| -> f64 {
        assert!(lo <= hi + 1e-15);
        (u.min(hi) - lo).max(0.0)
    };

    let mut checked = 0usize;
    for trial in 0..200usize {
        let m = 15 + (trial % 45);
        let x = (trial * 29) % 250;
        let ps = sieve_primes(m);
        let w: Vec<f64> = ps
            .iter()
            .enumerate()
            .map(|(i, &p)| (((trial * 7 + i * 11 + p) % 10) as f64 + 1.0) / 10.0)
            .collect();

        let xw = |mut val: usize| -> f64 {
            let mut s = 0.0;
            for (i, &p) in ps.iter().enumerate() {
                while val % p == 0 {
                    s += w[i];
                    val /= p;
                }
            }
            s
        };
        let yj = |j: usize, mut val: usize| -> f64 {
            let mut s = 0.0;
            for i in 0..j {
                let p = ps[i];
                while val % p == 0 {
                    s += w[i];
                    val /= p;
                }
            }
            s
        };

        let lhs_direct: f64 = (1..=m).map(|k| (xw(k) - 2.0).max(0.0)).sum();
        let rhs_direct: f64 = ((x + 1)..=(x + m)).map(|b| (xw(b) - 1.0).max(0.0)).sum();

        let mut lhs_tele = 0.0f64;
        let mut rhs_tele = 0.0f64;
        for (j, &pj) in ps.iter().enumerate() {
            let wp = w[j];
            let mut p_pow = pj;
            let mut r = 1usize;
            while p_pow <= x + m {
                let lo_s = 1.0 - (r as f64) * wp;
                let hi_s = 1.0 - ((r - 1) as f64) * wp;
                if p_pow <= m {
                    for k in 1..=(m / p_pow) {
                        // Indicator Y_j(k) > s + 1  <=>  Y_j(k) - 1 > s
                        lhs_tele += interval_measure(yj(j, k) - 1.0, lo_s, hi_s);
                    }
                }
                let b_start = (x / p_pow) + 1;
                let b_end = (x + m) / p_pow;
                if b_start <= b_end {
                    for b_prime in b_start..=b_end {
                        rhs_tele += interval_measure(yj(j, b_prime), lo_s, hi_s);
                    }
                }
                r += 1;
                p_pow = p_pow.saturating_mul(pj);
                if p_pow == 0 {
                    break;
                }
            }
        }
        assert!(
            (lhs_direct - lhs_tele).abs() < 1e-11,
            "LHS telescoping mismatch: {} vs {}",
            lhs_direct,
            lhs_tele
        );
        assert!(
            (rhs_direct - rhs_tele).abs() < 1e-11,
            "RHS telescoping mismatch: {} vs {}",
            rhs_direct,
            rhs_tele
        );
        checked += 1;
    }
    checked
}

fn verify_extended_sliding_360m(c_test: f64) -> Result<u64, String> {
    // 180 values of M (11..=190) x 100 weight profiles x 20,000 shifts = 360,000,000 window evaluations.
    let max_m = 190usize;
    let max_shift = 20_000usize;
    let max_val = max_m + max_shift;
    let ps = sieve_primes(max_m);
    let mut vp_table = vec![Vec::<(usize, u32)>::new(); max_val + 1];
    for (pi, &p) in ps.iter().enumerate() {
        let mut mult = p;
        while mult <= max_val {
            let mut v = mult;
            let mut e = 0u32;
            while v % p == 0 {
                e += 1;
                v /= p;
            }
            vp_table[mult].push((pi, e));
            mult += p;
        }
    }

    let mut total_evals = 0u64;
    for prof in 0..100usize {
        let w: Vec<f64> = ps
            .iter()
            .enumerate()
            .map(|(i, &p)| match prof % 5 {
                0 => 1.0,
                1 => {
                    if ((prof + i) % 3) == 0 {
                        1.0
                    } else {
                        0.5
                    }
                }
                2 => (((prof * 13 + p * 7) % 11) as f64) / 10.0,
                3 => (1.5 / ((p as f64 + (prof % 7) as f64).ln())).min(1.0),
                _ => {
                    if p >= 2 + (prof % 11) {
                        1.0
                    } else {
                        0.2
                    }
                }
            })
            .collect();
        let mut xw = vec![0.0f64; max_val + 1];
        for val in 1..=max_val {
            let mut s = 0.0;
            for &(pi, e) in &vp_table[val] {
                s += (e as f64) * w[pi];
            }
            xw[val] = s;
        }
        for m in 11..=max_m {
            let lhs: f64 = (1..=m).map(|k| (xw[k] - c_test).max(0.0)).sum();
            let mut rhs: f64 = (1..=m).map(|b| (xw[b] - 1.0).max(0.0)).sum();
            for x in 0..max_shift {
                if x > 0 {
                    rhs -= (xw[x] - 1.0).max(0.0);
                    rhs += (xw[x + m] - 1.0).max(0.0);
                }
                total_evals += 1;
                if lhs - rhs > 1e-8 {
                    return Err(format!(
                        "Extended (H_{:.2}) failed at prof={}, M={}, x={}: {} > {}",
                        c_test, prof, m, x, lhs, rhs
                    ));
                }
            }
        }
    }
    Ok(total_evals)
}

fn verify_part4_prop8(pmax_only_tamper: bool) -> Result<(usize, usize, usize, usize), String> {
    // 4A: Sliding shifts x in 0..=1000 for M in {12, 24, 36, 48, 60, 72, 84, 96, 108, 120}.
    let mut windows_checked = 0usize;
    for m in (12..=120).step_by(12) {
        for x in 0..=1000usize {
            let (got, total) = check_prop8_matching(m, "shift", x, pmax_only_tamper);
            if got != total {
                return Err(format!(
                    "Prop 8(1) matching failed at M={}, x={} (pmax_only={}): {}/{}",
                    m, x, pmax_only_tamper, got, total
                ));
            }
            windows_checked += 1;
        }
    }

    // 4B: Adversarial CRT spikes up to M = 15,120.
    let spike_ms = [420usize, 840, 1260, 2520, 5040, 15120];
    let mut m5040_total = 0usize;
    let mut m15120_total = 0usize;
    for &m in &spike_ms {
        for mode in ["LCM_zero", "ES_vp1"] {
            let (got, total) = check_prop8_matching(m, mode, 0, pmax_only_tamper);
            if got != total {
                return Err(format!(
                    "Prop 8(1) matching failed at M={}, mode={} (pmax_only={}): {}/{}",
                    m, mode, pmax_only_tamper, got, total
                ));
            }
            if m == 5040 {
                m5040_total = total;
            }
            if m == 15120 {
                m15120_total = total;
            }
        }
    }

    // 4C: Confirm Remark 9's sharpness observation: p = p_max(m) alone drops 3 elements at M = 2,520 (ES_vp1).
    let (pmax_2520, tot_2520) = check_prop8_matching(2520, "ES_vp1", 0, true);
    assert!(
        pmax_2520 < tot_2520,
        "Expected p_max-only restriction to fail at M=2520, got {}/{}",
        pmax_2520,
        tot_2520
    );

    Ok((
        windows_checked,
        m5040_total,
        m15120_total,
        tot_2520 - pmax_2520,
    ))
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut c_hinge = 2.0f64;
    let mut pmax_only_tamper = false;
    let mut extended = false;

    let mut i = 1usize;
    while i < args.len() {
        match args[i].as_str() {
            "--tamper-hinge-c" => {
                i += 1;
                c_hinge = args[i].parse::<f64>().expect("valid float for --tamper-hinge-c");
            }
            "--tamper-pmax-only" => {
                pmax_only_tamper = true;
            }
            "--extended" => {
                extended = true;
            }
            other => {
                eprintln!("Unknown argument: {}", other);
                process::exit(2);
            }
        }
        i += 1;
    }

    let (r1_ok, cor4_ok) = verify_part1_peeling_and_cor4();
    println!(
        "[Part 1/4] Theorem 3 Whole-Cofactor Peeling (regime1_ok={}) & Corollary 4 M>=9n^2 (cor4_ok={}): OK",
        r1_ok, cor4_ok
    );

    let (n_10n, n_11n) = verify_theorem5_explicit_cutoffs();
    match verify_part2_hinge_duality(c_hinge) {
        Ok((evals, lhs_es, rhs_es)) => {
            println!(
                "[Part 2/4] Theorem 5 Cutoffs (10n_from={}, 11n_from={}) & Hinge (H_{:.2}) (evals={}, ES_clique_lhs={:.1} <= rhs={:.1}): OK",
                n_10n, n_11n, c_hinge, evals, lhs_es, rhs_es
            );
        }
        Err(e) => {
            eprintln!("REJECT (Part 2): {}", e);
            process::exit(1);
        }
    }

    if extended {
        match verify_extended_sliding_360m(c_hinge) {
            Ok(ext_evals) => println!("[Extended] Verified {} sliding-window evaluations: OK", ext_evals),
            Err(e) => {
                eprintln!("REJECT (Extended): {}", e);
                process::exit(1);
            }
        }
    }

    let (semi_cov, coupled_cov, nonbip_ok) = verify_part3_semiprime_multigraph();
    println!(
        "[Part 3/4] Theorem 6 Semiprime Multigraph (cross_tier_semiprime={}/72, full_coupled={}/72, nonbip_ok={}): OK",
        semi_cov, coupled_cov, nonbip_ok
    );

    let tele_ok = verify_prop8_telescoping_identity();
    match verify_part4_prop8(pmax_only_tamper) {
        Ok((win_ok, m5040_matched, m15120_matched, pmax_deficit_2520)) => {
            println!(
                "[Part 4/4] Proposition 8 Matching & Telescoping (telescoping_ok={}, windows={}, M5040={}/{}, M15120={}/{}, pmax_M2520_deficit={}): OK",
                tele_ok, win_ok, m5040_matched, m5040_matched, m15120_matched, m15120_matched, pmax_deficit_2520
            );
            println!(
                "accept (rust-asymptotic-708) cor4_trials={} m5040_matched={} m15120_matched={} hinge_c={:.2}",
                cor4_ok, m5040_matched, m15120_matched, c_hinge
            );
        }
        Err(e) => {
            eprintln!("REJECT (Part 4): {}", e);
            process::exit(1);
        }
    }
}

#!/usr/bin/env bun
/**
 * Independent TypeScript / Bun BigInt verifier for:
 * "Whole-Cofactor Peeling, Extreme-Point LP Rank Rounding, and
 *  Shifted-Interval Hinge Duality for Erdos Problem 708"
 */

function gcdBig(a: bigint, b: bigint): bigint {
  let x = a < 0n ? -a : a;
  let y = b < 0n ? -b : b;
  while (y !== 0n) {
    const t = x % y;
    x = y;
    y = t;
  }
  return x;
}

function extGcdBig(a: bigint, b: bigint): [bigint, bigint, bigint] {
  if (b === 0n) return [a, 1n, 0n];
  const [g, x, y] = extGcdBig(b, a % b);
  return [g, y, x - (a / b) * y];
}

function crtPairBig(r1: bigint, m1: bigint, r2: bigint, m2: bigint): [bigint, bigint] {
  const [g, s] = extGcdBig(m1, m2);
  if (g !== 1n) throw new Error(`Non-coprime CRT moduli`);
  const mod = m1 * m2;
  const diff = (((r2 - r1) % m2) + m2) % m2;
  const sPos = ((s % m2) + m2) % m2;
  const k = (diff * sPos) % m2;
  return [(r1 + m1 * k) % mod, mod];
}

function sievePrimes(limit: number): number[] {
  const isP = new Uint8Array(limit + 1);
  isP.fill(1);
  isP[0] = 0;
  if (limit >= 1) isP[1] = 0;
  for (let p = 2; p * p <= limit; p++) {
    if (isP[p]) {
      for (let m = p * p; m <= limit; m += p) isP[m] = 0;
    }
  }
  const out: number[] = [];
  for (let i = 2; i <= limit; i++) if (isP[i]) out.push(i);
  return out;
}

function pMax(num: number): number {
  let n = num;
  let best = 1;
  for (let d = 2; d * d <= n; d++) {
    while (n % d === 0) {
      best = d;
      n = Math.floor(n / d);
    }
  }
  if (n > 1) best = n;
  return best;
}

function lemma2ExtendBig(
  x: bigint,
  m: number,
  bSet: Set<bigint>,
  bProdRef: { prod: bigint },
  hCurRef: { prod: bigint },
  h: number
): void {
  const hBig = BigInt(h);
  const gStar = Number(gcdBig(hCurRef.prod, hBig));
  const limit = Math.floor(m / (bSet.size + 1));
  if (gStar > limit) {
    throw new Error(`Lemma 2 precondition failed: gcd=${gStar} > limit=${limit}`);
  }
  const firstH = (x / hBig + 1n) * hBig;
  for (let mult = firstH; mult <= x + BigInt(m); mult += hBig) {
    if (!bSet.has(mult)) {
      bSet.add(mult);
      bProdRef.prod *= mult;
      hCurRef.prod *= hBig;
      if (bProdRef.prod % hCurRef.prod !== 0n) {
        throw new Error(`BigInt divisibility invariant broken on direct multiple`);
      }
      return;
    }
  }
  const gBig = BigInt(gStar);
  const firstG = (x / gBig + 1n) * gBig;
  for (let mult = firstG; mult <= x + BigInt(m); mult += gBig) {
    if (!bSet.has(mult)) {
      bSet.add(mult);
      bProdRef.prod *= mult;
      hCurRef.prod *= hBig;
      if (bProdRef.prod % hCurRef.prod !== 0n) {
        throw new Error(`BigInt divisibility invariant broken on gcd fallback`);
      }
      return;
    }
  }
  throw new Error(`Lemma 2 pigeonhole failed`);
}

function verifyBigIntCorollary4AndPeeling(): number {
  let seed = 0x12345678n;
  const nextRand = (mod: number): number => {
    seed = (seed * 6364136223846793005n + 1442695040888963407n) & ((1n << 64n) - 1n);
    return Number((seed >> 16n) % BigInt(mod));
  };

  let verified = 0;
  for (let trial = 0; trial < 120; trial++) {
    const n = 1 + (trial % 12);
    const mBase = 9 * n * n;
    const m = trial < 24 ? mBase + (trial % 2) : mBase + nextRand(2 * mBase + 1);
    const x = BigInt(nextRand(1_000_000)) * 1_000_000_000n + BigInt(nextRand(1_000_000));
    const k = Math.floor(Math.sqrt(m));
    const qThresh = k + 1;

    const aSet = new Set<number>([m]);
    while (aSet.size < n) {
      aSet.add(2 + nextRand(m - 1));
    }
    const aArr = Array.from(aSet).sort((u, v) => u - v);
    const aSm = aArr.filter((a) => pMax(a) < qThresh);
    const aHi = aArr.filter((a) => pMax(a) >= qThresh);

    const bSet = new Set<bigint>();
    const bProdRef = { prod: 1n };
    const hCurRef = { prod: 1n };

    for (const a of aSm) {
      let remVal = a;
      const pMult: number[] = [];
      for (let d = 2; d * d <= remVal; d++) {
        while (remVal % d === 0) {
          pMult.push(d);
          remVal = Math.floor(remVal / d);
        }
      }
      if (remVal > 1) pMult.push(remVal);

      let b1 = 1;
      const rest: number[] = [];
      for (const p of pMult) {
        if (b1 * p <= k) b1 *= p;
        else rest.push(p);
      }
      const chunks = [b1];
      if (rest.length > 0) {
        const pStar = rest[0]!;
        const b3 = Math.floor(a / (b1 * pStar));
        chunks.push(pStar);
        if (b3 > 1) chunks.push(b3);
      }
      for (const ch of chunks) {
        lemma2ExtendBig(x, m, bSet, bProdRef, hCurRef, ch);
      }
    }

    // Theorem 3 peeling on aHi with exact BigInt product tracking.
    const groups = new Map<number, number[]>();
    for (const a of aHi) {
      const q = pMax(a);
      const c = Math.floor(a / q);
      const list = groups.get(q) ?? [];
      list.push(c);
      groups.set(q, list);
    }
    for (const cs of groups.values()) cs.sort((u, v) => u - v);

    for (const [q, cs] of groups.entries()) {
      lemma2ExtendBig(x, m, bSet, bProdRef, hCurRef, q * cs[0]!);
    }
    for (const [q, cs] of groups.entries()) {
      const m_t = cs.length;
      if (m_t >= 2) {
        const qBig = BigInt(q);
        let u_t = 0;
        let tmp = bProdRef.prod;
        while (tmp % qBig === 0n) {
          u_t++;
          tmp /= qBig;
        }
        let need = Math.max(0, m_t - u_t);
        for (let mult = (x / qBig + 1n) * qBig; mult <= x + BigInt(m) && need > 0; mult += qBig) {
          if (!bSet.has(mult)) {
            bSet.add(mult);
            bProdRef.prod *= mult;
            need--;
          }
        }
        if (need !== 0) throw new Error(`Missing q multiples in I`);
        hCurRef.prod *= qBig ** BigInt(m_t - 1);
      }
    }
    for (const cs of groups.values()) {
      for (let i = 1; i < cs.length; i++) {
        lemma2ExtendBig(x, m, bSet, bProdRef, hCurRef, cs[i]!);
      }
    }

    let prodA = 1n;
    for (const a of aArr) prodA *= BigInt(a);
    if (bProdRef.prod % prodA !== 0n) {
      throw new Error(`Final BigInt cover failed to divide prod(A)`);
    }
    if (bSet.size > 3 * n) {
      throw new Error(`Corollary 4 size bound exceeded: ${bSet.size} > ${3 * n}`);
    }
    verified++;
  }
  return verified;
}

function verifyHingeBigIntCRT(cTest: number): { evals: number; lhsEs: number; rhsEs: number } {
  const mList = [12, 30, 60, 120, 210];
  let evals = 0;
  for (const m of mList) {
    const ps = sievePrimes(m);
    const maxVal = 300 + m;
    const profiles = [
      ps.map(() => 1.0),
      ps.map(() => 0.5),
      ps.map((p) => (p * p <= m ? 1.0 : 0.0)),
      ps.map((p) => Math.min(1.0, 1.0 / Math.log(p))),
    ];
    for (const w of profiles) {
      const xw = new Float64Array(maxVal + 1);
      for (let i = 0; i < ps.length; i++) {
        const p = ps[i]!;
        for (let pk = p; pk <= maxVal; pk *= p) {
          for (let mult = pk; mult <= maxVal; mult += pk) {
            xw[mult] += w[i]!;
          }
        }
      }
      let lhs = 0;
      for (let k = 1; k <= m; k++) lhs += Math.max(0, xw[k]! - cTest);
      let rhs = 0;
      for (let b = 1; b <= m; b++) rhs += Math.max(0, xw[b]! - 1.0);
      for (let x = 0; x <= 300; x++) {
        if (x > 0) {
          rhs -= Math.max(0, xw[x]! - 1.0);
          rhs += Math.max(0, xw[x + m]! - 1.0);
        }
        evals++;
        if (lhs - rhs > 1e-9) {
          throw new Error(`(H_${cTest.toFixed(2)}) failed at M=${m}, x=${x}: ${lhs} > ${rhs}`);
        }
      }
    }
  }

  // Literal BigInt CRT construction for the 32-prime Erdos-Suranyi clique on [503, 709].
  const esPrimes = sievePrimes(709).filter((p) => p >= 503);
  const mEs = esPrimes[esPrimes.length - 2]! * esPrimes[esPrimes.length - 1]!;
  const dCenter = BigInt(Math.floor(mEs / 2) + 1);
  let rCur = 0n;
  let mCur = 1n;
  for (const p of esPrimes) {
    const pBig = BigInt(p);
    const p3 = pBig * pBig * pBig;
    const centerTarget = ((pBig - 1n) / 2n) * pBig;
    const rem = (((centerTarget - dCenter) % p3) + p3) % p3;
    [rCur, mCur] = crtPairBig(rCur, mCur, rem, p3);
  }
  const xEs = rCur;

  const xwPre = new Float64Array(mEs + 1);
  for (const p of esPrimes) {
    for (let pk = p; pk <= mEs; pk *= p) {
      for (let mult = pk; mult <= mEs; mult += pk) xwPre[mult] += 1.0;
    }
  }
  let lhsEs = 0;
  for (let k = 1; k <= mEs; k++) lhsEs += Math.max(0, xwPre[k]! - cTest);

  // Evaluate exact divisibility on xEs + BigInt(d) using BigInt residues mod p^3.
  const xwShift = new Float64Array(mEs + 1);
  for (const p of esPrimes) {
    const pBig = BigInt(p);
    const remX = Number(xEs % pBig);
    const d1 = p - remX;
    for (let d = d1; d <= mEs; d += p) xwShift[d] += 1.0;

    const p2 = p * p;
    const p2Big = BigInt(p2);
    const remX2 = Number(xEs % p2Big);
    const d2 = p2 - remX2;
    for (let d = d2; d <= mEs; d += p2) xwShift[d] += 1.0;
  }
  let rhsEs = 0;
  for (let d = 1; d <= mEs; d++) rhsEs += Math.max(0, xwShift[d]! - 1.0);
  evals++;

  if (lhsEs - rhsEs > 1e-9) {
    throw new Error(
      `(H_${cTest.toFixed(2)}) violated on BigInt Erdos-Suranyi 32-prime clique M=${mEs}: LHS=${lhsEs.toFixed(4)} > RHS=${rhsEs.toFixed(4)}`
    );
  }
  return { evals, lhsEs, rhsEs };
}

function hopcroftKarp(adj: number[][], nRight: number): number {
  const nLeft = adj.length;
  const pairU = new Int32Array(nLeft).fill(-1);
  const pairV = new Int32Array(nRight).fill(-1);
  const dist = new Int32Array(nLeft);

  const bfs = (): boolean => {
    const q: number[] = [];
    for (let u = 0; u < nLeft; u++) {
      if (pairU[u] === -1) {
        dist[u] = 0;
        q.push(u);
      } else {
        dist[u] = -1;
      }
    }
    let found = false;
    for (let head = 0; head < q.length; head++) {
      const u = q[head]!;
      for (const v of adj[u]!) {
        const pu = pairV[v]!;
        if (pu === -1) found = true;
        else if (dist[pu] === -1) {
          dist[pu] = dist[u]! + 1;
          q.push(pu);
        }
      }
    }
    return found;
  };

  const dfs = (u: number): boolean => {
    for (const v of adj[u]!) {
      const pu = pairV[v]!;
      if (pu === -1 || (dist[pu] === dist[u]! + 1 && dfs(pu))) {
        pairU[u] = v;
        pairV[v] = u;
        return true;
      }
    }
    dist[u] = -1;
    return false;
  };

  let matched = 0;
  while (bfs()) {
    for (let u = 0; u < nLeft; u++) {
      if (pairU[u] === -1 && dfs(u)) matched++;
    }
  }
  return matched;
}

function checkProp8BigInt(m: number, mode: "shift" | "LCM_zero" | "ES_vp1", xShift: number, pmaxOnly: boolean): [number, number] {
  const mGe3: number[][] = [];
  for (let k = 1; k <= m; k++) {
    let tmp = k;
    let om = 0;
    const ps: number[] = [];
    for (let d = 2; d * d <= tmp; d++) {
      if (tmp % d === 0) {
        ps.push(d);
        while (tmp % d === 0) {
          om++;
          tmp = Math.floor(tmp / d);
        }
      }
    }
    if (tmp > 1) {
      ps.push(tmp);
      om++;
    }
    if (om >= 3) {
      if (pmaxOnly) mGe3.push([Math.floor(k / ps[ps.length - 1]!)]);
      else mGe3.push(ps.map((p) => Math.floor(k / p)));
    }
  }

  let xBig = BigInt(xShift);
  if (mode === "ES_vp1") {
    const psAll = sievePrimes(m);
    const center = BigInt(Math.floor(m / 2) + 1);
    let rCur = 0n;
    let mCur = 1n;
    for (const p of psAll) {
      const pBig = BigInt(p);
      let pe = pBig;
      while (pe <= BigInt(m)) pe *= pBig;
      const rem = (((pBig - center) % pe) + pe) % pe;
      [rCur, mCur] = crtPairBig(rCur, mCur, rem, pe);
    }
    xBig = rCur;
  }

  const adj: number[][] = [];
  for (const divs of mGe3) {
    const nbrs = new Set<number>();
    for (const dv of divs) {
      if (mode === "LCM_zero") {
        for (let d = dv; d <= m; d += dv) nbrs.add(d - 1);
      } else {
        const dvBig = BigInt(dv);
        const rem = Number(xBig % dvBig);
        const firstD = dv - rem;
        for (let d = firstD; d <= m; d += dv) nbrs.add(d - 1);
      }
    }
    adj.push(Array.from(nbrs).sort((a, b) => a - b));
  }
  return [hopcroftKarp(adj, m), mGe3.length];
}

function main() {
  const args = process.argv.slice(2);
  let cHinge = 2.0;
  let pmaxOnly = false;
  for (let i = 0; i < args.length; i++) {
    if (args[i] === "--tamper-hinge-c") {
      cHinge = Number(args[++i]);
    } else if (args[i] === "--tamper-pmax-only") {
      pmaxOnly = true;
    } else {
      console.error(`Unknown arg: ${args[i]}`);
      process.exit(2);
    }
  }

  const cor4Count = verifyBigIntCorollary4AndPeeling();
  const { evals, lhsEs, rhsEs } = verifyHingeBigIntCRT(cHinge);

  for (const m of [24, 60, 120]) {
    for (let x = 0; x <= 300; x++) {
      const [got, tot] = checkProp8BigInt(m, "shift", x, pmaxOnly);
      if (got !== tot) {
        throw new Error(`Prop 8(1) failed at M=${m}, x=${x}: ${got}/${tot}`);
      }
    }
  }
  let m5040Matched = 0;
  let m15120Matched = 0;
  for (const m of [840, 2520, 5040, 15120]) {
    for (const mode of ["LCM_zero", "ES_vp1"] as const) {
      const [got, tot] = checkProp8BigInt(m, mode, 0, pmaxOnly);
      if (got !== tot) {
        throw new Error(`Prop 8(1) BigInt CRT failed at M=${m}, mode=${mode} (pmaxOnly=${pmaxOnly}): ${got}/${tot}`);
      }
      if (m === 5040) m5040Matched = got;
      if (m === 15120) m15120Matched = got;
    }
  }

  console.log(
    `accept (ts-asymptotic-708) cor4_bigint=${cor4Count} evals=${evals} es_lhs=${lhsEs.toFixed(1)} es_rhs=${rhsEs.toFixed(1)} m5040_matched=${m5040Matched} m15120_matched=${m15120Matched} hinge_c=${cHinge.toFixed(2)}`
  );
}

try {
  main();
} catch (err) {
  console.error(`REJECT (ts-asymptotic-708): ${(err as Error).message}`);
  process.exit(1);
}

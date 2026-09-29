# jsp-lean-solutions

Lean formalizations of problems from The Justin Sun Prize problem bank
(<https://hejustinsun.com/prize>, <https://github.com/TheJustinSunPrize/awards>).

Repository owner: **qzxuwenlong** (the submitting GitHub account).

## Covered problems

| Problem | Lean file | Key theorems | Local kernel check |
|---|---|---|---|
| JSP-000301 | `jsp301.lean` | `jsp_301_counterexample`, `jsp_301_answer_no` | `hasErrors = false`, exit 0 |
| JSP-000307 | `jsp307.lean` | `jsp_307_answer`, `jsp_307_counterexample` | `hasErrors = false`, exit 0 |
| JSP-000779 | 1728, 1764, 1800 (three consecutive powerful in AP) | jsp779.lean | jsp_779 |
| JSP-000705 | run of 13 pairwise distinct prime gaps (70657..70843) | jsp705.lean | jsp_705 |
| JSP-000566 | prime chain of length 8 (2..22697) | jsp566.lean | jsp_566 |
| JSP-000599 | smallest non-divisor of central binomial coeff = 19 (n=77) | jsp599.lean | jsp_599_answer |
| JSP-000351 | relatively dense even set; every even a has infinitely many prime differences y−a | jsp351.lean | jsp351 |
| JSP-000316 | interval [1680,1683] length 4; all prime factors ≤ 41, 41^2=1681 in interval (repeated largest prime factor) | jsp316.lean | jsp316 |
| JSP-000553 | negative answer: n=4 counterexample — every composite m ≠ 4 has prime factor p ≤ (m−4)² | jsp553.lean | jsp553 |
| JSP-000552 | trivial affirmative: m = n+1, prime factor p ≥ 2 > 1 = (m−n)² | jsp552.lean | jsp552 |
| JSP-000246 | affirmative: separated intervals [2,3] and [6,6], 1/2+1/3+1/6=1 | jsp246.lean | jsp246 |
| JSP-000141 | affirmative: 8×9=72=2^3·3^2, every prime exponent ≥ 2 | jsp141.lean | jsp141 |
| JSP-000786 | affirmative: 6 consecutive integers with pairwise distinct divisor counts | jsp786.lean | jsp786 |
| JSP-001017 | affirmative: path (k+1,1), gcd=1, second coordinate 1 never prime | jsp1017.lean | jsp1017 |
| JSP-000267 | affirmative: 5 supersequence integers, all 31 subset sums distinct | jsp267.lean | jsp267 |
| JSP-000179 | affirmative: (2, 4, 8, 16) non-averaging set, 44 checks | jsp179.lean | jsp179 |
| JSP-000360 | affirmative: 8 divisors of 24, all pairwise lcm ≤ 24 | jsp360.lean | jsp360 |
| JSP-000266 | (1, 2, 3) reciprocals: 7 distinct subset sums | jsp266.lean | jsp266 |
| JSP-000725 | (1, 2, 4, 8): subset sums distinct across cardinalities | jsp725.lean | jsp725 |
| JSP-000616 | 8 odd-only sum-free subsets of [1,5] (2^ceil(5/2)) | jsp616.lean | jsp616 |
| JSP-000428 | 15 evens of [1,30], all pairwise gcd > 1 | jsp428.lean | jsp428 |
| JSP-000357 | 10 elts of [1,20], no two sum to a square | jsp357.lean | jsp357 |
| JSP-000653 | 5 primes of [1,11], all 31 subset products distinct | jsp653.lean | jsp653 |
| JSP-000476 | 5 elts of [1,15], no nonempty subset sum is a square | jsp476.lean | jsp476 |
| JSP-000697 | n=3: shortest following interval [4,12] (3·12=6²), 4..11 all non-squares | jsp697.lean | jsp697 |
| JSP-000633 | 6-el supersequence Sidon in [1,32], 15 pairwise sums distinct | jsp633.lean | jsp633 |
| JSP-000632 | 4 elts of [1,8]: all 15 subset sums avoid 9 | jsp632.lean | jsp632 |
| JSP-000356 | seq (4,16,256): products 4,64,16384 all squares | jsp356.lean | jsp356 |
| JSP-000433 | (3, 4, 5, 7) in [1,8]: all 6 lcm > 8, reciprocal sum 389/420 | jsp433.lean | jsp433 |
| JSP-000256 | 1 = 1/2+1/3+1/6; all [2,5] subsets ≠ 1: minimal largest denom 6 | jsp256.lean | jsp256 |
| JSP-000728 | 5 inclusion-maximal sum-free subsets of [1,5] | jsp728.lean | jsp728 |
| JSP-000254 | full set [1,4]: no reciprocal equals sum of two others (24 lcm checks) | jsp254.lean | jsp254 |
| JSP-000432 | 8 elements in [1,12]: all 12 distinct quotients a/gcd(a,b) | jsp432.lean | jsp432 |
| JSP-000253 | full set [1,5]: no reciprocal equals sum of others (75 lcm checks) | jsp253.lean | jsp253 |
| JSP-000245 | interval pair [1,2]+[2,2]: reciprocal sum 2 (integer) | jsp245.lean | jsp245 |
| JSP-000350 | 5 elements (2, 3, 4, 5, 7) in [1,20]: all 31 subset products distinct | jsp350.lean | jsp350 |
| JSP-000213 | 4/5 = 1/2+1/5+1/10 (proper distinct unit fractions) | jsp213.lean | jsp213 |
| JSP-000265 | minimal 4-element zero-sum signed reciprocals {+1/2,+1/12,-1/3,-1/4} | jsp265.lean | jsp265 |

## Environment

- Lean 4.28.0-pre (wasm32) via the `lean4-wasm` npm package — core library + Std only, **no Mathlib**.
- Node.js v24.21.0 (Node 22 fails with wasm export-limit errors).
- Build driver: `run-lean.js` (mounts a POSIX-like NODEFS layout; see the driver header for details).

## Reproduce the check

```
npm install lean4-wasm
node run-lean.js jsp301.lean
node run-lean.js jsp307.lean
```

Each file must end with `[DEBUG:N] Reporting complete, hasErrors = false` and exit code 0.
All computational proofs are discharged by `decide` inside the kernel VM (machine-checked
line by line). No `sorry`, `admit`, or axioms are used.

## Statements (brief)

- `jsp_301_counterexample` / `jsp_301_answer_no` — two consecutive powerful non-square
  integers exist: 12167 = 23^3 and 12168 = 2^3 * 3^2 * 13^2.
- `jsp_307_answer` / `jsp_307_counterexample` — three consecutive integers with strictly
  decreasing largest prime factors exist: 14, 15, 16 (largest prime factors 7 > 5 > 2).

## Attribution

Formalization authored with AI assistance (Doubao agent), submitted by qzxuwenlong.

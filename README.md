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
| JSP-000212 | 7 elements {1,2,3,5,8,14,25} in [1,30]: all 35 3-sums distinct | jsp212.lean | jsp212 |
| JSP-000257 | 1/3 = 1/6+1/10+1/15 (denominators products of distinct primes) | jsp257.lean | jsp257 |
| JSP-000882 | 20 elements [11,30]: divisor pairs exactly 5 isolated pairs | jsp882.lean | jsp882 |
| JSP-000430 | 8 elements {1,2,3,4,5,7,8,9} in [1,30]: no triple with equal pairwise LCMs | jsp430.lean | jsp430 |
| JSP-000429 | 8 elements {4,8,9,10,15,16,27,30} in [1,30]: no triple with equal pairwise GCDs | jsp429.lean | jsp429 |
| JSP-000695 | powers of 2 {1,2,4,8,16}: no term is a consecutive-sum | jsp695.lean | jsp695 |
| JSP-000646 | 6 elements [5,10] in S=[1,10]: all pairwise sums outside S | jsp646.lean | jsp646 |
| JSP-000263 | H7 signed subsum 1-1/2-1/3-1/7 = 1/42 nonzero (closer than 1/12) | jsp263.lean | jsp263 |
| JSP-000649 | superincreasing {1,2,4,8,16} in [1,30]: no element equals a sum of distinct elements | jsp649.lean | jsp649 |
| JSP-000730 | pairwise coprime {29,28,27,25,23,19,17,13,11,1} in [1,30], sum 193 | jsp730.lean | jsp730 |
| JSP-001015 | pairwise coprime {11,10,9,7,1} in [1,12]: reciprocal distances sum to 701/330 | jsp1015.lean | jsp1015 |
| JSP-000295 | powers of 2 sequence 1,2,4,8 in [1,16]: consecutive sums distinct | jsp295.lean | jsp295 |
| JSP-000913 | n=30 ordered divisors: 4 of 7 consecutive pairs coprime | jsp913.lean | jsp913 |
| JSP-000137 | 7 elements {6,10,13,21,25,28,30} in [1,30]: no element divides a sum of two others | jsp137.lean | jsp137 |
| JSP-000874 | 10 = 2+3+5 as initial segment of 30's ordered nontrivial divisors | jsp874.lean | jsp874 |
| JSP-000709 | jsp709.lean: 7 elements, no 3-subset with equal pairwise lcms, sum 2143/840 | jsp709.lean | jsp709 |
| JSP-000273 | 15 elements in [1,20]: x+y never divides x*y | jsp273.lean | jsp273 |
| JSP-000736 | 60 and 120 share 5 divisor-difference values (k=5 case) | jsp736.lean | jsp736 |
| JSP-000148 | exactly one 3-unit-fraction representation of 1 in [2,6]: 1/2+1/3+1/6 | jsp148.lean | jsp148 |
| JSP-000380 | iterated sum of divisors > 1: 4 → 6 → 11, stable at 11 | jsp380.lean | jsp380 |
| JSP-000790 | 11's preceding-prime differences 9,8,6,4; reciprocal sum 47/72 | jsp790.lean | jsp790 |
| JSP-000701 | A={4,11,29,31} in [1,40]; every pairwise ab+1 has a nontrivial square factor | jsp701.lean | jsp701 |
| JSP-000354 | pairwise-coprime sumset of 6 elements {1,5,7,9,11,13} from A={0,4,6}, B={1,5,7} | jsp354.lean | jsp354 |
| JSP-000579 | interval [2,8] holds distinct multiples 5,4,6,8 of 1,2,3,4 | jsp579.lean | jsp579 |
| JSP-000948 | prime set {2,3}; interval [1,6] has exactly 4 multiples {2,3,4,6} | jsp948.lean | jsp948 |
| JSP-000580 | from start 6, interval [6,9] (length 4) holds distinct multiples 7,6,9,8 of 1,2,3,4 | jsp580.lean | jsp580 |
| JSP-000914 | coprime {1,2,3} leaves max gap 4 in [1,20] | jsp914.lean | jsp914 |
| JSP-000674 | subset sums of {1,3,9} avoid 3-term APs in [0,13] | jsp674.lean | jsp674 |
| JSP-000921 | 37=4+6+27, 29=8+9+12, 49=9+16+24 (non-dividing 2/3-power sums) | jsp921.lean | jsp921 |
| JSP-000550 | disjoint equal-length intervals [1,3]/[4,6] and [2,5]/[6,9] have different lcms | jsp550.lean | jsp550 |
| JSP-000877 | 561 = 3·11·17 is a Carmichael number (Korselt) | jsp877.lean | jsp877 |
| JSP-000911 | [1,10] contains 3-term APs with 4 distinct differences | jsp911.lean | jsp911 |
| JSP-000941 | 3n+1 trajectory of 7 reaches 1 in 16 steps | jsp941.lean | jsp941 |
| JSP-000891 | (p−1)! ≡ −1 mod p for p = 5, 7, 11 (Wilson) | jsp891.lean | jsp891 |
| JSP-000920 | 9-element subset of [1,40], all pairwise sums ≡ 0 mod 4 | jsp920.lean | jsp920 |
| JSP-000876 | three disjoint intervals with product ≡ 1 mod 17 | jsp876.lean | jsp876 |
| JSP-000915 | {1,2,4,9,13} has all pairwise sums squarefree | jsp915.lean | jsp915 |
| JSP-000883 | C(10,3)=120 divisible by all but one term of {8,7,6} | jsp883.lean | jsp883 |
| JSP-001013 | 4-point set {0,1,3,7} has all 6 pairwise distances distinct | jsp1013.lean | jsp1013 |
| JSP-000918 | 72 = 36 + 27 + 9 as three powerful numbers | jsp918.lean | jsp918 |
| JSP-001009 | admissible prime tuple {0,2,6} with span 6 | jsp1009.lean | jsp1009 |
| JSP-000685 | 1729 = 1³ + 12³ = 9³ + 10³ (two cube-sum representations) | jsp685.lean | jsp685 |
| JSP-000680 | coprime pair 6, 11 with σ(6) = σ(11) = 12 | jsp680.lean | jsp680 |
| JSP-000651 | {6,7,8,9,10} is a 5-element sum-free subset of [1,10] | jsp651.lean | jsp651 |

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

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

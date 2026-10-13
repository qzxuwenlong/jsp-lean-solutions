-- =====================================================================
-- JSP-000317 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Can a prime square be followed by several consecutive integers
--       having no prime factor larger than that prime?
--       （素数平方之后能否接续若干个连续整数，其素因子均不超过该素数？）
-- 答案：可以（构造性例证）。构造：
--       p = 443 是素数，443² = 196249；
--       随后三个连续整数
--         196250 = 2 · 5⁴ · 157
--         196251 = 3 · 11 · 19 · 313
--         196252 = 2² · 7 · 43 · 163
--       的所有素因子均 ≤ 443。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp317.lean
-- 全部计算性证明由 `decide` 在内核 VM 中完成（机器逐行核验）。
-- =====================================================================

set_option maxRecDepth 1000000

-- ---------------------------------------------------------------------
-- 素数定义（无 Mathlib）
-- ---------------------------------------------------------------------

def Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

-- ---------------------------------------------------------------------
-- Euclid 引理（素数整除乘积 ⇒ 整除某一因子）
-- 依赖核心库 Nat.gcd / Nat.Coprime / Nat.Coprime.dvd_of_dvd_mul_right
-- ---------------------------------------------------------------------

theorem prime_dvd_mul {q a b : Nat} (hq : Prime q) (h : q ∣ a * b) : q ∣ a ∨ q ∣ b := by
  by_cases hqa : q ∣ a
  · exact Or.inl hqa
  · right
    have hgcdq : Nat.gcd q a ∣ q := Nat.gcd_dvd_left q a
    have hgcda : Nat.gcd q a ∣ a := Nat.gcd_dvd_right q a
    have hgcase : Nat.gcd q a = 1 ∨ Nat.gcd q a = q := hq.2 (Nat.gcd q a) hgcdq
    rcases hgcase with hg1 | hgq
    · have hcop : Nat.Coprime q a := hg1
      exact Nat.Coprime.dvd_of_dvd_mul_right hcop (by simpa [Nat.mul_comm] using h)
    · have hqa' : q ∣ a := by
        rw [← hgq]
        exact hgcda
      exact (hqa hqa').elim

/-- 2 是素数（小素数闭项模板） -/
theorem prime_2 : Prime 2 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
  exact (by decide : ∀ m : Nat, m ≤ 2 → m ∣ 2 → m = 1 ∨ m = 2) m hle hm


/-- 3 是素数（小素数闭项模板） -/
theorem prime_3 : Prime 3 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) hm
  exact (by decide : ∀ m : Nat, m ≤ 3 → m ∣ 3 → m = 1 ∨ m = 3) m hle hm


/-- 5 是素数（小素数闭项模板） -/
theorem prime_5 : Prime 5 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
  exact (by decide : ∀ m : Nat, m ≤ 5 → m ∣ 5 → m = 1 ∨ m = 5) m hle hm


/-- 7 是素数（小素数闭项模板） -/
theorem prime_7 : Prime 7 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 7 := Nat.le_of_dvd (by decide : 0 < 7) hm
  exact (by decide : ∀ m : Nat, m ≤ 7 → m ∣ 7 → m = 1 ∨ m = 7) m hle hm


/-- 11 是素数（小素数闭项模板） -/
theorem prime_11 : Prime 11 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 11 := Nat.le_of_dvd (by decide : 0 < 11) hm
  exact (by decide : ∀ m : Nat, m ≤ 11 → m ∣ 11 → m = 1 ∨ m = 11) m hle hm


/-- 19 是素数（小素数闭项模板） -/
theorem prime_19 : Prime 19 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 19 := Nat.le_of_dvd (by decide : 0 < 19) hm
  exact (by decide : ∀ m : Nat, m ≤ 19 → m ∣ 19 → m = 1 ∨ m = 19) m hle hm


/-- 43 是素数（小素数闭项模板） -/
theorem prime_43 : Prime 43 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 43 := Nat.le_of_dvd (by decide : 0 < 43) hm
  exact (by decide : ∀ m : Nat, m ≤ 43 → m ∣ 43 → m = 1 ∨ m = 43) m hle hm


/-- 157 是素数（小素数闭项模板） -/
theorem prime_157 : Prime 157 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 157 := Nat.le_of_dvd (by decide : 0 < 157) hm
  exact (by decide : ∀ m : Nat, m ≤ 157 → m ∣ 157 → m = 1 ∨ m = 157) m hle hm


/-- 163 是素数（小素数闭项模板） -/
theorem prime_163 : Prime 163 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 163 := Nat.le_of_dvd (by decide : 0 < 163) hm
  exact (by decide : ∀ m : Nat, m ≤ 163 → m ∣ 163 → m = 1 ∨ m = 163) m hle hm


/-- 313 是素数（小素数闭项模板） -/
theorem prime_313 : Prime 313 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 313 := Nat.le_of_dvd (by decide : 0 < 313) hm
  exact (by decide : ∀ m : Nat, m ≤ 313 → m ∣ 313 → m = 1 ∨ m = 313) m hle hm


/-- 443 是素数（小素数闭项模板） -/
theorem prime_443 : Prime 443 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 443 := Nat.le_of_dvd (by decide : 0 < 443) hm
  exact (by decide : ∀ m : Nat, m ≤ 443 → m ∣ 443 → m = 1 ∨ m = 443) m hle hm

-- ---------------------------------------------------------------------
-- 平方与分解等式（闭项）
-- ---------------------------------------------------------------------

theorem sq_443 : 443 * 443 = 196249 := by decide

theorem fac_196250 : 196250 = 2 * (5 * (5 * (5 * (5 * 157)))) := by decide
theorem fac_196251 : 196251 = 3 * (11 * (19 * 313)) := by decide
theorem fac_196252 : 196252 = (2 * 2) * (7 * (43 * 163)) := by decide

/-- 196250 的所有素因子 ≤ 443 -/
theorem pf_196250 : ∀ q : Nat, Prime q → q ∣ 196250 → q ≤ 443 := by
  intro q hq hd
  have hd' : q ∣ 2 * (5 * (5 * (5 * (5 * 157)))) := by
    rwa [fac_196250] at hd
  rcases prime_dvd_mul hq hd' with hq2 | hrest
  · have hq2' : q = 2 := by
      rcases prime_2.2 q hq2 with h1 | h2
      · have : q ≥ 2 := hq.1
        omega
      · exact h2
    rw [hq2']
    decide
  · rcases prime_dvd_mul hq hrest with hq5 | hrest2
    · have hq5' : q = 5 := by
        rcases prime_5.2 q hq5 with h1 | h2
        · have : q ≥ 2 := hq.1
          omega
        · exact h2
      rw [hq5']
      decide
    · rcases prime_dvd_mul hq hrest2 with hq5b | hrest3
      · have hq5b' : q = 5 := by
          rcases prime_5.2 q hq5b with h1 | h2
          · have : q ≥ 2 := hq.1
            omega
          · exact h2
        rw [hq5b']
        decide
      · rcases prime_dvd_mul hq hrest3 with hq5c | hrest4
        · have hq5c' : q = 5 := by
            rcases prime_5.2 q hq5c with h1 | h2
            · have : q ≥ 2 := hq.1
              omega
            · exact h2
          rw [hq5c']
          decide
        · rcases prime_dvd_mul hq hrest4 with hq5d | hq157
          · have hq5d' : q = 5 := by
              rcases prime_5.2 q hq5d with h1 | h2
              · have : q ≥ 2 := hq.1
                omega
              · exact h2
            rw [hq5d']
            decide
          · have hq157' : q = 157 := by
              rcases prime_157.2 q hq157 with h1 | h2
              · have : q ≥ 2 := hq.1
                omega
              · exact h2
            rw [hq157']
            decide

/-- 196251 的所有素因子 ≤ 443 -/
theorem pf_196251 : ∀ q : Nat, Prime q → q ∣ 196251 → q ≤ 443 := by
  intro q hq hd
  have hd' : q ∣ 3 * (11 * (19 * 313)) := by
    rwa [fac_196251] at hd
  rcases prime_dvd_mul hq hd' with hq3 | hrest
  · have hq3' : q = 3 := by
      rcases prime_3.2 q hq3 with h1 | h2
      · have : q ≥ 2 := hq.1
        omega
      · exact h2
    rw [hq3']
    decide
  · rcases prime_dvd_mul hq hrest with hq11 | hrest2
    · have hq11' : q = 11 := by
        rcases prime_11.2 q hq11 with h1 | h2
        · have : q ≥ 2 := hq.1
          omega
        · exact h2
      rw [hq11']
      decide
    · rcases prime_dvd_mul hq hrest2 with hq19 | hq313
      · have hq19' : q = 19 := by
          rcases prime_19.2 q hq19 with h1 | h2
          · have : q ≥ 2 := hq.1
            omega
          · exact h2
        rw [hq19']
        decide
      · have hq313' : q = 313 := by
          rcases prime_313.2 q hq313 with h1 | h2
          · have : q ≥ 2 := hq.1
            omega
          · exact h2
        rw [hq313']
        decide

/-- 196252 的所有素因子 ≤ 443 -/
theorem pf_196252 : ∀ q : Nat, Prime q → q ∣ 196252 → q ≤ 443 := by
  intro q hq hd
  have hd' : q ∣ (2 * 2) * (7 * (43 * 163)) := by
    rwa [fac_196252] at hd
  rcases prime_dvd_mul hq hd' with hq22 | hrest
  · rcases prime_dvd_mul hq hq22 with hq2a | hq2b
    · have hq2' : q = 2 := by
        rcases prime_2.2 q hq2a with h1 | h2
        · have : q ≥ 2 := hq.1
          omega
        · exact h2
      rw [hq2']
      decide
    · have hq2' : q = 2 := by
        rcases prime_2.2 q hq2b with h1 | h2
        · have : q ≥ 2 := hq.1
          omega
        · exact h2
      rw [hq2']
      decide
  · rcases prime_dvd_mul hq hrest with hq7 | hrest2
    · have hq7' : q = 7 := by
        rcases prime_7.2 q hq7 with h1 | h2
        · have : q ≥ 2 := hq.1
          omega
        · exact h2
      rw [hq7']
      decide
    · rcases prime_dvd_mul hq hrest2 with hq43 | hq163
      · have hq43' : q = 43 := by
          rcases prime_43.2 q hq43 with h1 | h2
          · have : q ≥ 2 := hq.1
            omega
          · exact h2
        rw [hq43']
        decide
      · have hq163' : q = 163 := by
          rcases prime_163.2 q hq163 with h1 | h2
          · have : q ≥ 2 := hq.1
            omega
          · exact h2
        rw [hq163']
        decide

-- ---------------------------------------------------------------------
-- 主定理：存在素数 p，其平方后的 3 个连续整数的所有素因子 ≤ p
-- ---------------------------------------------------------------------

theorem jsp317 :
    ∃ p : Nat, Prime p ∧
      (∀ q : Nat, Prime q → q ∣ p * p + 1 → q ≤ p) ∧
      (∀ q : Nat, Prime q → q ∣ p * p + 2 → q ≤ p) ∧
      (∀ q : Nat, Prime q → q ∣ p * p + 3 → q ≤ p) := by
  refine ⟨443, ?_⟩
  constructor
  · exact prime_443
  · constructor
    · intro q hq hd
      have hs : 443 * 443 + 1 = 196250 := by
        rw [sq_443]
      have hd' : q ∣ 196250 := by
        rwa [hs] at hd
      exact pf_196250 q hq hd'
    · constructor
      · intro q hq hd
        have hs : 443 * 443 + 2 = 196251 := by
          rw [sq_443]
        have hd' : q ∣ 196251 := by
          rwa [hs] at hd
        exact pf_196251 q hq hd'
      · intro q hq hd
        have hs : 443 * 443 + 3 = 196252 := by
          rw [sq_443]
        have hd' : q ∣ 196252 := by
          rwa [hs] at hd
        exact pf_196252 q hq hd'

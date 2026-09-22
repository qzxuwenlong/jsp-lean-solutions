-- =====================================================================
-- JSP-000316 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How long can a consecutive-integer interval be if its product's
--       largest prime factor must occur repeatedly?
--       （若连续整数区间乘积的最大素因子必须重复出现，区间最长能多长？）
-- 构造性下界：长度 4 的区间 [1680, 1683] 可行。
--   1680 = 2⁴·3·5·7
--   1681 = 41²
--   1682 = 2·29²
--   1683 = 3²·11·17
-- 所有素因子 ≤ 41，且 41 出现两次（41² = 1681 ∈ 区间）。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp316.lean
-- =====================================================================

set_option maxRecDepth 1000000

def Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

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

/-- 2 是素数 -/
theorem prime_2 : Prime 2 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
  exact (by decide : ∀ m : Nat, m ≤ 2 → m ∣ 2 → m = 1 ∨ m = 2) m hle hm


/-- 3 是素数 -/
theorem prime_3 : Prime 3 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) hm
  exact (by decide : ∀ m : Nat, m ≤ 3 → m ∣ 3 → m = 1 ∨ m = 3) m hle hm


/-- 5 是素数 -/
theorem prime_5 : Prime 5 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
  exact (by decide : ∀ m : Nat, m ≤ 5 → m ∣ 5 → m = 1 ∨ m = 5) m hle hm


/-- 7 是素数 -/
theorem prime_7 : Prime 7 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 7 := Nat.le_of_dvd (by decide : 0 < 7) hm
  exact (by decide : ∀ m : Nat, m ≤ 7 → m ∣ 7 → m = 1 ∨ m = 7) m hle hm


/-- 11 是素数 -/
theorem prime_11 : Prime 11 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 11 := Nat.le_of_dvd (by decide : 0 < 11) hm
  exact (by decide : ∀ m : Nat, m ≤ 11 → m ∣ 11 → m = 1 ∨ m = 11) m hle hm


/-- 17 是素数 -/
theorem prime_17 : Prime 17 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 17 := Nat.le_of_dvd (by decide : 0 < 17) hm
  exact (by decide : ∀ m : Nat, m ≤ 17 → m ∣ 17 → m = 1 ∨ m = 17) m hle hm


/-- 29 是素数 -/
theorem prime_29 : Prime 29 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 29 := Nat.le_of_dvd (by decide : 0 < 29) hm
  exact (by decide : ∀ m : Nat, m ≤ 29 → m ∣ 29 → m = 1 ∨ m = 29) m hle hm


/-- 41 是素数 -/
theorem prime_41 : Prime 41 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 41 := Nat.le_of_dvd (by decide : 0 < 41) hm
  exact (by decide : ∀ m : Nat, m ≤ 41 → m ∣ 41 → m = 1 ∨ m = 41) m hle hm


-- 分解等式
theorem fac_1680 : 1680 = 2 * (2 * (2 * (2 * (3 * (5 * 7))))) := by decide
theorem fac_1681 : 1681 = 41 * 41 := by decide
theorem fac_1682 : 1682 = 2 * (29 * 29) := by decide
theorem fac_1683 : 1683 = 3 * (3 * (11 * 17)) := by decide

/-- 1680 的所有素因子 ≤ 41 -/
theorem pf_1680 : ∀ q : Nat, Prime q → q ∣ 1680 → q ≤ 41 := by
  intro q hq hd
  have hd0' : q ∣ 2 * (2 * (2 * (2 * (3 * (5 * (7)))))) := by
    rwa [fac_1680] at hd
  rcases prime_dvd_mul hq hd0' with hq0 | hrest0
  · have hq' : q = 2 := by
      rcases prime_2.2 q hq0 with h1 | h2
      · have : q ≥ 2 := hq.1
        omega
      · exact h2
    rw [hq']
    decide
  ·
    have hd1' : q ∣ 2 * (2 * (2 * (3 * (5 * (7))))) := by
      simpa using hrest0
    rcases prime_dvd_mul hq hd1' with hq1 | hrest1
    · have hq' : q = 2 := by
        rcases prime_2.2 q hq1 with h1 | h2
        · have : q ≥ 2 := hq.1
          omega
        · exact h2
      rw [hq']
      decide
    ·
      have hd2' : q ∣ 2 * (2 * (3 * (5 * (7)))) := by
        simpa using hrest1
      rcases prime_dvd_mul hq hd2' with hq2 | hrest2
      · have hq' : q = 2 := by
          rcases prime_2.2 q hq2 with h1 | h2
          · have : q ≥ 2 := hq.1
            omega
          · exact h2
        rw [hq']
        decide
      ·
        have hd3' : q ∣ 2 * (3 * (5 * (7))) := by
          simpa using hrest2
        rcases prime_dvd_mul hq hd3' with hq3 | hrest3
        · have hq' : q = 2 := by
            rcases prime_2.2 q hq3 with h1 | h2
            · have : q ≥ 2 := hq.1
              omega
            · exact h2
          rw [hq']
          decide
        ·
          have hd4' : q ∣ 3 * (5 * (7)) := by
            simpa using hrest3
          rcases prime_dvd_mul hq hd4' with hq4 | hrest4
          · have hq' : q = 3 := by
              rcases prime_3.2 q hq4 with h1 | h2
              · have : q ≥ 2 := hq.1
                omega
              · exact h2
            rw [hq']
            decide
          ·
            have hd5' : q ∣ 5 * (7) := by
              simpa using hrest4
            rcases prime_dvd_mul hq hd5' with hq5 | hrest5
            · have hq' : q = 5 := by
                rcases prime_5.2 q hq5 with h1 | h2
                · have : q ≥ 2 := hq.1
                  omega
                · exact h2
              rw [hq']
              decide
            ·
              have hq' : q = 7 := by
                rcases prime_7.2 q hrest5 with h1 | h2
                · have : q ≥ 2 := hq.1
                  omega
                · exact h2
              rw [hq']
              decide
/-- 1681 的所有素因子 ≤ 41 -/
theorem pf_1681 : ∀ q : Nat, Prime q → q ∣ 1681 → q ≤ 41 := by
  intro q hq hd
  have hd0' : q ∣ 41 * (41) := by
    rwa [fac_1681] at hd
  rcases prime_dvd_mul hq hd0' with hq0 | hrest0
  · have hq' : q = 41 := by
      rcases prime_41.2 q hq0 with h1 | h2
      · have : q ≥ 2 := hq.1
        omega
      · exact h2
    rw [hq']
    decide
  ·
    have hq' : q = 41 := by
      rcases prime_41.2 q hrest0 with h1 | h2
      · have : q ≥ 2 := hq.1
        omega
      · exact h2
    rw [hq']
    decide
/-- 1682 的所有素因子 ≤ 41 -/
theorem pf_1682 : ∀ q : Nat, Prime q → q ∣ 1682 → q ≤ 41 := by
  intro q hq hd
  have hd0' : q ∣ 2 * (29 * (29)) := by
    rwa [fac_1682] at hd
  rcases prime_dvd_mul hq hd0' with hq0 | hrest0
  · have hq' : q = 2 := by
      rcases prime_2.2 q hq0 with h1 | h2
      · have : q ≥ 2 := hq.1
        omega
      · exact h2
    rw [hq']
    decide
  ·
    have hd1' : q ∣ 29 * (29) := by
      simpa using hrest0
    rcases prime_dvd_mul hq hd1' with hq1 | hrest1
    · have hq' : q = 29 := by
        rcases prime_29.2 q hq1 with h1 | h2
        · have : q ≥ 2 := hq.1
          omega
        · exact h2
      rw [hq']
      decide
    ·
      have hq' : q = 29 := by
        rcases prime_29.2 q hrest1 with h1 | h2
        · have : q ≥ 2 := hq.1
          omega
        · exact h2
      rw [hq']
      decide
/-- 1683 的所有素因子 ≤ 41 -/
theorem pf_1683 : ∀ q : Nat, Prime q → q ∣ 1683 → q ≤ 41 := by
  intro q hq hd
  have hd0' : q ∣ 3 * (3 * (11 * (17))) := by
    rwa [fac_1683] at hd
  rcases prime_dvd_mul hq hd0' with hq0 | hrest0
  · have hq' : q = 3 := by
      rcases prime_3.2 q hq0 with h1 | h2
      · have : q ≥ 2 := hq.1
        omega
      · exact h2
    rw [hq']
    decide
  ·
    have hd1' : q ∣ 3 * (11 * (17)) := by
      simpa using hrest0
    rcases prime_dvd_mul hq hd1' with hq1 | hrest1
    · have hq' : q = 3 := by
        rcases prime_3.2 q hq1 with h1 | h2
        · have : q ≥ 2 := hq.1
          omega
        · exact h2
      rw [hq']
      decide
    ·
      have hd2' : q ∣ 11 * (17) := by
        simpa using hrest1
      rcases prime_dvd_mul hq hd2' with hq2 | hrest2
      · have hq' : q = 11 := by
          rcases prime_11.2 q hq2 with h1 | h2
          · have : q ≥ 2 := hq.1
            omega
          · exact h2
        rw [hq']
        decide
      ·
        have hq' : q = 17 := by
          rcases prime_17.2 q hrest2 with h1 | h2
          · have : q ≥ 2 := hq.1
            omega
          · exact h2
        rw [hq']
        decide
-- ---------------------------------------------------------------------
-- 主定理：存在 4 个连续整数（区间），其乘积的所有素因子 ≤ 41
-- 且 41 出现两次（41² | 乘积）
-- ---------------------------------------------------------------------

theorem jsp316 :
    ∃ x1 x2 x3 x4 : Nat,
      x2 = x1 + 1 ∧ x3 = x2 + 1 ∧ x4 = x3 + 1 ∧
      (∀ q : Nat, Prime q → q ∣ x1 * x2 * x3 * x4 → q ≤ 41) ∧
      41 * 41 ∣ x1 * x2 * x3 * x4 := by
  refine ⟨1680, 1681, 1682, 1683, ?_⟩
  change 1681 = 1680 + 1 ∧ 1682 = 1681 + 1 ∧ 1683 = 1682 + 1 ∧
    (∀ q : Nat, Prime q → q ∣ 1680 * 1681 * 1682 * 1683 → q ≤ 41) ∧
    41 * 41 ∣ 1680 * 1681 * 1682 * 1683
  constructor
  · decide
  · constructor
    · decide
    · constructor
      · decide
      · constructor
        · intro q hq hd
          have hd1 : q ∣ 1680 * (1681 * 1682 * 1683) := by
            simpa [Nat.mul_assoc] using hd
          rcases prime_dvd_mul hq hd1 with hq1 | hrest1
          · exact pf_1680 q hq hq1
          · have hd2 : q ∣ 1681 * (1682 * 1683) := by
              simpa [Nat.mul_assoc] using hrest1
            rcases prime_dvd_mul hq hd2 with hq2 | hrest2
            · exact pf_1681 q hq hq2
            · have hd3 : q ∣ 1682 * 1683 := by
                simpa [Nat.mul_assoc] using hrest2
              rcases prime_dvd_mul hq hd3 with hq3 | hq4
              · exact pf_1682 q hq hq3
              · exact pf_1683 q hq hq4
        · have h41 : 41 * 41 = 1681 := by decide
          rw [h41]
          refine ⟨1680 * 1682 * 1683, ?_⟩
          decide

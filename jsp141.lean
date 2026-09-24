-- =====================================================================
-- JSP-000141 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Can a product of consecutive positive integers have every prime
--       factor occurring with exponent at least two?
--       （是否存在连续正整数乘积，其每个素因子出现的指数至少为 2？）
--
-- 答案：是。构造：8 × 9 = 72 = 2³ · 3²，其素因子 2 的指数为 3 ≥ 2，
--       素因子 3 的指数为 2 ≥ 2。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp141.lean
-- =====================================================================

set_option maxRecDepth 1000000

def Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- 欧几里得引理：素数 p 整除 a·b 则 p 整除 a 或 b。 -/
theorem euclid (p a b : Nat) (hp : Prime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · right
    have hg : Nat.gcd p a = 1 := by
      have hgl : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
      have hc : Nat.gcd p a = 1 ∨ Nat.gcd p a = p := hp.2 (Nat.gcd p a) hgl
      cases hc with
      | inl h1 => exact h1
      | inr hp' =>
          exfalso
          have hd : p ∣ Nat.gcd p a := by
            simpa [hp']
          have hda : p ∣ a := Nat.dvd_trans hd (Nat.gcd_dvd_right p a)
          exact hpa hda
    have hgm : Nat.gcd (p * b) (a * b) = b := by
      rw [Nat.gcd_mul_right p b a, hg]
      simp
    have hd1 : p ∣ p * b := Nat.dvd_mul_right p b
    have hpg : p ∣ Nat.gcd (p * b) (a * b) := Nat.dvd_gcd hd1 h
    rwa [hgm] at hpg

/-- 素数整除 2 则等于 2。 -/
theorem prime_dvd_two (p : Nat) (hp : Prime p) (h : p ∣ 2) : p = 2 := by
  have hp2 : p ≥ 2 := hp.1
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) h
  omega

/-- 素数整除 3 则等于 3。 -/
theorem prime_dvd_three (p : Nat) (hp : Prime p) (h : p ∣ 3) : p = 3 := by
  have hp2 : p ≥ 2 := hp.1
  have hle : p ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) h
  have hp_ne2 : p ≠ 2 := by
    intro h2
    subst p
    have h23 : ¬ 2 ∣ 3 := by decide
    exact h23 h
  omega

/-- 主定理：存在 n = 8，使 8·9 = 72 的每个素因子指数至少为 2
    （即 p | 8·9 ⇒ p² | 8·9）。 -/
theorem jsp141 : ∃ n : Nat, ∀ p : Nat, Prime p → p ∣ n * (n + 1) → p * p ∣ n * (n + 1) := by
  refine ⟨8, ?_⟩
  intro p hp hd
  have hprod : 8 * (8 + 1) = 2 ^ 3 * 3 ^ 2 := by
    decide
  have hd' : p ∣ 2 ^ 3 * 3 ^ 2 := by
    rwa [← hprod] at hd
  have hcases : p ∣ 2 ^ 3 ∨ p ∣ 3 ^ 2 := euclid p (2 ^ 3) (3 ^ 2) hp hd'
  rcases hcases with h8 | h9
  · have h2 : p ∣ 2 := by
      rcases (euclid p (2 ^ 2) 2 hp (by simpa [Nat.pow_succ] using h8)) with h4 | h2b
      · rcases (euclid p 2 2 hp (by simpa [Nat.pow_succ] using h4)) with h2c | h2d
        · exact h2c
        · exact h2d
      · exact h2b
    have hp2' : p = 2 := prime_dvd_two p hp h2
    subst p
    decide
  · have h3 : p ∣ 3 := by
      rcases (euclid p 3 3 hp (by simpa [Nat.pow_succ] using h9)) with h3a | h3b
      · exact h3a
      · exact h3b
    have hp3' : p = 3 := prime_dvd_three p hp h3
    subst p
    decide

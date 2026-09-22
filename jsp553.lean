-- =====================================================================
-- JSP-000553 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Near every integer, is there a composite integer whose least
--       prime factor exceeds the square of their distance?
--       （对任意整数 n，附近是否存在合数 m，其最小素因子大于距离平方？）
--
-- 答案：否。反例 n = 4。
--   对任意合数 m ≠ 4（即 m ≥ 6）：
--     · m ≥ 8 时：任一素因子 p ≤ m/2 ≤ (m−4) ≤ (m−4)²，故 lpf(m) ≤ (m−4)²；
--     · m = 6 时：素因子为 2 或 3，均 ≤ 4 = (6−4)²。
--   因此不存在合数 m 使 lpf(m) > |m−4|²。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp553.lean
-- =====================================================================

set_option maxRecDepth 1000000

def Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

def Composite (m : Nat) : Prop := ∃ a b : Nat, a ≥ 2 ∧ b ≥ 2 ∧ m = a * b

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

theorem prime_2 : Prime 2 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
  exact (by decide : ∀ m : Nat, m ≤ 2 → m ∣ 2 → m = 1 ∨ m = 2) m hle hm

theorem prime_3 : Prime 3 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) hm
  exact (by decide : ∀ m : Nat, m ≤ 3 → m ∣ 3 → m = 1 ∨ m = 3) m hle hm

theorem prime_5 : Prime 5 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
  exact (by decide : ∀ m : Nat, m ≤ 5 → m ∣ 5 → m = 1 ∨ m = 5) m hle hm

theorem prime_7 : Prime 7 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 7 := Nat.le_of_dvd (by decide : 0 < 7) hm
  exact (by decide : ∀ m : Nat, m ≤ 7 → m ∣ 7 → m = 1 ∨ m = 7) m hle hm

/-- 合数 m 的任一素因子 p 满足 p ≤ m/2 -/
theorem composite_prime_le_half {m : Nat} (hc : Composite m) {p : Nat} (hp : Prime p)
    (hdiv : p ∣ m) : p ≤ m / 2 := by
  rcases hc with ⟨a, b, ha, hb, hprod⟩
  have hd : p ∣ a * b := by
    rwa [hprod] at hdiv
  rcases prime_dvd_mul hp hd with hpa | hpb
  · have hpa_le : p ≤ a := Nat.le_of_dvd (by omega) hpa
    have hb2 : 2 ≤ b := hb
    have hmul : a * 2 ≤ a * b := Nat.mul_le_mul_left a hb2
    have hmge : a * 2 ≤ m := by
      calc
        a * 2 ≤ a * b := hmul
        _ = m := hprod.symm
    have ha_le : a ≤ m / 2 := by omega
    omega
  · have hpb_le : p ≤ b := Nat.le_of_dvd (by omega) hpb
    have ha2 : 2 ≤ a := ha
    have hmul : b * 2 ≤ b * a := Nat.mul_le_mul_left b ha2
    have hmge : b * 2 ≤ m := by
      calc
        b * 2 ≤ b * a := hmul
        _ = m := by simpa [Nat.mul_comm] using hprod.symm
    have hb_le : b ≤ m / 2 := by omega
    omega

/-- 5 或 7 不是合数 -/
theorem not_composite_5_7 : ∀ m : Nat, m = 5 ∨ m = 7 → ¬ Composite m := by
  intro m hm hc
  rcases hc with ⟨a, b, ha, hb, hprod⟩
  have hab : a * b = m := hprod.symm
  rcases hm with hm5 | hm7
  · have hpm : Prime 5 := prime_5
    have ha_dvd : a ∣ 5 := by
      rw [← hm5]
      rw [← hab]
      exact Nat.dvd_mul_right a b
    rcases hpm.2 a ha_dvd with ha1 | ha5
    · omega
    · have hb1 : b = 1 := by
        have h5b : 5 * b = 5 := by
          calc
            5 * b = a * b := by rw [ha5]
            _ = m := hab
            _ = 5 := hm5
        omega
      omega
  · have hpm : Prime 7 := prime_7
    have ha_dvd : a ∣ 7 := by
      rw [← hm7]
      rw [← hab]
      exact Nat.dvd_mul_right a b
    rcases hpm.2 a ha_dvd with ha1 | ha7
    · omega
    · have hb1 : b = 1 := by
        have h7b : 7 * b = 7 := by
          calc
            7 * b = a * b := by rw [ha7]
            _ = m := hab
            _ = 7 := hm7
        omega
      omega

/-- 主定理：n = 4 是反例。
    对任意 m ≠ 4，若 m 是合数，则其任一素因子 p 满足 p ≤ (m−4)²，
    因此不存在 m ≠ 4 使最小素因子 > 距离平方。 -/
theorem jsp553 :
    ∃ n : Nat, ∀ m : Nat, m ≠ n → Composite m → ∀ p : Nat, Prime p → p ∣ m → p ≤ (m - n) * (m - n) := by
  refine ⟨4, ?_⟩
  intro m hm hc p hp hdiv
  by_cases hm8 : m ≥ 8
  · have h1 : p ≤ m / 2 := composite_prime_le_half hc hp hdiv
    have h2 : m / 2 ≤ m - 4 := by omega
    have h3 : m - 4 ≤ (m - 4) * (m - 4) := by
      have hpos : 1 ≤ m - 4 := by omega
      have hmul : (m - 4) * 1 ≤ (m - 4) * (m - 4) := Nat.mul_le_mul_left (m - 4) hpos
      simpa using hmul
    omega
  · have hc0 : Composite m := hc
    rcases hc with ⟨a, b, ha, hb, hprod⟩
    have h22 : 2 * 2 ≤ a * b := Nat.mul_le_mul ha hb
    have hge4 : m ≥ 4 := by
      rw [hprod]
      omega
    have hmcases : m = 5 ∨ m = 6 ∨ m = 7 := by omega
    rcases hmcases with hm5 | hm6 | hm7
    · exact (not_composite_5_7 m (Or.inl hm5) hc0).elim
    · have hdiv6 : p ∣ 6 := by
        rwa [hm6] at hdiv
      have hd : p ∣ 2 * 3 := by
        change p ∣ 6
        exact hdiv6
      rcases prime_dvd_mul hp hd with hp2 | hp3
      · have hp26 : p = 2 := by
          rcases prime_2.2 p hp2 with h1 | h2
          · exfalso
            have : p ≥ 2 := hp.1
            omega
          · exact h2
        rw [hm6]
        change p ≤ 4
        omega
      · have hp36 : p = 3 := by
          rcases prime_3.2 p hp3 with h1 | h2
          · exfalso
            have : p ≥ 2 := hp.1
            omega
          · exact h2
        rw [hm6]
        change p ≤ 4
        omega
    · exact (not_composite_5_7 m (Or.inr hm7) hc0).elim

-- =====================================================================
-- JSP-000351 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Can a relatively dense integer set have prime differences with
--       each of infinitely many other integers?
--       （相对稠密整数集能否与无穷多个其他整数都有素数差？）
-- 答案：可以。构造：A = 所有偶数（gap ≤ 1，相对稠密）。
--       对任意偶数 a 与任意界限 N，取奇素数 p > N（Euclid：素数无穷），
--       令 y = a + p：则 N < y、y 为奇数（y ∉ A）、y - a = p 为素数。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp351.lean
-- 自证部件：素数定义、Euclid 引理、阶乘、最小素因子存在（良基归纳）、
--           素数无穷（N!+1 构造）。
-- =====================================================================

set_option maxRecDepth 1000000

-- ---------------------------------------------------------------------
-- 素数定义（无 Mathlib）
-- ---------------------------------------------------------------------

def Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

-- ---------------------------------------------------------------------
-- Euclid 引理（素数整除乘积 ⇒ 整除某一因子）
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

-- ---------------------------------------------------------------------
-- 阶乘（核心库无 Nat.factorial，自证）
-- ---------------------------------------------------------------------

def fac : Nat → Nat
  | 0 => 1
  | n + 1 => fac n * (n + 1)

theorem fac_pos (n : Nat) : 0 < fac n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos ih (Nat.zero_lt_succ n)

theorem fac_succ (n : Nat) : fac (n + 1) = fac n * (n + 1) := by rfl

-- p ≤ n 且 p ≥ 1 ⇒ p ∣ n!
theorem dvd_fac {p n : Nat} (hp1 : 1 ≤ p) (hpn : p ≤ n) : p ∣ fac n := by
  induction n with
  | zero =>
      have hp0 : p = 0 := by omega
      omega
  | succ n ih =>
      have hfac : fac (n + 1) = fac n * (n + 1) := fac_succ n
      rw [hfac]
      have hpn1 : p ≤ n + 1 := by omega
      by_cases hpns : p ≤ n
      · have hd : p ∣ fac n := ih hpns
        rcases hd with ⟨k, hk⟩
        refine ⟨k * (n + 1), ?_⟩
        rw [hk]
        rw [← Nat.mul_assoc]
      · have hpeq : p = n + 1 := by omega
        rw [hpeq]
        refine ⟨fac n, ?_⟩
        rw [Nat.mul_comm]

-- ---------------------------------------------------------------------
-- 最小素因子存在（良基归纳）
-- ---------------------------------------------------------------------

theorem exists_prime_factor {m : Nat} (hm : 2 ≤ m) : ∃ p : Nat, Prime p ∧ p ∣ m := by
  let C : Nat → Prop := fun x => 2 ≤ x → ∃ p : Nat, Prime p ∧ p ∣ x
  have hstep : ∀ x : Nat, (∀ y : Nat, y < x → C y) → C x := by
    intro x ih hx2
    by_cases hpx : Prime x
    · exact ⟨x, hpx, Nat.dvd_refl x⟩
    · have hnotall : ¬ ∀ q : Nat, q ∣ x → q = 1 ∨ q = x := by
        intro hall
        exact hpx ⟨hx2, hall⟩
      have hex : ∃ q : Nat, q ∣ x ∧ q ≠ 1 ∧ q ≠ x := by
        apply Classical.byContradiction
        intro hne
        apply hnotall
        intro q hq
        by_cases h1 : q = 1
        · left; exact h1
        · by_cases hx : q = x
          · right; exact hx
          · exact (hne ⟨q, hq, h1, hx⟩).elim
      rcases hex with ⟨d, hdx, hd1, hdx'⟩
      have hdpos : 0 < d := by
        apply Classical.byContradiction
        intro hd0
        have hdz : d = 0 := Nat.eq_zero_of_not_pos hd0
        rcases hdx with ⟨k, hk⟩
        rw [hdz] at hk
        have : x = 0 := by simpa using hk
        omega
      have hdle : d ≤ x := Nat.le_of_dvd (by omega : 0 < x) hdx
      have hd2 : 2 ≤ d := by
        apply Classical.byContradiction
        intro hlt
        have hdlt2 : d < 2 := by omega
        have hd01 : d = 0 ∨ d = 1 := by omega
        rcases hd01 with h0 | h1
        · omega
        · exact (hd1 h1).elim
      have hdlt : d < x := by
        exact Nat.lt_of_le_of_ne hdle hdx'
      rcases ih d hdlt hd2 with ⟨p, hpp, hpd⟩
      exact ⟨p, hpp, Nat.dvd_trans hpd hdx⟩
  exact WellFounded.fix Nat.lt_wfRel.wf hstep m hm

-- ---------------------------------------------------------------------
-- 素数无穷（Euclid：N!+1 的素因子 > N）
-- ---------------------------------------------------------------------

theorem primes_unbounded : ∀ N : Nat, ∃ p : Nat, N < p ∧ Prime p := by
  intro N
  let M := fac (N + 1) + 1
  have hM2 : 2 ≤ M := by
    have hf0 : 0 < fac (N + 1) := fac_pos (N + 1)
    have hf : 1 ≤ fac (N + 1) := Nat.succ_le_of_lt hf0
    omega
  rcases exists_prime_factor hM2 with ⟨p, hpp, hdM⟩
  refine ⟨p, ?_, hpp⟩
  apply Classical.byContradiction
  intro hnot
  have hpN : p ≤ N := by omega
  have hpN1 : p ≤ N + 1 := by omega
  have hp1a : 1 ≤ p := Nat.le_trans (by decide : 1 ≤ 2) hpp.1
  have hdf : p ∣ fac (N + 1) := dvd_fac hp1a hpN1
  have hdM' : p ∣ fac (N + 1) + 1 := by
    simpa [M] using hdM
  have hd1 : p ∣ 1 := by
    have hdsub : p ∣ (fac (N + 1) + 1) - fac (N + 1) := Nat.dvd_sub hdM' hdf
    have hsub : (fac (N + 1) + 1) - fac (N + 1) = 1 := by omega
    simpa [hsub] using hdsub
  have hp1 : p = 1 := Nat.dvd_one.mp hd1
  have hltp : 1 < p := Nat.lt_of_lt_of_le (by decide : 1 < 2) hpp.1
  have hp1le : p ≤ 1 := by
    rw [hp1]
    decide
  exact (Nat.not_le_of_gt hltp hp1le).elim

-- ---------------------------------------------------------------------
-- 偶数集：相邻数总有一个是偶数
-- ---------------------------------------------------------------------

theorem even_or_next (n : Nat) : 2 ∣ n ∨ 2 ∣ n + 1 := by
  induction n with
  | zero =>
      left
      exact ⟨0, rfl⟩
  | succ n ih =>
      rcases ih with hl | hr
      · right
        rcases hl with ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        omega
      · left
        exact hr

theorem even_relatively_dense :
    ∃ C : Nat, ∀ n : Nat, ∃ a : Nat, (2 ∣ a) ∧ n ≤ a ∧ a ≤ n + C := by
  refine ⟨1, ?_⟩
  intro n
  rcases even_or_next n with hl | hr
  · exact ⟨n, hl, Nat.le_refl n, by omega⟩
  · exact ⟨n + 1, hr, by omega, by omega⟩

-- ---------------------------------------------------------------------
-- 主定理：偶数集相对稠密，且每个偶数 a 与无穷多个 y 的差为素数
-- ---------------------------------------------------------------------

theorem jsp351 :
    ∃ A : Nat → Prop,
      (∃ C : Nat, ∀ n : Nat, ∃ a : Nat, A a ∧ n ≤ a ∧ a ≤ n + C) ∧
      ∀ a : Nat, A a → ∀ N : Nat, ∃ y : Nat, N < y ∧ ¬ A y ∧ Prime (y - a) := by
  refine ⟨fun n => 2 ∣ n, ?_⟩
  constructor
  · exact even_relatively_dense
  · intro a ha N
    rcases primes_unbounded (N + 2) with ⟨p, hpN, hpp⟩
    have hpge3 : 3 ≤ p := by omega
    have hpodd : ¬ 2 ∣ p := by
      intro hdp
      have h2p : 2 = 1 ∨ 2 = p := (hpp.2 (2 : Nat)) hdp
      omega
    refine ⟨a + p, ?_⟩
    constructor
    · omega
    · constructor
      · intro hdA
        have hdp2 : 2 ∣ p := by
          have hsub : 2 ∣ (a + p) - a := Nat.dvd_sub hdA ha
          have : (a + p) - a = p := by omega
          simpa [this] using hsub
        exact hpodd hdp2
      · have hsub : a + p - a = p := by omega
        simpa [hsub] using hpp

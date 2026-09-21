-- =====================================================================
-- JSP-000779 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How often do three consecutive members of the ordered powerful
--       numbers form an arithmetic progression?
--       （有序 powerful 数序列中，三个连续成员构成等差级数的频率如何？）
-- 答案：至少一次（构造性下界）。反例/构造：
--       1728 = 2^6·3^3，1764 = 2^2·3^2·7^2，1800 = 2^3·3^2·5^2
--       均为 powerful 数；三者构成等差级数（2·1764 = 1728 + 1800）；
--       (1728, 1764) 与 (1764, 1800) 之间无其他 powerful 数，
--       故它们是 powerful 数序列中的连续三成员。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp779.lean
-- 全部计算性证明由 `decide` 在内核 VM 中完成（机器逐行核验）。
-- =====================================================================

set_option maxRecDepth 1000000

-- ---------------------------------------------------------------------
-- 定义
-- ---------------------------------------------------------------------

/-- 素数（Mathlib 的 Nat.Prime 等价定义，避免依赖 Mathlib） -/
def Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- powerful 数：每个素因子 p 的平方 p² 都整除 n -/
def Powerful (n : Nat) : Prop := ∀ p : Nat, Prime p → p ∣ n → p ^ 2 ∣ n

-- ---------------------------------------------------------------------
-- 自建列表全称判定
-- ---------------------------------------------------------------------

def listAll (f : Nat → Bool) (l : List Nat) : Bool :=
  List.foldl (fun acc x => acc && f x) true l

-- ---------------------------------------------------------------------
-- 可判定机制
-- ---------------------------------------------------------------------

/-- 素性检查（有界、可判定） -/
def primeCheck (p : Nat) : Bool :=
  decide (2 ≤ p) && listAll (fun m => decide (m = 1) || decide (m = p) || Bool.not (decide (m ∣ p))) (List.range (p + 1))

/-- powerful 检查：对每个 p < B，若 p ∣ n 且 p 是素数，则 p² ∣ n。 -/
def powerfulIn (n : Nat) (r : List Nat) : Bool :=
  listAll (fun p => Bool.not (decide (p ∣ n)) || Bool.not (primeCheck p) || decide ((p ^ 2) ∣ n)) r

-- ---------------------------------------------------------------------
-- Bool 与列表引理
-- ---------------------------------------------------------------------

theorem and_eq_true (a b : Bool) : ((a && b) = true) ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

theorem foldl_and_intro (l : List Nat) (f : Nat → Bool) :
    ∀ acc : Bool, acc = true → (∀ x : Nat, x ∈ l → f x = true) →
    List.foldl (fun a x => a && f x) acc l = true := by
  intro acc hacc h
  induction l generalizing acc with
  | nil => simp [List.foldl, hacc]
  | cons x xs ih =>
      have hx : f x = true := h x (by simp)
      have hstep : (acc && f x) = true := by simp [hacc, hx]
      exact ih (acc && f x) hstep (fun y hy => h y (by simp [hy]))

theorem foldl_and_elim (l : List Nat) (f : Nat → Bool) :
    ∀ acc : Bool, List.foldl (fun a x => a && f x) acc l = true →
    acc = true ∧ ∀ x : Nat, x ∈ l → f x = true := by
  intro acc h
  induction l generalizing acc with
  | nil =>
      simp [List.foldl] at h
      exact ⟨h, by intro x hx; cases hx⟩
  | cons x xs ih =>
      have h' : List.foldl (fun a x => a && f x) (acc && f x) xs = true := by
        simpa [List.foldl] using h
      have ih' := ih (acc && f x) h'
      have hb := (and_eq_true acc (f x)).mp ih'.1
      refine ⟨hb.1, ?_⟩
      intro y hy
      rw [List.mem_cons] at hy
      rcases hy with hy1 | hy2
      · subst y
        exact hb.2
      · exact ih'.2 y hy2

theorem listAll_intro {l : List Nat} {f : Nat → Bool}
    (h : ∀ x : Nat, x ∈ l → f x = true) : listAll f l = true := by
  exact foldl_and_intro l f true rfl h

theorem listAll_elim {l : List Nat} {f : Nat → Bool}
    (h : listAll f l = true) : ∀ x : Nat, x ∈ l → f x = true := by
  exact (foldl_and_elim l f true h).2

theorem primeCheck_of_Prime (p : Nat) (hp : Prime p) : primeCheck p = true := by
  have hge : decide (2 ≤ p) = true := decide_eq_true hp.1
  have hall : listAll (fun m => decide (m = 1) || decide (m = p) || Bool.not (decide (m ∣ p))) (List.range (p + 1)) = true := by
    apply listAll_intro
    intro m hm
    by_cases hd : m ∣ p
    · have hm1p : m = 1 ∨ m = p := hp.2 m hd
      rcases hm1p with h1 | hp2
      · have hb1 : decide (m = 1) = true := by simp [h1]
        have : (decide (m = 1) || decide (m = p) || Bool.not (decide (m ∣ p))) = true := by
          simp [hb1]
        exact this
      · have hbp : decide (m = p) = true := by simp [hp2]
        have : (decide (m = 1) || decide (m = p) || Bool.not (decide (m ∣ p))) = true := by
          simp [hbp]
        exact this
    · have hdF : decide (m ∣ p) = false := decide_eq_false hd
      have : (decide (m = 1) || decide (m = p) || Bool.not (decide (m ∣ p))) = true := by
        simp [hdF]
      exact this
  simp [primeCheck, hge, hall]

theorem not_prime_of_dvd {p m : Nat} (hmd : m ∣ p) (hm1 : m ≠ 1) (hmp : m ≠ p) : ¬ Prime p := by
  intro hp
  rcases hp with ⟨_, hall⟩
  have hm := hall m hmd
  rcases hm with h1 | hp'
  · exact hm1 h1
  · exact hmp hp'


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

/-- 13 是素数 -/
theorem prime_13 : Prime 13 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 13 := Nat.le_of_dvd (by decide : 0 < 13) hm
  exact (by decide : ∀ m : Nat, m ≤ 13 → m ∣ 13 → m = 1 ∨ m = 13) m hle hm

/-- 17 是素数 -/
theorem prime_17 : Prime 17 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 17 := Nat.le_of_dvd (by decide : 0 < 17) hm
  exact (by decide : ∀ m : Nat, m ≤ 17 → m ∣ 17 → m = 1 ∨ m = 17) m hle hm

/-- 19 是素数 -/
theorem prime_19 : Prime 19 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 19 := Nat.le_of_dvd (by decide : 0 < 19) hm
  exact (by decide : ∀ m : Nat, m ≤ 19 → m ∣ 19 → m = 1 ∨ m = 19) m hle hm

/-- 23 是素数 -/
theorem prime_23 : Prime 23 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 23 := Nat.le_of_dvd (by decide : 0 < 23) hm
  exact (by decide : ∀ m : Nat, m ≤ 23 → m ∣ 23 → m = 1 ∨ m = 23) m hle hm

/-- 29 是素数 -/
theorem prime_29 : Prime 29 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 29 := Nat.le_of_dvd (by decide : 0 < 29) hm
  exact (by decide : ∀ m : Nat, m ≤ 29 → m ∣ 29 → m = 1 ∨ m = 29) m hle hm

/-- 31 是素数 -/
theorem prime_31 : Prime 31 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 31 := Nat.le_of_dvd (by decide : 0 < 31) hm
  exact (by decide : ∀ m : Nat, m ≤ 31 → m ∣ 31 → m = 1 ∨ m = 31) m hle hm

/-- 37 是素数 -/
theorem prime_37 : Prime 37 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 37 := Nat.le_of_dvd (by decide : 0 < 37) hm
  exact (by decide : ∀ m : Nat, m ≤ 37 → m ∣ 37 → m = 1 ∨ m = 37) m hle hm

/-- 41 是素数 -/
theorem prime_41 : Prime 41 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 41 := Nat.le_of_dvd (by decide : 0 < 41) hm
  exact (by decide : ∀ m : Nat, m ≤ 41 → m ∣ 41 → m = 1 ∨ m = 41) m hle hm

/-- 43 是素数 -/
theorem prime_43 : Prime 43 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hle : m ≤ 43 := Nat.le_of_dvd (by decide : 0 < 43) hm
  exact (by decide : ∀ m : Nat, m ≤ 43 → m ∣ 43 → m = 1 ∨ m = 43) m hle hm

/-- 71 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_71 : Prime 71 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 71 → m = 1 ∨ m = 71) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 71 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 71 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 71 := (by decide : ∀ k : Nat, k < 43 → k ∣ 71 → k = 1 ∨ k = 71) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 71 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 109 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_109 : Prime 109 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 109 → m = 1 ∨ m = 109) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 109 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 109 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 109 := (by decide : ∀ k : Nat, k < 43 → k ∣ 109 → k = 1 ∨ k = 109) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 109 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 193 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_193 : Prime 193 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 193 → m = 1 ∨ m = 193) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 193 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 193 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 193 := (by decide : ∀ k : Nat, k < 43 → k ∣ 193 → k = 1 ∨ k = 193) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 193 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 197 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_197 : Prime 197 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 197 → m = 1 ∨ m = 197) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 197 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 197 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 197 := (by decide : ∀ k : Nat, k < 43 → k ∣ 197 → k = 1 ∨ k = 197) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 197 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 199 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_199 : Prime 199 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 199 → m = 1 ∨ m = 199) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 199 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 199 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 199 := (by decide : ∀ k : Nat, k < 43 → k ∣ 199 → k = 1 ∨ k = 199) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 199 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 223 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_223 : Prime 223 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 223 → m = 1 ∨ m = 223) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 223 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 223 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 223 := (by decide : ∀ k : Nat, k < 43 → k ∣ 223 → k = 1 ∨ k = 223) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 223 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 433 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_433 : Prime 433 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 433 → m = 1 ∨ m = 433) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 433 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 433 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 433 := (by decide : ∀ k : Nat, k < 43 → k ∣ 433 → k = 1 ∨ k = 433) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 433 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 439 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_439 : Prime 439 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 439 → m = 1 ∨ m = 439) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 439 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 439 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 439 := (by decide : ∀ k : Nat, k < 43 → k ∣ 439 → k = 1 ∨ k = 439) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 439 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 443 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_443 : Prime 443 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 443 → m = 1 ∨ m = 443) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 443 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 443 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 443 := (by decide : ∀ k : Nat, k < 43 → k ∣ 443 → k = 1 ∨ k = 443) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 443 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 449 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_449 : Prime 449 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 449 → m = 1 ∨ m = 449) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 449 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 449 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 449 := (by decide : ∀ k : Nat, k < 43 → k ∣ 449 → k = 1 ∨ k = 449) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 449 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 1733 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_1733 : Prime 1733 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 1733 → m = 1 ∨ m = 1733) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 1733 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 1733 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 1733 := (by decide : ∀ k : Nat, k < 43 → k ∣ 1733 → k = 1 ∨ k = 1733) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 1733 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 1741 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_1741 : Prime 1741 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 1741 → m = 1 ∨ m = 1741) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 1741 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 1741 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 1741 := (by decide : ∀ k : Nat, k < 43 → k ∣ 1741 → k = 1 ∨ k = 1741) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 1741 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 1747 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_1747 : Prime 1747 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 1747 → m = 1 ∨ m = 1747) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 1747 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 1747 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 1747 := (by decide : ∀ k : Nat, k < 43 → k ∣ 1747 → k = 1 ∨ k = 1747) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 1747 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 1753 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_1753 : Prime 1753 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 1753 → m = 1 ∨ m = 1753) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 1753 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 1753 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 1753 := (by decide : ∀ k : Nat, k < 43 → k ∣ 1753 → k = 1 ∨ k = 1753) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 1753 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 1759 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_1759 : Prime 1759 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 1759 → m = 1 ∨ m = 1759) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 1759 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 1759 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 1759 := (by decide : ∀ k : Nat, k < 43 → k ∣ 1759 → k = 1 ∨ k = 1759) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 1759 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 1777 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_1777 : Prime 1777 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 1777 → m = 1 ∨ m = 1777) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 1777 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 1777 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 1777 := (by decide : ∀ k : Nat, k < 43 → k ∣ 1777 → k = 1 ∨ k = 1777) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 1777 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 1783 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_1783 : Prime 1783 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 1783 → m = 1 ∨ m = 1783) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 1783 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 1783 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 1783 := (by decide : ∀ k : Nat, k < 43 → k ∣ 1783 → k = 1 ∨ k = 1783) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 1783 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 1787 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_1787 : Prime 1787 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 1787 → m = 1 ∨ m = 1787) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 1787 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 1787 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 1787 := (by decide : ∀ k : Nat, k < 43 → k ∣ 1787 → k = 1 ∨ k = 1787) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 1787 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 1789 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_1789 : Prime 1789 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 43
  · exact (by decide : ∀ m : Nat, m < 43 → m ∣ 1789 → m = 1 ∨ m = 1789) m hmB hm
  · have hge : 43 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 43 := by
      have hle : 43 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 43 * k ≤ 1789 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 1789 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 1789 := (by decide : ∀ k : Nat, k < 43 → k ∣ 1789 → k = 1 ∨ k = 1789) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 1789 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 1729 不是 powerful 数（坏素因子 7 指数为 1） -/
theorem not_pow_1729 : ¬ Powerful 1729 := by
  intro h
  have hp : Prime 7 := prime_7
  have hd : 7 ∣ 1729 := by decide
  have hn : ¬ 7 ^ 2 ∣ 1729 := by decide
  exact hn (h 7 hp hd)

/-- 1730 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1730 : ¬ Powerful 1730 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1730 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1730 := by decide
  exact hn (h 2 hp hd)

/-- 1731 不是 powerful 数（坏素因子 3 指数为 1） -/
theorem not_pow_1731 : ¬ Powerful 1731 := by
  intro h
  have hp : Prime 3 := prime_3
  have hd : 3 ∣ 1731 := by decide
  have hn : ¬ 3 ^ 2 ∣ 1731 := by decide
  exact hn (h 3 hp hd)

/-- 1732 不是 powerful 数（坏素因子 433 指数为 1） -/
theorem not_pow_1732 : ¬ Powerful 1732 := by
  intro h
  have hp : Prime 433 := prime_433
  have hd : 433 ∣ 1732 := by decide
  have hn : ¬ 433 ^ 2 ∣ 1732 := by decide
  exact hn (h 433 hp hd)

/-- 1733 不是 powerful 数（坏素因子 1733 指数为 1） -/
theorem not_pow_1733 : ¬ Powerful 1733 := by
  intro h
  have hp : Prime 1733 := prime_1733
  have hd : 1733 ∣ 1733 := by decide
  have hn : ¬ 1733 ^ 2 ∣ 1733 := by decide
  exact hn (h 1733 hp hd)

/-- 1734 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1734 : ¬ Powerful 1734 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1734 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1734 := by decide
  exact hn (h 2 hp hd)

/-- 1735 不是 powerful 数（坏素因子 5 指数为 1） -/
theorem not_pow_1735 : ¬ Powerful 1735 := by
  intro h
  have hp : Prime 5 := prime_5
  have hd : 5 ∣ 1735 := by decide
  have hn : ¬ 5 ^ 2 ∣ 1735 := by decide
  exact hn (h 5 hp hd)

/-- 1736 不是 powerful 数（坏素因子 7 指数为 1） -/
theorem not_pow_1736 : ¬ Powerful 1736 := by
  intro h
  have hp : Prime 7 := prime_7
  have hd : 7 ∣ 1736 := by decide
  have hn : ¬ 7 ^ 2 ∣ 1736 := by decide
  exact hn (h 7 hp hd)

/-- 1737 不是 powerful 数（坏素因子 193 指数为 1） -/
theorem not_pow_1737 : ¬ Powerful 1737 := by
  intro h
  have hp : Prime 193 := prime_193
  have hd : 193 ∣ 1737 := by decide
  have hn : ¬ 193 ^ 2 ∣ 1737 := by decide
  exact hn (h 193 hp hd)

/-- 1738 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1738 : ¬ Powerful 1738 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1738 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1738 := by decide
  exact hn (h 2 hp hd)

/-- 1739 不是 powerful 数（坏素因子 37 指数为 1） -/
theorem not_pow_1739 : ¬ Powerful 1739 := by
  intro h
  have hp : Prime 37 := prime_37
  have hd : 37 ∣ 1739 := by decide
  have hn : ¬ 37 ^ 2 ∣ 1739 := by decide
  exact hn (h 37 hp hd)

/-- 1740 不是 powerful 数（坏素因子 3 指数为 1） -/
theorem not_pow_1740 : ¬ Powerful 1740 := by
  intro h
  have hp : Prime 3 := prime_3
  have hd : 3 ∣ 1740 := by decide
  have hn : ¬ 3 ^ 2 ∣ 1740 := by decide
  exact hn (h 3 hp hd)

/-- 1741 不是 powerful 数（坏素因子 1741 指数为 1） -/
theorem not_pow_1741 : ¬ Powerful 1741 := by
  intro h
  have hp : Prime 1741 := prime_1741
  have hd : 1741 ∣ 1741 := by decide
  have hn : ¬ 1741 ^ 2 ∣ 1741 := by decide
  exact hn (h 1741 hp hd)

/-- 1742 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1742 : ¬ Powerful 1742 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1742 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1742 := by decide
  exact hn (h 2 hp hd)

/-- 1743 不是 powerful 数（坏素因子 3 指数为 1） -/
theorem not_pow_1743 : ¬ Powerful 1743 := by
  intro h
  have hp : Prime 3 := prime_3
  have hd : 3 ∣ 1743 := by decide
  have hn : ¬ 3 ^ 2 ∣ 1743 := by decide
  exact hn (h 3 hp hd)

/-- 1744 不是 powerful 数（坏素因子 109 指数为 1） -/
theorem not_pow_1744 : ¬ Powerful 1744 := by
  intro h
  have hp : Prime 109 := prime_109
  have hd : 109 ∣ 1744 := by decide
  have hn : ¬ 109 ^ 2 ∣ 1744 := by decide
  exact hn (h 109 hp hd)

/-- 1745 不是 powerful 数（坏素因子 5 指数为 1） -/
theorem not_pow_1745 : ¬ Powerful 1745 := by
  intro h
  have hp : Prime 5 := prime_5
  have hd : 5 ∣ 1745 := by decide
  have hn : ¬ 5 ^ 2 ∣ 1745 := by decide
  exact hn (h 5 hp hd)

/-- 1746 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1746 : ¬ Powerful 1746 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1746 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1746 := by decide
  exact hn (h 2 hp hd)

/-- 1747 不是 powerful 数（坏素因子 1747 指数为 1） -/
theorem not_pow_1747 : ¬ Powerful 1747 := by
  intro h
  have hp : Prime 1747 := prime_1747
  have hd : 1747 ∣ 1747 := by decide
  have hn : ¬ 1747 ^ 2 ∣ 1747 := by decide
  exact hn (h 1747 hp hd)

/-- 1748 不是 powerful 数（坏素因子 19 指数为 1） -/
theorem not_pow_1748 : ¬ Powerful 1748 := by
  intro h
  have hp : Prime 19 := prime_19
  have hd : 19 ∣ 1748 := by decide
  have hn : ¬ 19 ^ 2 ∣ 1748 := by decide
  exact hn (h 19 hp hd)

/-- 1749 不是 powerful 数（坏素因子 3 指数为 1） -/
theorem not_pow_1749 : ¬ Powerful 1749 := by
  intro h
  have hp : Prime 3 := prime_3
  have hd : 3 ∣ 1749 := by decide
  have hn : ¬ 3 ^ 2 ∣ 1749 := by decide
  exact hn (h 3 hp hd)

/-- 1750 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1750 : ¬ Powerful 1750 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1750 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1750 := by decide
  exact hn (h 2 hp hd)

/-- 1751 不是 powerful 数（坏素因子 17 指数为 1） -/
theorem not_pow_1751 : ¬ Powerful 1751 := by
  intro h
  have hp : Prime 17 := prime_17
  have hd : 17 ∣ 1751 := by decide
  have hn : ¬ 17 ^ 2 ∣ 1751 := by decide
  exact hn (h 17 hp hd)

/-- 1752 不是 powerful 数（坏素因子 3 指数为 1） -/
theorem not_pow_1752 : ¬ Powerful 1752 := by
  intro h
  have hp : Prime 3 := prime_3
  have hd : 3 ∣ 1752 := by decide
  have hn : ¬ 3 ^ 2 ∣ 1752 := by decide
  exact hn (h 3 hp hd)

/-- 1753 不是 powerful 数（坏素因子 1753 指数为 1） -/
theorem not_pow_1753 : ¬ Powerful 1753 := by
  intro h
  have hp : Prime 1753 := prime_1753
  have hd : 1753 ∣ 1753 := by decide
  have hn : ¬ 1753 ^ 2 ∣ 1753 := by decide
  exact hn (h 1753 hp hd)

/-- 1754 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1754 : ¬ Powerful 1754 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1754 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1754 := by decide
  exact hn (h 2 hp hd)

/-- 1755 不是 powerful 数（坏素因子 5 指数为 1） -/
theorem not_pow_1755 : ¬ Powerful 1755 := by
  intro h
  have hp : Prime 5 := prime_5
  have hd : 5 ∣ 1755 := by decide
  have hn : ¬ 5 ^ 2 ∣ 1755 := by decide
  exact hn (h 5 hp hd)

/-- 1756 不是 powerful 数（坏素因子 439 指数为 1） -/
theorem not_pow_1756 : ¬ Powerful 1756 := by
  intro h
  have hp : Prime 439 := prime_439
  have hd : 439 ∣ 1756 := by decide
  have hn : ¬ 439 ^ 2 ∣ 1756 := by decide
  exact hn (h 439 hp hd)

/-- 1757 不是 powerful 数（坏素因子 7 指数为 1） -/
theorem not_pow_1757 : ¬ Powerful 1757 := by
  intro h
  have hp : Prime 7 := prime_7
  have hd : 7 ∣ 1757 := by decide
  have hn : ¬ 7 ^ 2 ∣ 1757 := by decide
  exact hn (h 7 hp hd)

/-- 1758 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1758 : ¬ Powerful 1758 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1758 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1758 := by decide
  exact hn (h 2 hp hd)

/-- 1759 不是 powerful 数（坏素因子 1759 指数为 1） -/
theorem not_pow_1759 : ¬ Powerful 1759 := by
  intro h
  have hp : Prime 1759 := prime_1759
  have hd : 1759 ∣ 1759 := by decide
  have hn : ¬ 1759 ^ 2 ∣ 1759 := by decide
  exact hn (h 1759 hp hd)

/-- 1760 不是 powerful 数（坏素因子 5 指数为 1） -/
theorem not_pow_1760 : ¬ Powerful 1760 := by
  intro h
  have hp : Prime 5 := prime_5
  have hd : 5 ∣ 1760 := by decide
  have hn : ¬ 5 ^ 2 ∣ 1760 := by decide
  exact hn (h 5 hp hd)

/-- 1761 不是 powerful 数（坏素因子 3 指数为 1） -/
theorem not_pow_1761 : ¬ Powerful 1761 := by
  intro h
  have hp : Prime 3 := prime_3
  have hd : 3 ∣ 1761 := by decide
  have hn : ¬ 3 ^ 2 ∣ 1761 := by decide
  exact hn (h 3 hp hd)

/-- 1762 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1762 : ¬ Powerful 1762 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1762 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1762 := by decide
  exact hn (h 2 hp hd)

/-- 1763 不是 powerful 数（坏素因子 41 指数为 1） -/
theorem not_pow_1763 : ¬ Powerful 1763 := by
  intro h
  have hp : Prime 41 := prime_41
  have hd : 41 ∣ 1763 := by decide
  have hn : ¬ 41 ^ 2 ∣ 1763 := by decide
  exact hn (h 41 hp hd)

/-- 1765 不是 powerful 数（坏素因子 5 指数为 1） -/
theorem not_pow_1765 : ¬ Powerful 1765 := by
  intro h
  have hp : Prime 5 := prime_5
  have hd : 5 ∣ 1765 := by decide
  have hn : ¬ 5 ^ 2 ∣ 1765 := by decide
  exact hn (h 5 hp hd)

/-- 1766 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1766 : ¬ Powerful 1766 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1766 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1766 := by decide
  exact hn (h 2 hp hd)

/-- 1767 不是 powerful 数（坏素因子 3 指数为 1） -/
theorem not_pow_1767 : ¬ Powerful 1767 := by
  intro h
  have hp : Prime 3 := prime_3
  have hd : 3 ∣ 1767 := by decide
  have hn : ¬ 3 ^ 2 ∣ 1767 := by decide
  exact hn (h 3 hp hd)

/-- 1768 不是 powerful 数（坏素因子 13 指数为 1） -/
theorem not_pow_1768 : ¬ Powerful 1768 := by
  intro h
  have hp : Prime 13 := prime_13
  have hd : 13 ∣ 1768 := by decide
  have hn : ¬ 13 ^ 2 ∣ 1768 := by decide
  exact hn (h 13 hp hd)

/-- 1769 不是 powerful 数（坏素因子 29 指数为 1） -/
theorem not_pow_1769 : ¬ Powerful 1769 := by
  intro h
  have hp : Prime 29 := prime_29
  have hd : 29 ∣ 1769 := by decide
  have hn : ¬ 29 ^ 2 ∣ 1769 := by decide
  exact hn (h 29 hp hd)

/-- 1770 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1770 : ¬ Powerful 1770 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1770 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1770 := by decide
  exact hn (h 2 hp hd)

/-- 1771 不是 powerful 数（坏素因子 7 指数为 1） -/
theorem not_pow_1771 : ¬ Powerful 1771 := by
  intro h
  have hp : Prime 7 := prime_7
  have hd : 7 ∣ 1771 := by decide
  have hn : ¬ 7 ^ 2 ∣ 1771 := by decide
  exact hn (h 7 hp hd)

/-- 1772 不是 powerful 数（坏素因子 443 指数为 1） -/
theorem not_pow_1772 : ¬ Powerful 1772 := by
  intro h
  have hp : Prime 443 := prime_443
  have hd : 443 ∣ 1772 := by decide
  have hn : ¬ 443 ^ 2 ∣ 1772 := by decide
  exact hn (h 443 hp hd)

/-- 1773 不是 powerful 数（坏素因子 197 指数为 1） -/
theorem not_pow_1773 : ¬ Powerful 1773 := by
  intro h
  have hp : Prime 197 := prime_197
  have hd : 197 ∣ 1773 := by decide
  have hn : ¬ 197 ^ 2 ∣ 1773 := by decide
  exact hn (h 197 hp hd)

/-- 1774 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1774 : ¬ Powerful 1774 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1774 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1774 := by decide
  exact hn (h 2 hp hd)

/-- 1775 不是 powerful 数（坏素因子 71 指数为 1） -/
theorem not_pow_1775 : ¬ Powerful 1775 := by
  intro h
  have hp : Prime 71 := prime_71
  have hd : 71 ∣ 1775 := by decide
  have hn : ¬ 71 ^ 2 ∣ 1775 := by decide
  exact hn (h 71 hp hd)

/-- 1776 不是 powerful 数（坏素因子 3 指数为 1） -/
theorem not_pow_1776 : ¬ Powerful 1776 := by
  intro h
  have hp : Prime 3 := prime_3
  have hd : 3 ∣ 1776 := by decide
  have hn : ¬ 3 ^ 2 ∣ 1776 := by decide
  exact hn (h 3 hp hd)

/-- 1777 不是 powerful 数（坏素因子 1777 指数为 1） -/
theorem not_pow_1777 : ¬ Powerful 1777 := by
  intro h
  have hp : Prime 1777 := prime_1777
  have hd : 1777 ∣ 1777 := by decide
  have hn : ¬ 1777 ^ 2 ∣ 1777 := by decide
  exact hn (h 1777 hp hd)

/-- 1778 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1778 : ¬ Powerful 1778 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1778 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1778 := by decide
  exact hn (h 2 hp hd)

/-- 1779 不是 powerful 数（坏素因子 3 指数为 1） -/
theorem not_pow_1779 : ¬ Powerful 1779 := by
  intro h
  have hp : Prime 3 := prime_3
  have hd : 3 ∣ 1779 := by decide
  have hn : ¬ 3 ^ 2 ∣ 1779 := by decide
  exact hn (h 3 hp hd)

/-- 1780 不是 powerful 数（坏素因子 5 指数为 1） -/
theorem not_pow_1780 : ¬ Powerful 1780 := by
  intro h
  have hp : Prime 5 := prime_5
  have hd : 5 ∣ 1780 := by decide
  have hn : ¬ 5 ^ 2 ∣ 1780 := by decide
  exact hn (h 5 hp hd)

/-- 1781 不是 powerful 数（坏素因子 13 指数为 1） -/
theorem not_pow_1781 : ¬ Powerful 1781 := by
  intro h
  have hp : Prime 13 := prime_13
  have hd : 13 ∣ 1781 := by decide
  have hn : ¬ 13 ^ 2 ∣ 1781 := by decide
  exact hn (h 13 hp hd)

/-- 1782 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1782 : ¬ Powerful 1782 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1782 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1782 := by decide
  exact hn (h 2 hp hd)

/-- 1783 不是 powerful 数（坏素因子 1783 指数为 1） -/
theorem not_pow_1783 : ¬ Powerful 1783 := by
  intro h
  have hp : Prime 1783 := prime_1783
  have hd : 1783 ∣ 1783 := by decide
  have hn : ¬ 1783 ^ 2 ∣ 1783 := by decide
  exact hn (h 1783 hp hd)

/-- 1784 不是 powerful 数（坏素因子 223 指数为 1） -/
theorem not_pow_1784 : ¬ Powerful 1784 := by
  intro h
  have hp : Prime 223 := prime_223
  have hd : 223 ∣ 1784 := by decide
  have hn : ¬ 223 ^ 2 ∣ 1784 := by decide
  exact hn (h 223 hp hd)

/-- 1785 不是 powerful 数（坏素因子 3 指数为 1） -/
theorem not_pow_1785 : ¬ Powerful 1785 := by
  intro h
  have hp : Prime 3 := prime_3
  have hd : 3 ∣ 1785 := by decide
  have hn : ¬ 3 ^ 2 ∣ 1785 := by decide
  exact hn (h 3 hp hd)

/-- 1786 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1786 : ¬ Powerful 1786 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1786 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1786 := by decide
  exact hn (h 2 hp hd)

/-- 1787 不是 powerful 数（坏素因子 1787 指数为 1） -/
theorem not_pow_1787 : ¬ Powerful 1787 := by
  intro h
  have hp : Prime 1787 := prime_1787
  have hd : 1787 ∣ 1787 := by decide
  have hn : ¬ 1787 ^ 2 ∣ 1787 := by decide
  exact hn (h 1787 hp hd)

/-- 1788 不是 powerful 数（坏素因子 3 指数为 1） -/
theorem not_pow_1788 : ¬ Powerful 1788 := by
  intro h
  have hp : Prime 3 := prime_3
  have hd : 3 ∣ 1788 := by decide
  have hn : ¬ 3 ^ 2 ∣ 1788 := by decide
  exact hn (h 3 hp hd)

/-- 1789 不是 powerful 数（坏素因子 1789 指数为 1） -/
theorem not_pow_1789 : ¬ Powerful 1789 := by
  intro h
  have hp : Prime 1789 := prime_1789
  have hd : 1789 ∣ 1789 := by decide
  have hn : ¬ 1789 ^ 2 ∣ 1789 := by decide
  exact hn (h 1789 hp hd)

/-- 1790 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1790 : ¬ Powerful 1790 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1790 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1790 := by decide
  exact hn (h 2 hp hd)

/-- 1791 不是 powerful 数（坏素因子 199 指数为 1） -/
theorem not_pow_1791 : ¬ Powerful 1791 := by
  intro h
  have hp : Prime 199 := prime_199
  have hd : 199 ∣ 1791 := by decide
  have hn : ¬ 199 ^ 2 ∣ 1791 := by decide
  exact hn (h 199 hp hd)

/-- 1792 不是 powerful 数（坏素因子 7 指数为 1） -/
theorem not_pow_1792 : ¬ Powerful 1792 := by
  intro h
  have hp : Prime 7 := prime_7
  have hd : 7 ∣ 1792 := by decide
  have hn : ¬ 7 ^ 2 ∣ 1792 := by decide
  exact hn (h 7 hp hd)

/-- 1793 不是 powerful 数（坏素因子 11 指数为 1） -/
theorem not_pow_1793 : ¬ Powerful 1793 := by
  intro h
  have hp : Prime 11 := prime_11
  have hd : 11 ∣ 1793 := by decide
  have hn : ¬ 11 ^ 2 ∣ 1793 := by decide
  exact hn (h 11 hp hd)

/-- 1794 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1794 : ¬ Powerful 1794 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1794 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1794 := by decide
  exact hn (h 2 hp hd)

/-- 1795 不是 powerful 数（坏素因子 5 指数为 1） -/
theorem not_pow_1795 : ¬ Powerful 1795 := by
  intro h
  have hp : Prime 5 := prime_5
  have hd : 5 ∣ 1795 := by decide
  have hn : ¬ 5 ^ 2 ∣ 1795 := by decide
  exact hn (h 5 hp hd)

/-- 1796 不是 powerful 数（坏素因子 449 指数为 1） -/
theorem not_pow_1796 : ¬ Powerful 1796 := by
  intro h
  have hp : Prime 449 := prime_449
  have hd : 449 ∣ 1796 := by decide
  have hn : ¬ 449 ^ 2 ∣ 1796 := by decide
  exact hn (h 449 hp hd)

/-- 1797 不是 powerful 数（坏素因子 3 指数为 1） -/
theorem not_pow_1797 : ¬ Powerful 1797 := by
  intro h
  have hp : Prime 3 := prime_3
  have hd : 3 ∣ 1797 := by decide
  have hn : ¬ 3 ^ 2 ∣ 1797 := by decide
  exact hn (h 3 hp hd)

/-- 1798 不是 powerful 数（坏素因子 2 指数为 1） -/
theorem not_pow_1798 : ¬ Powerful 1798 := by
  intro h
  have hp : Prime 2 := prime_2
  have hd : 2 ∣ 1798 := by decide
  have hn : ¬ 2 ^ 2 ∣ 1798 := by decide
  exact hn (h 2 hp hd)

/-- 1799 不是 powerful 数（坏素因子 7 指数为 1） -/
theorem not_pow_1799 : ¬ Powerful 1799 := by
  intro h
  have hp : Prime 7 := prime_7
  have hd : 7 ∣ 1799 := by decide
  have hn : ¬ 7 ^ 2 ∣ 1799 := by decide
  exact hn (h 7 hp hd)

/-- 1728 的小范围约数（< 43） -/
theorem divisors_1728 (q : Nat) (hq : q < 43) (hd : q ∣ 1728) :
    q ∈ [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 32, 36] := by
  exact (by decide : ∀ q : Nat, q < 43 → q ∣ 1728 → q ∈ [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 32, 36]) q hq hd

/-- 1728 无 ≥ 43 的素因子 -/
theorem no_large_prime_1728 {p : Nat} (hp : Prime p) (hge : 43 ≤ p) : ¬ p ∣ 1728 := by
  intro hd
  rcases hd with ⟨k, hk⟩
  have hklt : k < 43 := by
    have hle : 43 * k ≤ p * k := Nat.mul_le_mul_right k hge
    have hb : 43 * k ≤ 1728 := by rw [hk]; exact hle
    omega
  have hkd : k ∣ 1728 := ⟨p, by rw [hk]; exact Nat.mul_comm p k⟩
  have hmem := divisors_1728 k hklt hkd
  have hOr : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6 ∨ k = 8 ∨ k = 9 ∨ k = 12 ∨ k = 16 ∨ k = 18 ∨ k = 24 ∨ k = 27 ∨ k = 32 ∨ k = 36 := by
    simpa using hmem
  rcases hOr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · subst k; have hpv : p = 1728 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 1728) (by decide : 2 ≠ 1) (by decide : 2 ≠ 1728) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 864 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 864) (by decide : 2 ≠ 1) (by decide : 2 ≠ 864) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 576 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 576) (by decide : 2 ≠ 1) (by decide : 2 ≠ 576) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 432 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 432) (by decide : 2 ≠ 1) (by decide : 2 ≠ 432) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 288 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 288) (by decide : 2 ≠ 1) (by decide : 2 ≠ 288) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 216 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 216) (by decide : 2 ≠ 1) (by decide : 2 ≠ 216) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 192 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 192) (by decide : 2 ≠ 1) (by decide : 2 ≠ 192) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 144 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 144) (by decide : 2 ≠ 1) (by decide : 2 ≠ 144) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 108 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 108) (by decide : 2 ≠ 1) (by decide : 2 ≠ 108) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 96 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 96) (by decide : 2 ≠ 1) (by decide : 2 ≠ 96) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 72 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 72) (by decide : 2 ≠ 1) (by decide : 2 ≠ 72) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 64 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 64) (by decide : 2 ≠ 1) (by decide : 2 ≠ 64) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 54 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 54) (by decide : 2 ≠ 1) (by decide : 2 ≠ 54) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 48 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 48) (by decide : 2 ≠ 1) (by decide : 2 ≠ 48) (by simpa [hpv] using hp)

/-- 1728 是 powerful 数 -/
theorem powerful_1728 : Powerful 1728 := by
  intro p hp hdvd
  by_cases hpB : p < 43
  · have hmem : p ∈ List.range 43 := List.mem_range.mpr (by omega)
    have hcheck : powerfulIn 1728 (List.range 43) = true := by decide
    have hfp := listAll_elim hcheck p hmem
    have hdvb : decide (p ∣ 1728) = true := by exact decide_eq_true hdvd
    have hpb : primeCheck p = true := primeCheck_of_Prime p hp
    have hn1 : Bool.not (decide (p ∣ 1728)) = false := by simp [hdvb]
    have hn2 : Bool.not (primeCheck p) = false := by simp [hpb]
    have hc : decide (((p ^ 2) ∣ 1728)) = true := by simpa [hn1, hn2] using hfp
    exact of_decide_eq_true hc
  · exact False.elim ((no_large_prime_1728 hp (by omega)) hdvd)

/-- 1764 的小范围约数（< 43） -/
theorem divisors_1764 (q : Nat) (hq : q < 43) (hd : q ∣ 1764) :
    q ∈ [1, 2, 3, 4, 6, 7, 9, 12, 14, 18, 21, 28, 36, 42] := by
  exact (by decide : ∀ q : Nat, q < 43 → q ∣ 1764 → q ∈ [1, 2, 3, 4, 6, 7, 9, 12, 14, 18, 21, 28, 36, 42]) q hq hd

/-- 1764 无 ≥ 43 的素因子 -/
theorem no_large_prime_1764 {p : Nat} (hp : Prime p) (hge : 43 ≤ p) : ¬ p ∣ 1764 := by
  intro hd
  rcases hd with ⟨k, hk⟩
  have hklt : k < 43 := by
    have hle : 43 * k ≤ p * k := Nat.mul_le_mul_right k hge
    have hb : 43 * k ≤ 1764 := by rw [hk]; exact hle
    omega
  have hkd : k ∣ 1764 := ⟨p, by rw [hk]; exact Nat.mul_comm p k⟩
  have hmem := divisors_1764 k hklt hkd
  have hOr : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 9 ∨ k = 12 ∨ k = 14 ∨ k = 18 ∨ k = 21 ∨ k = 28 ∨ k = 36 ∨ k = 42 := by
    simpa using hmem
  rcases hOr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · subst k; have hpv : p = 1764 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 1764) (by decide : 2 ≠ 1) (by decide : 2 ≠ 1764) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 882 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 882) (by decide : 2 ≠ 1) (by decide : 2 ≠ 882) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 588 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 588) (by decide : 2 ≠ 1) (by decide : 2 ≠ 588) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 441 := by omega
    exact not_prime_of_dvd (by decide : 3 ∣ 441) (by decide : 3 ≠ 1) (by decide : 3 ≠ 441) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 294 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 294) (by decide : 2 ≠ 1) (by decide : 2 ≠ 294) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 252 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 252) (by decide : 2 ≠ 1) (by decide : 2 ≠ 252) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 196 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 196) (by decide : 2 ≠ 1) (by decide : 2 ≠ 196) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 147 := by omega
    exact not_prime_of_dvd (by decide : 3 ∣ 147) (by decide : 3 ≠ 1) (by decide : 3 ≠ 147) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 126 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 126) (by decide : 2 ≠ 1) (by decide : 2 ≠ 126) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 98 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 98) (by decide : 2 ≠ 1) (by decide : 2 ≠ 98) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 84 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 84) (by decide : 2 ≠ 1) (by decide : 2 ≠ 84) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 63 := by omega
    exact not_prime_of_dvd (by decide : 3 ∣ 63) (by decide : 3 ≠ 1) (by decide : 3 ≠ 63) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 49 := by omega
    exact not_prime_of_dvd (by decide : 7 ∣ 49) (by decide : 7 ≠ 1) (by decide : 7 ≠ 49) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 42 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 42) (by decide : 2 ≠ 1) (by decide : 2 ≠ 42) (by simpa [hpv] using hp)

/-- 1764 是 powerful 数 -/
theorem powerful_1764 : Powerful 1764 := by
  intro p hp hdvd
  by_cases hpB : p < 43
  · have hmem : p ∈ List.range 43 := List.mem_range.mpr (by omega)
    have hcheck : powerfulIn 1764 (List.range 43) = true := by decide
    have hfp := listAll_elim hcheck p hmem
    have hdvb : decide (p ∣ 1764) = true := by exact decide_eq_true hdvd
    have hpb : primeCheck p = true := primeCheck_of_Prime p hp
    have hn1 : Bool.not (decide (p ∣ 1764)) = false := by simp [hdvb]
    have hn2 : Bool.not (primeCheck p) = false := by simp [hpb]
    have hc : decide (((p ^ 2) ∣ 1764)) = true := by simpa [hn1, hn2] using hfp
    exact of_decide_eq_true hc
  · exact False.elim ((no_large_prime_1764 hp (by omega)) hdvd)

/-- 1800 的小范围约数（< 43） -/
theorem divisors_1800 (q : Nat) (hq : q < 43) (hd : q ∣ 1800) :
    q ∈ [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 25, 30, 36, 40] := by
  exact (by decide : ∀ q : Nat, q < 43 → q ∣ 1800 → q ∈ [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 25, 30, 36, 40]) q hq hd

/-- 1800 无 ≥ 43 的素因子 -/
theorem no_large_prime_1800 {p : Nat} (hp : Prime p) (hge : 43 ≤ p) : ¬ p ∣ 1800 := by
  intro hd
  rcases hd with ⟨k, hk⟩
  have hklt : k < 43 := by
    have hle : 43 * k ≤ p * k := Nat.mul_le_mul_right k hge
    have hb : 43 * k ≤ 1800 := by rw [hk]; exact hle
    omega
  have hkd : k ∣ 1800 := ⟨p, by rw [hk]; exact Nat.mul_comm p k⟩
  have hmem := divisors_1800 k hklt hkd
  have hOr : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 12 ∨ k = 15 ∨ k = 18 ∨ k = 20 ∨ k = 24 ∨ k = 25 ∨ k = 30 ∨ k = 36 ∨ k = 40 := by
    simpa using hmem
  rcases hOr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17
  · subst k; have hpv : p = 1800 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 1800) (by decide : 2 ≠ 1) (by decide : 2 ≠ 1800) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 900 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 900) (by decide : 2 ≠ 1) (by decide : 2 ≠ 900) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 600 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 600) (by decide : 2 ≠ 1) (by decide : 2 ≠ 600) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 450 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 450) (by decide : 2 ≠ 1) (by decide : 2 ≠ 450) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 360 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 360) (by decide : 2 ≠ 1) (by decide : 2 ≠ 360) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 300 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 300) (by decide : 2 ≠ 1) (by decide : 2 ≠ 300) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 225 := by omega
    exact not_prime_of_dvd (by decide : 3 ∣ 225) (by decide : 3 ≠ 1) (by decide : 3 ≠ 225) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 200 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 200) (by decide : 2 ≠ 1) (by decide : 2 ≠ 200) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 180 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 180) (by decide : 2 ≠ 1) (by decide : 2 ≠ 180) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 150 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 150) (by decide : 2 ≠ 1) (by decide : 2 ≠ 150) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 120 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 120) (by decide : 2 ≠ 1) (by decide : 2 ≠ 120) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 100 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 100) (by decide : 2 ≠ 1) (by decide : 2 ≠ 100) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 90 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 90) (by decide : 2 ≠ 1) (by decide : 2 ≠ 90) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 75 := by omega
    exact not_prime_of_dvd (by decide : 3 ∣ 75) (by decide : 3 ≠ 1) (by decide : 3 ≠ 75) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 72 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 72) (by decide : 2 ≠ 1) (by decide : 2 ≠ 72) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 60 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 60) (by decide : 2 ≠ 1) (by decide : 2 ≠ 60) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 50 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 50) (by decide : 2 ≠ 1) (by decide : 2 ≠ 50) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 45 := by omega
    exact not_prime_of_dvd (by decide : 3 ∣ 45) (by decide : 3 ≠ 1) (by decide : 3 ≠ 45) (by simpa [hpv] using hp)

/-- 1800 是 powerful 数 -/
theorem powerful_1800 : Powerful 1800 := by
  intro p hp hdvd
  by_cases hpB : p < 43
  · have hmem : p ∈ List.range 43 := List.mem_range.mpr (by omega)
    have hcheck : powerfulIn 1800 (List.range 43) = true := by decide
    have hfp := listAll_elim hcheck p hmem
    have hdvb : decide (p ∣ 1800) = true := by exact decide_eq_true hdvd
    have hpb : primeCheck p = true := primeCheck_of_Prime p hp
    have hn1 : Bool.not (decide (p ∣ 1800)) = false := by simp [hdvb]
    have hn2 : Bool.not (primeCheck p) = false := by simp [hpb]
    have hc : decide (((p ^ 2) ∣ 1800)) = true := by simpa [hn1, hn2] using hfp
    exact of_decide_eq_true hc
  · exact False.elim ((no_large_prime_1800 hp (by omega)) hdvd)

theorem nd_1729_1730 : ∀ x : Nat, 1728 < x → x < 1731 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1729 ∨ x = 1730 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1729
  · rw [hx]
    exact not_pow_1730

theorem nd_1731_1732 : ∀ x : Nat, 1730 < x → x < 1733 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1731 ∨ x = 1732 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1731
  · rw [hx]
    exact not_pow_1732

theorem nd_1729_1732 : ∀ x : Nat, 1728 < x → x < 1733 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1731 ∨ 1731 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1729_1730 x h1 hc
  · exact nd_1731_1732 x (by omega) h2

theorem nd_1733_1734 : ∀ x : Nat, 1732 < x → x < 1735 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1733 ∨ x = 1734 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1733
  · rw [hx]
    exact not_pow_1734

theorem nd_1735_1736 : ∀ x : Nat, 1734 < x → x < 1737 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1735 ∨ x = 1736 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1735
  · rw [hx]
    exact not_pow_1736

theorem nd_1733_1736 : ∀ x : Nat, 1732 < x → x < 1737 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1735 ∨ 1735 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1733_1734 x h1 hc
  · exact nd_1735_1736 x (by omega) h2

theorem nd_1729_1736 : ∀ x : Nat, 1728 < x → x < 1737 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1733 ∨ 1733 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1729_1732 x h1 hc
  · exact nd_1733_1736 x (by omega) h2

theorem nd_1737_1738 : ∀ x : Nat, 1736 < x → x < 1739 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1737 ∨ x = 1738 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1737
  · rw [hx]
    exact not_pow_1738

theorem nd_1739_1740 : ∀ x : Nat, 1738 < x → x < 1741 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1739 ∨ x = 1740 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1739
  · rw [hx]
    exact not_pow_1740

theorem nd_1737_1740 : ∀ x : Nat, 1736 < x → x < 1741 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1739 ∨ 1739 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1737_1738 x h1 hc
  · exact nd_1739_1740 x (by omega) h2

theorem nd_1741_1742 : ∀ x : Nat, 1740 < x → x < 1743 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1741 ∨ x = 1742 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1741
  · rw [hx]
    exact not_pow_1742

theorem nd_1743_1743 : ∀ x : Nat, 1742 < x → x < 1744 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1743 := by omega
  rw [hx]
  exact not_pow_1743

theorem nd_1744_1745 : ∀ x : Nat, 1743 < x → x < 1746 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1744 ∨ x = 1745 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1744
  · rw [hx]
    exact not_pow_1745

theorem nd_1743_1745 : ∀ x : Nat, 1742 < x → x < 1746 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1744 ∨ 1744 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1743_1743 x h1 hc
  · exact nd_1744_1745 x (by omega) h2

theorem nd_1741_1745 : ∀ x : Nat, 1740 < x → x < 1746 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1743 ∨ 1743 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1741_1742 x h1 hc
  · exact nd_1743_1745 x (by omega) h2

theorem nd_1737_1745 : ∀ x : Nat, 1736 < x → x < 1746 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1741 ∨ 1741 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1737_1740 x h1 hc
  · exact nd_1741_1745 x (by omega) h2

theorem nd_1729_1745 : ∀ x : Nat, 1728 < x → x < 1746 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1737 ∨ 1737 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1729_1736 x h1 hc
  · exact nd_1737_1745 x (by omega) h2

theorem nd_1746_1747 : ∀ x : Nat, 1745 < x → x < 1748 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1746 ∨ x = 1747 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1746
  · rw [hx]
    exact not_pow_1747

theorem nd_1748_1749 : ∀ x : Nat, 1747 < x → x < 1750 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1748 ∨ x = 1749 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1748
  · rw [hx]
    exact not_pow_1749

theorem nd_1746_1749 : ∀ x : Nat, 1745 < x → x < 1750 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1748 ∨ 1748 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1746_1747 x h1 hc
  · exact nd_1748_1749 x (by omega) h2

theorem nd_1750_1751 : ∀ x : Nat, 1749 < x → x < 1752 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1750 ∨ x = 1751 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1750
  · rw [hx]
    exact not_pow_1751

theorem nd_1752_1752 : ∀ x : Nat, 1751 < x → x < 1753 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1752 := by omega
  rw [hx]
  exact not_pow_1752

theorem nd_1753_1754 : ∀ x : Nat, 1752 < x → x < 1755 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1753 ∨ x = 1754 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1753
  · rw [hx]
    exact not_pow_1754

theorem nd_1752_1754 : ∀ x : Nat, 1751 < x → x < 1755 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1753 ∨ 1753 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1752_1752 x h1 hc
  · exact nd_1753_1754 x (by omega) h2

theorem nd_1750_1754 : ∀ x : Nat, 1749 < x → x < 1755 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1752 ∨ 1752 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1750_1751 x h1 hc
  · exact nd_1752_1754 x (by omega) h2

theorem nd_1746_1754 : ∀ x : Nat, 1745 < x → x < 1755 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1750 ∨ 1750 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1746_1749 x h1 hc
  · exact nd_1750_1754 x (by omega) h2

theorem nd_1755_1756 : ∀ x : Nat, 1754 < x → x < 1757 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1755 ∨ x = 1756 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1755
  · rw [hx]
    exact not_pow_1756

theorem nd_1757_1758 : ∀ x : Nat, 1756 < x → x < 1759 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1757 ∨ x = 1758 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1757
  · rw [hx]
    exact not_pow_1758

theorem nd_1755_1758 : ∀ x : Nat, 1754 < x → x < 1759 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1757 ∨ 1757 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1755_1756 x h1 hc
  · exact nd_1757_1758 x (by omega) h2

theorem nd_1759_1760 : ∀ x : Nat, 1758 < x → x < 1761 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1759 ∨ x = 1760 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1759
  · rw [hx]
    exact not_pow_1760

theorem nd_1761_1761 : ∀ x : Nat, 1760 < x → x < 1762 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1761 := by omega
  rw [hx]
  exact not_pow_1761

theorem nd_1762_1763 : ∀ x : Nat, 1761 < x → x < 1764 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1762 ∨ x = 1763 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1762
  · rw [hx]
    exact not_pow_1763

theorem nd_1761_1763 : ∀ x : Nat, 1760 < x → x < 1764 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1762 ∨ 1762 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1761_1761 x h1 hc
  · exact nd_1762_1763 x (by omega) h2

theorem nd_1759_1763 : ∀ x : Nat, 1758 < x → x < 1764 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1761 ∨ 1761 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1759_1760 x h1 hc
  · exact nd_1761_1763 x (by omega) h2

theorem nd_1755_1763 : ∀ x : Nat, 1754 < x → x < 1764 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1759 ∨ 1759 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1755_1758 x h1 hc
  · exact nd_1759_1763 x (by omega) h2

theorem nd_1746_1763 : ∀ x : Nat, 1745 < x → x < 1764 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1755 ∨ 1755 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1746_1754 x h1 hc
  · exact nd_1755_1763 x (by omega) h2

theorem nd_1729_1763 : ∀ x : Nat, 1728 < x → x < 1764 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1746 ∨ 1746 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1729_1745 x h1 hc
  · exact nd_1746_1763 x (by omega) h2

theorem nd_1765_1766 : ∀ x : Nat, 1764 < x → x < 1767 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1765 ∨ x = 1766 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1765
  · rw [hx]
    exact not_pow_1766

theorem nd_1767_1768 : ∀ x : Nat, 1766 < x → x < 1769 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1767 ∨ x = 1768 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1767
  · rw [hx]
    exact not_pow_1768

theorem nd_1765_1768 : ∀ x : Nat, 1764 < x → x < 1769 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1767 ∨ 1767 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1765_1766 x h1 hc
  · exact nd_1767_1768 x (by omega) h2

theorem nd_1769_1770 : ∀ x : Nat, 1768 < x → x < 1771 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1769 ∨ x = 1770 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1769
  · rw [hx]
    exact not_pow_1770

theorem nd_1771_1772 : ∀ x : Nat, 1770 < x → x < 1773 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1771 ∨ x = 1772 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1771
  · rw [hx]
    exact not_pow_1772

theorem nd_1769_1772 : ∀ x : Nat, 1768 < x → x < 1773 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1771 ∨ 1771 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1769_1770 x h1 hc
  · exact nd_1771_1772 x (by omega) h2

theorem nd_1765_1772 : ∀ x : Nat, 1764 < x → x < 1773 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1769 ∨ 1769 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1765_1768 x h1 hc
  · exact nd_1769_1772 x (by omega) h2

theorem nd_1773_1774 : ∀ x : Nat, 1772 < x → x < 1775 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1773 ∨ x = 1774 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1773
  · rw [hx]
    exact not_pow_1774

theorem nd_1775_1776 : ∀ x : Nat, 1774 < x → x < 1777 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1775 ∨ x = 1776 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1775
  · rw [hx]
    exact not_pow_1776

theorem nd_1773_1776 : ∀ x : Nat, 1772 < x → x < 1777 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1775 ∨ 1775 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1773_1774 x h1 hc
  · exact nd_1775_1776 x (by omega) h2

theorem nd_1777_1778 : ∀ x : Nat, 1776 < x → x < 1779 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1777 ∨ x = 1778 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1777
  · rw [hx]
    exact not_pow_1778

theorem nd_1779_1779 : ∀ x : Nat, 1778 < x → x < 1780 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1779 := by omega
  rw [hx]
  exact not_pow_1779

theorem nd_1780_1781 : ∀ x : Nat, 1779 < x → x < 1782 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1780 ∨ x = 1781 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1780
  · rw [hx]
    exact not_pow_1781

theorem nd_1779_1781 : ∀ x : Nat, 1778 < x → x < 1782 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1780 ∨ 1780 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1779_1779 x h1 hc
  · exact nd_1780_1781 x (by omega) h2

theorem nd_1777_1781 : ∀ x : Nat, 1776 < x → x < 1782 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1779 ∨ 1779 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1777_1778 x h1 hc
  · exact nd_1779_1781 x (by omega) h2

theorem nd_1773_1781 : ∀ x : Nat, 1772 < x → x < 1782 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1777 ∨ 1777 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1773_1776 x h1 hc
  · exact nd_1777_1781 x (by omega) h2

theorem nd_1765_1781 : ∀ x : Nat, 1764 < x → x < 1782 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1773 ∨ 1773 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1765_1772 x h1 hc
  · exact nd_1773_1781 x (by omega) h2

theorem nd_1782_1783 : ∀ x : Nat, 1781 < x → x < 1784 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1782 ∨ x = 1783 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1782
  · rw [hx]
    exact not_pow_1783

theorem nd_1784_1785 : ∀ x : Nat, 1783 < x → x < 1786 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1784 ∨ x = 1785 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1784
  · rw [hx]
    exact not_pow_1785

theorem nd_1782_1785 : ∀ x : Nat, 1781 < x → x < 1786 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1784 ∨ 1784 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1782_1783 x h1 hc
  · exact nd_1784_1785 x (by omega) h2

theorem nd_1786_1787 : ∀ x : Nat, 1785 < x → x < 1788 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1786 ∨ x = 1787 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1786
  · rw [hx]
    exact not_pow_1787

theorem nd_1788_1788 : ∀ x : Nat, 1787 < x → x < 1789 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1788 := by omega
  rw [hx]
  exact not_pow_1788

theorem nd_1789_1790 : ∀ x : Nat, 1788 < x → x < 1791 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1789 ∨ x = 1790 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1789
  · rw [hx]
    exact not_pow_1790

theorem nd_1788_1790 : ∀ x : Nat, 1787 < x → x < 1791 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1789 ∨ 1789 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1788_1788 x h1 hc
  · exact nd_1789_1790 x (by omega) h2

theorem nd_1786_1790 : ∀ x : Nat, 1785 < x → x < 1791 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1788 ∨ 1788 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1786_1787 x h1 hc
  · exact nd_1788_1790 x (by omega) h2

theorem nd_1782_1790 : ∀ x : Nat, 1781 < x → x < 1791 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1786 ∨ 1786 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1782_1785 x h1 hc
  · exact nd_1786_1790 x (by omega) h2

theorem nd_1791_1792 : ∀ x : Nat, 1790 < x → x < 1793 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1791 ∨ x = 1792 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1791
  · rw [hx]
    exact not_pow_1792

theorem nd_1793_1794 : ∀ x : Nat, 1792 < x → x < 1795 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1793 ∨ x = 1794 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1793
  · rw [hx]
    exact not_pow_1794

theorem nd_1791_1794 : ∀ x : Nat, 1790 < x → x < 1795 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1793 ∨ 1793 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1791_1792 x h1 hc
  · exact nd_1793_1794 x (by omega) h2

theorem nd_1795_1796 : ∀ x : Nat, 1794 < x → x < 1797 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1795 ∨ x = 1796 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1795
  · rw [hx]
    exact not_pow_1796

theorem nd_1797_1797 : ∀ x : Nat, 1796 < x → x < 1798 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1797 := by omega
  rw [hx]
  exact not_pow_1797

theorem nd_1798_1799 : ∀ x : Nat, 1797 < x → x < 1800 → ¬ Powerful x := by
  intro x h1 h2
  have hx : x = 1798 ∨ x = 1799 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_pow_1798
  · rw [hx]
    exact not_pow_1799

theorem nd_1797_1799 : ∀ x : Nat, 1796 < x → x < 1800 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1798 ∨ 1798 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1797_1797 x h1 hc
  · exact nd_1798_1799 x (by omega) h2

theorem nd_1795_1799 : ∀ x : Nat, 1794 < x → x < 1800 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1797 ∨ 1797 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1795_1796 x h1 hc
  · exact nd_1797_1799 x (by omega) h2

theorem nd_1791_1799 : ∀ x : Nat, 1790 < x → x < 1800 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1795 ∨ 1795 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1791_1794 x h1 hc
  · exact nd_1795_1799 x (by omega) h2

theorem nd_1782_1799 : ∀ x : Nat, 1781 < x → x < 1800 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1791 ∨ 1791 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1782_1790 x h1 hc
  · exact nd_1791_1799 x (by omega) h2

theorem nd_1765_1799 : ∀ x : Nat, 1764 < x → x < 1800 → ¬ Powerful x := by
  intro x h1 h2
  have hc : x < 1782 ∨ 1782 ≤ x := by omega
  rcases hc with hc | hc
  · exact nd_1765_1781 x h1 hc
  · exact nd_1782_1799 x (by omega) h2

/-- 左区间 (1728, 1764) 内无 powerful 数 -/
theorem npl_left : ∀ x : Nat, 1728 < x → x < 1764 → ¬ Powerful x := nd_1729_1763

/-- 右区间 (1764, 1800) 内无 powerful 数 -/
theorem npr_right : ∀ x : Nat, 1764 < x → x < 1800 → ¬ Powerful x := nd_1765_1799

-- ---------------------------------------------------------------------
-- 主定理（对题目陈述的直接回答：构造性下界，至少一次）
-- ---------------------------------------------------------------------

/-- 存在三个连续 powerful 数构成等差级数（1728, 1764, 1800） -/
theorem jsp_779 :
    ∃ a b c : Nat,
      a > 0 ∧ b > 0 ∧ c > 0 ∧ a < b ∧ b < c ∧ Powerful a ∧ Powerful b ∧ Powerful c ∧
      2 * b = a + c ∧
      (∀ x : Nat, a < x → x < b → ¬ Powerful x) ∧
      (∀ x : Nat, b < x → x < c → ¬ Powerful x) := by
  refine ⟨1728, 1764, 1800, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact powerful_1728
  · exact powerful_1764
  · exact powerful_1800
  · decide
  · exact npl_left
  · exact npr_right

-- =====================================================================
-- JSP-000705 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How long a run of pairwise distinct consecutive prime gaps can occur?
--       （连续互异的素数间隙 run 最长能有多长？）
-- 答案：至少 13（构造性下界）。构造：
--       素数 70657, 70663, 70667, 70687, 70709, 70717, 70729, 70753,
--             70769, 70783, 70793, 70823, 70841, 70843
--       相邻间隙为 6, 4, 20, 22, 8, 12, 24, 16, 14, 10, 30, 18, 2 —— 全部互异。
--       每个间隙内所有整数均为合数（故间隙确实是相邻素数之差）。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp705.lean
-- 全部计算性证明由 `decide` 在内核 VM 中完成（机器逐行核验）。
-- =====================================================================

set_option maxRecDepth 1000000

-- ---------------------------------------------------------------------
-- 定义
-- ---------------------------------------------------------------------

/-- 素数（Mathlib 的 Nat.Prime 等价定义，避免依赖 Mathlib） -/
def Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

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


/-- 70657 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70657 : Prime 70657 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70657 → m = 1 ∨ m = 70657) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70657 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70657 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70657 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70657 → k = 1 ∨ k = 70657) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70657 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70663 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70663 : Prime 70663 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70663 → m = 1 ∨ m = 70663) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70663 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70663 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70663 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70663 → k = 1 ∨ k = 70663) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70663 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70667 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70667 : Prime 70667 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70667 → m = 1 ∨ m = 70667) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70667 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70667 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70667 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70667 → k = 1 ∨ k = 70667) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70667 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70687 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70687 : Prime 70687 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70687 → m = 1 ∨ m = 70687) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70687 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70687 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70687 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70687 → k = 1 ∨ k = 70687) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70687 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70709 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70709 : Prime 70709 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70709 → m = 1 ∨ m = 70709) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70709 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70709 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70709 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70709 → k = 1 ∨ k = 70709) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70709 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70717 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70717 : Prime 70717 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70717 → m = 1 ∨ m = 70717) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70717 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70717 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70717 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70717 → k = 1 ∨ k = 70717) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70717 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70729 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70729 : Prime 70729 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70729 → m = 1 ∨ m = 70729) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70729 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70729 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70729 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70729 → k = 1 ∨ k = 70729) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70729 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70753 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70753 : Prime 70753 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70753 → m = 1 ∨ m = 70753) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70753 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70753 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70753 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70753 → k = 1 ∨ k = 70753) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70753 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70769 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70769 : Prime 70769 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70769 → m = 1 ∨ m = 70769) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70769 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70769 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70769 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70769 → k = 1 ∨ k = 70769) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70769 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70783 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70783 : Prime 70783 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70783 → m = 1 ∨ m = 70783) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70783 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70783 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70783 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70783 → k = 1 ∨ k = 70783) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70783 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70793 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70793 : Prime 70793 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70793 → m = 1 ∨ m = 70793) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70793 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70793 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70793 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70793 → k = 1 ∨ k = 70793) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70793 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70823 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70823 : Prime 70823 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70823 → m = 1 ∨ m = 70823) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70823 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70823 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70823 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70823 → k = 1 ∨ k = 70823) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70823 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70841 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70841 : Prime 70841 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70841 → m = 1 ∨ m = 70841) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70841 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70841 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70841 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70841 → k = 1 ∨ k = 70841) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70841 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70843 是素数（分段验证：小因子闭项 + 大因子商论证） -/
theorem prime_70843 : Prime 70843 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  by_cases hmB : m < 268
  · exact (by decide : ∀ m : Nat, m < 268 → m ∣ 70843 → m = 1 ∨ m = 70843) m hmB hm
  · have hge : 268 ≤ m := by omega
    rcases hm with ⟨k, hk⟩
    have hklt : k < 268 := by
      have hle : 268 * k ≤ m * k := Nat.mul_le_mul_right k hge
      have hb : 268 * k ≤ 70843 := by rw [hk]; exact hle
      omega
    have hkd : k ∣ 70843 := ⟨m, by rw [hk]; exact Nat.mul_comm m k⟩
    have hk1v : k = 1 ∨ k = 70843 := (by decide : ∀ k : Nat, k < 268 → k ∣ 70843 → k = 1 ∨ k = 70843) k hklt hkd
    rcases hk1v with hk1 | hkp
    · subst hk1
      have hmv : m = 70843 := by omega
      exact Or.inr hmv
    · exfalso
      omega

/-- 70658 是合数（见证因子 2） -/
theorem not_prime_70658 : ¬ Prime 70658 :=
  not_prime_of_dvd (by decide : 2 ∣ 70658) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70658)

/-- 70659 是合数（见证因子 3） -/
theorem not_prime_70659 : ¬ Prime 70659 :=
  not_prime_of_dvd (by decide : 3 ∣ 70659) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70659)

/-- 70660 是合数（见证因子 2） -/
theorem not_prime_70660 : ¬ Prime 70660 :=
  not_prime_of_dvd (by decide : 2 ∣ 70660) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70660)

/-- 70661 是合数（见证因子 19） -/
theorem not_prime_70661 : ¬ Prime 70661 :=
  not_prime_of_dvd (by decide : 19 ∣ 70661) (by decide : 19 ≠ 1) (by decide : 19 ≠ 70661)

/-- 70662 是合数（见证因子 2） -/
theorem not_prime_70662 : ¬ Prime 70662 :=
  not_prime_of_dvd (by decide : 2 ∣ 70662) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70662)

/-- 70664 是合数（见证因子 2） -/
theorem not_prime_70664 : ¬ Prime 70664 :=
  not_prime_of_dvd (by decide : 2 ∣ 70664) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70664)

/-- 70665 是合数（见证因子 3） -/
theorem not_prime_70665 : ¬ Prime 70665 :=
  not_prime_of_dvd (by decide : 3 ∣ 70665) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70665)

/-- 70666 是合数（见证因子 2） -/
theorem not_prime_70666 : ¬ Prime 70666 :=
  not_prime_of_dvd (by decide : 2 ∣ 70666) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70666)

/-- 70668 是合数（见证因子 2） -/
theorem not_prime_70668 : ¬ Prime 70668 :=
  not_prime_of_dvd (by decide : 2 ∣ 70668) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70668)

/-- 70669 是合数（见证因子 17） -/
theorem not_prime_70669 : ¬ Prime 70669 :=
  not_prime_of_dvd (by decide : 17 ∣ 70669) (by decide : 17 ≠ 1) (by decide : 17 ≠ 70669)

/-- 70670 是合数（见证因子 2） -/
theorem not_prime_70670 : ¬ Prime 70670 :=
  not_prime_of_dvd (by decide : 2 ∣ 70670) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70670)

/-- 70671 是合数（见证因子 3） -/
theorem not_prime_70671 : ¬ Prime 70671 :=
  not_prime_of_dvd (by decide : 3 ∣ 70671) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70671)

/-- 70672 是合数（见证因子 2） -/
theorem not_prime_70672 : ¬ Prime 70672 :=
  not_prime_of_dvd (by decide : 2 ∣ 70672) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70672)

/-- 70673 是合数（见证因子 29） -/
theorem not_prime_70673 : ¬ Prime 70673 :=
  not_prime_of_dvd (by decide : 29 ∣ 70673) (by decide : 29 ≠ 1) (by decide : 29 ≠ 70673)

/-- 70674 是合数（见证因子 2） -/
theorem not_prime_70674 : ¬ Prime 70674 :=
  not_prime_of_dvd (by decide : 2 ∣ 70674) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70674)

/-- 70675 是合数（见证因子 5） -/
theorem not_prime_70675 : ¬ Prime 70675 :=
  not_prime_of_dvd (by decide : 5 ∣ 70675) (by decide : 5 ≠ 1) (by decide : 5 ≠ 70675)

/-- 70676 是合数（见证因子 2） -/
theorem not_prime_70676 : ¬ Prime 70676 :=
  not_prime_of_dvd (by decide : 2 ∣ 70676) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70676)

/-- 70677 是合数（见证因子 3） -/
theorem not_prime_70677 : ¬ Prime 70677 :=
  not_prime_of_dvd (by decide : 3 ∣ 70677) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70677)

/-- 70678 是合数（见证因子 2） -/
theorem not_prime_70678 : ¬ Prime 70678 :=
  not_prime_of_dvd (by decide : 2 ∣ 70678) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70678)

/-- 70679 是合数（见证因子 7） -/
theorem not_prime_70679 : ¬ Prime 70679 :=
  not_prime_of_dvd (by decide : 7 ∣ 70679) (by decide : 7 ≠ 1) (by decide : 7 ≠ 70679)

/-- 70680 是合数（见证因子 2） -/
theorem not_prime_70680 : ¬ Prime 70680 :=
  not_prime_of_dvd (by decide : 2 ∣ 70680) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70680)

/-- 70681 是合数（见证因子 13） -/
theorem not_prime_70681 : ¬ Prime 70681 :=
  not_prime_of_dvd (by decide : 13 ∣ 70681) (by decide : 13 ≠ 1) (by decide : 13 ≠ 70681)

/-- 70682 是合数（见证因子 2） -/
theorem not_prime_70682 : ¬ Prime 70682 :=
  not_prime_of_dvd (by decide : 2 ∣ 70682) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70682)

/-- 70683 是合数（见证因子 3） -/
theorem not_prime_70683 : ¬ Prime 70683 :=
  not_prime_of_dvd (by decide : 3 ∣ 70683) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70683)

/-- 70684 是合数（见证因子 2） -/
theorem not_prime_70684 : ¬ Prime 70684 :=
  not_prime_of_dvd (by decide : 2 ∣ 70684) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70684)

/-- 70685 是合数（见证因子 5） -/
theorem not_prime_70685 : ¬ Prime 70685 :=
  not_prime_of_dvd (by decide : 5 ∣ 70685) (by decide : 5 ≠ 1) (by decide : 5 ≠ 70685)

/-- 70686 是合数（见证因子 2） -/
theorem not_prime_70686 : ¬ Prime 70686 :=
  not_prime_of_dvd (by decide : 2 ∣ 70686) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70686)

/-- 70688 是合数（见证因子 2） -/
theorem not_prime_70688 : ¬ Prime 70688 :=
  not_prime_of_dvd (by decide : 2 ∣ 70688) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70688)

/-- 70689 是合数（见证因子 3） -/
theorem not_prime_70689 : ¬ Prime 70689 :=
  not_prime_of_dvd (by decide : 3 ∣ 70689) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70689)

/-- 70690 是合数（见证因子 2） -/
theorem not_prime_70690 : ¬ Prime 70690 :=
  not_prime_of_dvd (by decide : 2 ∣ 70690) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70690)

/-- 70691 是合数（见证因子 223） -/
theorem not_prime_70691 : ¬ Prime 70691 :=
  not_prime_of_dvd (by decide : 223 ∣ 70691) (by decide : 223 ≠ 1) (by decide : 223 ≠ 70691)

/-- 70692 是合数（见证因子 2） -/
theorem not_prime_70692 : ¬ Prime 70692 :=
  not_prime_of_dvd (by decide : 2 ∣ 70692) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70692)

/-- 70693 是合数（见证因子 7） -/
theorem not_prime_70693 : ¬ Prime 70693 :=
  not_prime_of_dvd (by decide : 7 ∣ 70693) (by decide : 7 ≠ 1) (by decide : 7 ≠ 70693)

/-- 70694 是合数（见证因子 2） -/
theorem not_prime_70694 : ¬ Prime 70694 :=
  not_prime_of_dvd (by decide : 2 ∣ 70694) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70694)

/-- 70695 是合数（见证因子 3） -/
theorem not_prime_70695 : ¬ Prime 70695 :=
  not_prime_of_dvd (by decide : 3 ∣ 70695) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70695)

/-- 70696 是合数（见证因子 2） -/
theorem not_prime_70696 : ¬ Prime 70696 :=
  not_prime_of_dvd (by decide : 2 ∣ 70696) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70696)

/-- 70697 是合数（见证因子 11） -/
theorem not_prime_70697 : ¬ Prime 70697 :=
  not_prime_of_dvd (by decide : 11 ∣ 70697) (by decide : 11 ≠ 1) (by decide : 11 ≠ 70697)

/-- 70698 是合数（见证因子 2） -/
theorem not_prime_70698 : ¬ Prime 70698 :=
  not_prime_of_dvd (by decide : 2 ∣ 70698) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70698)

/-- 70699 是合数（见证因子 19） -/
theorem not_prime_70699 : ¬ Prime 70699 :=
  not_prime_of_dvd (by decide : 19 ∣ 70699) (by decide : 19 ≠ 1) (by decide : 19 ≠ 70699)

/-- 70700 是合数（见证因子 2） -/
theorem not_prime_70700 : ¬ Prime 70700 :=
  not_prime_of_dvd (by decide : 2 ∣ 70700) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70700)

/-- 70701 是合数（见证因子 3） -/
theorem not_prime_70701 : ¬ Prime 70701 :=
  not_prime_of_dvd (by decide : 3 ∣ 70701) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70701)

/-- 70702 是合数（见证因子 2） -/
theorem not_prime_70702 : ¬ Prime 70702 :=
  not_prime_of_dvd (by decide : 2 ∣ 70702) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70702)

/-- 70703 是合数（见证因子 17） -/
theorem not_prime_70703 : ¬ Prime 70703 :=
  not_prime_of_dvd (by decide : 17 ∣ 70703) (by decide : 17 ≠ 1) (by decide : 17 ≠ 70703)

/-- 70704 是合数（见证因子 2） -/
theorem not_prime_70704 : ¬ Prime 70704 :=
  not_prime_of_dvd (by decide : 2 ∣ 70704) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70704)

/-- 70705 是合数（见证因子 5） -/
theorem not_prime_70705 : ¬ Prime 70705 :=
  not_prime_of_dvd (by decide : 5 ∣ 70705) (by decide : 5 ≠ 1) (by decide : 5 ≠ 70705)

/-- 70706 是合数（见证因子 2） -/
theorem not_prime_70706 : ¬ Prime 70706 :=
  not_prime_of_dvd (by decide : 2 ∣ 70706) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70706)

/-- 70707 是合数（见证因子 3） -/
theorem not_prime_70707 : ¬ Prime 70707 :=
  not_prime_of_dvd (by decide : 3 ∣ 70707) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70707)

/-- 70708 是合数（见证因子 2） -/
theorem not_prime_70708 : ¬ Prime 70708 :=
  not_prime_of_dvd (by decide : 2 ∣ 70708) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70708)

/-- 70710 是合数（见证因子 2） -/
theorem not_prime_70710 : ¬ Prime 70710 :=
  not_prime_of_dvd (by decide : 2 ∣ 70710) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70710)

/-- 70711 是合数（见证因子 31） -/
theorem not_prime_70711 : ¬ Prime 70711 :=
  not_prime_of_dvd (by decide : 31 ∣ 70711) (by decide : 31 ≠ 1) (by decide : 31 ≠ 70711)

/-- 70712 是合数（见证因子 2） -/
theorem not_prime_70712 : ¬ Prime 70712 :=
  not_prime_of_dvd (by decide : 2 ∣ 70712) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70712)

/-- 70713 是合数（见证因子 3） -/
theorem not_prime_70713 : ¬ Prime 70713 :=
  not_prime_of_dvd (by decide : 3 ∣ 70713) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70713)

/-- 70714 是合数（见证因子 2） -/
theorem not_prime_70714 : ¬ Prime 70714 :=
  not_prime_of_dvd (by decide : 2 ∣ 70714) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70714)

/-- 70715 是合数（见证因子 5） -/
theorem not_prime_70715 : ¬ Prime 70715 :=
  not_prime_of_dvd (by decide : 5 ∣ 70715) (by decide : 5 ≠ 1) (by decide : 5 ≠ 70715)

/-- 70716 是合数（见证因子 2） -/
theorem not_prime_70716 : ¬ Prime 70716 :=
  not_prime_of_dvd (by decide : 2 ∣ 70716) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70716)

/-- 70718 是合数（见证因子 2） -/
theorem not_prime_70718 : ¬ Prime 70718 :=
  not_prime_of_dvd (by decide : 2 ∣ 70718) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70718)

/-- 70719 是合数（见证因子 3） -/
theorem not_prime_70719 : ¬ Prime 70719 :=
  not_prime_of_dvd (by decide : 3 ∣ 70719) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70719)

/-- 70720 是合数（见证因子 2） -/
theorem not_prime_70720 : ¬ Prime 70720 :=
  not_prime_of_dvd (by decide : 2 ∣ 70720) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70720)

/-- 70721 是合数（见证因子 7） -/
theorem not_prime_70721 : ¬ Prime 70721 :=
  not_prime_of_dvd (by decide : 7 ∣ 70721) (by decide : 7 ≠ 1) (by decide : 7 ≠ 70721)

/-- 70722 是合数（见证因子 2） -/
theorem not_prime_70722 : ¬ Prime 70722 :=
  not_prime_of_dvd (by decide : 2 ∣ 70722) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70722)

/-- 70723 是合数（见证因子 197） -/
theorem not_prime_70723 : ¬ Prime 70723 :=
  not_prime_of_dvd (by decide : 197 ∣ 70723) (by decide : 197 ≠ 1) (by decide : 197 ≠ 70723)

/-- 70724 是合数（见证因子 2） -/
theorem not_prime_70724 : ¬ Prime 70724 :=
  not_prime_of_dvd (by decide : 2 ∣ 70724) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70724)

/-- 70725 是合数（见证因子 3） -/
theorem not_prime_70725 : ¬ Prime 70725 :=
  not_prime_of_dvd (by decide : 3 ∣ 70725) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70725)

/-- 70726 是合数（见证因子 2） -/
theorem not_prime_70726 : ¬ Prime 70726 :=
  not_prime_of_dvd (by decide : 2 ∣ 70726) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70726)

/-- 70727 是合数（见证因子 107） -/
theorem not_prime_70727 : ¬ Prime 70727 :=
  not_prime_of_dvd (by decide : 107 ∣ 70727) (by decide : 107 ≠ 1) (by decide : 107 ≠ 70727)

/-- 70728 是合数（见证因子 2） -/
theorem not_prime_70728 : ¬ Prime 70728 :=
  not_prime_of_dvd (by decide : 2 ∣ 70728) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70728)

/-- 70730 是合数（见证因子 2） -/
theorem not_prime_70730 : ¬ Prime 70730 :=
  not_prime_of_dvd (by decide : 2 ∣ 70730) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70730)

/-- 70731 是合数（见证因子 3） -/
theorem not_prime_70731 : ¬ Prime 70731 :=
  not_prime_of_dvd (by decide : 3 ∣ 70731) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70731)

/-- 70732 是合数（见证因子 2） -/
theorem not_prime_70732 : ¬ Prime 70732 :=
  not_prime_of_dvd (by decide : 2 ∣ 70732) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70732)

/-- 70733 是合数（见证因子 13） -/
theorem not_prime_70733 : ¬ Prime 70733 :=
  not_prime_of_dvd (by decide : 13 ∣ 70733) (by decide : 13 ≠ 1) (by decide : 13 ≠ 70733)

/-- 70734 是合数（见证因子 2） -/
theorem not_prime_70734 : ¬ Prime 70734 :=
  not_prime_of_dvd (by decide : 2 ∣ 70734) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70734)

/-- 70735 是合数（见证因子 5） -/
theorem not_prime_70735 : ¬ Prime 70735 :=
  not_prime_of_dvd (by decide : 5 ∣ 70735) (by decide : 5 ≠ 1) (by decide : 5 ≠ 70735)

/-- 70736 是合数（见证因子 2） -/
theorem not_prime_70736 : ¬ Prime 70736 :=
  not_prime_of_dvd (by decide : 2 ∣ 70736) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70736)

/-- 70737 是合数（见证因子 3） -/
theorem not_prime_70737 : ¬ Prime 70737 :=
  not_prime_of_dvd (by decide : 3 ∣ 70737) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70737)

/-- 70738 是合数（见证因子 2） -/
theorem not_prime_70738 : ¬ Prime 70738 :=
  not_prime_of_dvd (by decide : 2 ∣ 70738) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70738)

/-- 70739 是合数（见证因子 127） -/
theorem not_prime_70739 : ¬ Prime 70739 :=
  not_prime_of_dvd (by decide : 127 ∣ 70739) (by decide : 127 ≠ 1) (by decide : 127 ≠ 70739)

/-- 70740 是合数（见证因子 2） -/
theorem not_prime_70740 : ¬ Prime 70740 :=
  not_prime_of_dvd (by decide : 2 ∣ 70740) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70740)

/-- 70741 是合数（见证因子 11） -/
theorem not_prime_70741 : ¬ Prime 70741 :=
  not_prime_of_dvd (by decide : 11 ∣ 70741) (by decide : 11 ≠ 1) (by decide : 11 ≠ 70741)

/-- 70742 是合数（见证因子 2） -/
theorem not_prime_70742 : ¬ Prime 70742 :=
  not_prime_of_dvd (by decide : 2 ∣ 70742) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70742)

/-- 70743 是合数（见证因子 3） -/
theorem not_prime_70743 : ¬ Prime 70743 :=
  not_prime_of_dvd (by decide : 3 ∣ 70743) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70743)

/-- 70744 是合数（见证因子 2） -/
theorem not_prime_70744 : ¬ Prime 70744 :=
  not_prime_of_dvd (by decide : 2 ∣ 70744) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70744)

/-- 70745 是合数（见证因子 5） -/
theorem not_prime_70745 : ¬ Prime 70745 :=
  not_prime_of_dvd (by decide : 5 ∣ 70745) (by decide : 5 ≠ 1) (by decide : 5 ≠ 70745)

/-- 70746 是合数（见证因子 2） -/
theorem not_prime_70746 : ¬ Prime 70746 :=
  not_prime_of_dvd (by decide : 2 ∣ 70746) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70746)

/-- 70747 是合数（见证因子 263） -/
theorem not_prime_70747 : ¬ Prime 70747 :=
  not_prime_of_dvd (by decide : 263 ∣ 70747) (by decide : 263 ≠ 1) (by decide : 263 ≠ 70747)

/-- 70748 是合数（见证因子 2） -/
theorem not_prime_70748 : ¬ Prime 70748 :=
  not_prime_of_dvd (by decide : 2 ∣ 70748) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70748)

/-- 70749 是合数（见证因子 3） -/
theorem not_prime_70749 : ¬ Prime 70749 :=
  not_prime_of_dvd (by decide : 3 ∣ 70749) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70749)

/-- 70750 是合数（见证因子 2） -/
theorem not_prime_70750 : ¬ Prime 70750 :=
  not_prime_of_dvd (by decide : 2 ∣ 70750) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70750)

/-- 70751 是合数（见证因子 139） -/
theorem not_prime_70751 : ¬ Prime 70751 :=
  not_prime_of_dvd (by decide : 139 ∣ 70751) (by decide : 139 ≠ 1) (by decide : 139 ≠ 70751)

/-- 70752 是合数（见证因子 2） -/
theorem not_prime_70752 : ¬ Prime 70752 :=
  not_prime_of_dvd (by decide : 2 ∣ 70752) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70752)

/-- 70754 是合数（见证因子 2） -/
theorem not_prime_70754 : ¬ Prime 70754 :=
  not_prime_of_dvd (by decide : 2 ∣ 70754) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70754)

/-- 70755 是合数（见证因子 3） -/
theorem not_prime_70755 : ¬ Prime 70755 :=
  not_prime_of_dvd (by decide : 3 ∣ 70755) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70755)

/-- 70756 是合数（见证因子 2） -/
theorem not_prime_70756 : ¬ Prime 70756 :=
  not_prime_of_dvd (by decide : 2 ∣ 70756) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70756)

/-- 70757 是合数（见证因子 173） -/
theorem not_prime_70757 : ¬ Prime 70757 :=
  not_prime_of_dvd (by decide : 173 ∣ 70757) (by decide : 173 ≠ 1) (by decide : 173 ≠ 70757)

/-- 70758 是合数（见证因子 2） -/
theorem not_prime_70758 : ¬ Prime 70758 :=
  not_prime_of_dvd (by decide : 2 ∣ 70758) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70758)

/-- 70759 是合数（见证因子 13） -/
theorem not_prime_70759 : ¬ Prime 70759 :=
  not_prime_of_dvd (by decide : 13 ∣ 70759) (by decide : 13 ≠ 1) (by decide : 13 ≠ 70759)

/-- 70760 是合数（见证因子 2） -/
theorem not_prime_70760 : ¬ Prime 70760 :=
  not_prime_of_dvd (by decide : 2 ∣ 70760) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70760)

/-- 70761 是合数（见证因子 3） -/
theorem not_prime_70761 : ¬ Prime 70761 :=
  not_prime_of_dvd (by decide : 3 ∣ 70761) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70761)

/-- 70762 是合数（见证因子 2） -/
theorem not_prime_70762 : ¬ Prime 70762 :=
  not_prime_of_dvd (by decide : 2 ∣ 70762) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70762)

/-- 70763 是合数（见证因子 7） -/
theorem not_prime_70763 : ¬ Prime 70763 :=
  not_prime_of_dvd (by decide : 7 ∣ 70763) (by decide : 7 ≠ 1) (by decide : 7 ≠ 70763)

/-- 70764 是合数（见证因子 2） -/
theorem not_prime_70764 : ¬ Prime 70764 :=
  not_prime_of_dvd (by decide : 2 ∣ 70764) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70764)

/-- 70765 是合数（见证因子 5） -/
theorem not_prime_70765 : ¬ Prime 70765 :=
  not_prime_of_dvd (by decide : 5 ∣ 70765) (by decide : 5 ≠ 1) (by decide : 5 ≠ 70765)

/-- 70766 是合数（见证因子 2） -/
theorem not_prime_70766 : ¬ Prime 70766 :=
  not_prime_of_dvd (by decide : 2 ∣ 70766) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70766)

/-- 70767 是合数（见证因子 3） -/
theorem not_prime_70767 : ¬ Prime 70767 :=
  not_prime_of_dvd (by decide : 3 ∣ 70767) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70767)

/-- 70768 是合数（见证因子 2） -/
theorem not_prime_70768 : ¬ Prime 70768 :=
  not_prime_of_dvd (by decide : 2 ∣ 70768) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70768)

/-- 70770 是合数（见证因子 2） -/
theorem not_prime_70770 : ¬ Prime 70770 :=
  not_prime_of_dvd (by decide : 2 ∣ 70770) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70770)

/-- 70771 是合数（见证因子 17） -/
theorem not_prime_70771 : ¬ Prime 70771 :=
  not_prime_of_dvd (by decide : 17 ∣ 70771) (by decide : 17 ≠ 1) (by decide : 17 ≠ 70771)

/-- 70772 是合数（见证因子 2） -/
theorem not_prime_70772 : ¬ Prime 70772 :=
  not_prime_of_dvd (by decide : 2 ∣ 70772) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70772)

/-- 70773 是合数（见证因子 3） -/
theorem not_prime_70773 : ¬ Prime 70773 :=
  not_prime_of_dvd (by decide : 3 ∣ 70773) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70773)

/-- 70774 是合数（见证因子 2） -/
theorem not_prime_70774 : ¬ Prime 70774 :=
  not_prime_of_dvd (by decide : 2 ∣ 70774) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70774)

/-- 70775 是合数（见证因子 5） -/
theorem not_prime_70775 : ¬ Prime 70775 :=
  not_prime_of_dvd (by decide : 5 ∣ 70775) (by decide : 5 ≠ 1) (by decide : 5 ≠ 70775)

/-- 70776 是合数（见证因子 2） -/
theorem not_prime_70776 : ¬ Prime 70776 :=
  not_prime_of_dvd (by decide : 2 ∣ 70776) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70776)

/-- 70777 是合数（见证因子 7） -/
theorem not_prime_70777 : ¬ Prime 70777 :=
  not_prime_of_dvd (by decide : 7 ∣ 70777) (by decide : 7 ≠ 1) (by decide : 7 ≠ 70777)

/-- 70778 是合数（见证因子 2） -/
theorem not_prime_70778 : ¬ Prime 70778 :=
  not_prime_of_dvd (by decide : 2 ∣ 70778) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70778)

/-- 70779 是合数（见证因子 3） -/
theorem not_prime_70779 : ¬ Prime 70779 :=
  not_prime_of_dvd (by decide : 3 ∣ 70779) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70779)

/-- 70780 是合数（见证因子 2） -/
theorem not_prime_70780 : ¬ Prime 70780 :=
  not_prime_of_dvd (by decide : 2 ∣ 70780) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70780)

/-- 70781 是合数（见证因子 37） -/
theorem not_prime_70781 : ¬ Prime 70781 :=
  not_prime_of_dvd (by decide : 37 ∣ 70781) (by decide : 37 ≠ 1) (by decide : 37 ≠ 70781)

/-- 70782 是合数（见证因子 2） -/
theorem not_prime_70782 : ¬ Prime 70782 :=
  not_prime_of_dvd (by decide : 2 ∣ 70782) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70782)

/-- 70784 是合数（见证因子 2） -/
theorem not_prime_70784 : ¬ Prime 70784 :=
  not_prime_of_dvd (by decide : 2 ∣ 70784) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70784)

/-- 70785 是合数（见证因子 3） -/
theorem not_prime_70785 : ¬ Prime 70785 :=
  not_prime_of_dvd (by decide : 3 ∣ 70785) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70785)

/-- 70786 是合数（见证因子 2） -/
theorem not_prime_70786 : ¬ Prime 70786 :=
  not_prime_of_dvd (by decide : 2 ∣ 70786) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70786)

/-- 70787 是合数（见证因子 71） -/
theorem not_prime_70787 : ¬ Prime 70787 :=
  not_prime_of_dvd (by decide : 71 ∣ 70787) (by decide : 71 ≠ 1) (by decide : 71 ≠ 70787)

/-- 70788 是合数（见证因子 2） -/
theorem not_prime_70788 : ¬ Prime 70788 :=
  not_prime_of_dvd (by decide : 2 ∣ 70788) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70788)

/-- 70789 是合数（见证因子 29） -/
theorem not_prime_70789 : ¬ Prime 70789 :=
  not_prime_of_dvd (by decide : 29 ∣ 70789) (by decide : 29 ≠ 1) (by decide : 29 ≠ 70789)

/-- 70790 是合数（见证因子 2） -/
theorem not_prime_70790 : ¬ Prime 70790 :=
  not_prime_of_dvd (by decide : 2 ∣ 70790) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70790)

/-- 70791 是合数（见证因子 3） -/
theorem not_prime_70791 : ¬ Prime 70791 :=
  not_prime_of_dvd (by decide : 3 ∣ 70791) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70791)

/-- 70792 是合数（见证因子 2） -/
theorem not_prime_70792 : ¬ Prime 70792 :=
  not_prime_of_dvd (by decide : 2 ∣ 70792) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70792)

/-- 70794 是合数（见证因子 2） -/
theorem not_prime_70794 : ¬ Prime 70794 :=
  not_prime_of_dvd (by decide : 2 ∣ 70794) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70794)

/-- 70795 是合数（见证因子 5） -/
theorem not_prime_70795 : ¬ Prime 70795 :=
  not_prime_of_dvd (by decide : 5 ∣ 70795) (by decide : 5 ≠ 1) (by decide : 5 ≠ 70795)

/-- 70796 是合数（见证因子 2） -/
theorem not_prime_70796 : ¬ Prime 70796 :=
  not_prime_of_dvd (by decide : 2 ∣ 70796) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70796)

/-- 70797 是合数（见证因子 3） -/
theorem not_prime_70797 : ¬ Prime 70797 :=
  not_prime_of_dvd (by decide : 3 ∣ 70797) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70797)

/-- 70798 是合数（见证因子 2） -/
theorem not_prime_70798 : ¬ Prime 70798 :=
  not_prime_of_dvd (by decide : 2 ∣ 70798) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70798)

/-- 70799 是合数（见证因子 83） -/
theorem not_prime_70799 : ¬ Prime 70799 :=
  not_prime_of_dvd (by decide : 83 ∣ 70799) (by decide : 83 ≠ 1) (by decide : 83 ≠ 70799)

/-- 70800 是合数（见证因子 2） -/
theorem not_prime_70800 : ¬ Prime 70800 :=
  not_prime_of_dvd (by decide : 2 ∣ 70800) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70800)

/-- 70801 是合数（见证因子 101） -/
theorem not_prime_70801 : ¬ Prime 70801 :=
  not_prime_of_dvd (by decide : 101 ∣ 70801) (by decide : 101 ≠ 1) (by decide : 101 ≠ 70801)

/-- 70802 是合数（见证因子 2） -/
theorem not_prime_70802 : ¬ Prime 70802 :=
  not_prime_of_dvd (by decide : 2 ∣ 70802) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70802)

/-- 70803 是合数（见证因子 3） -/
theorem not_prime_70803 : ¬ Prime 70803 :=
  not_prime_of_dvd (by decide : 3 ∣ 70803) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70803)

/-- 70804 是合数（见证因子 2） -/
theorem not_prime_70804 : ¬ Prime 70804 :=
  not_prime_of_dvd (by decide : 2 ∣ 70804) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70804)

/-- 70805 是合数（见证因子 5） -/
theorem not_prime_70805 : ¬ Prime 70805 :=
  not_prime_of_dvd (by decide : 5 ∣ 70805) (by decide : 5 ≠ 1) (by decide : 5 ≠ 70805)

/-- 70806 是合数（见证因子 2） -/
theorem not_prime_70806 : ¬ Prime 70806 :=
  not_prime_of_dvd (by decide : 2 ∣ 70806) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70806)

/-- 70807 是合数（见证因子 11） -/
theorem not_prime_70807 : ¬ Prime 70807 :=
  not_prime_of_dvd (by decide : 11 ∣ 70807) (by decide : 11 ≠ 1) (by decide : 11 ≠ 70807)

/-- 70808 是合数（见证因子 2） -/
theorem not_prime_70808 : ¬ Prime 70808 :=
  not_prime_of_dvd (by decide : 2 ∣ 70808) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70808)

/-- 70809 是合数（见证因子 3） -/
theorem not_prime_70809 : ¬ Prime 70809 :=
  not_prime_of_dvd (by decide : 3 ∣ 70809) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70809)

/-- 70810 是合数（见证因子 2） -/
theorem not_prime_70810 : ¬ Prime 70810 :=
  not_prime_of_dvd (by decide : 2 ∣ 70810) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70810)

/-- 70811 是合数（见证因子 13） -/
theorem not_prime_70811 : ¬ Prime 70811 :=
  not_prime_of_dvd (by decide : 13 ∣ 70811) (by decide : 13 ≠ 1) (by decide : 13 ≠ 70811)

/-- 70812 是合数（见证因子 2） -/
theorem not_prime_70812 : ¬ Prime 70812 :=
  not_prime_of_dvd (by decide : 2 ∣ 70812) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70812)

/-- 70813 是合数（见证因子 19） -/
theorem not_prime_70813 : ¬ Prime 70813 :=
  not_prime_of_dvd (by decide : 19 ∣ 70813) (by decide : 19 ≠ 1) (by decide : 19 ≠ 70813)

/-- 70814 是合数（见证因子 2） -/
theorem not_prime_70814 : ¬ Prime 70814 :=
  not_prime_of_dvd (by decide : 2 ∣ 70814) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70814)

/-- 70815 是合数（见证因子 3） -/
theorem not_prime_70815 : ¬ Prime 70815 :=
  not_prime_of_dvd (by decide : 3 ∣ 70815) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70815)

/-- 70816 是合数（见证因子 2） -/
theorem not_prime_70816 : ¬ Prime 70816 :=
  not_prime_of_dvd (by decide : 2 ∣ 70816) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70816)

/-- 70817 是合数（见证因子 23） -/
theorem not_prime_70817 : ¬ Prime 70817 :=
  not_prime_of_dvd (by decide : 23 ∣ 70817) (by decide : 23 ≠ 1) (by decide : 23 ≠ 70817)

/-- 70818 是合数（见证因子 2） -/
theorem not_prime_70818 : ¬ Prime 70818 :=
  not_prime_of_dvd (by decide : 2 ∣ 70818) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70818)

/-- 70819 是合数（见证因子 7） -/
theorem not_prime_70819 : ¬ Prime 70819 :=
  not_prime_of_dvd (by decide : 7 ∣ 70819) (by decide : 7 ≠ 1) (by decide : 7 ≠ 70819)

/-- 70820 是合数（见证因子 2） -/
theorem not_prime_70820 : ¬ Prime 70820 :=
  not_prime_of_dvd (by decide : 2 ∣ 70820) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70820)

/-- 70821 是合数（见证因子 3） -/
theorem not_prime_70821 : ¬ Prime 70821 :=
  not_prime_of_dvd (by decide : 3 ∣ 70821) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70821)

/-- 70822 是合数（见证因子 2） -/
theorem not_prime_70822 : ¬ Prime 70822 :=
  not_prime_of_dvd (by decide : 2 ∣ 70822) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70822)

/-- 70824 是合数（见证因子 2） -/
theorem not_prime_70824 : ¬ Prime 70824 :=
  not_prime_of_dvd (by decide : 2 ∣ 70824) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70824)

/-- 70825 是合数（见证因子 5） -/
theorem not_prime_70825 : ¬ Prime 70825 :=
  not_prime_of_dvd (by decide : 5 ∣ 70825) (by decide : 5 ≠ 1) (by decide : 5 ≠ 70825)

/-- 70826 是合数（见证因子 2） -/
theorem not_prime_70826 : ¬ Prime 70826 :=
  not_prime_of_dvd (by decide : 2 ∣ 70826) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70826)

/-- 70827 是合数（见证因子 3） -/
theorem not_prime_70827 : ¬ Prime 70827 :=
  not_prime_of_dvd (by decide : 3 ∣ 70827) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70827)

/-- 70828 是合数（见证因子 2） -/
theorem not_prime_70828 : ¬ Prime 70828 :=
  not_prime_of_dvd (by decide : 2 ∣ 70828) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70828)

/-- 70829 是合数（见证因子 11） -/
theorem not_prime_70829 : ¬ Prime 70829 :=
  not_prime_of_dvd (by decide : 11 ∣ 70829) (by decide : 11 ≠ 1) (by decide : 11 ≠ 70829)

/-- 70830 是合数（见证因子 2） -/
theorem not_prime_70830 : ¬ Prime 70830 :=
  not_prime_of_dvd (by decide : 2 ∣ 70830) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70830)

/-- 70831 是合数（见证因子 193） -/
theorem not_prime_70831 : ¬ Prime 70831 :=
  not_prime_of_dvd (by decide : 193 ∣ 70831) (by decide : 193 ≠ 1) (by decide : 193 ≠ 70831)

/-- 70832 是合数（见证因子 2） -/
theorem not_prime_70832 : ¬ Prime 70832 :=
  not_prime_of_dvd (by decide : 2 ∣ 70832) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70832)

/-- 70833 是合数（见证因子 3） -/
theorem not_prime_70833 : ¬ Prime 70833 :=
  not_prime_of_dvd (by decide : 3 ∣ 70833) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70833)

/-- 70834 是合数（见证因子 2） -/
theorem not_prime_70834 : ¬ Prime 70834 :=
  not_prime_of_dvd (by decide : 2 ∣ 70834) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70834)

/-- 70835 是合数（见证因子 5） -/
theorem not_prime_70835 : ¬ Prime 70835 :=
  not_prime_of_dvd (by decide : 5 ∣ 70835) (by decide : 5 ≠ 1) (by decide : 5 ≠ 70835)

/-- 70836 是合数（见证因子 2） -/
theorem not_prime_70836 : ¬ Prime 70836 :=
  not_prime_of_dvd (by decide : 2 ∣ 70836) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70836)

/-- 70837 是合数（见证因子 13） -/
theorem not_prime_70837 : ¬ Prime 70837 :=
  not_prime_of_dvd (by decide : 13 ∣ 70837) (by decide : 13 ≠ 1) (by decide : 13 ≠ 70837)

/-- 70838 是合数（见证因子 2） -/
theorem not_prime_70838 : ¬ Prime 70838 :=
  not_prime_of_dvd (by decide : 2 ∣ 70838) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70838)

/-- 70839 是合数（见证因子 3） -/
theorem not_prime_70839 : ¬ Prime 70839 :=
  not_prime_of_dvd (by decide : 3 ∣ 70839) (by decide : 3 ≠ 1) (by decide : 3 ≠ 70839)

/-- 70840 是合数（见证因子 2） -/
theorem not_prime_70840 : ¬ Prime 70840 :=
  not_prime_of_dvd (by decide : 2 ∣ 70840) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70840)

/-- 70842 是合数（见证因子 2） -/
theorem not_prime_70842 : ¬ Prime 70842 :=
  not_prime_of_dvd (by decide : 2 ∣ 70842) (by decide : 2 ≠ 1) (by decide : 2 ≠ 70842)

theorem adj_70658_70659 : ∀ x : Nat, 70657 < x → x < 70660 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70658 ∨ x = 70659 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70658
  · rw [hx]
    exact not_prime_70659

theorem adj_70660_70660 : ∀ x : Nat, 70659 < x → x < 70661 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70660 := by omega
  rw [hx]
  exact not_prime_70660

theorem adj_70661_70662 : ∀ x : Nat, 70660 < x → x < 70663 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70661 ∨ x = 70662 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70661
  · rw [hx]
    exact not_prime_70662

theorem adj_70660_70662 : ∀ x : Nat, 70659 < x → x < 70663 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70661 ∨ 70661 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70660_70660 x h1 hc
  · exact adj_70661_70662 x (by omega) h2

theorem adj_70658_70662 : ∀ x : Nat, 70657 < x → x < 70663 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70660 ∨ 70660 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70658_70659 x h1 hc
  · exact adj_70660_70662 x (by omega) h2

theorem adj_70664_70664 : ∀ x : Nat, 70663 < x → x < 70665 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70664 := by omega
  rw [hx]
  exact not_prime_70664

theorem adj_70665_70666 : ∀ x : Nat, 70664 < x → x < 70667 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70665 ∨ x = 70666 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70665
  · rw [hx]
    exact not_prime_70666

theorem adj_70664_70666 : ∀ x : Nat, 70663 < x → x < 70667 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70665 ∨ 70665 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70664_70664 x h1 hc
  · exact adj_70665_70666 x (by omega) h2

theorem adj_70668_70669 : ∀ x : Nat, 70667 < x → x < 70670 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70668 ∨ x = 70669 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70668
  · rw [hx]
    exact not_prime_70669

theorem adj_70670_70671 : ∀ x : Nat, 70669 < x → x < 70672 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70670 ∨ x = 70671 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70670
  · rw [hx]
    exact not_prime_70671

theorem adj_70668_70671 : ∀ x : Nat, 70667 < x → x < 70672 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70670 ∨ 70670 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70668_70669 x h1 hc
  · exact adj_70670_70671 x (by omega) h2

theorem adj_70672_70673 : ∀ x : Nat, 70671 < x → x < 70674 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70672 ∨ x = 70673 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70672
  · rw [hx]
    exact not_prime_70673

theorem adj_70674_70674 : ∀ x : Nat, 70673 < x → x < 70675 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70674 := by omega
  rw [hx]
  exact not_prime_70674

theorem adj_70675_70676 : ∀ x : Nat, 70674 < x → x < 70677 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70675 ∨ x = 70676 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70675
  · rw [hx]
    exact not_prime_70676

theorem adj_70674_70676 : ∀ x : Nat, 70673 < x → x < 70677 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70675 ∨ 70675 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70674_70674 x h1 hc
  · exact adj_70675_70676 x (by omega) h2

theorem adj_70672_70676 : ∀ x : Nat, 70671 < x → x < 70677 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70674 ∨ 70674 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70672_70673 x h1 hc
  · exact adj_70674_70676 x (by omega) h2

theorem adj_70668_70676 : ∀ x : Nat, 70667 < x → x < 70677 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70672 ∨ 70672 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70668_70671 x h1 hc
  · exact adj_70672_70676 x (by omega) h2

theorem adj_70677_70678 : ∀ x : Nat, 70676 < x → x < 70679 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70677 ∨ x = 70678 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70677
  · rw [hx]
    exact not_prime_70678

theorem adj_70679_70679 : ∀ x : Nat, 70678 < x → x < 70680 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70679 := by omega
  rw [hx]
  exact not_prime_70679

theorem adj_70680_70681 : ∀ x : Nat, 70679 < x → x < 70682 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70680 ∨ x = 70681 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70680
  · rw [hx]
    exact not_prime_70681

theorem adj_70679_70681 : ∀ x : Nat, 70678 < x → x < 70682 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70680 ∨ 70680 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70679_70679 x h1 hc
  · exact adj_70680_70681 x (by omega) h2

theorem adj_70677_70681 : ∀ x : Nat, 70676 < x → x < 70682 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70679 ∨ 70679 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70677_70678 x h1 hc
  · exact adj_70679_70681 x (by omega) h2

theorem adj_70682_70683 : ∀ x : Nat, 70681 < x → x < 70684 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70682 ∨ x = 70683 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70682
  · rw [hx]
    exact not_prime_70683

theorem adj_70684_70684 : ∀ x : Nat, 70683 < x → x < 70685 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70684 := by omega
  rw [hx]
  exact not_prime_70684

theorem adj_70685_70686 : ∀ x : Nat, 70684 < x → x < 70687 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70685 ∨ x = 70686 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70685
  · rw [hx]
    exact not_prime_70686

theorem adj_70684_70686 : ∀ x : Nat, 70683 < x → x < 70687 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70685 ∨ 70685 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70684_70684 x h1 hc
  · exact adj_70685_70686 x (by omega) h2

theorem adj_70682_70686 : ∀ x : Nat, 70681 < x → x < 70687 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70684 ∨ 70684 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70682_70683 x h1 hc
  · exact adj_70684_70686 x (by omega) h2

theorem adj_70677_70686 : ∀ x : Nat, 70676 < x → x < 70687 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70682 ∨ 70682 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70677_70681 x h1 hc
  · exact adj_70682_70686 x (by omega) h2

theorem adj_70668_70686 : ∀ x : Nat, 70667 < x → x < 70687 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70677 ∨ 70677 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70668_70676 x h1 hc
  · exact adj_70677_70686 x (by omega) h2

theorem adj_70688_70689 : ∀ x : Nat, 70687 < x → x < 70690 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70688 ∨ x = 70689 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70688
  · rw [hx]
    exact not_prime_70689

theorem adj_70690_70690 : ∀ x : Nat, 70689 < x → x < 70691 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70690 := by omega
  rw [hx]
  exact not_prime_70690

theorem adj_70691_70692 : ∀ x : Nat, 70690 < x → x < 70693 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70691 ∨ x = 70692 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70691
  · rw [hx]
    exact not_prime_70692

theorem adj_70690_70692 : ∀ x : Nat, 70689 < x → x < 70693 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70691 ∨ 70691 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70690_70690 x h1 hc
  · exact adj_70691_70692 x (by omega) h2

theorem adj_70688_70692 : ∀ x : Nat, 70687 < x → x < 70693 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70690 ∨ 70690 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70688_70689 x h1 hc
  · exact adj_70690_70692 x (by omega) h2

theorem adj_70693_70694 : ∀ x : Nat, 70692 < x → x < 70695 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70693 ∨ x = 70694 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70693
  · rw [hx]
    exact not_prime_70694

theorem adj_70695_70695 : ∀ x : Nat, 70694 < x → x < 70696 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70695 := by omega
  rw [hx]
  exact not_prime_70695

theorem adj_70696_70697 : ∀ x : Nat, 70695 < x → x < 70698 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70696 ∨ x = 70697 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70696
  · rw [hx]
    exact not_prime_70697

theorem adj_70695_70697 : ∀ x : Nat, 70694 < x → x < 70698 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70696 ∨ 70696 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70695_70695 x h1 hc
  · exact adj_70696_70697 x (by omega) h2

theorem adj_70693_70697 : ∀ x : Nat, 70692 < x → x < 70698 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70695 ∨ 70695 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70693_70694 x h1 hc
  · exact adj_70695_70697 x (by omega) h2

theorem adj_70688_70697 : ∀ x : Nat, 70687 < x → x < 70698 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70693 ∨ 70693 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70688_70692 x h1 hc
  · exact adj_70693_70697 x (by omega) h2

theorem adj_70698_70699 : ∀ x : Nat, 70697 < x → x < 70700 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70698 ∨ x = 70699 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70698
  · rw [hx]
    exact not_prime_70699

theorem adj_70700_70700 : ∀ x : Nat, 70699 < x → x < 70701 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70700 := by omega
  rw [hx]
  exact not_prime_70700

theorem adj_70701_70702 : ∀ x : Nat, 70700 < x → x < 70703 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70701 ∨ x = 70702 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70701
  · rw [hx]
    exact not_prime_70702

theorem adj_70700_70702 : ∀ x : Nat, 70699 < x → x < 70703 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70701 ∨ 70701 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70700_70700 x h1 hc
  · exact adj_70701_70702 x (by omega) h2

theorem adj_70698_70702 : ∀ x : Nat, 70697 < x → x < 70703 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70700 ∨ 70700 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70698_70699 x h1 hc
  · exact adj_70700_70702 x (by omega) h2

theorem adj_70703_70703 : ∀ x : Nat, 70702 < x → x < 70704 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70703 := by omega
  rw [hx]
  exact not_prime_70703

theorem adj_70704_70705 : ∀ x : Nat, 70703 < x → x < 70706 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70704 ∨ x = 70705 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70704
  · rw [hx]
    exact not_prime_70705

theorem adj_70703_70705 : ∀ x : Nat, 70702 < x → x < 70706 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70704 ∨ 70704 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70703_70703 x h1 hc
  · exact adj_70704_70705 x (by omega) h2

theorem adj_70706_70706 : ∀ x : Nat, 70705 < x → x < 70707 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70706 := by omega
  rw [hx]
  exact not_prime_70706

theorem adj_70707_70708 : ∀ x : Nat, 70706 < x → x < 70709 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70707 ∨ x = 70708 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70707
  · rw [hx]
    exact not_prime_70708

theorem adj_70706_70708 : ∀ x : Nat, 70705 < x → x < 70709 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70707 ∨ 70707 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70706_70706 x h1 hc
  · exact adj_70707_70708 x (by omega) h2

theorem adj_70703_70708 : ∀ x : Nat, 70702 < x → x < 70709 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70706 ∨ 70706 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70703_70705 x h1 hc
  · exact adj_70706_70708 x (by omega) h2

theorem adj_70698_70708 : ∀ x : Nat, 70697 < x → x < 70709 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70703 ∨ 70703 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70698_70702 x h1 hc
  · exact adj_70703_70708 x (by omega) h2

theorem adj_70688_70708 : ∀ x : Nat, 70687 < x → x < 70709 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70698 ∨ 70698 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70688_70697 x h1 hc
  · exact adj_70698_70708 x (by omega) h2

theorem adj_70710_70710 : ∀ x : Nat, 70709 < x → x < 70711 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70710 := by omega
  rw [hx]
  exact not_prime_70710

theorem adj_70711_70712 : ∀ x : Nat, 70710 < x → x < 70713 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70711 ∨ x = 70712 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70711
  · rw [hx]
    exact not_prime_70712

theorem adj_70710_70712 : ∀ x : Nat, 70709 < x → x < 70713 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70711 ∨ 70711 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70710_70710 x h1 hc
  · exact adj_70711_70712 x (by omega) h2

theorem adj_70713_70714 : ∀ x : Nat, 70712 < x → x < 70715 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70713 ∨ x = 70714 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70713
  · rw [hx]
    exact not_prime_70714

theorem adj_70715_70716 : ∀ x : Nat, 70714 < x → x < 70717 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70715 ∨ x = 70716 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70715
  · rw [hx]
    exact not_prime_70716

theorem adj_70713_70716 : ∀ x : Nat, 70712 < x → x < 70717 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70715 ∨ 70715 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70713_70714 x h1 hc
  · exact adj_70715_70716 x (by omega) h2

theorem adj_70710_70716 : ∀ x : Nat, 70709 < x → x < 70717 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70713 ∨ 70713 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70710_70712 x h1 hc
  · exact adj_70713_70716 x (by omega) h2

theorem adj_70718_70719 : ∀ x : Nat, 70717 < x → x < 70720 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70718 ∨ x = 70719 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70718
  · rw [hx]
    exact not_prime_70719

theorem adj_70720_70720 : ∀ x : Nat, 70719 < x → x < 70721 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70720 := by omega
  rw [hx]
  exact not_prime_70720

theorem adj_70721_70722 : ∀ x : Nat, 70720 < x → x < 70723 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70721 ∨ x = 70722 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70721
  · rw [hx]
    exact not_prime_70722

theorem adj_70720_70722 : ∀ x : Nat, 70719 < x → x < 70723 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70721 ∨ 70721 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70720_70720 x h1 hc
  · exact adj_70721_70722 x (by omega) h2

theorem adj_70718_70722 : ∀ x : Nat, 70717 < x → x < 70723 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70720 ∨ 70720 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70718_70719 x h1 hc
  · exact adj_70720_70722 x (by omega) h2

theorem adj_70723_70723 : ∀ x : Nat, 70722 < x → x < 70724 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70723 := by omega
  rw [hx]
  exact not_prime_70723

theorem adj_70724_70725 : ∀ x : Nat, 70723 < x → x < 70726 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70724 ∨ x = 70725 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70724
  · rw [hx]
    exact not_prime_70725

theorem adj_70723_70725 : ∀ x : Nat, 70722 < x → x < 70726 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70724 ∨ 70724 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70723_70723 x h1 hc
  · exact adj_70724_70725 x (by omega) h2

theorem adj_70726_70726 : ∀ x : Nat, 70725 < x → x < 70727 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70726 := by omega
  rw [hx]
  exact not_prime_70726

theorem adj_70727_70728 : ∀ x : Nat, 70726 < x → x < 70729 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70727 ∨ x = 70728 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70727
  · rw [hx]
    exact not_prime_70728

theorem adj_70726_70728 : ∀ x : Nat, 70725 < x → x < 70729 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70727 ∨ 70727 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70726_70726 x h1 hc
  · exact adj_70727_70728 x (by omega) h2

theorem adj_70723_70728 : ∀ x : Nat, 70722 < x → x < 70729 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70726 ∨ 70726 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70723_70725 x h1 hc
  · exact adj_70726_70728 x (by omega) h2

theorem adj_70718_70728 : ∀ x : Nat, 70717 < x → x < 70729 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70723 ∨ 70723 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70718_70722 x h1 hc
  · exact adj_70723_70728 x (by omega) h2

theorem adj_70730_70731 : ∀ x : Nat, 70729 < x → x < 70732 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70730 ∨ x = 70731 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70730
  · rw [hx]
    exact not_prime_70731

theorem adj_70732_70732 : ∀ x : Nat, 70731 < x → x < 70733 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70732 := by omega
  rw [hx]
  exact not_prime_70732

theorem adj_70733_70734 : ∀ x : Nat, 70732 < x → x < 70735 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70733 ∨ x = 70734 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70733
  · rw [hx]
    exact not_prime_70734

theorem adj_70732_70734 : ∀ x : Nat, 70731 < x → x < 70735 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70733 ∨ 70733 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70732_70732 x h1 hc
  · exact adj_70733_70734 x (by omega) h2

theorem adj_70730_70734 : ∀ x : Nat, 70729 < x → x < 70735 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70732 ∨ 70732 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70730_70731 x h1 hc
  · exact adj_70732_70734 x (by omega) h2

theorem adj_70735_70735 : ∀ x : Nat, 70734 < x → x < 70736 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70735 := by omega
  rw [hx]
  exact not_prime_70735

theorem adj_70736_70737 : ∀ x : Nat, 70735 < x → x < 70738 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70736 ∨ x = 70737 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70736
  · rw [hx]
    exact not_prime_70737

theorem adj_70735_70737 : ∀ x : Nat, 70734 < x → x < 70738 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70736 ∨ 70736 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70735_70735 x h1 hc
  · exact adj_70736_70737 x (by omega) h2

theorem adj_70738_70738 : ∀ x : Nat, 70737 < x → x < 70739 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70738 := by omega
  rw [hx]
  exact not_prime_70738

theorem adj_70739_70740 : ∀ x : Nat, 70738 < x → x < 70741 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70739 ∨ x = 70740 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70739
  · rw [hx]
    exact not_prime_70740

theorem adj_70738_70740 : ∀ x : Nat, 70737 < x → x < 70741 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70739 ∨ 70739 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70738_70738 x h1 hc
  · exact adj_70739_70740 x (by omega) h2

theorem adj_70735_70740 : ∀ x : Nat, 70734 < x → x < 70741 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70738 ∨ 70738 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70735_70737 x h1 hc
  · exact adj_70738_70740 x (by omega) h2

theorem adj_70730_70740 : ∀ x : Nat, 70729 < x → x < 70741 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70735 ∨ 70735 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70730_70734 x h1 hc
  · exact adj_70735_70740 x (by omega) h2

theorem adj_70741_70741 : ∀ x : Nat, 70740 < x → x < 70742 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70741 := by omega
  rw [hx]
  exact not_prime_70741

theorem adj_70742_70743 : ∀ x : Nat, 70741 < x → x < 70744 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70742 ∨ x = 70743 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70742
  · rw [hx]
    exact not_prime_70743

theorem adj_70741_70743 : ∀ x : Nat, 70740 < x → x < 70744 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70742 ∨ 70742 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70741_70741 x h1 hc
  · exact adj_70742_70743 x (by omega) h2

theorem adj_70744_70744 : ∀ x : Nat, 70743 < x → x < 70745 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70744 := by omega
  rw [hx]
  exact not_prime_70744

theorem adj_70745_70746 : ∀ x : Nat, 70744 < x → x < 70747 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70745 ∨ x = 70746 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70745
  · rw [hx]
    exact not_prime_70746

theorem adj_70744_70746 : ∀ x : Nat, 70743 < x → x < 70747 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70745 ∨ 70745 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70744_70744 x h1 hc
  · exact adj_70745_70746 x (by omega) h2

theorem adj_70741_70746 : ∀ x : Nat, 70740 < x → x < 70747 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70744 ∨ 70744 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70741_70743 x h1 hc
  · exact adj_70744_70746 x (by omega) h2

theorem adj_70747_70747 : ∀ x : Nat, 70746 < x → x < 70748 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70747 := by omega
  rw [hx]
  exact not_prime_70747

theorem adj_70748_70749 : ∀ x : Nat, 70747 < x → x < 70750 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70748 ∨ x = 70749 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70748
  · rw [hx]
    exact not_prime_70749

theorem adj_70747_70749 : ∀ x : Nat, 70746 < x → x < 70750 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70748 ∨ 70748 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70747_70747 x h1 hc
  · exact adj_70748_70749 x (by omega) h2

theorem adj_70750_70750 : ∀ x : Nat, 70749 < x → x < 70751 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70750 := by omega
  rw [hx]
  exact not_prime_70750

theorem adj_70751_70752 : ∀ x : Nat, 70750 < x → x < 70753 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70751 ∨ x = 70752 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70751
  · rw [hx]
    exact not_prime_70752

theorem adj_70750_70752 : ∀ x : Nat, 70749 < x → x < 70753 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70751 ∨ 70751 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70750_70750 x h1 hc
  · exact adj_70751_70752 x (by omega) h2

theorem adj_70747_70752 : ∀ x : Nat, 70746 < x → x < 70753 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70750 ∨ 70750 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70747_70749 x h1 hc
  · exact adj_70750_70752 x (by omega) h2

theorem adj_70741_70752 : ∀ x : Nat, 70740 < x → x < 70753 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70747 ∨ 70747 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70741_70746 x h1 hc
  · exact adj_70747_70752 x (by omega) h2

theorem adj_70730_70752 : ∀ x : Nat, 70729 < x → x < 70753 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70741 ∨ 70741 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70730_70740 x h1 hc
  · exact adj_70741_70752 x (by omega) h2

theorem adj_70754_70754 : ∀ x : Nat, 70753 < x → x < 70755 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70754 := by omega
  rw [hx]
  exact not_prime_70754

theorem adj_70755_70756 : ∀ x : Nat, 70754 < x → x < 70757 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70755 ∨ x = 70756 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70755
  · rw [hx]
    exact not_prime_70756

theorem adj_70754_70756 : ∀ x : Nat, 70753 < x → x < 70757 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70755 ∨ 70755 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70754_70754 x h1 hc
  · exact adj_70755_70756 x (by omega) h2

theorem adj_70757_70758 : ∀ x : Nat, 70756 < x → x < 70759 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70757 ∨ x = 70758 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70757
  · rw [hx]
    exact not_prime_70758

theorem adj_70759_70760 : ∀ x : Nat, 70758 < x → x < 70761 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70759 ∨ x = 70760 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70759
  · rw [hx]
    exact not_prime_70760

theorem adj_70757_70760 : ∀ x : Nat, 70756 < x → x < 70761 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70759 ∨ 70759 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70757_70758 x h1 hc
  · exact adj_70759_70760 x (by omega) h2

theorem adj_70754_70760 : ∀ x : Nat, 70753 < x → x < 70761 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70757 ∨ 70757 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70754_70756 x h1 hc
  · exact adj_70757_70760 x (by omega) h2

theorem adj_70761_70762 : ∀ x : Nat, 70760 < x → x < 70763 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70761 ∨ x = 70762 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70761
  · rw [hx]
    exact not_prime_70762

theorem adj_70763_70764 : ∀ x : Nat, 70762 < x → x < 70765 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70763 ∨ x = 70764 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70763
  · rw [hx]
    exact not_prime_70764

theorem adj_70761_70764 : ∀ x : Nat, 70760 < x → x < 70765 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70763 ∨ 70763 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70761_70762 x h1 hc
  · exact adj_70763_70764 x (by omega) h2

theorem adj_70765_70766 : ∀ x : Nat, 70764 < x → x < 70767 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70765 ∨ x = 70766 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70765
  · rw [hx]
    exact not_prime_70766

theorem adj_70767_70768 : ∀ x : Nat, 70766 < x → x < 70769 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70767 ∨ x = 70768 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70767
  · rw [hx]
    exact not_prime_70768

theorem adj_70765_70768 : ∀ x : Nat, 70764 < x → x < 70769 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70767 ∨ 70767 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70765_70766 x h1 hc
  · exact adj_70767_70768 x (by omega) h2

theorem adj_70761_70768 : ∀ x : Nat, 70760 < x → x < 70769 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70765 ∨ 70765 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70761_70764 x h1 hc
  · exact adj_70765_70768 x (by omega) h2

theorem adj_70754_70768 : ∀ x : Nat, 70753 < x → x < 70769 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70761 ∨ 70761 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70754_70760 x h1 hc
  · exact adj_70761_70768 x (by omega) h2

theorem adj_70770_70770 : ∀ x : Nat, 70769 < x → x < 70771 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70770 := by omega
  rw [hx]
  exact not_prime_70770

theorem adj_70771_70772 : ∀ x : Nat, 70770 < x → x < 70773 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70771 ∨ x = 70772 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70771
  · rw [hx]
    exact not_prime_70772

theorem adj_70770_70772 : ∀ x : Nat, 70769 < x → x < 70773 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70771 ∨ 70771 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70770_70770 x h1 hc
  · exact adj_70771_70772 x (by omega) h2

theorem adj_70773_70773 : ∀ x : Nat, 70772 < x → x < 70774 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70773 := by omega
  rw [hx]
  exact not_prime_70773

theorem adj_70774_70775 : ∀ x : Nat, 70773 < x → x < 70776 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70774 ∨ x = 70775 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70774
  · rw [hx]
    exact not_prime_70775

theorem adj_70773_70775 : ∀ x : Nat, 70772 < x → x < 70776 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70774 ∨ 70774 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70773_70773 x h1 hc
  · exact adj_70774_70775 x (by omega) h2

theorem adj_70770_70775 : ∀ x : Nat, 70769 < x → x < 70776 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70773 ∨ 70773 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70770_70772 x h1 hc
  · exact adj_70773_70775 x (by omega) h2

theorem adj_70776_70776 : ∀ x : Nat, 70775 < x → x < 70777 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70776 := by omega
  rw [hx]
  exact not_prime_70776

theorem adj_70777_70778 : ∀ x : Nat, 70776 < x → x < 70779 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70777 ∨ x = 70778 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70777
  · rw [hx]
    exact not_prime_70778

theorem adj_70776_70778 : ∀ x : Nat, 70775 < x → x < 70779 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70777 ∨ 70777 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70776_70776 x h1 hc
  · exact adj_70777_70778 x (by omega) h2

theorem adj_70779_70780 : ∀ x : Nat, 70778 < x → x < 70781 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70779 ∨ x = 70780 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70779
  · rw [hx]
    exact not_prime_70780

theorem adj_70781_70782 : ∀ x : Nat, 70780 < x → x < 70783 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70781 ∨ x = 70782 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70781
  · rw [hx]
    exact not_prime_70782

theorem adj_70779_70782 : ∀ x : Nat, 70778 < x → x < 70783 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70781 ∨ 70781 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70779_70780 x h1 hc
  · exact adj_70781_70782 x (by omega) h2

theorem adj_70776_70782 : ∀ x : Nat, 70775 < x → x < 70783 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70779 ∨ 70779 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70776_70778 x h1 hc
  · exact adj_70779_70782 x (by omega) h2

theorem adj_70770_70782 : ∀ x : Nat, 70769 < x → x < 70783 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70776 ∨ 70776 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70770_70775 x h1 hc
  · exact adj_70776_70782 x (by omega) h2

theorem adj_70784_70785 : ∀ x : Nat, 70783 < x → x < 70786 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70784 ∨ x = 70785 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70784
  · rw [hx]
    exact not_prime_70785

theorem adj_70786_70787 : ∀ x : Nat, 70785 < x → x < 70788 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70786 ∨ x = 70787 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70786
  · rw [hx]
    exact not_prime_70787

theorem adj_70784_70787 : ∀ x : Nat, 70783 < x → x < 70788 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70786 ∨ 70786 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70784_70785 x h1 hc
  · exact adj_70786_70787 x (by omega) h2

theorem adj_70788_70789 : ∀ x : Nat, 70787 < x → x < 70790 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70788 ∨ x = 70789 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70788
  · rw [hx]
    exact not_prime_70789

theorem adj_70790_70790 : ∀ x : Nat, 70789 < x → x < 70791 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70790 := by omega
  rw [hx]
  exact not_prime_70790

theorem adj_70791_70792 : ∀ x : Nat, 70790 < x → x < 70793 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70791 ∨ x = 70792 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70791
  · rw [hx]
    exact not_prime_70792

theorem adj_70790_70792 : ∀ x : Nat, 70789 < x → x < 70793 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70791 ∨ 70791 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70790_70790 x h1 hc
  · exact adj_70791_70792 x (by omega) h2

theorem adj_70788_70792 : ∀ x : Nat, 70787 < x → x < 70793 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70790 ∨ 70790 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70788_70789 x h1 hc
  · exact adj_70790_70792 x (by omega) h2

theorem adj_70784_70792 : ∀ x : Nat, 70783 < x → x < 70793 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70788 ∨ 70788 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70784_70787 x h1 hc
  · exact adj_70788_70792 x (by omega) h2

theorem adj_70794_70794 : ∀ x : Nat, 70793 < x → x < 70795 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70794 := by omega
  rw [hx]
  exact not_prime_70794

theorem adj_70795_70796 : ∀ x : Nat, 70794 < x → x < 70797 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70795 ∨ x = 70796 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70795
  · rw [hx]
    exact not_prime_70796

theorem adj_70794_70796 : ∀ x : Nat, 70793 < x → x < 70797 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70795 ∨ 70795 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70794_70794 x h1 hc
  · exact adj_70795_70796 x (by omega) h2

theorem adj_70797_70798 : ∀ x : Nat, 70796 < x → x < 70799 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70797 ∨ x = 70798 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70797
  · rw [hx]
    exact not_prime_70798

theorem adj_70799_70800 : ∀ x : Nat, 70798 < x → x < 70801 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70799 ∨ x = 70800 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70799
  · rw [hx]
    exact not_prime_70800

theorem adj_70797_70800 : ∀ x : Nat, 70796 < x → x < 70801 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70799 ∨ 70799 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70797_70798 x h1 hc
  · exact adj_70799_70800 x (by omega) h2

theorem adj_70794_70800 : ∀ x : Nat, 70793 < x → x < 70801 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70797 ∨ 70797 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70794_70796 x h1 hc
  · exact adj_70797_70800 x (by omega) h2

theorem adj_70801_70801 : ∀ x : Nat, 70800 < x → x < 70802 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70801 := by omega
  rw [hx]
  exact not_prime_70801

theorem adj_70802_70803 : ∀ x : Nat, 70801 < x → x < 70804 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70802 ∨ x = 70803 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70802
  · rw [hx]
    exact not_prime_70803

theorem adj_70801_70803 : ∀ x : Nat, 70800 < x → x < 70804 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70802 ∨ 70802 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70801_70801 x h1 hc
  · exact adj_70802_70803 x (by omega) h2

theorem adj_70804_70805 : ∀ x : Nat, 70803 < x → x < 70806 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70804 ∨ x = 70805 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70804
  · rw [hx]
    exact not_prime_70805

theorem adj_70806_70807 : ∀ x : Nat, 70805 < x → x < 70808 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70806 ∨ x = 70807 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70806
  · rw [hx]
    exact not_prime_70807

theorem adj_70804_70807 : ∀ x : Nat, 70803 < x → x < 70808 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70806 ∨ 70806 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70804_70805 x h1 hc
  · exact adj_70806_70807 x (by omega) h2

theorem adj_70801_70807 : ∀ x : Nat, 70800 < x → x < 70808 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70804 ∨ 70804 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70801_70803 x h1 hc
  · exact adj_70804_70807 x (by omega) h2

theorem adj_70794_70807 : ∀ x : Nat, 70793 < x → x < 70808 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70801 ∨ 70801 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70794_70800 x h1 hc
  · exact adj_70801_70807 x (by omega) h2

theorem adj_70808_70808 : ∀ x : Nat, 70807 < x → x < 70809 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70808 := by omega
  rw [hx]
  exact not_prime_70808

theorem adj_70809_70810 : ∀ x : Nat, 70808 < x → x < 70811 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70809 ∨ x = 70810 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70809
  · rw [hx]
    exact not_prime_70810

theorem adj_70808_70810 : ∀ x : Nat, 70807 < x → x < 70811 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70809 ∨ 70809 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70808_70808 x h1 hc
  · exact adj_70809_70810 x (by omega) h2

theorem adj_70811_70812 : ∀ x : Nat, 70810 < x → x < 70813 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70811 ∨ x = 70812 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70811
  · rw [hx]
    exact not_prime_70812

theorem adj_70813_70814 : ∀ x : Nat, 70812 < x → x < 70815 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70813 ∨ x = 70814 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70813
  · rw [hx]
    exact not_prime_70814

theorem adj_70811_70814 : ∀ x : Nat, 70810 < x → x < 70815 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70813 ∨ 70813 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70811_70812 x h1 hc
  · exact adj_70813_70814 x (by omega) h2

theorem adj_70808_70814 : ∀ x : Nat, 70807 < x → x < 70815 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70811 ∨ 70811 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70808_70810 x h1 hc
  · exact adj_70811_70814 x (by omega) h2

theorem adj_70815_70816 : ∀ x : Nat, 70814 < x → x < 70817 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70815 ∨ x = 70816 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70815
  · rw [hx]
    exact not_prime_70816

theorem adj_70817_70818 : ∀ x : Nat, 70816 < x → x < 70819 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70817 ∨ x = 70818 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70817
  · rw [hx]
    exact not_prime_70818

theorem adj_70815_70818 : ∀ x : Nat, 70814 < x → x < 70819 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70817 ∨ 70817 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70815_70816 x h1 hc
  · exact adj_70817_70818 x (by omega) h2

theorem adj_70819_70820 : ∀ x : Nat, 70818 < x → x < 70821 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70819 ∨ x = 70820 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70819
  · rw [hx]
    exact not_prime_70820

theorem adj_70821_70822 : ∀ x : Nat, 70820 < x → x < 70823 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70821 ∨ x = 70822 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70821
  · rw [hx]
    exact not_prime_70822

theorem adj_70819_70822 : ∀ x : Nat, 70818 < x → x < 70823 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70821 ∨ 70821 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70819_70820 x h1 hc
  · exact adj_70821_70822 x (by omega) h2

theorem adj_70815_70822 : ∀ x : Nat, 70814 < x → x < 70823 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70819 ∨ 70819 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70815_70818 x h1 hc
  · exact adj_70819_70822 x (by omega) h2

theorem adj_70808_70822 : ∀ x : Nat, 70807 < x → x < 70823 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70815 ∨ 70815 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70808_70814 x h1 hc
  · exact adj_70815_70822 x (by omega) h2

theorem adj_70794_70822 : ∀ x : Nat, 70793 < x → x < 70823 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70808 ∨ 70808 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70794_70807 x h1 hc
  · exact adj_70808_70822 x (by omega) h2

theorem adj_70824_70825 : ∀ x : Nat, 70823 < x → x < 70826 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70824 ∨ x = 70825 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70824
  · rw [hx]
    exact not_prime_70825

theorem adj_70826_70827 : ∀ x : Nat, 70825 < x → x < 70828 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70826 ∨ x = 70827 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70826
  · rw [hx]
    exact not_prime_70827

theorem adj_70824_70827 : ∀ x : Nat, 70823 < x → x < 70828 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70826 ∨ 70826 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70824_70825 x h1 hc
  · exact adj_70826_70827 x (by omega) h2

theorem adj_70828_70829 : ∀ x : Nat, 70827 < x → x < 70830 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70828 ∨ x = 70829 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70828
  · rw [hx]
    exact not_prime_70829

theorem adj_70830_70831 : ∀ x : Nat, 70829 < x → x < 70832 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70830 ∨ x = 70831 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70830
  · rw [hx]
    exact not_prime_70831

theorem adj_70828_70831 : ∀ x : Nat, 70827 < x → x < 70832 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70830 ∨ 70830 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70828_70829 x h1 hc
  · exact adj_70830_70831 x (by omega) h2

theorem adj_70824_70831 : ∀ x : Nat, 70823 < x → x < 70832 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70828 ∨ 70828 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70824_70827 x h1 hc
  · exact adj_70828_70831 x (by omega) h2

theorem adj_70832_70833 : ∀ x : Nat, 70831 < x → x < 70834 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70832 ∨ x = 70833 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70832
  · rw [hx]
    exact not_prime_70833

theorem adj_70834_70835 : ∀ x : Nat, 70833 < x → x < 70836 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70834 ∨ x = 70835 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70834
  · rw [hx]
    exact not_prime_70835

theorem adj_70832_70835 : ∀ x : Nat, 70831 < x → x < 70836 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70834 ∨ 70834 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70832_70833 x h1 hc
  · exact adj_70834_70835 x (by omega) h2

theorem adj_70836_70837 : ∀ x : Nat, 70835 < x → x < 70838 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70836 ∨ x = 70837 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70836
  · rw [hx]
    exact not_prime_70837

theorem adj_70838_70838 : ∀ x : Nat, 70837 < x → x < 70839 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70838 := by omega
  rw [hx]
  exact not_prime_70838

theorem adj_70839_70840 : ∀ x : Nat, 70838 < x → x < 70841 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70839 ∨ x = 70840 := by omega
  rcases hx with hx | hx
  · rw [hx]
    exact not_prime_70839
  · rw [hx]
    exact not_prime_70840

theorem adj_70838_70840 : ∀ x : Nat, 70837 < x → x < 70841 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70839 ∨ 70839 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70838_70838 x h1 hc
  · exact adj_70839_70840 x (by omega) h2

theorem adj_70836_70840 : ∀ x : Nat, 70835 < x → x < 70841 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70838 ∨ 70838 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70836_70837 x h1 hc
  · exact adj_70838_70840 x (by omega) h2

theorem adj_70832_70840 : ∀ x : Nat, 70831 < x → x < 70841 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70836 ∨ 70836 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70832_70835 x h1 hc
  · exact adj_70836_70840 x (by omega) h2

theorem adj_70824_70840 : ∀ x : Nat, 70823 < x → x < 70841 → ¬ Prime x := by
  intro x h1 h2
  have hc : x < 70832 ∨ 70832 ≤ x := by omega
  rcases hc with hc | hc
  · exact adj_70824_70831 x h1 hc
  · exact adj_70832_70840 x (by omega) h2

theorem adj_70842_70842 : ∀ x : Nat, 70841 < x → x < 70843 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 70842 := by omega
  rw [hx]
  exact not_prime_70842

-- ---------------------------------------------------------------------
-- 主定理（对题目陈述的直接回答：构造性下界，至少 13）
-- ---------------------------------------------------------------------

/-- 存在 14 个相邻素数，其 13 个连续间隙全部互异（run 长度 13） -/
theorem jsp_705 :
    ∃ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Nat,
      Prime p0 ∧ Prime p1 ∧ Prime p2 ∧ Prime p3 ∧ Prime p4 ∧ Prime p5 ∧ Prime p6 ∧ Prime p7 ∧ Prime p8 ∧ Prime p9 ∧ Prime p10 ∧ Prime p11 ∧ Prime p12 ∧ Prime p13 ∧ p0 + 6 = p1 ∧ p1 + 4 = p2 ∧ p2 + 20 = p3 ∧ p3 + 22 = p4 ∧ p4 + 8 = p5 ∧ p5 + 12 = p6 ∧ p6 + 24 = p7 ∧ p7 + 16 = p8 ∧ p8 + 14 = p9 ∧ p9 + 10 = p10 ∧ p10 + 30 = p11 ∧ p11 + 18 = p12 ∧ p12 + 2 = p13 ∧ (∀ x : Nat, p0 < x → x < p1 → ¬ Prime x) ∧ (∀ x : Nat, p1 < x → x < p2 → ¬ Prime x) ∧ (∀ x : Nat, p2 < x → x < p3 → ¬ Prime x) ∧ (∀ x : Nat, p3 < x → x < p4 → ¬ Prime x) ∧ (∀ x : Nat, p4 < x → x < p5 → ¬ Prime x) ∧ (∀ x : Nat, p5 < x → x < p6 → ¬ Prime x) ∧ (∀ x : Nat, p6 < x → x < p7 → ¬ Prime x) ∧ (∀ x : Nat, p7 < x → x < p8 → ¬ Prime x) ∧ (∀ x : Nat, p8 < x → x < p9 → ¬ Prime x) ∧ (∀ x : Nat, p9 < x → x < p10 → ¬ Prime x) ∧ (∀ x : Nat, p10 < x → x < p11 → ¬ Prime x) ∧ (∀ x : Nat, p11 < x → x < p12 → ¬ Prime x) ∧ (∀ x : Nat, p12 < x → x < p13 → ¬ Prime x) := by
  refine ⟨70657, 70663, 70667, 70687, 70709, 70717, 70729, 70753, 70769, 70783, 70793, 70823, 70841, 70843, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact prime_70657
  · exact prime_70663
  · exact prime_70667
  · exact prime_70687
  · exact prime_70709
  · exact prime_70717
  · exact prime_70729
  · exact prime_70753
  · exact prime_70769
  · exact prime_70783
  · exact prime_70793
  · exact prime_70823
  · exact prime_70841
  · exact prime_70843
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact adj_70658_70662
  · exact adj_70664_70666
  · exact adj_70668_70686
  · exact adj_70688_70708
  · exact adj_70710_70716
  · exact adj_70718_70728
  · exact adj_70730_70752
  · exact adj_70754_70768
  · exact adj_70770_70782
  · exact adj_70784_70792
  · exact adj_70794_70822
  · exact adj_70824_70840
  · exact adj_70842_70842

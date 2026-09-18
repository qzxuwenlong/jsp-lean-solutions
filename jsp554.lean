-- =====================================================================
-- JSP-000554 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Between consecutive primes, is there an integer whose least
--       prime factor is at least their gap?
--       （任意相邻素数之间，是否存在整数，其最小素因子至少等于间隙？）
-- 答案：否。反例：相邻素数 89 与 97（间隙 8），中间的整数
--         90, 91, 92, 93, 94, 95, 96
--       的最小素因子分别为 2, 7, 2, 3, 2, 5, 2，全部严格小于 8。
--       因此该间隙内不存在最小素因子 ≥ 间隙长度的整数。
--       （Gafni–Tao 2025 证明"几乎所有"间隙都有，反例间隙为例外。）
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp554.lean
-- 全部计算性证明由 `decide` 在内核 VM 中完成。
-- 定义与引理层复用自 jsp301/307/598（已验证通过本地内核）。
-- =====================================================================

set_option maxRecDepth 1000000

-- ---------------------------------------------------------------------
-- 定义（来自 jsp598，已通过内核核验）
-- ---------------------------------------------------------------------

/-- 素数（Mathlib 的 Nat.Prime 等价定义，避免依赖 Mathlib） -/
def Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- 自建列表全称判定 -/
def listAll (f : Nat → Bool) (l : List Nat) : Bool :=
  List.foldl (fun acc x => acc && f x) true l

def primeCheck (p : Nat) : Bool :=
  decide (2 ≤ p) && listAll (fun m => decide (m = 1) || decide (m = p) || Bool.not (decide (m ∣ p))) (List.range (p + 1))

theorem and_eq_true (a b : Bool) : ((a && b) = true) ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

theorem or_eq_true (a b : Bool) : ((a || b) = true) ↔ (a = true ∨ b = true) := by
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

theorem primeCheck_sound {p : Nat} (hp : p ≥ 2) (h : primeCheck p = true) : Prime p := by
  have hb := (and_eq_true (decide (2 ≤ p))
      (listAll (fun m => decide (m = 1) || decide (m = p) || Bool.not (decide (m ∣ p))) (List.range (p + 1)))).mp
    (by simpa [primeCheck] using h)
  refine ⟨hp, ?_⟩
  intro m hmd
  have hmle : m ≤ p := Nat.le_of_dvd (by omega) hmd
  have hmem : m ∈ List.range (p + 1) := List.mem_range.mpr (by omega)
  have hf := listAll_elim hb.2 m hmem
  have hf' := (or_eq_true (decide (m = 1) || decide (m = p)) (Bool.not (decide (m ∣ p)))).mp hf
  rcases hf' with h1 | h3
  · rcases (or_eq_true (decide (m = 1)) (decide (m = p))).mp h1 with h1m | h2m
    · exact Or.inl (of_decide_eq_true h1m)
    · exact Or.inr (of_decide_eq_true h2m)
  · exfalso
    have hdF : decide (m ∣ p) = false := by
      cases hd' : decide (m ∣ p)
      · rfl
      · exfalso
        simpa [hd'] using h3
    have hdT : decide (m ∣ p) = true := decide_eq_true hmd
    simp [hdF] at hdT

-- ---------------------------------------------------------------------
-- 反例：相邻素数 89 与 97
-- ---------------------------------------------------------------------

/-- 若 m ≠ 1 且 m ≠ p 且 m ∣ p，则 p 不是素数 -/
theorem not_prime_of_factor {p m : Nat} (hm1 : m ≠ 1) (hmp : m ≠ p) (hmd : m ∣ p) : ¬ Prime p := by
  intro hp
  rcases hp.2 m hmd with h1 | h2 <;> omega

theorem not_prime_90 : ¬ Prime 90 := by
  exact not_prime_of_factor (by decide : 2 ≠ 1) (by decide : 2 ≠ 90) (by decide : 2 ∣ 90)

theorem not_prime_91 : ¬ Prime 91 := by
  exact not_prime_of_factor (by decide : 7 ≠ 1) (by decide : 7 ≠ 91) (by decide : 7 ∣ 91)

theorem not_prime_92 : ¬ Prime 92 := by
  exact not_prime_of_factor (by decide : 2 ≠ 1) (by decide : 2 ≠ 92) (by decide : 2 ∣ 92)

theorem not_prime_93 : ¬ Prime 93 := by
  exact not_prime_of_factor (by decide : 3 ≠ 1) (by decide : 3 ≠ 93) (by decide : 3 ∣ 93)

theorem not_prime_94 : ¬ Prime 94 := by
  exact not_prime_of_factor (by decide : 2 ≠ 1) (by decide : 2 ≠ 94) (by decide : 2 ∣ 94)

theorem not_prime_95 : ¬ Prime 95 := by
  exact not_prime_of_factor (by decide : 5 ≠ 1) (by decide : 5 ≠ 95) (by decide : 5 ∣ 95)

theorem not_prime_96 : ¬ Prime 96 := by
  exact not_prime_of_factor (by decide : 2 ≠ 1) (by decide : 2 ≠ 96) (by decide : 2 ∣ 96)

/-- 89 是素数（primeCheck 计算核验） -/
theorem prime_89 : Prime 89 := primeCheck_sound (by decide) (by decide)

/-- 97 是素数（primeCheck 计算核验） -/
theorem prime_97 : Prime 97 := primeCheck_sound (by decide) (by decide)

/-- 89 与 97 之间没有素数（90..96 全部合数） -/
theorem consecutive_89_97 : ∀ x : Nat, 89 < x → x < 97 → ¬ Prime x := by
  intro x h1 h2
  have hx : x = 90 ∨ x = 91 ∨ x = 92 ∨ x = 93 ∨ x = 94 ∨ x = 95 ∨ x = 96 := by
    omega
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_prime_90
  · exact not_prime_91
  · exact not_prime_92
  · exact not_prime_93
  · exact not_prime_94
  · exact not_prime_95
  · exact not_prime_96

theorem prime_2 : Prime 2 := primeCheck_sound (by decide) (by decide)
theorem prime_3 : Prime 3 := primeCheck_sound (by decide) (by decide)
theorem prime_5 : Prime 5 := primeCheck_sound (by decide) (by decide)
theorem prime_7 : Prime 7 := primeCheck_sound (by decide) (by decide)

/-- 90..96 中每个整数都有一个 < 8 的素因子（即最小素因子 < 间隙 8） -/
theorem small_prime_factor :
    ∀ n : Nat, 89 < n → n < 97 → ∃ r : Nat, Prime r ∧ r ∣ n ∧ r < 8 := by
  intro n h1 h2
  have hn : n = 90 ∨ n = 91 ∨ n = 92 ∨ n = 93 ∨ n = 94 ∨ n = 95 ∨ n = 96 := by
    omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, prime_2, by decide, by decide⟩
  · exact ⟨7, prime_7, by decide, by decide⟩
  · exact ⟨2, prime_2, by decide, by decide⟩
  · exact ⟨3, prime_3, by decide, by decide⟩
  · exact ⟨2, prime_2, by decide, by decide⟩
  · exact ⟨5, prime_5, by decide, by decide⟩
  · exact ⟨2, prime_2, by decide, by decide⟩

-- ---------------------------------------------------------------------
-- 主定理：不是每对相邻素数之间都存在最小素因子 ≥ 间隙的整数
-- ---------------------------------------------------------------------

/-- 对问题陈述的否定回答：存在相邻素数对（89 与 97，间隙 8），
    其间的任何整数都有某个 < 8 的素因子，
    因此最小素因子都 < 8，不存在最小素因子 ≥ 8 的整数。 -/
theorem jsp_554_answer :
    ¬ (∀ p q : Nat, Prime p → Prime q → p < q →
          (∀ x : Nat, p < x → x < q → ¬ Prime x) →
          ∃ n : Nat, p < n ∧ n < q ∧ (∀ r : Nat, Prime r → r ∣ n → r ≥ q - p)) := by
  intro h
  rcases h 89 97 prime_89 prime_97 (by omega) consecutive_89_97 with ⟨n, hn1, hn2, hbig⟩
  rcases small_prime_factor n hn1 hn2 with ⟨s, hs, hsdiv, hslt⟩
  have hsge : s ≥ 8 := by simpa using hbig s hs hsdiv
  omega

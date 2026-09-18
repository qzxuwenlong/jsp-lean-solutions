-- =====================================================================
-- JSP-000307 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交（草稿 v1）
--
-- 题目：Can three consecutive integers have strictly decreasing largest
--       prime factors?
--       （是否存在三个连续正整数，其最大素因子严格递减？）
-- 答案：是。反例：14, 15, 16。
--         14 = 2·7   → 最大素因子 7
--         15 = 3·5   → 最大素因子 5
--         16 = 2^4   → 最大素因子 2
--       且 7 > 5 > 2，严格递减。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp307.lean （驱动见 run-lean.js）
-- 全部计算性证明由 `decide` 在内核 VM 中完成（机器逐行核验）。
-- 定义与引理层复用自 jsp301.lean（已验证通过本地内核）。
-- =====================================================================

set_option maxRecDepth 1000000

-- ---------------------------------------------------------------------
-- 定义
-- ---------------------------------------------------------------------

/-- 素数（Mathlib 的 Nat.Prime 等价定义，避免依赖 Mathlib） -/
def Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

-- ---------------------------------------------------------------------
-- 自建列表全称判定（该 Std 构建的 List.all 不可直接调用，自写等价物）
-- ---------------------------------------------------------------------

def listAll (f : Nat → Bool) (l : List Nat) : Bool :=
  List.foldl (fun acc x => acc && f x) true l

-- ---------------------------------------------------------------------
-- 可判定素性检查（走内核 VM 计算，可被 decide 归约）
-- ---------------------------------------------------------------------

/-- 素性检查（有界、可判定；对真素数返回 true，见 primeCheck_of_Prime） -/
def primeCheck (p : Nat) : Bool :=
  decide (2 ≤ p) && listAll (fun m => decide (m = 1) || decide (m = p) || Bool.not (decide (m ∣ p))) (List.range (p + 1))

-- ---------------------------------------------------------------------
-- Bool 与列表引理（来自 jsp301.lean，已通过内核核验）
-- ---------------------------------------------------------------------

theorem and_eq_true (a b : Bool) : ((a && b) = true) ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

theorem or_eq_true (a b : Bool) : ((a || b) = true) ↔ (a = true ∨ b = true) := by
  cases a <;> cases b <;> simp

/-- foldl 版的充分方向（对任意累加器，广义归纳） -/
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

/-- foldl 版的必要方向（广义归纳） -/
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

/-- listAll 的充分方向：逐点成立则全体成立 -/
theorem listAll_intro {l : List Nat} {f : Nat → Bool}
    (h : ∀ x : Nat, x ∈ l → f x = true) : listAll f l = true := by
  exact foldl_and_intro l f true rfl h

/-- listAll 的必要方向：全体成立则逐点成立 -/
theorem listAll_elim {l : List Nat} {f : Nat → Bool}
    (h : listAll f l = true) : ∀ x : Nat, x ∈ l → f x = true := by
  exact (foldl_and_elim l f true h).2

/-- primeCheck 对真素数为 true（完备性） -/
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

/-- primeCheck 的可靠性：检查通过则素数 -/
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
-- 反例核验（浅计算：有界全称 by decide，14/15/16 均为小界）
-- ---------------------------------------------------------------------

/-- 7 是素数 -/
theorem prime_7 : Prime 7 :=
  primeCheck_sound (by decide : 7 ≥ 2) (by decide : primeCheck 7 = true)

/-- 5 是素数 -/
theorem prime_5 : Prime 5 :=
  primeCheck_sound (by decide : 5 ≥ 2) (by decide : primeCheck 5 = true)

/-- 2 是素数 -/
theorem prime_2 : Prime 2 :=
  primeCheck_sound (by decide : 2 ≥ 2) (by decide : primeCheck 2 = true)

/-- 14 的任意素因子 ≤ 7（有界全称：q ≤ 14 的 q 中只有 2 与 7 是素因子） -/
theorem maxpf_14 (x : Nat) (hxP : Prime x) (hxd : x ∣ 14) : x ≤ 7 := by
  have hqc : primeCheck x = true := primeCheck_of_Prime x hxP
  have hxle : x ≤ 14 := Nat.le_of_dvd (by decide : 0 < 14) hxd
  exact (by decide : ∀ q : Nat, q ≤ 14 → primeCheck q = true → q ∣ 14 → q ≤ 7) x hxle hqc hxd

/-- 15 的任意素因子 ≤ 5（有界全称：q ≤ 15 的 q 中只有 3 与 5 是素因子） -/
theorem maxpf_15 (x : Nat) (hxP : Prime x) (hxd : x ∣ 15) : x ≤ 5 := by
  have hqc : primeCheck x = true := primeCheck_of_Prime x hxP
  have hxle : x ≤ 15 := Nat.le_of_dvd (by decide : 0 < 15) hxd
  exact (by decide : ∀ q : Nat, q ≤ 15 → primeCheck q = true → q ∣ 15 → q ≤ 5) x hxle hqc hxd

/-- 16 的任意素因子 ≤ 2（有界全称：q ≤ 16 的 q 中只有 2 是素因子） -/
theorem maxpf_16 (x : Nat) (hxP : Prime x) (hxd : x ∣ 16) : x ≤ 2 := by
  have hqc : primeCheck x = true := primeCheck_of_Prime x hxP
  have hxle : x ≤ 16 := Nat.le_of_dvd (by decide : 0 < 16) hxd
  exact (by decide : ∀ q : Nat, q ≤ 16 → primeCheck q = true → q ∣ 16 → q ≤ 2) x hxle hqc hxd

-- ---------------------------------------------------------------------
-- 主定理（对题目陈述的构造性回答：是）
-- ---------------------------------------------------------------------

/-- 存在连续正整数 a, a+1, a+2，其最大素因子严格递减：
    p、q、r 分别为三数的最大素因子，且 p > q > r。 -/
theorem jsp_307_answer :
    ∃ a p q r : Nat,
      Prime p ∧ Prime q ∧ Prime r ∧
      p ∣ a ∧ q ∣ (a + 1) ∧ r ∣ (a + 2) ∧
      (∀ x : Nat, Prime x → x ∣ a → x ≤ p) ∧
      (∀ x : Nat, Prime x → x ∣ (a + 1) → x ≤ q) ∧
      (∀ x : Nat, Prime x → x ∣ (a + 2) → x ≤ r) ∧
      p > q ∧ q > r := by
  refine ⟨14, 7, 5, 2, prime_7, prime_5, prime_2,
    by decide, by decide, by decide,
    maxpf_14, maxpf_15, maxpf_16, by decide, by decide⟩

/-- 直接陈述反例三元组及其最大素因子 -/
theorem jsp_307_counterexample :
    ∃ a p q r : Nat, p ∣ a ∧ q ∣ (a + 1) ∧ r ∣ (a + 2) ∧
      (∀ x : Nat, Prime x → x ∣ a → x ≤ p) ∧
      (∀ x : Nat, Prime x → x ∣ (a + 1) → x ≤ q) ∧
      (∀ x : Nat, Prime x → x ∣ (a + 2) → x ≤ r) ∧
      p > q ∧ q > r := by
  refine ⟨14, 7, 5, 2, by decide, by decide, by decide,
    maxpf_14, maxpf_15, maxpf_16, by decide, by decide⟩

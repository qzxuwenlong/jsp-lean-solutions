-- =====================================================================
-- JSP-000301 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交（草稿 v2）
--
-- 题目：If two consecutive positive integers are powerful, must at least
--       one be a perfect square?
--       （若两个连续正整数都是 powerful 数，是否至少有一个是完全平方数？）
-- 答案：否。反例：12167 = 23^3 与 12168 = 2^3·3^2·13^2 连续、均 powerful、均非平方。
--       （官方卷目录 Review notes 给出同一反例：Golomb 1970 的构造。）
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp301.lean （驱动见 run-lean.js）
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

/-- 完全平方数 -/
def IsSquare (n : Nat) : Prop := ∃ x : Nat, x ^ 2 = n

-- ---------------------------------------------------------------------
-- 自建列表全称判定（该 Std 构建的 List.all 不可直接调用，自写等价物）
-- ---------------------------------------------------------------------

def listAll (f : Nat → Bool) (l : List Nat) : Bool :=
  List.foldl (fun acc x => acc && f x) true l

-- ---------------------------------------------------------------------
-- 可判定机制（全部走内核 VM 计算，可被 decide 归约）
-- ---------------------------------------------------------------------

/-- 素性检查（有界、可判定；对真素数返回 true，见 primeCheck_of_Prime） -/
def primeCheck (p : Nat) : Bool :=
  decide (2 ≤ p) && listAll (fun m => decide (m = 1) || decide (m = p) || Bool.not (decide (m ∣ p))) (List.range (p + 1))

/-- powerful 检查：对每个 p ≤ n，若 p ∣ n 且 p 是素数，则 p² ∣ n。
    利用 &&/|| 短路：对绝大多数不整除 n 的 p 不展开 primeCheck，计算量极小。 -/
def powerfulCheck (n : Nat) : Bool :=
  listAll (fun p => Bool.not (decide (p ∣ n)) || Bool.not (primeCheck p) || decide ((p ^ 2) ∣ n)) (List.range (n + 1))

def powerfulIn (n : Nat) (r : List Nat) : Bool :=
  listAll (fun p => Bool.not (decide (p ∣ n)) || Bool.not (primeCheck p) || decide ((p ^ 2) ∣ n)) r

/-- 非平方检查：对每个 x ≤ n，x² ≠ n -/
def squareCheck (n : Nat) : Bool :=
  listAll (fun x => decide ((x ^ 2) ≠ n)) (List.range (n + 1))

-- ---------------------------------------------------------------------
-- Bool 与列表引理
-- ---------------------------------------------------------------------

theorem and_eq_true (a b : Bool) : ((a && b) = true) ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

theorem or_eq_true (a b : Bool) : ((a || b) = true) ↔ (a = true ∨ b = true) := by
  cases a <;> cases b <;> simp

/-- x² = x·x 的桥引理（核心库不直接提供） -/
theorem pow_two_eq (x : Nat) : x ^ 2 = x * x := by
  calc
    x ^ 2 = x ^ (1 + 1) := rfl
    _ = x ^ 1 * x := by rw [Nat.pow_succ]
    _ = x * x := by rw [Nat.pow_one]

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

/-- primeCheck 对真素数为 true（只证这一个方向即可） -/
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

/-- powerfulCheck 的可靠性：检查通过则 Powerful -/
theorem powerfulCheck_sound (n : Nat) (hn : n > 0) (h : powerfulCheck n = true) : Powerful n := by
  intro p hp hdvd
  have hle : p ≤ n := Nat.le_of_dvd hn hdvd
  have hmem : p ∈ List.range (n + 1) := List.mem_range.mpr (by omega)
  have hpb : primeCheck p = true := primeCheck_of_Prime p hp
  have hdvb : decide (p ∣ n) = true := decide_eq_true hdvd
  have hfp := listAll_elim h p hmem
  have hfirst : (Bool.not (decide (p ∣ n)) || Bool.not (primeCheck p)) = false := by
    simp [hdvb, hpb]
  have hc : decide (((p ^ 2) ∣ n)) = true := by
    rw [hfirst] at hfp
    simpa using hfp
  exact of_decide_eq_true hc

/-- squareCheck 的可靠性：检查通过则非平方 -/
theorem squareCheck_sound (n : Nat) (hn : n > 0) (h : squareCheck n = true) : ¬ IsSquare n := by
  rintro ⟨x, hx⟩
  by_cases hx0 : x = 0
  · subst x
    have hz : (0 : Nat) ^ 2 = 0 := by decide
    omega
  · have hpos : 0 < x := Nat.pos_of_ne_zero hx0
    have hself : x ≤ x * x := Nat.le_mul_of_pos_left x hpos
    have hle : x ≤ n := by
      calc
        x ≤ x * x := hself
        _ = x ^ 2 := (pow_two_eq x).symm
        _ = n := hx
    have hmem : x ∈ List.range (n + 1) := List.mem_range.mpr (by omega)
    have hfx : decide ((x ^ 2) ≠ n) = true := listAll_elim h x hmem
    exact of_decide_eq_true hfx hx

-- ---------------------------------------------------------------------
-- 反例核验（浅计算：小范围检查 + 约数覆盖 + 大素因子排除）
-- ---------------------------------------------------------------------

/-- 12167 = 23^3 -/
theorem factor_12167 : 12167 = 23 ^ 3 := by decide

/-- 12168 = 2^3·3^2·13^2 -/
theorem factor_12168 : 12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by decide

/-- 12167 的小范围约数（< 112）：1 或 23 -/
theorem divisors_12167 (q : Nat) (hq : q < 112) (hd : q ∣ 12167) : q = 1 ∨ q = 23 := by
  exact (by decide : ∀ q : Nat, q < 112 → q ∣ 12167 → q = 1 ∨ q = 23) q hq hd

/-- 12168 的小范围约数（< 113）：18 个候选（成员态） -/
theorem divisors_12168 (q : Nat) (hq : q < 113) (hd : q ∣ 12168) :
    q ∈ [1, 2, 3, 4, 6, 8, 9, 12, 13, 18, 24, 26, 36, 39, 52, 72, 78, 104] := by
  exact (by decide : ∀ q : Nat, q < 113 → q ∣ 12168 →
    q ∈ [1, 2, 3, 4, 6, 8, 9, 12, 13, 18, 24, 26, 36, 39, 52, 72, 78, 104]) q hq hd

/-- 合数见证引理：m 是 p 的非平凡因子 → p 非素数 -/
theorem not_prime_of_dvd {p m : Nat} (hmd : m ∣ p) (hm1 : m ≠ 1) (hmp : m ≠ p) : ¬ Prime p := by
  intro hp
  rcases hp with ⟨_, hall⟩
  have hm := hall m hmd
  rcases hm with h1 | hp'
  · exact hm1 h1
  · exact hmp hp'

theorem not_prime_12167 : ¬ Prime 12167 :=
  not_prime_of_dvd (by decide : 23 ∣ 12167) (by decide : 23 ≠ 1) (by decide : 23 ≠ 12167)

theorem not_prime_529 : ¬ Prime 529 :=
  not_prime_of_dvd (by decide : 23 ∣ 529) (by decide : 23 ≠ 1) (by decide : 23 ≠ 529)

/-- 12167：无 ≥ 112 的素因子（覆盖引理） -/
theorem no_large_prime_12167 {p : Nat} (hp : Prime p) (hge : 112 ≤ p) : ¬ p ∣ 12167 := by
  intro hd
  rcases hd with ⟨k, hk⟩
  have hklt : k < 112 := by
    have hle : 112 * k ≤ p * k := Nat.mul_le_mul_right k hge
    have hb : 112 * k ≤ 12167 := by rw [hk]; exact hle
    omega
  have hkd : k ∣ 12167 := ⟨p, by rw [hk]; exact Nat.mul_comm p k⟩
  rcases divisors_12167 k hklt hkd with hk_eq1 | hk_eq23
  · have h121 : 12167 = p := by simpa [hk_eq1] using hk
    have hp121 : p = 12167 := h121.symm
    exact not_prime_12167 (by simpa [hp121] using hp)
  · have hmm : 23 * p = 23 * 529 := by
      calc
        23 * p = p * 23 := (Nat.mul_comm p 23).symm
        _ = 12167 := by simpa [hk_eq23] using hk.symm
        _ = 23 * 529 := by decide
    have hp529 : p = 529 := Nat.mul_left_cancel (by omega : 0 < 23) hmm
    exact not_prime_529 (by simpa [hp529] using hp)

/-- 12167 是 powerful 数 -/
theorem powerful_12167 : Powerful 12167 := by
  intro p hp hdvd
  by_cases hp112 : p < 112
  · have hmem : p ∈ List.range 112 := List.mem_range.mpr (by omega)
    have hcheck : powerfulIn 12167 (List.range 112) = true := by decide
    have hfp := listAll_elim hcheck p hmem
    have hdvb : decide (p ∣ 12167) = true := by exact decide_eq_true hdvd
    have hpb : primeCheck p = true := primeCheck_of_Prime p hp
    have hn1 : Bool.not (decide (p ∣ 12167)) = false := by simp [hdvb]
    have hn2 : Bool.not (primeCheck p) = false := by simp [hpb]
    have hc : decide (((p ^ 2) ∣ 12167)) = true := by simpa [hn1, hn2] using hfp
    exact of_decide_eq_true hc
  · exact False.elim ((no_large_prime_12167 hp (by omega)) hdvd)

/-- 12168 无 ≥ 113 的素因子（18 个候选值的合数性逐项核验） -/
theorem no_large_prime_12168 {p : Nat} (hp : Prime p) (hge : 113 ≤ p) : ¬ p ∣ 12168 := by
  intro hd
  rcases hd with ⟨k, hk⟩
  have hklt : k < 113 := by
    have hle : 113 * k ≤ p * k := Nat.mul_le_mul_right k hge
    have hb : 113 * k ≤ 12168 := by rw [hk]; exact hle
    omega
  have hkd : k ∣ 12168 := ⟨p, by rw [hk]; exact Nat.mul_comm p k⟩
  have hmem := divisors_12168 k hklt hkd
  have hOr : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6 ∨ k = 8 ∨ k = 9 ∨ k = 12 ∨ k = 13 ∨ k = 18 ∨
      k = 24 ∨ k = 26 ∨ k = 36 ∨ k = 39 ∨ k = 52 ∨ k = 72 ∨ k = 78 ∨ k = 104 := by
    simpa using hmem
  rcases hOr with hk1 | hk2 | hk3 | hk4 | hk6 | hk8 | hk9 | hk12 | hk13 | hk18 |
      hk24 | hk26 | hk36 | hk39 | hk52 | hk72 | hk78 | hk104
  · subst k; have hpv : p = 12168 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 12168) (by decide : 2 ≠ 1) (by decide : 2 ≠ 12168) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 6084 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 6084) (by decide : 2 ≠ 1) (by decide : 2 ≠ 6084) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 4056 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 4056) (by decide : 2 ≠ 1) (by decide : 2 ≠ 4056) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 3042 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 3042) (by decide : 2 ≠ 1) (by decide : 2 ≠ 3042) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 2028 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 2028) (by decide : 2 ≠ 1) (by decide : 2 ≠ 2028) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 1521 := by omega
    exact not_prime_of_dvd (by decide : 3 ∣ 1521) (by decide : 3 ≠ 1) (by decide : 3 ≠ 1521) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 1352 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 1352) (by decide : 2 ≠ 1) (by decide : 2 ≠ 1352) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 1014 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 1014) (by decide : 2 ≠ 1) (by decide : 2 ≠ 1014) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 936 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 936) (by decide : 2 ≠ 1) (by decide : 2 ≠ 936) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 676 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 676) (by decide : 2 ≠ 1) (by decide : 2 ≠ 676) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 507 := by omega
    exact not_prime_of_dvd (by decide : 3 ∣ 507) (by decide : 3 ≠ 1) (by decide : 3 ≠ 507) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 468 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 468) (by decide : 2 ≠ 1) (by decide : 2 ≠ 468) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 338 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 338) (by decide : 2 ≠ 1) (by decide : 2 ≠ 338) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 312 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 312) (by decide : 2 ≠ 1) (by decide : 2 ≠ 312) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 234 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 234) (by decide : 2 ≠ 1) (by decide : 2 ≠ 234) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 169 := by omega
    exact not_prime_of_dvd (by decide : 13 ∣ 169) (by decide : 13 ≠ 1) (by decide : 13 ≠ 169) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 156 := by omega
    exact not_prime_of_dvd (by decide : 2 ∣ 156) (by decide : 2 ≠ 1) (by decide : 2 ≠ 156) (by simpa [hpv] using hp)
  · subst k; have hpv : p = 117 := by omega
    exact not_prime_of_dvd (by decide : 3 ∣ 117) (by decide : 3 ≠ 1) (by decide : 3 ≠ 117) (by simpa [hpv] using hp)

/-- 12168 是 powerful 数 -/
theorem powerful_12168 : Powerful 12168 := by
  intro p hp hdvd
  by_cases hp113 : p < 113
  · have hmem : p ∈ List.range 113 := List.mem_range.mpr (by omega)
    have hcheck : powerfulIn 12168 (List.range 113) = true := by decide
    have hfp := listAll_elim hcheck p hmem
    have hdvb : decide (p ∣ 12168) = true := by exact decide_eq_true hdvd
    have hpb : primeCheck p = true := primeCheck_of_Prime p hp
    have hn1 : Bool.not (decide (p ∣ 12168)) = false := by simp [hdvb]
    have hn2 : Bool.not (primeCheck p) = false := by simp [hpb]
    have hc : decide (((p ^ 2) ∣ 12168)) = true := by simpa [hn1, hn2] using hfp
    exact of_decide_eq_true hc
  · exact False.elim ((no_large_prime_12168 hp (by omega)) hdvd)

/-- 12167 不是完全平方数 -/
theorem not_square_12167 : ¬ IsSquare 12167 := by
  rintro ⟨x, hx⟩
  have hxsmall : x < 112 := by
    by_cases h : x < 112
    · exact h
    · have hge : 112 ≤ x := by omega
      have hb : 112 * 112 ≤ x * x := Nat.mul_le_mul hge hge
      have hbb : 112 * 112 ≤ 12167 := by
        calc
          112 * 112 ≤ x * x := hb
          _ = x ^ 2 := (pow_two_eq x).symm
          _ = 12167 := hx
      omega
  exact (by decide : ∀ y : Nat, y < 112 → (y ^ 2) ≠ 12167) x hxsmall hx

/-- 12168 不是完全平方数 -/
theorem not_square_12168 : ¬ IsSquare 12168 := by
  rintro ⟨x, hx⟩
  have hxsmall : x < 113 := by
    by_cases h : x < 113
    · exact h
    · have hge : 113 ≤ x := by omega
      have hb : 113 * 113 ≤ x * x := Nat.mul_le_mul hge hge
      have hbb : 113 * 113 ≤ 12168 := by
        calc
          113 * 113 ≤ x * x := hb
          _ = x ^ 2 := (pow_two_eq x).symm
          _ = 12168 := hx
      omega
  exact (by decide : ∀ y : Nat, y < 113 → (y ^ 2) ≠ 12168) x hxsmall hx

/-- 连续性：12167 + 1 = 12168 -/
theorem consecutive : 12167 + 1 = 12168 := by decide

-- ---------------------------------------------------------------------
-- 主定理（对题目陈述的直接回答）
-- ---------------------------------------------------------------------

/-- 存在两个连续正整数，均 powerful 且均非完全平方数（构造性反例） -/
theorem jsp_301_counterexample :
    ∃ a b : Nat, a > 0 ∧ b > 0 ∧ b = a + 1 ∧ Powerful a ∧ Powerful b ∧ ¬ IsSquare a ∧ ¬ IsSquare b := by
  refine ⟨12167, 12168, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · exact powerful_12167
  · exact powerful_12168
  · exact not_square_12167
  · exact not_square_12168

/-- 对题目陈述的直接回答：否 -/
theorem jsp_301_answer_no :
    ¬ ∀ a b : Nat, a > 0 → b = a + 1 → Powerful a → Powerful b → IsSquare a ∨ IsSquare b := by
  intro h
  have hc := h 12167 12168 (by decide) (by decide) powerful_12167 powerful_12168
  rcases hc with hs | hs
  · exact not_square_12167 hs
  · exact not_square_12168 hs

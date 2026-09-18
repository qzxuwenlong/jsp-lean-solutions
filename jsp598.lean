-- =====================================================================
-- JSP-000598 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交（草稿 v1）
--
-- 题目：Can two distinct central binomial coefficients have exactly the
--       same prime divisors?
--       （是否存在两个不同的中心二项式系数，其素因子集合完全相同？）
-- 答案：是。反例：
--         C(174,87) = 1446307705450557558142084756547133980616347954754720
--         C(176,88) = 5752360192132899378974200736267010150178656638229000
--       二者的素因子集完全相同（28 个素数）：
--         {2,3,5,7,11,13,19,23,31,47,53,89,97,101,103,107,109,113,
--          127,131,137,139,149,151,157,163,167,173}
--       但素因子指数不同（如 2^5 对 2^3、5^1 对 5^3），故二者不同。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp598.lean （驱动见 run-lean.js）
-- 全部计算性证明由 `decide` 在内核 VM 中完成（机器逐行核验）。
-- 定义与引理层复用自 jsp301/307（已验证通过本地内核）。
-- =====================================================================

set_option maxRecDepth 1000000

-- ---------------------------------------------------------------------
-- 定义
-- ---------------------------------------------------------------------

/-- 素数（Mathlib 的 Nat.Prime 等价定义，避免依赖 Mathlib） -/
def Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- 中心二项式系数 C(2n,n)。标准乘积公式：
    C(2n,n) = (n+1)(n+2)···(2n)/n! = ∏_{i=0}^{n-1} (n+1+i)/(i+1)。
    每步先乘后除，中间值保持整数（逐段恰为组合数），远小于 (2n)!，
    使内核 VM 可计算 10^51 量级的 C(174,87)、C(176,88)。 -/
def centralBinom (n : Nat) : Nat :=
  (List.range n).foldl (fun a i => (a * (n + 1 + i)) / (i + 1)) 1

/-- 列表乘积 -/
def listProd : List Nat → Nat
  | [] => 1
  | x :: xs => x * listProd xs

-- ---------------------------------------------------------------------
-- 自建列表全称判定与素性检查（来自 jsp301/307，已通过内核核验）
-- ---------------------------------------------------------------------

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
-- 反例数值与素因子集合
-- ---------------------------------------------------------------------

/-- C(174,87) 的精确值 -/
def c174_87 : Nat := 1446307705450557558142084756547133980616347954754720

/-- C(176,88) 的精确值 -/
def c176_88 : Nat := 5752360192132899378974200736267010150178656638229000

/-- 共同素因子集合（28 个素数） -/
def S : List Nat := [2,3,5,7,11,13,19,23,31,47,53,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173]

/-- C(174,87) 的素因子展开（按指数展开为列表）：
    2^5 · 3 · 5 · 7 · 11^2 · 13^2 · 19 · 23 · 31 · 47 · 53 · 89 · 97 · 101 · 103 · 107 · 109 · 113 · 127 · 131 · 137 · 139 · 149 · 151 · 157 · 163 · 167 · 173 -/
def F1 : List Nat := [2,2,2,2,2,3,5,7,11,11,13,13,19,23,31,47,53,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173]

/-- C(176,88) 的素因子展开（按指数展开为列表）：
    2^3 · 3 · 5^3 · 7^2 · 11 · 13^2 · 19 · 23 · 31 · 47 · 53 · 89 · 97 · 101 · 103 · 107 · 109 · 113 · 127 · 131 · 137 · 139 · 149 · 151 · 157 · 163 · 167 · 173 -/
def F2 : List Nat := [2,2,2,3,5,5,5,7,7,11,13,13,19,23,31,47,53,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173]

-- ---------------------------------------------------------------------
-- 计算核验（内核 VM 逐行验证大数事实）
-- ---------------------------------------------------------------------

/-- centralBinom 87 = C(174,87) 的精确值 -/
theorem cb_87 : centralBinom 87 = c174_87 := by decide

/-- centralBinom 88 = C(176,88) 的精确值 -/
theorem cb_88 : centralBinom 88 = c176_88 := by decide

/-- 素因子展开的乘积等于 C(174,87) -/
theorem factor_c1 : listProd F1 = c174_87 := by decide

/-- 素因子展开的乘积等于 C(176,88) -/
theorem factor_c2 : listProd F2 = c176_88 := by decide

/-- F1 的元素都在 S 中 -/
theorem sub_F1_S : ∀ x : Nat, x ∈ F1 → x ∈ S := by decide

/-- F2 的元素都在 S 中 -/
theorem sub_F2_S : ∀ x : Nat, x ∈ F2 → x ∈ S := by decide

/-- S 中每个元素都是素数（通过 primeCheck 判定） -/
theorem prime_check_S : ∀ x : Nat, x ∈ S → primeCheck x = true := by decide

/-- S 中每个元素 ≥ 2 -/
theorem S_ge_two : ∀ x : Nat, x ∈ S → x ≥ 2 := by decide

/-- S 中元素整除 c176_88（有界成员判定） -/
theorem mem_bound_dvd_c2 : ∀ p : Nat, p ∈ S → p ∣ c176_88 := by decide

/-- S 中元素整除 c174_87（有界成员判定） -/
theorem mem_bound_dvd_c1 : ∀ p : Nat, p ∈ S → p ∣ c174_87 := by decide

-- ---------------------------------------------------------------------
-- 欧几里得引理（素数整除乘积 → 整除某因子）
-- ---------------------------------------------------------------------

/-- 欧几里得引理：素数 p 整除 a·b 则整除 a 或 b。
    证明：若 p ∤ a，则 gcd p a = 1（p 素数的约数只有 1 与 p），
    由 Nat.Coprime.dvd_of_dvd_mul_left 消去 a。 -/
theorem prime_dvd_mul {p a b : Nat} (hp : Prime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · right
    have hcop : p.Coprime a := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have hgdp : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
      have hg1p : Nat.gcd p a = 1 ∨ Nat.gcd p a = p := hp.2 (Nat.gcd p a) hgdp
      rcases hg1p with h1 | hp'
      · exact h1
      · exfalso
        apply hpa
        simpa [hp'] using Nat.gcd_dvd_right p a
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop h

/-- 素数 p 整除素数 q 则 p = q -/
theorem prime_dvd_prime {p q : Nat} (hp : Prime p) (hq : Prime q) (h : p ∣ q) : p = q := by
  rcases hq.2 p h with h1 | hpq
  · exfalso
    have hp2 : p ≥ 2 := hp.1
    omega
  · exact hpq

/-- 素数 p 整除 q^k（k > 0）则整除 q -/
theorem prime_dvd_pow {p q : Nat} (hp : Prime p) (k : Nat) (hk : k > 0) (h : p ∣ q ^ k) : p ∣ q := by
  induction k with
  | zero =>
      exfalso
      have hz : False := by simpa using hk
      exact hz
  | succ k ih =>
      have h' : p ∣ q ^ k * q := by simpa [Nat.pow_succ] using h
      rcases prime_dvd_mul hp h' with hqk | hq
      · by_cases hk0 : k = 0
        · subst k
          exfalso
          have hp1 : p = 1 := Nat.eq_one_of_dvd_one hqk
          have hp2 : p ≥ 2 := hp.1
          omega
        · exact ih (Nat.pos_of_ne_zero hk0) hqk
      · exact hq

/-- 素数 p 整除素数幂 q^k（k > 0）则 p = q -/
theorem prime_dvd_prime_pow {p q : Nat} (hp : Prime p) (hq : Prime q) (k : Nat) (hk : k > 0) (h : p ∣ q ^ k) : p = q := by
  exact prime_dvd_prime hp hq (prime_dvd_pow hp k hk h)

/-- 素数 p 整除列表乘积，则整除其中某个元素 -/
theorem dvd_listProd_elim {p : Nat} (hp : Prime p) :
    ∀ l : List Nat, p ∣ listProd l → ∃ q : Nat, q ∈ l ∧ p ∣ q := by
  intro l
  induction l with
  | nil =>
      intro h
      have hp1 : p = 1 := Nat.eq_one_of_dvd_one (by simpa [listProd] using h)
      exfalso
      have hp2 : p ≥ 2 := hp.1
      omega
  | cons x xs ih =>
      intro h
      have h' : p ∣ x * listProd xs := by simpa [listProd] using h
      rcases prime_dvd_mul hp h' with hpx | hpxs
      · exact ⟨x, by simp, hpx⟩
      · rcases ih hpxs with ⟨q, hqm, hqd⟩
        exact ⟨q, by simp [hqm], hqd⟩

-- ---------------------------------------------------------------------
-- 素因子归属：C(174,87) / C(176,88) 的任一素因子都在 S 中
-- ---------------------------------------------------------------------

theorem prime_member_of_dvd_c1 {p : Nat} (hp : Prime p) (h : p ∣ c174_87) : p ∈ S := by
  have hf : p ∣ listProd F1 := by simpa [factor_c1] using h
  rcases dvd_listProd_elim hp F1 hf with ⟨q, hqm, hqd⟩
  have hqS : q ∈ S := sub_F1_S q hqm
  have hqP : Prime q := primeCheck_sound (S_ge_two q hqS) (prime_check_S q hqS)
  have hpq : p = q := prime_dvd_prime hp hqP hqd
  simpa [hpq] using hqS

theorem prime_member_of_dvd_c2 {p : Nat} (hp : Prime p) (h : p ∣ c176_88) : p ∈ S := by
  have hf : p ∣ listProd F2 := by simpa [factor_c2] using h
  rcases dvd_listProd_elim hp F2 hf with ⟨q, hqm, hqd⟩
  have hqS : q ∈ S := sub_F2_S q hqm
  have hqP : Prime q := primeCheck_sound (S_ge_two q hqS) (prime_check_S q hqS)
  have hpq : p = q := prime_dvd_prime hp hqP hqd
  simpa [hpq] using hqS

-- ---------------------------------------------------------------------
-- 主定理（对题目陈述的构造性回答：是）
-- ---------------------------------------------------------------------

/-- 存在两个不同的中心二项式系数 C(2n,n) 与 C(2m,m)（n=87, m=88），
    对每个素数 p：p 整除其中一个当且仅当整除另一个，
    即二者的素因子集合完全相同。 -/
theorem jsp_598_answer :
    ∃ n m : Nat, n ≠ m ∧
      ∀ p : Nat, Prime p → (p ∣ centralBinom n ↔ p ∣ centralBinom m) := by
  refine ⟨87, 88, by decide, ?_⟩
  intro p hp
  constructor
  · intro h
    have h1 : p ∣ c174_87 := by simpa [cb_87] using h
    have hS : p ∈ S := prime_member_of_dvd_c1 hp h1
    have h2 : p ∣ c176_88 := mem_bound_dvd_c2 p hS
    simpa [cb_88] using h2
  · intro h
    have h1 : p ∣ c176_88 := by simpa [cb_88] using h
    have hS : p ∈ S := prime_member_of_dvd_c2 hp h1
    have h2 : p ∣ c174_87 := mem_bound_dvd_c1 p hS
    simpa [cb_87] using h2

import Std

set_option maxRecDepth 1000000

-- =====================================================================
-- JSP-000234 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Can the integers be covered by residue classes whose moduli are
--       all one less than a prime?
--       （能否用模数均为素数减一的剩余类覆盖所有整数？）
-- 回答：可以。11 个剩余类（模数两两不同、每个模数加一为素数）。
--       周期 lcm = 2880（每个模数整除 2880），0..2879 全部被覆盖。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp234.lean
-- 覆盖性由 11 个闭项分块定理（每块 270 个整数）在内核 VM 中 decide 验证。
-- =====================================================================


-- ---------------------------------------------------------------------
-- 覆盖定义：17 个剩余类的析取
-- ---------------------------------------------------------------------

def coversProp (x : Nat) : Prop := x % 2 = 0 ∨ x % 4 = 1 ∨ x % 6 = 3 ∨ x % 12 = 11 ∨ x % 18 = 7 ∨ x % 36 = 19 ∨ x % 72 = 31 ∨ x % 16 = 3 ∨ x % 96 = 43 ∨ x % 192 = 187 ∨ x % 576 = 283

-- 分块定理（闭项 decide：每块 270 个整数）

theorem coversProp_off_0 : ∀ x : Nat, x < 270 → coversProp (0 * 270 + x) := by
  decide

theorem coversProp_off_1 : ∀ x : Nat, x < 270 → coversProp (1 * 270 + x) := by
  decide

theorem coversProp_off_2 : ∀ x : Nat, x < 270 → coversProp (2 * 270 + x) := by
  decide

theorem coversProp_off_3 : ∀ x : Nat, x < 270 → coversProp (3 * 270 + x) := by
  decide

theorem coversProp_off_4 : ∀ x : Nat, x < 270 → coversProp (4 * 270 + x) := by
  decide

theorem coversProp_off_5 : ∀ x : Nat, x < 270 → coversProp (5 * 270 + x) := by
  decide

theorem coversProp_off_6 : ∀ x : Nat, x < 270 → coversProp (6 * 270 + x) := by
  decide

theorem coversProp_off_7 : ∀ x : Nat, x < 270 → coversProp (7 * 270 + x) := by
  decide

theorem coversProp_off_8 : ∀ x : Nat, x < 270 → coversProp (8 * 270 + x) := by
  decide

theorem coversProp_off_9 : ∀ x : Nat, x < 270 → coversProp (9 * 270 + x) := by
  decide

theorem coversProp_off_10 : ∀ x : Nat, x < 270 → coversProp (10 * 270 + x) := by
  decide

/-- 2880 以内全部覆盖 -/
theorem coversProp_all_lt : ∀ x : Nat, x < 2880 → coversProp x := by
  intro x hx
by_cases h1440 : x < 1440
  · by_cases h720 : x < 720
      · by_cases h360 : x < 360
          · by_cases h180 : x < 180
              ·       have hxq : x < 270 := by omega
                      exact coversProp_off_0 x hxq
                
              · by_cases h270 : x < 270
                  ·       have hxq : x < 270 := by omega
                          exact coversProp_off_0 x hxq
                    
                  ·       have hsub : x - 1 * 270 < 270 := by omega
                          have hsplit : x = 1 * 270 + (x - 1 * 270) := by omega
                          have hb := coversProp_off_1 (x - 1 * 270) hsub
                          rwa [← hsplit] at hb
                    
                
            
          · by_cases h540 : x < 540
              ·       have hsub : x - 1 * 270 < 270 := by omega
                      have hsplit : x = 1 * 270 + (x - 1 * 270) := by omega
                      have hb := coversProp_off_1 (x - 1 * 270) hsub
                      rwa [← hsplit] at hb
                
              ·       have hsub : x - 2 * 270 < 270 := by omega
                      have hsplit : x = 2 * 270 + (x - 2 * 270) := by omega
                      have hb := coversProp_off_2 (x - 2 * 270) hsub
                      rwa [← hsplit] at hb
                
            
        
      · by_cases h1080 : x < 1080
          · by_cases h900 : x < 900
              · by_cases h810 : x < 810
                  ·       have hsub : x - 2 * 270 < 270 := by omega
                          have hsplit : x = 2 * 270 + (x - 2 * 270) := by omega
                          have hb := coversProp_off_2 (x - 2 * 270) hsub
                          rwa [← hsplit] at hb
                    
                  ·       have hsub : x - 3 * 270 < 270 := by omega
                          have hsplit : x = 3 * 270 + (x - 3 * 270) := by omega
                          have hb := coversProp_off_3 (x - 3 * 270) hsub
                          rwa [← hsplit] at hb
                    
                
              ·       have hsub : x - 3 * 270 < 270 := by omega
                      have hsplit : x = 3 * 270 + (x - 3 * 270) := by omega
                      have hb := coversProp_off_3 (x - 3 * 270) hsub
                      rwa [← hsplit] at hb
                
            
          · by_cases h1260 : x < 1260
              ·       have hsub : x - 4 * 270 < 270 := by omega
                      have hsplit : x = 4 * 270 + (x - 4 * 270) := by omega
                      have hb := coversProp_off_4 (x - 4 * 270) hsub
                      rwa [← hsplit] at hb
                
              · by_cases h1350 : x < 1350
                  ·       have hsub : x - 4 * 270 < 270 := by omega
                          have hsplit : x = 4 * 270 + (x - 4 * 270) := by omega
                          have hb := coversProp_off_4 (x - 4 * 270) hsub
                          rwa [← hsplit] at hb
                    
                  ·       have hsub : x - 5 * 270 < 270 := by omega
                          have hsplit : x = 5 * 270 + (x - 5 * 270) := by omega
                          have hb := coversProp_off_5 (x - 5 * 270) hsub
                          rwa [← hsplit] at hb
                    
                
            
        
    
  · by_cases h2160 : x < 2160
      · by_cases h1800 : x < 1800
          · by_cases h1620 : x < 1620
              ·       have hsub : x - 5 * 270 < 270 := by omega
                      have hsplit : x = 5 * 270 + (x - 5 * 270) := by omega
                      have hb := coversProp_off_5 (x - 5 * 270) hsub
                      rwa [← hsplit] at hb
                
              ·       have hsub : x - 6 * 270 < 270 := by omega
                      have hsplit : x = 6 * 270 + (x - 6 * 270) := by omega
                      have hb := coversProp_off_6 (x - 6 * 270) hsub
                      rwa [← hsplit] at hb
                
            
          · by_cases h1980 : x < 1980
              · by_cases h1890 : x < 1890
                  ·       have hsub : x - 6 * 270 < 270 := by omega
                          have hsplit : x = 6 * 270 + (x - 6 * 270) := by omega
                          have hb := coversProp_off_6 (x - 6 * 270) hsub
                          rwa [← hsplit] at hb
                    
                  ·       have hsub : x - 7 * 270 < 270 := by omega
                          have hsplit : x = 7 * 270 + (x - 7 * 270) := by omega
                          have hb := coversProp_off_7 (x - 7 * 270) hsub
                          rwa [← hsplit] at hb
                    
                
              ·       have hsub : x - 7 * 270 < 270 := by omega
                      have hsplit : x = 7 * 270 + (x - 7 * 270) := by omega
                      have hb := coversProp_off_7 (x - 7 * 270) hsub
                      rwa [← hsplit] at hb
                
            
        
      · by_cases h2520 : x < 2520
          · by_cases h2340 : x < 2340
              ·       have hsub : x - 8 * 270 < 270 := by omega
                      have hsplit : x = 8 * 270 + (x - 8 * 270) := by omega
                      have hb := coversProp_off_8 (x - 8 * 270) hsub
                      rwa [← hsplit] at hb
                
              · by_cases h2430 : x < 2430
                  ·       have hsub : x - 8 * 270 < 270 := by omega
                          have hsplit : x = 8 * 270 + (x - 8 * 270) := by omega
                          have hb := coversProp_off_8 (x - 8 * 270) hsub
                          rwa [← hsplit] at hb
                    
                  ·       have hsub : x - 9 * 270 < 270 := by omega
                          have hsplit : x = 9 * 270 + (x - 9 * 270) := by omega
                          have hb := coversProp_off_9 (x - 9 * 270) hsub
                          rwa [← hsplit] at hb
                    
                
            
          · by_cases h2700 : x < 2700
              ·       have hsub : x - 9 * 270 < 270 := by omega
                      have hsplit : x = 9 * 270 + (x - 9 * 270) := by omega
                      have hb := coversProp_off_9 (x - 9 * 270) hsub
                      rwa [← hsplit] at hb
                
              ·       have hsub : x - 10 * 270 < 270 := by omega
                      have hsplit : x = 10 * 270 + (x - 10 * 270) := by omega
                      have hb := coversProp_off_10 (x - 10 * 270) hsub
                      rwa [← hsplit] at hb
                
            
        
    


/-- 周期引理：覆盖性以 2880 为周期 -/
theorem coversProp_period : ∀ x : Nat, coversProp x ↔ coversProp (x % 2880) := by
  intro x
  unfold coversProp
  rw [← Nat.mod_mod_of_dvd x (by decide : 2 ∣ 2880),
      ← Nat.mod_mod_of_dvd x (by decide : 4 ∣ 2880),
      ← Nat.mod_mod_of_dvd x (by decide : 6 ∣ 2880),
      ← Nat.mod_mod_of_dvd x (by decide : 12 ∣ 2880),
      ← Nat.mod_mod_of_dvd x (by decide : 18 ∣ 2880),
      ← Nat.mod_mod_of_dvd x (by decide : 36 ∣ 2880),
      ← Nat.mod_mod_of_dvd x (by decide : 72 ∣ 2880),
      ← Nat.mod_mod_of_dvd x (by decide : 16 ∣ 2880),
      ← Nat.mod_mod_of_dvd x (by decide : 96 ∣ 2880),
      ← Nat.mod_mod_of_dvd x (by decide : 192 ∣ 2880),
      ← Nat.mod_mod_of_dvd x (by decide : 576 ∣ 2880)]

/-- 所有整数被覆盖 -/
theorem covers_all : ∀ x : Nat, coversProp x := by
  intro x
  have hper := coversProp_period x
  rw [hper]
  have hlt : x % 2880 < 2880 := Nat.mod_lt x (by decide : 2880 > 0)
  exact coversProp_all_lt (x % 2880) hlt

-- ---------------------------------------------------------------------
-- 素数（与 JSP-598 相同的基础设施）
-- ---------------------------------------------------------------------

/-- 素数 -/
def Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

def listAll (f : Nat → Bool) (l : List Nat) : Bool :=
  List.foldl (fun acc x => acc && f x) true l

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

/-- 素性检查（有界、可判定） -/
def primeCheck (p : Nat) : Bool :=
  decide (2 ≤ p) && listAll (fun m => decide (m = 1) || decide (m = p) || Bool.not (decide (m ∣ p))) (List.range (p + 1))

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


theorem prime_3 : Prime 3 := primeCheck_sound (by decide) (by decide)

theorem prime_5 : Prime 5 := primeCheck_sound (by decide) (by decide)

theorem prime_7 : Prime 7 := primeCheck_sound (by decide) (by decide)

theorem prime_13 : Prime 13 := primeCheck_sound (by decide) (by decide)

theorem prime_19 : Prime 19 := primeCheck_sound (by decide) (by decide)

theorem prime_37 : Prime 37 := primeCheck_sound (by decide) (by decide)

theorem prime_73 : Prime 73 := primeCheck_sound (by decide) (by decide)

theorem prime_17 : Prime 17 := primeCheck_sound (by decide) (by decide)

theorem prime_97 : Prime 97 := primeCheck_sound (by decide) (by decide)

theorem prime_193 : Prime 193 := primeCheck_sound (by decide) (by decide)

theorem prime_577 : Prime 577 := primeCheck_sound (by decide) (by decide)

-- ---------------------------------------------------------------------
-- 主定理（对题目陈述的肯定回答：可以）
-- ---------------------------------------------------------------------

/-- 存在 11 个剩余类（模数两两不同、每个模数加一为素数）覆盖所有整数 -/
theorem jsp_234 :
    ∃ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
       m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 : Nat,
      Prime (m1 + 1) ∧ Prime (m2 + 1) ∧ Prime (m3 + 1) ∧ Prime (m4 + 1) ∧
      Prime (m5 + 1) ∧ Prime (m6 + 1) ∧ Prime (m7 + 1) ∧ Prime (m8 + 1) ∧
      Prime (m9 + 1) ∧ Prime (m10 + 1) ∧ Prime (m11 + 1) ∧
      List.Nodup [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11] ∧
      (∀ x : Nat, x % m1 = a1 ∨ x % m2 = a2 ∨ x % m3 = a3 ∨ x % m4 = a4 ∨
                  x % m5 = a5 ∨ x % m6 = a6 ∨ x % m7 = a7 ∨ x % m8 = a8 ∨
                  x % m9 = a9 ∨ x % m10 = a10 ∨ x % m11 = a11) := by
  refine ⟨0, 1, 3, 11, 7, 19, 31, 3, 43, 187, 283, 2, 4, 6, 12, 18, 36, 72, 16, 96, 192, 576, ?_, ?_, ?_⟩
  · simpa using prime_3
  · simpa using prime_5
  · simpa using prime_7
  · simpa using prime_13
  · simpa using prime_19
  · simpa using prime_37
  · simpa using prime_73
  · simpa using prime_17
  · simpa using prime_97
  · simpa using prime_193
  · simpa using prime_577
  · decide
  · intro x
    simpa [coversProp] using covers_all x

-- JSP-000246
-- "Can separated integer intervals be chosen so that the reciprocals of
--  all their integers sum to one?"
--
-- Answer: YES.  Construction: the separated intervals [2,3] and [6,6]
-- (single point intervals are allowed), with
--   1/2 + 1/3 + 1/6 = 1.
--
-- We formalize the reciprocal-sum condition in its exact integer form:
-- multiplying by the common denominator N = 6, the condition
--   Σ_{k ∈ [a,b]} 1/k  +  Σ_{k ∈ [c,d]} 1/k  =  1
-- is equivalent to
--   Σ_{k ∈ [a,b]} N/k  +  Σ_{k ∈ [c,d]} N/k  =  N
-- (here every k divides N, so N/k is the exact numerator of 1/k scaled by N).

def rangeSum (N a b : Nat) : Nat :=
  (List.range (b + 1 - a)).foldl (fun acc k => acc + N / (a + k)) 0

theorem jsp246 : ∃ (N a b c d : Nat),
    a ≤ b ∧ c ≤ d ∧ b < c ∧
    rangeSum N a b + rangeSum N c d = N := by
  refine ⟨6, 2, 3, 6, 6, ?_, ?_, ?_, ?_⟩
  · decide            -- 2 ≤ 3  (interval [2,3] is valid)
  · decide            -- 6 ≤ 6  (interval [6,6] is valid)
  · decide            -- 3 < 6  (the two intervals are separated)
  · decide            -- 6/2 + 6/3 + 6/6 = 6, i.e. 3 + 2 + 1 = 6

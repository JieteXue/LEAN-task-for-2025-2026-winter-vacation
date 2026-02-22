import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
variable (a : ℕ → ℝ)

def EventuallyStable : Prop :=
  ∃ N, ∀ n ≥ N, a n = a N

def has_strictly_decreasing_subseq : Prop :=
  ∃ m : ℕ → ℕ, StrictMono m ∧ StrictAnti (a ∘ m)

-- 引理 1: 如果非增序列不是最终稳定的，那么对于任意项 a_N，后面总能找到一个更小的项
lemma exists_smaller_of_not_stable (h_anti : Antitone a) (h_not_stable : ¬ EventuallyStable a) :
  ∀ N, ∃ n > N, a n < a N := by
  intro N
  by_contra h_contra
  push_neg at h_contra
  apply h_not_stable
  use N
  intro n hn
  rcases eq_or_lt_of_le hn with rfl | h_lt
  · rfl
  · have h1 : a n ≤ a N := h_anti hn
    have h2 : a n ≥ a N := h_contra n h_lt
    linarith

-- 引理 2: 如果不稳定，则存在严格递减子序列
lemma subseq_of_not_stable (h_anti : Antitone a) (h_not_stable : ¬ EventuallyStable a) :
  has_strictly_decreasing_subseq a := by
  -- 利用引理 1 和选择公理 (choose)，构造一个函数 next_idx
  -- 给定任意 k，next_idx k 会返回一个比 k 大且值更小的下标
  have h_step := exists_smaller_of_not_stable a h_anti h_not_stable
  choose next_idx h_next using h_step

  -- 递归定义子序列的下标 m
  -- m(0) = 0
  -- m(n+1) = next_idx(m(n))
  let m : ℕ → ℕ := Nat.rec 0 (fun _ k => next_idx k)

  refine ⟨m, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    exact (h_next (m n)).1
  · apply strictAnti_nat_of_succ_lt
    intro n
    exact (h_next (m n)).2

theorem question_3 (h_anti : Antitone a) :
  Xor' (EventuallyStable a) (has_strictly_decreasing_subseq a) := by
  rw [xor_iff_iff_not]
  constructor

  -- 方向 (⇒): 如果稳定，则不存在严格递减子序列
  · rintro ⟨N, hN⟩ ⟨m, hm_mono, ham_anti⟩
    let k := N
    have hk_ge : m k ≥ N := StrictMono.id_le hm_mono k

    have val_k     : a (m k)     = a N := hN (m k) hk_ge
    have val_succ  : a (m (k+1)) = a N := by
      apply hN
      apply le_trans hk_ge
      apply le_of_lt (hm_mono (Nat.lt_succ_self k))
    have strict : a (m (k+1)) < a (m k) := ham_anti (Nat.lt_succ_self k)
    linarith

  -- 方向 (⇐): 如果不存在严格递减子序列，则必须稳定
  -- (这等价于：如果不稳定，则存在严格递减子序列，即引理 2)
  · intro h_no_subseq
    by_contra h_not_stable
    have h_has_subseq := subseq_of_not_stable a h_anti h_not_stable
    contradiction

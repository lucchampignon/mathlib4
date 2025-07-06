/-
Copyright (c) 2025 Luc Champignon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luc Champignon
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Theorem of Van der Waerden on arithmetic progressions

In this file we prove the theorem of Van der Waerden on arithmetic progressions. The demonstration
is adapted from the following article.

## References

R. L. Graham and B. L. Rothschild, Proc. Amer. Math. Soc. 42 (1974), 385-386,
DOI: 10.1090/S0002-9939-1974-0329917-8
https://www.ams.org/journals/proc/1974-042-02/S0002-9939-1974-0329917-8/S0002-9939-1974-0329917-8.pdf
-/

open BigOperators
open Finset

private def S (l m : Nat) : Prop := ∀ r : Nat, ∃ N : Nat, ∀ C : Nat → Fin r,
  ∃ a : Nat, ∃ d : Nat → Nat, ∃ q : Nat → Fin r, (∀ i : Nat, d i ≠ 0) ∧
  (a + (l + 1) * ∑ x in range (m + 1), d x < N) ∧
  (∀ I : Nat → Nat, ∀ n : Nat, n ≤ m + 1 →
  (∀ i : Nat, (i < n → I i = l + 1) ∧ (n ≤ i → i ≤ m → I i ≤ l)) →
  C (a + ∑ x in range (m + 1), d x * I x) = q n) ∧ 1 ≤ N

private lemma aux {r : Nat} (F : Nat → Fin r) : ∃ u v : Nat,
    u < v ∧ u < r + 1 ∧ v < r + 1 ∧ F u = F v := by
  obtain ⟨u, v, h1⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun u : Fin (r + 1) ↦ F u) (by simp [Fintype.card_fin])
  rcases lt_or_gt_of_ne (Fin.val_ne_iff.2 h1.1) with h2 | h3
  · use u.1, v.1, h2, u.2, v.2, h1.2
  use v.1, u.1, h3, v.2, u.2, Eq.symm h1.2

private lemma sum_if {f g : Nat → Nat} {m : Nat} : (∑ x in range (m + 1),
    if x < m then f x else g x) = (∑ x in range m, f x) + g m := by
  simp [sum_range_succ]
  apply sum_congr rfl
  intro _ h1
  simp at h1
  simp [h1]

private lemma sum_if_2 {u v : Nat} {f g : Nat → Nat} (h1 : u < v) :
    (∑ x in range u, f x + ∑ x in range v, if x < u then 0 else g x) =
    ∑ x in range v, if x < u then f x else g x := by
  have h1 {h : Nat → Nat} : ∑ x in range v, h x =
    ∑ x in range u, h x + ∑ x in ((range v) \ (range u)), h x := by
    rw [ ← sum_disjUnion Finset.disjoint_sdiff]
    exact sum_congr (by simp [disjUnion_eq_union, le_of_lt h1]) (by simp)
  rw [h1, h1, ← add_assoc, ← sum_add_distrib]
  congr 1
  repeat
    apply sum_congr rfl
    intro _ h2
    simp at h2
    split <;> omega

private lemma n1 (l m : Nat) : S l 0 → S l m → S l (m + 1) := by
  intro h h0 r
  obtain ⟨M, h1⟩ := h0 r
  obtain ⟨M', h2⟩ := h (r ^ M)
  use M' * M + M
  intro C
  let C' := fun k ↦ finFunctionFinEquiv (fun j : Fin M ↦ C (k * M + j))
  obtain ⟨a', d', q', h3⟩ := h2 C'
  simp at h3
  obtain ⟨a, d, q, h4⟩ := h1 (fun k ↦ C (a' * M + k))
  let d'' := fun i ↦ if i < m + 1 then d i else d' 0 * M
  let q'' := fun k ↦ if k < m + 2 then q k else C (a' * M + a +
    ∑ x in range (m + 2), if x < m + 1 then d x * (l + 1) else d' 0 * M * (l + 1))
  use a' * M + a, d'', q''
  simp
  constructor
  · exact fun i ↦ by simp [mt ite_eq_iff'.1, h4.1 i, Nat.one_le_iff_ne_zero.1 h4.2.2.2, h3.1 0]
  constructor
  · calc
    (a' * M + a + (l + 1) * ∑ x in range (m + 2), if x < m + 1 then d x else d' 0 * M)
    _ = (a' * M + a + (l + 1) * (∑ x in range (m + 1), d x + d' 0 * M)) := by simp [sum_if]
    _ = (a' + (l + 1) * d' 0) * M + (a + (l + 1) * (∑ x in range (m + 1), d x)) := by
      simp_arith [add_mul _ _ M, mul_add (l + 1), mul_assoc]
    _ < (a' + (l + 1) * d' 0) * M + M := by simp [h4.2.1]
    _ ≤  M' * M + M := by simp [Nat.mul_le_mul_right M (le_of_lt h3.2.1)]
  constructor
  · intro I n _ h5
    split
    case inl h6 =>
      have h7 : ∀ i : ℕ, (i < n → I i = l + 1) ∧ (n ≤ i → i ≤ m → I i ≤ l) :=
        fun i ↦ ⟨And.left (h5 i), fun h h' ↦ And.right (h5 i) h (Nat.le_step h')⟩
      have h8 : ∀ y : Nat, y ≤ l →  C' (a' + d' 0 * y) = q' 0 := by
        intro y h9
        apply h3.2.2.1 (fun _ ↦ y) 0 zero_le_one
        simp [h9]
      have h10 : C' (a' + d' 0 * I (m + 1)) = C' (a' + d' 0 * 0) := by
        rw [h8 (I (m + 1)) (And.right (h5 (m + 1))
          (Nat.lt_add_one_iff.1 h6) (le_refl (m + 1))), h8 0 (zero_le l)]
      simp at h10
      have h11 : ∀ x ∈ range (m + 1), d x * I x ≤ d x * (l + 1) := by
        intro x h12
        apply Nat.mul_le_mul_left
        rcases le_or_lt n x with h13 | h14
        · exact Nat.le_step (And.right (h5 x) h13 (le_of_lt (mem_range.1 h12)))
        · exact le_of_eq (And.left (h5 x) h14)
      have h15 : a + ∑ x in range (m + 1), d x * I x < M := by calc
        a + ∑ x in range (m + 1), d x * I x
        _ ≤ a + ∑ x in range (m + 1), d x * (l  + 1) := by simp [sum_le_sum h11]
        _ = a + (l + 1) * ∑ x in range (m + 1), d x := by
          simp [mul_comm, mul_sum (range (m + 1)) d (l + 1)]
        _ < M := h4.2.1
      rw [← h4.2.2.1 I n (Nat.lt_add_one_iff.1 h6) h7, ← congr_fun h10 (⟨ _ , h15⟩ : Fin M)]
      congr 1
      simp [sum_if, add_mul _ _ M]
      simp_arith [mul_assoc, mul_comm M]
    case inr h16 =>
      congr 2
      apply sum_congr rfl
      intro x h17
      rw [And.left (h5 x) (lt_of_lt_of_le (mem_range.1 h17) (le_of_not_lt h16))]
  calc
    1 ≤ M := h4.2.2.2
    _ ≤ M' * M + M := by simp

private lemma n2 (l : Nat) : (∀ m, S l m) → S (l + 1) 0 := by
  intro h1 r
  obtain ⟨N, h2⟩ := h1 r r
  use 2 * N
  intro C
  obtain ⟨a, d, q, h3⟩ := h2 C
  obtain ⟨u, v, h4⟩ := aux q
  use a + ∑ x in range u, d x * (l + 1),
    fun n ↦ if n = 0 then ∑ x in range v, if x < u then 0 else d x else 1,
    fun k ↦ if k = 0 then q u else C (a + ∑ x in range u, d x * (l + 1) +
      (∑ x in range v, if x < u then 0 else d x) * (l + 2))
  constructor
  · rintro _
    split
    · simp [mt sum_eq_zero_iff.1]
      use u, le_refl u, h4.1, h3.1 u
    exact one_ne_zero
  simp
  constructor
  · calc
    a + ∑ x in range u, (d x * (l + 1)) +
      (l + 1 + 1) * (∑ x in range v, if x < u then 0 else d x)
    _ = a + (l + 1) * ∑ x in range u, d x +
      (l + 1 + 1) * ∑ x in range v, if x < u then 0 else d x := by
        simp [mul_sum (range u) d (l + 1)]
        simp [mul_comm]
    _ = a + (l + 1) * ∑ x in range u, d x +
      (l + 1) * (∑ x in range v, if x < u then 0 else d x)
      + (∑ x in range v, if x < u then 0 else d x) := by
        rw [add_mul (l + 1) 1 (∑ x in range v, if x < u then 0 else d x), one_mul]
        omega
    _ = a + (l + 1) * (∑ x in range u, d x + ∑ x in range v, if x < u then 0 else d x)
      + (∑ x in range v, if x < u then 0 else d x) := by simp [mul_add, add_assoc]
    _ = a + (l + 1) * (∑ x in range v, d x) +
      (∑ x in range v, if x < u then 0 else d x) := by simp [sum_if_2 h4.1]
    _ ≤ a + (l + 1) * (∑ x in range (r + 1), d x) +
      (∑ x in range v, if x < u then 0 else d x) := by
        simp [sum_le_sum_of_subset (range_subset.2 (le_of_lt h4.2.2.1))]
    _ < N + (∑ x in range v, if x < u then 0 else d x) := by simp [h3.2.1]
    _ ≤ N + (∑ x in range v, d x) := by
        simp [add_assoc]
        apply sum_le_sum
        intro _ _
        split <;> simp
    _ ≤ N + (∑ x in range (r + 1), d x) := by
        simp [sum_le_sum_of_subset (range_subset.2 (le_of_lt h4.2.2.1))]
    _ ≤ N + a + (∑ x in range (r + 1), d x) := by simp
    _ ≤ N + a + (l + 1) * (∑ x in range (r + 1), d x) := by simp [add_mul]
    _ < N + N := by simp [add_assoc, h3.2.1]
    _ = 2 * N := by omega
  constructor
  · intro I x _ h5
    split
    case inl h6 =>
      rw [h6] at h5
      rcases eq_or_lt_of_le (And.right (h5 0) le_rfl rfl) with h7 | _
      · let I' := fun x ↦ if x < v then l + 1 else 0
        have h8 : ∀ i : ℕ, (i < v → I' i = l + 1) ∧ (v ≤ i → i ≤ r → I' i ≤ l) := by
          simp
          intro
          constructor
          all_goals (try split) <;> omega
        rw [h4.2.2.2, h7, ← h3.2.2.1 I' v (le_of_lt h4.2.2.1) h8]
        simp [add_assoc, sum_mul, ← sum_if_2 h4.2.2.1, sum_if_2 h4.1]
      let I'' := fun x ↦ if x < v then if x < u then l + 1 else I 0 else 0
      have h9 : ∀ (i : ℕ), (i < u → I'' i = l + 1) ∧ (u ≤ i → i ≤ r → I'' i ≤ l) := by
        simp
        intro
        constructor
        all_goals (try repeat split) <;> omega
      rw [ ← h3.2.2.1 I'' u (le_of_lt h4.2.1) h9]
      simp [add_assoc, sum_mul, ← sum_if_2 h4.2.2.1, sum_if_2 h4.1]
    case inr h10 =>
      simp [h5 0, Nat.zero_lt_of_ne_zero h10]
  omega

private lemma n3 : S 0 0 := by
  intro
  use 2
  intro C
  use 0, fun _ ↦ 1, C
  simp
  intro _ _ h1 h2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h3 | h3
  all_goals simp [h2, h3]

private lemma n4 : ∀ l m : Nat, S l m := by
  have h1 : ∀ l : Nat, S l 0 → ∀ m : Nat, S l m := by
    rintro l h1 m
    induction m with
    | zero => exact h1
    | succ n h2 => exact n1 l n h1 h2
  intro l
  induction l with
  | zero => exact h1 0 n3
  | succ n ih => exact h1 (n + 1) (n2 n ih)

/-- **The theorem of Van der Waerden on arithmetic progressions** which asserts that for any
partition of the naturel into a finite number of classes, some class contains arbitrarily long
arithmetic progressions.-/
theorem VanDerWaerden (r l : Nat) : ∃ N : Nat, ∀ C : Nat → Fin r, ∃ a b : Nat, ∃ c : Fin r,
    b ≠ 0 ∧ a + (l + 1) * b < N ∧ ∀ n : Nat, n ≤ l → C (a + b * n) = c := by
  obtain ⟨N, h1⟩ := n4 l 0 r
  use N
  intro C
  obtain ⟨a, d, q, h2⟩ := h1 C
  simp at h2
  use a, d 0, q 0, h2.1 0, h2.2.1, fun n h ↦ by simp [h2.2.2.1 (fun _ ↦ n) 0, h]

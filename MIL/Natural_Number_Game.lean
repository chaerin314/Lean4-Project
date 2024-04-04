import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import MIL.Common
import Mathlib.Init.Data.Nat.Lemmas

open Nat

lemma two_eq_succ_one : 2 = succ 1 := rfl


#eval "Hello World!"

example (a b c d : Nat) : a + (b + 0) + (c + 0) + (d + 0) = a + b + c + d := by
  rw [add_zero c]
  rw [add_zero b]
-- sorry
  rw [add_zero d]
-- rfl

theorem succ_eq_add_one n : succ n = n + 1 := by
rw [one_eq_succ_zero]
-- rw [add_succ]

example : (2 : ℕ) + 2 = 4 := by
nth_rewrite 2 [two_eq_succ_one]
rw [add_succ]
-- rw [one_eq_succ_zero]
-- rw [add_succ, add_zero]
-- rw [<-three_eq_succ_two]
-- rw [<-four_eq_succ_three]

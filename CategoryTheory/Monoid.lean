
universe v u
namespace Monoid

inductive List (α : Type u) : Type u where
  | nil : List α
  | cons : α → List α → List α

open List
notation "[]" => nil
infixr:50 " ∷ " => cons



def append {α : Type u} (xs : List α) (ys : List α) : List α :=
  match xs with
  | nil => ys
  | cons x xs => cons x (append xs ys)

infixr:70 " ++ " => append


theorem nil_append  {α : Type u} (xs : List α) : [] ++ xs = xs := by
  rfl

theorem append_nil  {α : Type u} (xs : List α) : xs ++ [] = xs := by
  induction xs with
    | nil => rfl
    | cons x xs IH =>
      simp [append]
      apply IH

theorem append_assoc  {α : Type u} (xs ys zs : List α) : xs ++ ys ++ zs = (xs ++ ys) ++ zs := by
  induction xs with
    | nil => rfl
    | cons x xs IH =>
      simp [append]
      apply IH

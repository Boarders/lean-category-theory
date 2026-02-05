import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Hom.Defs

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

theorem append_assoc  {α : Type u} (xs ys zs : List α) : (xs ++ ys) ++ zs = xs ++ ys ++ zs := by
  induction xs with
    | nil => rfl
    | cons x xs IH =>
      simp [append]
      apply IH

instance {α : Type u} : Monoid (List α) where
  mul := append
  one := []
  one_mul := nil_append
  mul_one := append_nil
  mul_assoc := append_assoc

open Monoid

def fold {α : Type u}{M : Type v} [Monoid M] (f : α → M) (xs : List α) : M :=
  match xs with
  | [] => 1
  | cons x xs => f x * (fold f xs)

def fold_homomorphic {α : Type u}{M : Type v} [Monoid M] (f : α → M) (xs ys : List α) :
  fold f (xs * ys) = fold f xs * fold f ys := by
  induction xs with
  | nil =>
     simp [fold]
     rw [show ([] : List α) * ys = ys from one_mul ys]
  | cons x xs IH =>
     change fold f ((cons x xs) ++ ys) = (fold f (x ∷ xs)) * (fold f ys)
     simp [fold, append]
     have eq : fold f (xs ++ ys) = fold f xs * fold f ys := IH
     rw [eq, Semigroup.mul_assoc]

def fold_hom {α : Type u}{M : Type v} [Monoid M]  (f : α → M) : MonoidHom (List α) M := by
    refine {toFun := ?_, map_one' := ?_, map_mul' := ?_}
    · exact fold f
    · simp [fold]
    · exact fold_homomorphic f

theorem fold_uniq {α : Type u}{M : Type v} [Monoid M] (xs : List α) (f : α → M) (μ : MonoidHom (List α) M) (eq_elements : (a : α) → μ (a ∷ []) = f a) : μ xs = fold f xs := by
  induction xs with
  | nil =>
      have μ_eq : μ [] = 1 := by
        apply μ.map_one'
      have hom_eq : fold f [] = 1 := by
        rfl
      rw [μ_eq, hom_eq]
  | cons x xs IH =>
      have eq_cons : (x ∷ xs) = (x ∷ []) * xs := by
        rfl
      have eq_μ : μ (x ∷ xs) = μ (x ∷ []) * μ xs := by
        rw [eq_cons]
        apply μ.map_mul'
      have eq_f : fold f (x ∷ xs) = fold f (x ∷ []) * fold f xs := by
        rw [eq_cons]
        apply fold_homomorphic f
      rw [eq_μ, eq_f, IH]
      rw [eq_elements x]
      have fold_hom_extends : fold f (x ∷ []) = f x := by
        simp [fold]
      rw [fold_hom_extends]

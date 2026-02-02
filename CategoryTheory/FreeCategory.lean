import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Hom.Defs
import CategoryTheory.Category

universe v u
namespace Cat
open Quiver

structure Graph (e : Type u) (v : Type v) where
  s : e → v
  t : e → v

inductive Path {Q : Type u} [Quiver.{v} Q] : Q → Q → Type max u v where
  | nil : ∀ {q : Q}, Path q q
  | cons : ∀ {q₁ q₂ q₃ : Q}, Hom q₁ q₂ → Path q₂ q₃ → Path q₁ q₃

structure FreeCat (Q : Type u) [Quiver.{v} Q] where
  obj : Q

instance {Q : Type u} [Quiver Q] : Quiver (FreeCat Q) where
  Hom q₁ q₂ := Path q₁.obj q₂.obj

def id_free {Q : Type u} [Quiver Q] : ∀ {q : FreeCat Q} , Quiver.Hom q q  := Path.nil

def comp_free {Q : Type u} [Quiver Q] {q₁ q₂ q₃ : Q} (p₁ : Path q₁ q₂) (p₂ : Path q₂ q₃) : Path q₁ q₃ :=
  match p₁ with
  | Path.nil => p₂
  | Path.cons p p₁' => Path.cons p (comp_free p₁' p₂)
infixr:70 " ++ " => comp_free


instance {Q : Type u} [Quiver Q] : DeductiveSystem (FreeCat Q) where
  id _q := id_free
  comp := comp_free


theorem id_comp {Q : Type u} [Quiver Q] {q₁ q₂ : Q} (p : Path q₁ q₂) : comp_free id_free p = p := by
  rfl

theorem comp_id {Q : Type u} [Quiver Q] {q₁ q₂ : Q} (p : Path q₁ q₂) : comp_free p id_free = p := by
  induction p with
  | nil => rfl
  | cons x xs IH =>
    simp [comp_free, IH]

theorem comp_assoc {Q : Type u} [Quiver Q] {q₁ q₂ q₃ q₄ : Q}
  (p₁ : Path q₁ q₂)(p₂ : Path q₂ q₃)(p₃ : Path q₃ q₄) :
  (p₁ ++ p₂) ++ p₃ = p₁ ++ (p₂ ++ p₃) := by
  induction p₁ with
    | nil => rfl
    | cons x xs IH =>
      simp [comp_free]
      apply IH

instance {Q : Type u} [Quiver Q] : Category (FreeCat Q) where
  id_comp := id_comp
  comp_id := comp_id
  assoc := comp_assoc

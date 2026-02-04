import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Hom.Defs
import CategoryTheory.Category
import CategoryTheory.Functor

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


@[simp] theorem id_comp {Q : Type u} [Quiver Q] {q₁ q₂ : Q} (p : Path q₁ q₂) : comp_free id_free p = p := by
  rfl

@[simp] theorem comp_id {Q : Type u} [Quiver Q] {q₁ q₂ : Q} (p : Path q₁ q₂) : comp_free p id_free = p := by
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

open QuiverHom
open Functor

def fold_path {Q : Type u₁} [Quiver.{v₁} Q] {D : Type u₂} [Category.{v₂} D]
    (M : QuiverHom Q D) {q₁ q₂ : Q} : Path q₁ q₂ → Hom (M.F₀ q₁) (M.F₀ q₂)
  | Path.nil => 𝟙 (M.F₀ _)
  | Path.cons p ps => M.F₁ p ≫ fold_path M ps

theorem fold_path_functoriality  {Q : Type u₁} [Quiver.{v₁} Q] {D : Type u₂} [Category.{v₂} D]
    (M : QuiverHom Q D) {q₁ q₂ q₃ : Q} (p₁ : Path q₁ q₂) (p₂ : Path q₂ q₃) :
  fold_path M (comp_free p₁ p₂) = fold_path M p₁ ≫ fold_path M p₂ := by
  induction p₁ with
  | nil =>
      simp [comp_free, fold_path]
  | cons p ps IH =>
      simp [comp_free, fold_path]
      rw [IH]


def fold_free_cat {Q : Type u₁} [Quiver.{v₁} Q] {D : Type u₂} [Category.{v₂} D] (M : QuiverHom Q D) : Functor (FreeCat Q) D := by
  refine {F₀ := ?_, F₁ := ?_, F_id := ?_, F_comp := ?_ }
  · intro q
    exact M.F₀ q.obj
  · intro q₁ q₂ p
    exact fold_path M p
  · intro c
    rfl
  · intro q₁ q₂ q₃ q₁q₂ q₂q₃
    apply fold_path_functoriality
end Cat

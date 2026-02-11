import CategoryTheory.Category
import CategoryTheory.Functor
import CategoryTheory.Constructions

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver
open DeductiveSystem
open Category

structure QuiverHomOp (Q₁ : Type u₁) [Quiver.{v₁} Q₁] (Q₂ : Type u₂) [Quiver.{v₂} Q₂] where
  F₀ : Q₁ → Q₂
  F₁ : ∀ {q₁ q₂ : Q₁}, Hom q₁ q₂ → Hom (F₀ q₂) (F₀ q₁)

structure ContravariantFunctor (C : Type u₁) [Category C] (D : Type u₂) [Category D]
    extends QuiverHomOp C D where
  F_id : ∀ {c : C}, F₁ (id c) = (DeductiveSystem.id (F₀ c))
  F_comp : ∀ {a b c : C} (f : Hom a b) (g : Hom b c),
    F₁ (f ≫ g) = F₁ g ≫ F₁ f

def contravariant_as_functor (C : Type u₁) [Category C] (D : Type u₂) [Category D]
  (F_op : ContravariantFunctor C D) :
  Functor (Opposite C) D := by
  refine {F₀ := ?_, F₁ := ?_, F_id := ?_, F_comp := ?_}
  · intro op_c
    exact F_op.F₀ op_c.obj
  · exact F_op.F₁
  . exact F_op.F_id
  · intro _op_c _op_d _op_e g f
    exact F_op.F_comp f g

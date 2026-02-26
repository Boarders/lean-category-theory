import CategoryTheory.Category
import CategoryTheory.Covariant.Functor
import CategoryTheory.Constructions

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver
open DeductiveSystem
open Category

structure QuiverHomOp (Q₁ : Type u₁) [Quiver.{v₁} Q₁] (Q₂ : Type u₂) [Quiver.{v₂} Q₂] where
  F₀ : Q₁ → Q₂
  F₁ : ∀ {q₁ q₂ : Q₁}, Hom q₁ q₂ → Hom (F₀ q₂) (F₀ q₁)

@[ext]
theorem QuiverHomOp.ext {C D : Type u} [Quiver C][Quiver D] {F G : QuiverHom C D}
      (h₀ : F.F₀ = G.F₀)
      (h₁ : @HEq (∀ {c₁ c₂ : C}, Hom c₁ c₂ → Hom (F.F₀ c₁) (F.F₀ c₂))
                  F.F₁
                  (∀ {c₁ c₂ : C}, Hom c₁ c₂ → Hom (G.F₀ c₁) (G.F₀ c₂))
                  G.F₁)
      : F = G := by
  cases F with
  | mk qhF =>
    cases G with
    | mk qhG =>
      congr

namespace Contravariant

structure Functor (C : Type u₁) [Category C] (D : Type u₂) [Category D]
    extends QuiverHomOp C D where
  F_id : ∀ {c : C}, F₁ (id c) = (DeductiveSystem.id (F₀ c))
  F_comp : ∀ {a b c : C} (f : Hom a b) (g : Hom b c),
    F₁ (f ≫ g) = F₁ g ≫ F₁ f

def contravariant_as_functor (C : Type u₁) [Category C] (D : Type u₂) [Category D]
  (F_op : Contravariant.Functor C D) :
  Covariant.Functor (Opposite C) D := by
  refine {F₀ := ?_, F₁ := ?_, F_id := ?_, F_comp := ?_}
  · intro op_c
    exact F_op.F₀ op_c.obj
  · exact F_op.F₁
  . exact F_op.F_id
  · intro _op_c _op_d _op_e g f
    exact F_op.F_comp f g

end Contravariant
end Cat

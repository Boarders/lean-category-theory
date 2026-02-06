import CategoryTheory.Category

universe u₁ u₂ v₁ v₂ u v

namespace Cat

open Quiver
open DeductiveSystem
open Category

structure QuiverHom (Q₁ : Type u₁) [Quiver.{v₁} Q₁] (Q₂ : Type u₂) [Quiver.{v₂} Q₂] where
  F₀ : Q₁ → Q₂
  F₁ : ∀ {q₁ q₂ : Q₁}, Hom q₁ q₂ → Hom (F₀ q₁) (F₀ q₂)

structure Functor (C : Type u₁) [Category C] (D : Type u₂) [Category D]
    extends QuiverHom C D where
  F_id : ∀ {c : C}, F₁ (id c) = (DeductiveSystem.id (F₀ c))
  F_comp : ∀ {a b c : C} (f : Hom a b) (g : Hom b c),
    F₁ (f ≫ g) = F₁ f ≫ F₁ g

/-!
### The identity functor

The identity functor is the identity map on objects and morphisms
-/
def Id_Hom (Q : Type u) [Quiver Q] : QuiverHom Q Q :=
  { F₀ := id,
    F₁ := id
  }

def Id_Functor (C : Type u) [Category C] : Functor C C :=
  { Id_Hom C with
    F_id := by
      intro c
      rfl
    F_comp := by
      intro a b c f g
      rfl
  }

/-!
### Composition of functors

  C ---F---> D ---G---> E

  - This is defined as the function composition of the actions of F and G on objects
    and morphisms

  - The functor laws follow from those of the underlying functors e.g
    F (G id) = F (id) = id etc.
-/

def Comp_Hom {Q₁ Q₂ Q₃ : Type u} [Quiver Q₁] [Quiver Q₂] [Quiver Q₃] (F : QuiverHom Q₁ Q₂) (G : QuiverHom Q₂ Q₃) : QuiverHom Q₁ Q₃ :=
  { F₀ := G.F₀ ∘ F.F₀
    F₁ := G.F₁ ∘ F.F₁
  }

def Comp_Functor (C D E : Type u) [Category C] [Category D] [Category E] (F : Functor C D) (G : Functor D E) : Functor C E :=
  { Comp_Hom F.toQuiverHom G.toQuiverHom with
    F_id := by
      intro c
      simp [Comp_Hom, F.F_id, G.F_id]
    F_comp := by
      intro c d e f g
      simp [Comp_Hom, F.F_comp, G.F_comp]
  }

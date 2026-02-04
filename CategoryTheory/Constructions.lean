import CategoryTheory.Category
import CategoryTheory.Functor

universe u₁ u₂ v₁ v₂ u v

namespace Cat

open Quiver
open DeductiveSystem
open Category

/--
The opposite of a category C, written C^{op} is a category with
the same objects and every arrow reversed:
  Ob(C^op) = C
  C^op(c₁, c₂) = Hom(c₂, c₁)
-/
structure Opposite (C : Type u) : Type u where
  obj : C

instance (C : Type u) [Quiver C] : Quiver (Opposite C) where
  Hom c₁ c₂ := Hom c₂.obj c₁.obj

instance (C : Type u) [DeductiveSystem C] : DeductiveSystem (Opposite C) where
  id C := id C.obj
  comp f g := comp g f

instance (C : Type u) [Category C] : Category (Opposite C) where
  id_comp _f := by
    apply comp_id

  comp_id _f := by
    apply id_comp

  assoc f g h := by
    simp [DeductiveSystem.comp]

/--
The product of two categories is a product category where:
  Ob(C × D) = C₀ × D₀
  Hom(c₁ × d₁, c₂ × d₂) = Hom(c₁, c₂) × Hom(d₁, d₂)
-/
instance (C : Type u₁)(D : Type u₂) [Category C] [Category D] : Quiver (C × D) where
  Hom t1 t2 := match t1 , t2 with
  | (c₁, d₁) , (c₂, d₂) => Hom c₁ c₂ × Hom d₁ d₂

instance (C : Type u₁)(D : Type u₂) [Category C] [Category D] : DeductiveSystem (C × D) where
  id X := (𝟙 X.fst, 𝟙 X.snd)
  comp fs gs := match fs, gs with
  | (f₁, f₂), (g₁, g₂) => (f₁ ≫ g₁, f₂ ≫ g₂)

instance (C : Type u₁)(D : Type u₂) [Category C] [Category D] : Category (C × D) where
  id_comp := by
    intro P1 P2 f
    cases f with
    | mk f₁ f₂ =>
      simp [comp]

  comp_id := by
    intro P1 P1 f
    cases f with
    | mk f₁ f₂ =>
      simp [comp]

  assoc := by
    intro P1 P2 P3 P4 f g h
    simp [comp]

def Proj₁ (C : Type u₁)(D : Type u₂) [Category C] [Category D] : Functor (C × D) C
  := by
  refine {F₀ := ?_, F₁ := ?_, F_id := ?_, F_comp := ?_}
  · exact fun p => p.fst
  · intro P1 P2 f
    exact f.fst
  · intro P
    rfl
  · intro P1 P2 P3 f g
    simp [comp]

def Proj₂ (C : Type u₁)(D : Type u₂) [Category C] [Category D] : Functor (C × D) D
  := by
  refine {F₀ := ?_, F₁ := ?_, F_id := ?_, F_comp := ?_}
  · exact fun p => p.snd
  · intro P1 P2 f
    exact f.snd
  · intro P
    rfl
  · intro P1 P2 P3 f g
    simp [comp]

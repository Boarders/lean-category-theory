import CategoryTheory.Category
import CategoryTheory.Functor

universe u₁ u₂ v₁ v₂ u v

namespace Cat

open Quiver
open DeductiveSystem
open Category

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

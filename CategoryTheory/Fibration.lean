import CategoryTheory.Category
import CategoryTheory.Functor
import CategoryTheory.Commutative
import CategoryTheory.Morphisms


universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver


structure IsCartesian {E : Type u₁}{B : Type u₂}[Category.{v₁} E][Category.{v₂} B] {e₁ e₂ : E} (F : Functor E B) (top : Hom e₁ e₂) : Type (max u₁ u₂ v₁ v₂) where
    morphism :
      ∀ {a : E} {u : Hom (F.F₀ a) (F.F₀ e₁)} (h : Hom a e₂),
       u ≫ F.F₁ top  = F.F₁ h →  Hom a e₁
    mediates :
      ∀ {a : E} {u : Hom (F.F₀ a) (F.F₀ e₁)} (h : Hom a e₂)
       (eq : u ≫ F.F₁ top  = F.F₁ h),
         morphism h eq ≫ top  = h
    F_morphism :
      ∀ {a : E} {u : Hom (F.F₀ a) (F.F₀ e₁)} (h : Hom a e₂)
       (eq : u ≫ F.F₁ top  = F.F₁ h),
          F.F₁ (morphism h eq) = u

import CategoryTheory.Category
import CategoryTheory.Morphisms
import Mathlib.Data.Quot

universe u₁ u₂ v₁ v₂ u v

namespace Cat

open Quiver
open DeductiveSystem
open Category

structure IsPart {C : Type u} [Category C] {a a' b : C}(f : Hom a b) (g : Hom a' b) where
  factors : ∃ i : Hom a a' , i ≫ g = f

theorem IsPart_refl {C : Type u} [Category C] {a b : C} {f : Hom a b} :
  IsPart f f := by
  refine {factors := ?_}
  exists (𝟙 a)
  · simp [id_comp]

theorem IsPart_trans {C : Type u} [Category C] {a b c T : C}
  {f : Hom a T} {g : Hom b T} {h : Hom c T}
  (f_in_g : IsPart f g) (g_in_h : IsPart g h) :
  IsPart f h := by
  refine {factors := ?_}
  obtain ⟨i , i_factors⟩ := f_in_g.factors
  obtain ⟨j , j_factors⟩ := g_in_h.factors
  exists (i ≫ j)
  -- Need to show:
  --   ⊢ (i ≫ j) ≫ h = f
  · rw [assoc]
    rw [j_factors, i_factors]

def IsEquiv {C : Type u} [Category C] {a a' b : C}(f : Hom a b) (g : Hom a' b) :=
  IsPart f g ∧ IsPart g f

theorem IsEquiv_refl {C : Type u} [Category C] {a T : C}
  (f : Hom a T) : IsEquiv f f := by
  constructor
  · apply IsPart_refl
  · apply IsPart_refl


theorem IsEquiv_symm {C : Type u} [Category C] {a a' T : C}
  {f : Hom a T} {g : Hom a' T}
  (equiv : IsEquiv f g) : IsEquiv g f := by
  simp [IsEquiv]
  constructor
  · exact equiv.right
  · exact equiv.left

theorem IsEquiv_trans {C : Type u} [Category C] {a a' a'' T : C}
  {f : Hom a T} {g : Hom a' T} {h : Hom a'' T}
  (f_eq_g : IsEquiv f g) (g_eq_h : IsEquiv g h) :
  IsEquiv f h := by
  constructor
  · apply IsPart_trans f_eq_g.left g_eq_h.left
  · apply IsPart_trans g_eq_h.right f_eq_g.right

structure Monos {C : Type u} [Category C] (b : C) where
  source : C
  morphism : Hom source b
  is_mono : IsMono morphism

def equivMonos {C : Type u} [Category C] (b : C) : Setoid (Monos b) where
  r f g := IsEquiv f.morphism g.morphism
  iseqv := {
    refl := fun f => IsEquiv_refl f.morphism
    symm := fun eq => IsEquiv_symm eq
    trans := fun eq₁ eq₂ => IsEquiv_trans eq₁ eq₂
  }

abbrev Sub {C : Type u} [Category C] (c : C) := Quotient (equivMonos c)

def pullback_sub :

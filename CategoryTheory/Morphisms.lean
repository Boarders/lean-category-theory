import CategoryTheory.Category

universe u₁ u₂ v₁ v₂ u v

namespace Cat

open Quiver
open DeductiveSystem
open Category

structure IsIso {C : Type u} [Category C] {a b : C} (f : Hom a b) where
  inv : Hom b a
  -- Note: Because we use diagrammatic order, these are the opposite
  -- of the usual left inverse and right inverse laws
  l_inv : (inv ≫ f) = (𝟙 b)
  r_inv : (f ≫ inv) = (𝟙 a)

open IsIso

theorem uniq_inv
   {C : Type u} {a b : C} [Category C] (f : Hom a b) (g₁ g₂ : IsIso f) :
    g₁.inv = g₂.inv
  := by
  have h₁ :  g₁.inv = g₁.inv ≫ (f ≫ g₂.inv) := by {
    rw [g₂.r_inv]
    simp
  }
  rw [h₁]
  rw [<- assoc, l_inv]
  simp


structure IsMono {C : Type u} [Category C] {b c : C} (i : Hom b c) where
  post_cancel : ∀ {a : C} , (e e' : Hom a b) → e ≫ i = e' ≫ i → e = e'

structure IsEpi {C : Type u} [Category C] {b c : C} (s : Hom b c) where
  pre_cancel : ∀ {d : C} , (f f' : Hom c d) → s ≫ f = s ≫ f' → s = s'

/--
Proof that the composition of two monos is a mono
-/
theorem comp_mono {C : Type u} [Category C] {a b c : C}
    (i₁ : Hom a b) (i₂ : Hom b c)
    (i₁_mono : IsMono i₁)(i₂_mono : IsMono i₂) :
  IsMono (i₁ ≫ i₂) := by
  refine {post_cancel := ?_}
  · intro c x x' eq
    rw [<- Category.assoc, <- Category.assoc] at eq
    have cancel_i₂ : x ≫ i₁ = x' ≫ i₁ := by
      apply i₂_mono.post_cancel (x ≫ i₁) (x' ≫ i₁) eq

    have cancel_i₁ : x = x' := by
      apply i₁_mono.post_cancel x x' cancel_i₂

    exact cancel_i₁

/--
Proof that if i₁ ≫ i₂ is mono, then i₁ is mono
-/
theorem post_comp_mono {C : Type u} [Category C] {a b c : C}
    (i₁ : Hom a b) (i₂ : Hom b c)
    (i₁i₂_mono : IsMono (i₁ ≫ i₂)) :
  IsMono i₁ := by
  refine {post_cancel := ?_}
  · intro c x x' eq

    have add_i₂ : x ≫ i₁ ≫ i₂ = x' ≫ i₁ ≫ i₂ := by
      rw [<- Category.assoc, <- Category.assoc]
      rw [eq]

    have cancel_i₁i₂ : x = x' := by
      apply i₁i₂_mono.post_cancel x x' add_i₂

    exact cancel_i₁i₂

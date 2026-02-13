import CategoryTheory.Category

universe u₁ u₂ v₁ v₂ u v

namespace Cat

open Quiver
open DeductiveSystem
open Category

structure IsIso {C : Type u} [Category C] {a b : C} (f : Hom a b) where
  inv : Hom b a
  pre_inv : (inv ≫ f) = (𝟙 b)
  post_inv : (f ≫ inv) = (𝟙 a)

open IsIso

theorem uniq_inv
   {C : Type u} {a b : C} [Category C] (f : Hom a b) (g₁ g₂ : IsIso f) :
    g₁.inv = g₂.inv
  := by
  have h₁ :  g₁.inv = g₁.inv ≫ (f ≫ g₂.inv) := by {
    rw [g₂.post_inv]
    simp
  }
  rw [h₁]
  rw [<- assoc, pre_inv]
  simp


structure IsMono {C : Type u} [Category C] {b c : C} (i : Hom b c) where
  post_cancel : ∀ {a : C} , (e e' : Hom a b) → e ≫ i = e' ≫ i → e = e'

structure IsSplitMono {C : Type u} [Category C] {b c : C} (i : Hom b c) where
  post_inverse : Hom c b
  is_post_inverse : i ≫ post_inverse = (𝟙 b)

structure IsEpi {C : Type u} [Category C] {b c : C} (s : Hom b c) where
  pre_cancel : ∀ {d : C} , (f f' : Hom c d) → s ≫ f = s ≫ f' → f = f'

structure IsSplitEpi {C : Type u} [Category C] {b c : C} (s : Hom b c) where
  pre_inverse : Hom c b
  is_pre_inverse : pre_inverse ≫ s = (𝟙 c)

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

theorem split_mono_is_mono {C : Type u} [Category C] {b c : C}
  (i : Hom b c) (i_split : IsSplitMono i) : IsMono i := by
  refine {post_cancel := ?_}
  · intro a ab ab' post_eq
    have eq_post : ab ≫  (i ≫ i_split.post_inverse) = ab' ≫ (i ≫ i_split.post_inverse) := by
      rw [<- assoc, <- assoc, post_eq]
    have eq : ab = ab':= by
      rw [i_split.is_post_inverse] at eq_post
      rw [comp_id, comp_id] at eq_post
      exact eq_post
    exact eq

theorem split_epi_is_epi {C : Type u} [Category C] {b c : C}
  (s : Hom b c) (s_split : IsSplitEpi s) : IsEpi s := by
  refine {pre_cancel := ?_}
  · intro d cd cd' post_eq
    have eq_pre : (s_split.pre_inverse ≫ s) ≫ cd =  (s_split.pre_inverse ≫ s) ≫ cd' := by
      rw [assoc, assoc, post_eq]
    have eq : cd = cd':= by
      rw [s_split.is_pre_inverse] at eq_pre
      rw [id_comp, id_comp] at eq_pre
      exact eq_pre
    exact eq

def iso_is_split_mono {C : Type u} [Category C] {b c : C}
  (f : Hom b c) (f_iso : IsIso f) : IsSplitMono f := by
  refine { post_inverse := ?_, is_post_inverse := ?_}
  · exact f_iso.inv
  · exact f_iso.post_inv

def iso_is_mono {C : Type u} [Category C] {b c : C}
  (f : Hom b c) (f_iso : IsIso f) : IsMono f := by
  apply split_mono_is_mono
  exact iso_is_split_mono f f_iso

def iso_is_split_epi {C : Type u} [Category C] {b c : C}
  (f : Hom b c) (f_iso : IsIso f) : IsSplitEpi f := by
  refine { pre_inverse := ?_, is_pre_inverse := ?_}
  · exact f_iso.inv
  · exact f_iso.pre_inv

def iso_is_epi {C : Type u} [Category C] {b c : C}
  (f : Hom b c) (f_iso : IsIso f) : IsEpi f := by
  apply split_epi_is_epi
  exact iso_is_split_epi f f_iso

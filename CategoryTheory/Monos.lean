import CategoryTheory.Category
import CategoryTheory.Morphisms
import CategoryTheory.Pullback
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

/--
     a₁ a₂ -------→ b₁ b₁
   j₁ ↓≅↓ j₂     i₁ ↓≅↓ i₂
       c-----f-----→ d
-/
def Sub_Hom {C : Type u} [Category C]
  {c d : C} (mkPullback : HasPullbacks C) (f : Hom c d) : Sub d → Sub c :=
  Quotient.lift
    (fun m : Monos d => by
      obtain ⟨j_src, ⟨jc, jd⟩, j_pullback⟩ := mkPullback f m.morphism
      exact Quotient.mk (equivMonos c) ⟨j_src, jd, mono_pullback j_pullback m.is_mono⟩)
        (by
          intro m₁ m₂ eq_m₁m₂
          -- Need to show:
          --   if m₁ ≈ m₂, then the morphism
          --   arising from mkPullback m₁ f is equiv to the morphism arising
          --   from mkPullback m₂ f
          cases m₁ with
          | mk a₁ i₁ i₁_mono =>
          cases m₂ with
          | mk a₂ i₂ i₂_mono =>
          cases eq_m₁m₂ with
          | intro i₁i₂_part i₂i₁_part =>
             simp at i₁i₂_part
             simp at i₂i₁_part
             obtain ⟨i₁i₂, i₁_is_part⟩ := i₁i₂_part.factors
             obtain ⟨i₂i₁, i₂_is_part⟩ := i₂i₁_part.factors
             simp
             have equiv : IsEquiv (pullback_left mkPullback f i₁) (pullback_left mkPullback f i₂) := by
               let j₁_src := pullback_obj mkPullback f i₁
               let j₁b₁ := pullback_top mkPullback f i₁
               let j₁c := pullback_left mkPullback f i₁
               let j₁_pullback := pullback_proof mkPullback f i₁
               let j₂_src := pullback_obj mkPullback f i₂
               let j₂b₂ := pullback_top mkPullback f i₂
               let j₂c := pullback_left mkPullback f i₂
               let j₂_pullback := pullback_proof mkPullback f i₂
               have j₁comm : CommutativeSquare (j₁b₁ ≫ i₁i₂) i₂ j₁c f := by
                 simp [CommutativeSquare]
                 rw [i₁_is_part]
                 apply j₁_pullback.commutes
               have j₂comm : CommutativeSquare (j₂b₂ ≫ i₂i₁) i₁ j₂c f := by
                 simp [CommutativeSquare]
                 rw [i₂_is_part]
                 apply j₂_pullback.commutes
               have j₁_mediate :
                 ∃! (i : Hom j₁_src j₂_src) , i ≫ j₂b₂ = (j₁b₁ ≫ i₁i₂) ∧ i ≫ j₂c = j₁c := by
                 apply j₂_pullback.mediating_morphism (j₁b₁ ≫ i₁i₂) j₁c j₁comm
               have j₂_mediate :
                 ∃! (i : Hom j₂_src j₁_src) , i ≫ j₁b₁ = (j₂b₂ ≫ i₂i₁) ∧ i ≫ j₁c = j₂c := by
                 apply j₁_pullback.mediating_morphism (j₂b₂ ≫ i₂i₁) j₂c j₂comm
               obtain ⟨j₁j₂ , ⟨j₁_j₂b₂, j₁_j₂c⟩, j₁_uniq⟩ := j₁_mediate
               obtain ⟨j₂j₁ , ⟨j₂_j₁b₁, j₂_j₁c⟩, j₂_uniq⟩ := j₂_mediate
               simp [IsEquiv]
               constructor
               · refine {factors := ?_}
                 change ∃ i, i ≫ j₂c = j₁c
                 exact ⟨j₁j₂, j₁_j₂c⟩
               · refine {factors := ?_}
                 change ∃ i, i ≫ j₁c = j₂c
                 exact ⟨j₂j₁, j₂_j₁c⟩
             exact Quotient.sound equiv
        )

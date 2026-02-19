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
def Sub_Hom {C : Type u} [Category C] [HasPullbacks C]
  {c d : C} (f : Hom c d) : Sub d → Sub c :=
  Quotient.lift
    (fun m : Monos d => by
      obtain ⟨j_src, ⟨jc, jd⟩, j_pullback⟩ := HasPullbacks.mkPullback f m.morphism
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
             have equiv : IsEquiv (pullback_left f i₁) (pullback_left f i₂) := by
               let j₁_src := pullback_obj f i₁
               let j₁b₁ := pullback_top f i₁
               let j₁c := pullback_left f i₁
               let j₁_pullback := pullback_proof f i₁
               let j₂_src := pullback_obj f i₂
               let j₂b₂ := pullback_top f i₂
               let j₂c := pullback_left f i₂
               let j₂_pullback := pullback_proof f i₂
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

/--
    b──𝟙b─→ b
    │        │
    f        f
    ↓        ↓
    c──𝟙c──→ c

Any morphism f : b → c forms a pullback along 𝟙 c
-/
def id_pullback {C : Type u} [Category C] {b c : C} (f : Hom b c) :
  IsPullback (𝟙 c) f b (𝟙 b) f := by
  refine {commutes := ?_, mediating_morphism := ?_}
  · simp [CommutativeSquare]
  · intro a top left comm
    simp [CommutativeSquare] at comm
    exists top
    simp
    exact comm

theorem pullback_id_equiv {C : Type u} [Category C] [HasPullbacks C]
  {b c : C} (f : Hom b c) :
  IsEquiv (pullback_left (𝟙 c) f) f := by
  refine ⟨?_, ?_⟩
  -- IsPart (pullback_left (𝟙 c) f) f
  · refine {factors := ?_}
    exists pullback_top (𝟙 c) f
    -- pullback commutes giving
    --   top ≫ f = left ≫ 𝟙 c = left
    let top := pullback_top (𝟙 c) f
    let left := pullback_left  (𝟙 c) f
    have comm : CommutativeSquare _ _ _ _ := (pullback_proof (𝟙 c) f).commutes
    simp [CommutativeSquare] at comm
    exact comm
  -- Direction 2: IsPart f (pullback_left (𝟙 c) f)
  -- Use the mediating morphism from the universal property
  · refine {factors := ?_}
    have med := (pullback_proof (𝟙 c) f).mediating_morphism (𝟙 b) f (id_pullback f).commutes
    obtain ⟨i, ⟨_, _⟩, _⟩ := med
    exists i

/--
Given:
   g : c → d,
   h : d → e,
   f : b → e,
pulling back f along g ≫ h is equivalent (as a mono) to first pulling back f along h,
then pulling back the result along g. This follows from the pullback lemma.
-/
theorem pullback_comp_equiv {C : Type u} [Category C] [HasPullbacks C]
  {b c d e : C} (g : Hom c d) (h : Hom d e) (f : Hom b e) :
  IsEquiv (pullback_left (g ≫ h) f) (pullback_left g (pullback_left h f)) := by
  have comp_pb : IsPullback (g ≫ h) f
      (pullback_obj g (pullback_left h f))
      (pullback_top g (pullback_left h f) ≫ pullback_top h f)
      (pullback_left g (pullback_left h f)) :=
    PBL_outer
      (pullback_top g (pullback_left h f))
      (pullback_top h f)
      (pullback_left g (pullback_left h f))
      (pullback_left h f)
      f g h
      (pullback_proof h f)
      (pullback_proof g (pullback_left h f))

  let direct_pb := pullback_proof (g ≫ h) f
  refine ⟨?_, ?_⟩
  -- WTS: IsPart (pullback_left (g ≫ h) f) (pullback_left g (pullback_left h f))
  · refine {factors := ?_}
    have med := comp_pb.mediating_morphism
      (pullback_top (g ≫ h) f)
      (pullback_left (g ≫ h) f)
      direct_pb.commutes
    obtain ⟨i, ⟨_, i_left⟩, _⟩ := med
    exact ⟨i, i_left⟩
  -- WTS : IsPart (pullback_left g (pullback_left h f)) (pullback_left (g ≫ h) f)
  · refine {factors := ?_}
    have med := direct_pb.mediating_morphism
      (pullback_top g (pullback_left h f) ≫ pullback_top h f)
      (pullback_left g (pullback_left h f))
      comp_pb.commutes
    obtain ⟨i, ⟨_, i_left⟩, _⟩ := med
    exact ⟨i, i_left⟩

theorem Sub_Hom_id {C : Type u} [Category C] [HasPullbacks C]
  {c : C} : Sub_Hom (𝟙 c) = id := by
  funext sub_c
  refine Quotient.inductionOn sub_c ?_
  intros mono_c
  cases mono_c with
  | mk a i i_mono =>
    simp [Sub_Hom]
    exact Quotient.sound (pullback_id_equiv i)

theorem Sub_Hom_comp {C : Type u} [Category C] [HasPullbacks C]
  {c d e : C} (f : Hom c d) (g : Hom d e) : Sub_Hom (f ≫ g) = (Sub_Hom f ∘ Sub_Hom g) := by
  funext sub_c
  refine Quotient.inductionOn sub_c ?_
  intros mono_c
  cases mono_c with
  | mk a i i_mono =>
    simp [Sub_Hom]
    exact Quotient.sound (pullback_comp_equiv f g i)

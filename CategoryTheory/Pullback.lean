import CategoryTheory.Category
import CategoryTheory.Commutative
import CategoryTheory.Morphisms

universe u₁ u₂ v₁ v₂ u v

namespace Cat
open Quiver
open DeductiveSystem

/--
       a → b
       ↓   ↓
       c → d
-/
structure IsPullback {C : Type u}[Category.{v} C] {b c d : C} (bottom : Hom c d) (right : Hom b d) (obj : C) (top : Hom obj b) (left : Hom obj c) where
  commutes : CommutativeSquare top right left bottom
  mediating_morphism : ∀ {a : C}
    (top' : Hom a b) (left' : Hom a c)
    (_commutes' : CommutativeSquare top' right left' bottom),
    {i : Hom a obj // i ≫ top = top' ∧ i ≫ left = left'}
  unique : ∀ {a : C} (top' : Hom a b) (left' : Hom a c)
    (commutes' : CommutativeSquare top' right left' bottom)
    (j : Hom a obj), j ≫ top = top' → j ≫ left = left' →
    j = (mediating_morphism top' left' commutes').val

structure PullbackData {C : Type u} [Category C] {b c d : C}
    (cd : Hom c d) (bd : Hom b d) where
  obj : C
  top : Hom obj b
  left : Hom obj c
  is_pullback : IsPullback cd bd obj top left

/--
When we say a category has all pullbacks, we mean that there is some specific choice
of pullback for each appropriate diagram.
-/
class HasPullbacks (C : Type u)[Category C] where
  mkPullback : ∀ {b c d : C} (cd : Hom c d) (bd : Hom b d),
    PullbackData cd bd

def pullback_obj {C : Type u}[Category C] [hp : HasPullbacks C]
  {b c d : C} (cd : Hom c d) (bd : Hom b d) : C :=
  (hp.mkPullback cd bd).obj

def pullback_top {C : Type u}[Category C] [hp : HasPullbacks C]
  {b c d : C} (cd : Hom c d) (bd : Hom b d) :
  Hom (pullback_obj cd bd) b :=
  (hp.mkPullback cd bd).top

def pullback_left {C : Type u}[Category C] [hp : HasPullbacks C]
  {b c d : C} (cd : Hom c d) (bd : Hom b d) :
  Hom (pullback_obj cd bd) c :=
  (hp.mkPullback cd bd).left

def pullback_proof {C : Type u}[Category C] [hp : HasPullbacks C]
  {b c d : C} (cd : Hom c d) (bd : Hom b d) :
  IsPullback cd bd (pullback_obj cd bd)
    (pullback_top cd bd) (pullback_left cd bd) :=
  (hp.mkPullback cd bd).is_pullback

theorem PullbackEndo {C : Type u}[Category.{v} C] (p : C) (a b c : C)
  (pa : Hom p a) (pb : Hom p b)
  (ac : Hom a c) (bc : Hom b c)
  (is_pullback : IsPullback ac bc p pb pa)
  (i : Hom p p)
  (i_pa : i ≫ pa = pa)
  (i_pb : i ≫ pb = pb) : i = 𝟙 p := by
  let med := is_pullback.mediating_morphism pb pa is_pullback.commutes
  -- show i mediates
  have i_mediates : i = med.val := by
    apply is_pullback.unique pb pa is_pullback.commutes
    · exact i_pb
    · exact i_pa
  -- show id mediates
  have id_mediates : (𝟙 p) = med.val := by
    apply is_pullback.unique pb pa is_pullback.commutes
    · simp [Category.id_comp]
    · simp [Category.id_comp]
  trans med.val
  · exact i_mediates
  · symm
    exact id_mediates


/--
       p'
       ├───────┐
       │ !≅↓   ↓
       │   p → b
       │   ↓   ↓
       └───a → c

If a and a' are both pullbacks then they are iso
-/
theorem PullbackUnique {C : Type u}[Category.{v} C] (p p' : C) (a b c : C)
  (pa : Hom p a) (pb : Hom p b)
  (pa' : Hom p' a) (pb' : Hom p' b)
  (ac : Hom a c) (bc : Hom b c)
  (is_pullback : IsPullback ac bc p pb pa)
  (is_pullback' : IsPullback ac bc p' pb' pa') :
  ∃ (f : Hom p' p), IsIso' f := by
  let f_med := is_pullback.mediating_morphism pb' pa' is_pullback'.commutes
  let g_med := is_pullback'.mediating_morphism pb pa is_pullback.commutes
  let f := f_med.val
  let g := g_med.val
  have f_pb := f_med.property.left
  have f_pa := f_med.property.right
  have g_pb := g_med.property.left
  have g_pa := g_med.property.right
  exists f
  simp [IsIso']
  exists g
  -- prove g is a two sided inverse
  constructor
  · let pp_med := is_pullback.mediating_morphism pb pa is_pullback.commutes
    trans pp_med.val
    · apply is_pullback.unique pb pa is_pullback.commutes
      · rw [Category.assoc, f_pb, g_pb]
      · rw [Category.assoc, f_pa, g_pa]
    · symm
      apply is_pullback.unique pb pa is_pullback.commutes
      · rw [Category.id_comp]
      · rw [Category.id_comp]
  · let p'p'_med := is_pullback'.mediating_morphism pb' pa' is_pullback'.commutes
    trans p'p'_med.val
    · apply is_pullback'.unique pb' pa' is_pullback'.commutes
      · rw [Category.assoc, g_pb, f_pb]
      · rw [Category.assoc, g_pa, f_pa]
    · symm
      apply is_pullback'.unique pb' pa' is_pullback'.commutes
      · rw [Category.id_comp]
      · rw [Category.id_comp]

/--
       T
       ├───────────┐
       │           ↓
       │   a → b → c
       │   ↓   ↓   ↓
       └───d → e → f

If the LHS and the RHS are pullbacks then the overall square is a pullback
-/
def PBL_outer {C : Type u}{a b c d e f : C} [Category C]
  (ab : Hom a b) (bc : Hom b c)
  (ad : Hom a d) (be : Hom b e) (cf : Hom c f)
  (de : Hom d e) (ef : Hom e f)
  (rhs_pullback : IsPullback ef cf b bc be)
  (lhs_pullback : IsPullback de be a ab ad) :
  IsPullback (de ≫ ef) cf a (ab ≫ bc) ad := by
  refine {commutes := ?_, mediating_morphism := ?_, unique := ?_}
  · simp [CommutativeSquare]
    -- need to show: ab ≫ bc ≫ cf = ad ≫ de ≫ ef
    have eq_1 : ab ≫ bc ≫ cf = ab ≫ be ≫ ef := by
      rw [rhs_pullback.commutes]
    have eq_2 : ab ≫ be ≫ ef = ad ≫ de ≫ ef := by
      rw [<- Category.assoc, lhs_pullback.commutes]
      rw [Category.assoc]
    trans (ab ≫ be ≫ ef)
    · exact eq_1
    · exact eq_2
  · intro T Tc Td T_commSq
    -- first get a map to b via b's pullback property
    have rhs_comm : CommutativeSquare Tc cf (Td ≫ de) ef := by
      simp [CommutativeSquare] at T_commSq ⊢
      exact T_commSq
    let tb_med := rhs_pullback.mediating_morphism Tc (Td ≫ de) rhs_comm
    let tb := tb_med.val
    have tb_bc := tb_med.property.left
    have tb_be := tb_med.property.right
    -- now get a map to a via a's pullback property using the map to b
    have lhs_comm : CommutativeSquare tb be Td de := by
      simp [CommutativeSquare]
      exact tb_be
    let ta_med := lhs_pullback.mediating_morphism tb Td lhs_comm
    exact ⟨ta_med.val, ⟨by rw [← Category.assoc, ta_med.property.left, tb_bc],
                         ta_med.property.right⟩⟩
  · intro T Tc Td T_commSq ta' ta'_abc ta'_ad
    have rhs_comm : CommutativeSquare Tc cf (Td ≫ de) ef := by
      simp [CommutativeSquare] at T_commSq ⊢
      exact T_commSq
    let tb_med := rhs_pullback.mediating_morphism Tc (Td ≫ de) rhs_comm
    let tb := tb_med.val
    have tb_be := tb_med.property.right
    have lhs_comm : CommutativeSquare tb be Td de := by
      simp [CommutativeSquare]
      exact tb_be
    apply lhs_pullback.unique tb Td lhs_comm
    · -- ta' ≫ ab = tb
      apply rhs_pullback.unique Tc (Td ≫ de) rhs_comm
      · rw [Category.assoc]; exact ta'_abc
      · rw [Category.assoc, lhs_pullback.commutes, ← Category.assoc, ta'_ad]
    · exact ta'_ad


/--
       T
       ├───────┐
       │       ↓
       │   a → b → c
       │   ↓   ↓   ↓
       └───d → e → f

If the outer square and the RHS are pullbacks then the LHS is a pullback
-/
def PBL_left {C : Type u}{a b c d e f : C} [Category C]
  (ab : Hom a b) (bc : Hom b c)
  (ad : Hom a d) (be : Hom b e) (cf : Hom c f)
  (de : Hom d e) (ef : Hom e f)
  (rhs_pullback : IsPullback ef cf b bc be)
  (outer_pullback : IsPullback (de ≫ ef) cf a (ab ≫ bc) ad)
  (lhs_commutes : CommutativeSquare ab be ad de)
  :
  IsPullback de be a ab ad := by
  refine {commutes := ?_, mediating_morphism := ?_, unique := ?_}
  · exact lhs_commutes
  · intro T Tb Td T_commSq
    have rhs_comm : CommutativeSquare (Tb ≫ bc) cf (Td ≫ de) ef := by
      simp [CommutativeSquare]
      rw [rhs_pullback.commutes, ← Category.assoc, T_commSq, Category.assoc]
    let tb_med := rhs_pullback.mediating_morphism (Tb ≫ bc) (Td ≫ de) rhs_comm
    have tb_be := tb_med.property.right

    have Tb_eq_tb : Tb = tb_med.val :=
      rhs_pullback.unique (Tb ≫ bc) (Td ≫ de) rhs_comm Tb rfl T_commSq

    let ta_med := outer_pullback.mediating_morphism (Tb ≫ bc) Td
      (by simp [CommutativeSquare] at rhs_comm ⊢; exact rhs_comm)
    have ta_abc := ta_med.property.left
    have ta_ad := ta_med.property.right

    exact ⟨ta_med.val,
      ⟨by trans tb_med.val
          · apply rhs_pullback.unique (Tb ≫ bc) (Td ≫ de) rhs_comm
            · rw [Category.assoc]; exact ta_abc
            · rw [Category.assoc, lhs_commutes, ← Category.assoc, ta_ad]
          · exact Tb_eq_tb.symm,
       ta_ad⟩⟩
  · intro T Tb Td T_commSq ta' ta'_ab ta'_ad
    apply outer_pullback.unique (Tb ≫ bc) Td
      (by simp [CommutativeSquare]
          rw [rhs_pullback.commutes, ← Category.assoc, T_commSq, Category.assoc])
    · rw [← Category.assoc, ta'_ab]
    · exact ta'_ad


/--
       a → b
       ↓   ↓
       c → d

If bd is a mono then ac is a mono
-/
theorem mono_pullback {C : Type u}{a b c d : C} [Category C]
  {ab : Hom a b} {ac : Hom a c}
  {bd : Hom b d} {cd : Hom c d}
  (is_pullback : IsPullback cd bd a ab ac)
  (bd_mono : IsMono bd)
  : IsMono ac := by
  refine {post_cancel := ?_}
  · intro e ea ea' eq_post
    have eq₁ : ea ≫ ab ≫ bd = ea' ≫ ab ≫ bd := by
      rw [is_pullback.commutes]
      rw [<- Category.assoc, <- Category.assoc]
      rw [eq_post]
    have eq₂ : ea ≫ ab = ea' ≫ ab := by
      apply bd_mono.post_cancel
      rw [Category.assoc, Category.assoc]
      exact eq₁
    have eq₃ : ea ≫ ac = ea' ≫ ac := eq_post
    have ea_comm : CommutativeSquare (ea ≫ ab) bd (ea ≫ ac) cd := by
      simp [CommutativeSquare]
      rw [is_pullback.commutes]
    let med := is_pullback.mediating_morphism (ea ≫ ab) (ea ≫ ac) ea_comm
    have ab_eq_uniq : ea = med.val := by
      apply is_pullback.unique (ea ≫ ab) (ea ≫ ac) ea_comm
      · rfl
      · rfl
    have ab'_eq_uniq : ea' = med.val := by
      apply is_pullback.unique (ea ≫ ab) (ea ≫ ac) ea_comm
      · exact eq₂.symm
      · exact eq₃.symm
    trans med.val
    · exact ab_eq_uniq
    · rw [ab'_eq_uniq]

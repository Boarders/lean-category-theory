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
structure IsPullback {C : Type u}[Category.{v} C] {b c d : C} (bottom : Hom c d) (right : Hom b d) (obj : C) (top : Hom obj b) (left : Hom obj c) : Type (max v u) where
  commutes : CommutativeSquare top right left bottom
  mediating_morphism : ∀ {a : C}
    (top' : Hom a b) (left' : Hom a c)
    (_commutes' : CommutativeSquare top' right left' bottom),
    ∃! (i : Hom a obj) , i ≫ top = top' ∧ i ≫ left = left'

/--
When we say a category has all pullbacks, we mean that there is some specific choice
for each collection of morphisms. This is needed to define `Sub` as a functor
without using choice.
-/
def HasPullbacks (C : Type u)[Category C] :=
  ∀ {b c d : C} (cd : Hom c d) (bd : Hom b d),
    Σ (a : C) , Σ (abac : Hom a b × Hom a c),
      IsPullback cd bd a abac.fst abac.snd

def pullback_obj {C : Type u}[Category C] (hp : HasPullbacks C)
  {b c d : C} (cd : Hom c d) (bd : Hom b d) : C :=
  (hp cd bd).fst

def pullback_top {C : Type u}[Category C] (hp : HasPullbacks C)
  {b c d : C} (cd : Hom c d) (bd : Hom b d) :
  Hom (pullback_obj hp cd bd) b :=
  (hp cd bd).snd.fst.fst

def pullback_left {C : Type u}[Category C] (hp : HasPullbacks C)
  {b c d : C} (cd : Hom c d) (bd : Hom b d) :
  Hom (pullback_obj hp cd bd) c :=
  (hp cd bd).snd.fst.snd

def pullback_proof {C : Type u}[Category C] (hp : HasPullbacks C)
  {b c d : C} (cd : Hom c d) (bd : Hom b d) :
  IsPullback cd bd (pullback_obj hp cd bd)
    (pullback_top hp cd bd) (pullback_left hp cd bd) :=
  (hp cd bd).snd.snd

theorem PullbackEndo {C : Type u}[Category.{v} C] (p : C) (a b c : C)
  (pa : Hom p a) (pb : Hom p b)
  (ac : Hom a c) (bc : Hom b c)
  (is_pullback : IsPullback ac bc p pb pa)
  (i : Hom p p)
  (i_pa : i ≫ pa = pa)
  (i_pb : i ≫ pb = pb) : i = 𝟙 p := by
  -- take any mediating morphism for pb and pa
  obtain ⟨j , ⟨j_pb, j_pa⟩, j_uniq⟩ :=
    is_pullback.mediating_morphism pb pa is_pullback.commutes
  -- show i mediates
  have i_mediates : i = j := by
    apply j_uniq
    aesop
  -- show id mediates
  have id_mediates : (𝟙 p) = j := by
    apply j_uniq
    aesop
  trans j
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
  have p_mediating : ∃! (i : Hom p' p) , i ≫ pb = pb' ∧ i ≫ pa = pa' := by
    apply is_pullback.mediating_morphism
    exact is_pullback'.commutes
  have p'_mediating : ∃! (i : Hom p p') , i ≫ pb' = pb ∧ i ≫ pa' = pa := by
    apply is_pullback'.mediating_morphism
    exact is_pullback.commutes
  have pp_mediating : ∃! (i : Hom p p) , i ≫ pb = pb ∧ i ≫ pa = pa := by
    apply is_pullback.mediating_morphism
    exact is_pullback.commutes
  have p'p'_mediating : ∃! (i : Hom p' p') , i ≫ pb' = pb' ∧ i ≫ pa' = pa' := by
    apply is_pullback'.mediating_morphism
    exact is_pullback'.commutes
  obtain ⟨f , ⟨f_pb, f_pa⟩, _f_uniq⟩ := p_mediating
  obtain ⟨g , ⟨g_pb, g_pa⟩, _g_uniq⟩ := p'_mediating
  obtain ⟨i , ⟨_i_pb, _i_pa⟩, i_uniq⟩ := pp_mediating
  obtain ⟨i' , ⟨_i'_pb, _i'_pa⟩, i'_uniq⟩ := p'p'_mediating
  exists f
  simp [IsIso']
  exists g
  -- prove g is a two sided inverse
  constructor
  · trans i
    · apply i_uniq
      rw [Category.assoc, Category.assoc]
      rw [f_pb, g_pb, f_pa, g_pa]
      aesop
    · symm
      apply i_uniq
      rw [Category.id_comp, Category.id_comp]
      aesop
  · trans i'
    · apply i'_uniq
      rw [Category.assoc, Category.assoc]
      rw [g_pb, f_pb, g_pa, f_pa]
      aesop
    · symm
      apply i'_uniq
      rw [Category.id_comp, Category.id_comp]
      aesop



















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
  refine {commutes := ?_, mediating_morphism := ?_}
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
    have Tb : ∃! (i : Hom T b) , i ≫ bc = Tc ∧ i ≫ be = Td ≫ de  := by
      apply rhs_pullback.mediating_morphism
      simp [CommutativeSquare]
      rw [T_commSq]
    have map_to_a : ∃! (i : Hom T a) , i ≫ ab = Tb.fst ∧ i ≫ ad = Td  := by
      apply lhs_pullback.mediating_morphism
      simp [CommutativeSquare]
    have Ta : ∃! i, i ≫ ab ≫ bc = Tc ∧ i ≫ ad = Td  := by
      cases map_to_a with
      | intro i P =>
        exists i
        constructor
        · simp
        · intro Ta'
          simp
    exact Ta


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
  refine {commutes := ?_, mediating_morphism := ?_}
  · exact lhs_commutes
  · intro T Tb Td T_commSq
    have Tb : ∃! (i : Hom T b) , i ≫ bc = Tb ≫ bc ∧ i ≫ be = Td ≫ de  := by
      apply rhs_pullback.mediating_morphism
      simp [CommutativeSquare]
      -- need to show: Tb ≫ bc ≫ cf = Td ≫ de ≫ ef
      have eq_1 : Tb ≫ bc ≫ cf = Tb ≫ be ≫ ef := by
        rw [rhs_pullback.commutes]
      have eq_2 : Tb ≫ be ≫ ef = Td ≫ de ≫ ef := by
        rw [<- Category.assoc, <- Category.assoc]
        rw [T_commSq]
      trans Tb ≫ be ≫ ef
      · exact eq_1
      · exact eq_2
    have map_to_a : ∃! (i : Hom T a) , i ≫ ab ≫ bc = Tb.fst ≫ bc ∧ i ≫ ad = Td  := by
      apply outer_pullback.mediating_morphism
      simp [CommutativeSquare]
    have Ta : ∃! (i : Hom T a), i ≫ ab = Tb.fst ∧ i ≫ ad = Td  := by
      cases map_to_a with
      | intro i P =>
        exists i
        constructor
        · simp
        · intro Ta'
          simp
    exact Ta


/--
       a → b
       ↓   ↓
       c → d

If bd is a mono then ac is a mono
-/
def mono_pullback {C : Type u}{a b c d : C} [Category C]
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
    have uniq_ea : ∃! (i : Hom e a), i ≫ ab = ea ≫ ab ∧ i ≫ ac = ea ≫ ac  := by
      apply is_pullback.mediating_morphism
      · simp [CommutativeSquare]
        rw [is_pullback.commutes]
    have eq₃ : ea ≫ ac = ea' ≫ ac := by
      exact eq_post
    obtain ⟨witness_ea, ⟨witness_ab, witness_ac⟩, unique_ea⟩ := uniq_ea
    have ab_eq_uniq : ea = witness_ea := by
      apply unique_ea
      -- prove that ea is also mediating
      constructor
      · rfl
      · rfl
    have ab'_eq_uniq : ea' = witness_ea := by
      apply unique_ea
      -- prove that ea' is also mediating
      constructor
      · rw [eq₂]
      · rw [eq₃]
    trans witness_ea
    · exact ab_eq_uniq
    · rw [ab'_eq_uniq]

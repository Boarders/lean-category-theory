import CategoryTheory.Category
import CategoryTheory.Contravariant.Functor
import CategoryTheory.Morphisms
import CategoryTheory.Pullback
import CategoryTheory.TerminalObject
import CategoryTheory.Monos
import Mathlib.Data.Quot


universe u₁ u₂ v₁ v₂ u v

namespace Cat

open Quiver
open DeductiveSystem
open Category


structure SubobjectClassifier (C : Type i) [Category C] [HasTerminalObject C] where
  Ω : C
  true : Hom (terminal_object C) Ω
  ch : ∀ {c d} {f : Hom c d} , IsMono f → Hom d Ω
  /--
         !
       c → t
     f ↓   ↓ true
       d → Ω
        ch f
  -/
  pullback : ∀ {c d} {f : Hom c d} {i : IsMono f} ,
     IsPullback (ch i) true c (terminal_map c) f
  unique : ∀ {c d } {f : Hom c d} {g : Hom d Ω} {i : IsMono f} ,
    IsPullback g true c (terminal_map c) f → ch i = g


class HasSubobjectClassifier (C : Type u)[Category C] [HasTerminalObject C] where
  get_Subobject_Classifier : SubobjectClassifier C

def p_fiber {X Y : Type u} (f : X → Y) (y : Y) : Prop :=
  ∃ (x : X) , f x = y

abbrev IsSetMono := @IsMono (Type u) inferInstance
abbrev IsSetPart := @IsPart (Type u) inferInstance
abbrev IsSetEquiv := @IsEquiv (Type u) inferInstance
abbrev IsSetPullback := @IsPullback (Type u) inferInstance
abbrev terminal_map_set := @terminal_map (Type u) inferInstance

structure TotalSpace {X : Type u}(P : X → Prop) where
  Tot : Type u
  over : Tot → X
  is_mono : @IsMono (Type u) inferInstance Tot X over

def total_space {X : Type u} (P : X → Prop) : TotalSpace P := by
 refine { Tot := ?_, over := ?_, is_mono := ?_}
 · exact {x : X // P x}
 · exact Subtype.val
 · refine {post_cancel := ?_}

   intro T t t' post_eq
   funext x
   exact Subtype.val_injective (congr_fun post_eq x)

theorem to_total
  {X Y : Type u}
  (i : X → Y) :
  IsSetPart i ((total_space (p_fiber i)).over) := by
  refine {factors := ?_}
  exact ⟨fun x => ⟨i x, ⟨x, rfl⟩⟩, rfl⟩

theorem from_total
  {X Y : Type u}
  (i : X → Y) :
  IsSetPart ((total_space (p_fiber i)).over) i := by
  refine {factors := ?_}
  let i₁ : {y : Y // p_fiber i y} → X := by
    intro y
    cases y with
    | mk y fib =>
    apply Classical.choose fib
  exists i₁
  funext y
  cases y with
  | mk y fib =>
  simp only [DeductiveSystem.comp, total_space]
  exact Classical.choose_spec fib

theorem equiv_to_subtype
  {X Y : Type u}
  (i : X → Y) : IsSetEquiv i ((total_space (p_fiber i))).over :=
  And.intro (to_total i) (from_total i)

/-
     Need to show this is a pullback:
         !
       c → t
     i ↓   ↓ true
       d → ↑Prop
      p_fiber i
-/
noncomputable def fiber_pullback
  {X Y : Type u}
  (i : X → Y) (i_mono : IsSetMono i) :
  IsPullback
    (fun y => ULift.up (p_fiber i y))
    (fun _ => ULift.up True)
    X
    (terminal_map X)
    i  := by
  refine {commutes := ?_, mediating_morphism := ?_, unique := ?_}
  · simp [CommutativeSquare, DeductiveSystem.comp, p_fiber]
  · intro T top' left' comm
    simp [CommutativeSquare, DeductiveSystem.comp, p_fiber] at comm
    -- comm shows that left' lands in the fiber of i
    have left'_in_fib : ∀ t, ∃ x, i x = left' t := by
      intro t
      have eq := congr_arg ULift.down (congr_fun comm t)
      simp at eq
      exact eq
    -- mediating map
    exact ⟨fun t => Classical.choose (left'_in_fib t), ⟨
      by apply HasTerminalObject.get_terminal.uniq_term top',
      by funext t; simp [DeductiveSystem.comp]; apply Classical.choose_spec (left'_in_fib t)⟩⟩
  · intro T top' left' comm tx top_eq left_eq
    simp [CommutativeSquare, DeductiveSystem.comp, p_fiber] at comm
    have left'_in_fib : ∀ t, ∃ x, i x = left' t := by
      intro t
      have eq := congr_arg ULift.down (congr_fun comm t)
      simp at eq
      exact eq
    -- Use that i is a mono to show the mediating map is unique
    apply i_mono.post_cancel
    simp [DeductiveSystem.comp]
    funext t
    have h₁ : i (tx t) = left' t := congr_fun left_eq t
    have h₂ : i (Classical.choose (left'_in_fib t)) = left' t := Classical.choose_spec (left'_in_fib t)
    rw [h₁, h₂]


noncomputable instance : HasSubobjectClassifier (Type u) where
  get_Subobject_Classifier := by
    refine {Ω := ?_, true := ?_, ch := ?_, pullback := ?_, unique := ?_}
    · exact ULift Prop
    · exact fun _c => ULift.up True
    · intro C D f _f_mono d
      exact (ULift.up (p_fiber f d))
    /-
     Need to show this is a pullback:
         !
       c → t
     i ↓   ↓ true
       d → ↑Prop
      p_fiber i
    -/
    · intro _c _d i i_mono
      exact fiber_pullback i i_mono
    · intro C D i ch' i_mono ch'_pullback
      cases ch'_pullback with
      | mk commutes mediating uniq =>
      simp [CommutativeSquare, DeductiveSystem.comp] at commutes
      funext d
      ext
      constructor
      · simp [p_fiber]
        intro x ix_d
        rw [<- ix_d, <- (congr_fun commutes x)]
        simp
      · simp [p_fiber]
        intro ch'_d
        have ch'_d_true : (ch' d).down = True := by
          apply propext
          constructor
          · simp
          · intro _
            exact ch'_d
        have med_comm : CommutativeSquare (terminal_map (ULift Unit)) (fun _ => ULift.up True) (fun _ => d) ch' := by
          simp [CommutativeSquare, terminal_map]
          funext _
          rw [<- ch'_d_true]
          rfl
        let med := mediating (terminal_map (ULift Unit)) (fun _ => d) med_comm
        exists (med.val (ULift.up ()))
        apply congr_fun med.property.right

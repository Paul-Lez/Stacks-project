/-
Copyright (c) 2024 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/
import LS.Stacks.Basic

/-!

# THe empty stack

This file defines a category structure on the empty type and shows that it is a stack over itself

-/

open CategoryTheory Functor Category

instance : Category Empty where
  Hom a _ := by cases a
  id a := by cases a
  comp := by aesop

lemma EmptyCone {C : Type*} [Category C] (p : C ⥤ Empty) : IsEmpty (Limits.Cone p) := ⟨by  intro a ; cases a.pt⟩

lemma EmptyLimitCone {C : Type*} [Category C] (p : C ⥤ Empty) : IsEmpty (Limits.LimitCone p) :=
  ⟨fun a => isEmpty_iff.mp (EmptyCone p) a.cone⟩

instance {C : Type*} [Category C] [Nonempty C] : Limits.HasLimitsOfShape C Empty := by
  constructor
  intro F ; cases F.obj (Classical.ofNonempty)

instance : Limits.HasPullbacks Empty := ⟨fun F => Limits.hasLimitOfHasLimitsOfShape F⟩

variable (J : GrothendieckTopology Empty)

lemma IsFiberedInGroupoid.EmptyCat.id : IsFiberedInGroupoids (Functor.id Empty) where
  has_pullbacks := fun a f => by aesop
  IsPullback := fun a => by aesop

lemma EmptyCat_morphisms_glue : morphisms_glue J (IsFiberedInGroupoid.EmptyCat.id) := fun S => by cases S

lemma EmptyCat_objects_glue : objects_glue J (IsFiberedInGroupoid.EmptyCat.id) := fun S => by cases S.toPreDescentData.S

instance emptyStack : Stack J IsFiberedInGroupoid.EmptyCat.id where
  GlueMorphism := EmptyCat_morphisms_glue J
  ObjectsGlue := EmptyCat_objects_glue J

#print axioms emptyStack

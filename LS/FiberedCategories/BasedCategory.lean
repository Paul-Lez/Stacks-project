/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import LS.FiberedCategories.Basic
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Functor.Category
-- import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
# The bicategory of based categories

In this file we define the type `BasedCategory 𝒮`, and give it the structure of a (strict) bicategory.

The type `BasedCategory 𝒮` is defined as the type of categories `𝒳` equiped with a functor `𝒳.p : 𝒳 ⥤ 𝒮`.

Functors between based categories, `BasedFunctor`, are defined as functors between the underlying categories
that commute with the projections.

Natural transformations between based functors, `BasedNatTrans`, are defined as natural transformations `α`
such that `α.app a` lifts `𝟙 S` whenever `𝒳.p.obj a = S`.

-/

universe u₁ v₁ u₂ v₂

open CategoryTheory Functor Category NatTrans

namespace Fibered

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- A based category over `𝒮` is a category `𝒳` together with a functor `p : 𝒳 ⥤ 𝒮` -/
structure BasedCategory (𝒮 : Type u₁) [Category.{v₁} 𝒮] where
  (cat : Type u₂) -- TODO: other types also OK?
  [isCat : Category.{v₂} cat]
  (p : cat ⥤ 𝒮)

-- TODO: can this be done automatically?
instance (𝒳 : BasedCategory 𝒮) : Category 𝒳.cat := 𝒳.isCat

/-- A functor between based categories is a functor between the underlying categories that commutes with the projections. -/
structure BasedFunctor (𝒳 𝒴 : BasedCategory 𝒮) extends CategoryTheory.Functor 𝒳.cat 𝒴.cat where
  (w : toFunctor ⋙ 𝒴.p = 𝒳.p)

/-- The identity functor is also a `BasedFunctor` -/
@[simps!]
protected def BasedFunctor.id (𝒳 : BasedCategory 𝒮) : BasedFunctor 𝒳 𝒳 :=
  { 𝟭 𝒳.cat with w := CategoryTheory.Functor.id_comp _ }

/-- Composition of `BasedFunctor`s is defined as the composition of the underlying functors -/
@[simps!]
def BasedFunctor.comp {𝒳 𝒴 𝒵 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴)
    (G : BasedFunctor 𝒴 𝒵) : BasedFunctor 𝒳 𝒵 :=
  { F.toFunctor ⋙ G.toFunctor with w := by rw [Functor.assoc, G.w, F.w] }

@[simp]
lemma BasedFunctor.assoc {𝒳 𝒴 𝒵 𝒯 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒴 𝒵)
    (H : BasedFunctor 𝒵 𝒯) : BasedFunctor.comp (BasedFunctor.comp F G) H = BasedFunctor.comp F (BasedFunctor.comp G H) := rfl

@[simp]
lemma BasedFunctor.comp_id {𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) : BasedFunctor.comp (BasedFunctor.id 𝒳) F = F := rfl

@[simp]
lemma BasedFunctor.id_comp {𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) : BasedFunctor.comp F (BasedFunctor.id 𝒴) = F := rfl

-- TODO: possibly think about renaming these

@[simp]
lemma BasedFunctor.obj_proj {𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) (a : 𝒳.cat) :
    𝒴.p.obj (F.obj a) = 𝒳.p.obj a := by
  rw [←Functor.comp_obj, F.w]

lemma BasedFunctor.IsHomLift_map{𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴)
    {a b : 𝒳.cat} (φ : a ⟶ b) : IsHomLift 𝒴.p (𝒳.p.map φ) (F.map φ) where
  ObjLiftDomain := BasedFunctor.obj_proj F a
  ObjLiftCodomain := BasedFunctor.obj_proj F b
  HomLift := ⟨by simp [congr_hom F.w.symm]⟩

lemma BasedFunctor.pres_IsHomLift {𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴)
    {R S : 𝒮} {a b : 𝒳.cat} {φ : a ⟶ b} {f : R ⟶ S} (hφ : IsHomLift 𝒳.p f φ) : IsHomLift 𝒴.p f (F.map φ) where
  ObjLiftDomain := Eq.trans (BasedFunctor.obj_proj F a) hφ.ObjLiftDomain
  ObjLiftCodomain := Eq.trans (BasedFunctor.obj_proj F b) hφ.ObjLiftCodomain
  HomLift := ⟨by
    rw [←Functor.comp_map, congr_hom F.w]
    simp [hφ.3.1] ⟩

lemma BasedFunctor.HomLift_ofImage {𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) {S R : 𝒮} {a b : 𝒳.cat}
    {φ : a ⟶ b} {f : R ⟶ S} (hφ : IsHomLift 𝒴.p f (F.map φ)) : IsHomLift 𝒳.p f φ where
  ObjLiftDomain := F.obj_proj a ▸ hφ.ObjLiftDomain
  ObjLiftCodomain := F.obj_proj b ▸ hφ.ObjLiftCodomain
  HomLift := ⟨by
    rw [congr_hom F.w.symm]
    simp only [Functor.comp_map, Category.assoc, eqToHom_trans, hφ.HomLift.1,
      eqToHom_trans_assoc]⟩

/-- A `BasedNatTrans` between two `BasedFunctor`s is a natural transformation `α` between the underlying functors,
    such that for all `a : 𝒳`, `α.app a` lifts `𝟙 S` whenever `𝒳.p.obj a = S`. -/
structure BasedNatTrans {𝒳 𝒴 : BasedCategory 𝒮} (F G : BasedFunctor 𝒳 𝒴) extends
  CategoryTheory.NatTrans F.toFunctor G.toFunctor where
  (aboveId : ∀ {a : 𝒳.cat} {S : 𝒮} (_ : 𝒳.p.obj a = S), IsHomLift 𝒴.p (𝟙 S) (toNatTrans.app a))

@[ext]
lemma BasedNatTrans.ext {𝒳 𝒴 : BasedCategory 𝒮} {F G : BasedFunctor 𝒳 𝒴} (α β : BasedNatTrans F G)
  (h : α.toNatTrans = β.toNatTrans) : α = β := by
  cases α
  cases β
  simp at h
  subst h
  rfl

/-- The identity natural transformation is also a `BasedNatTrans` -/
@[simps!]
def BasedNatTrans.id {𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) : BasedNatTrans F F := {
  toNatTrans := CategoryTheory.NatTrans.id F.toFunctor
  aboveId := by
    intro a S ha
    constructor
    · constructor
      simp only [NatTrans.id_app', map_id, id_comp, comp_id]
    all_goals rwa [←CategoryTheory.Functor.comp_obj, F.w] }

@[simp]
lemma BasedNatTrans.id_toNatTrans {𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) : (BasedNatTrans.id F).toNatTrans = CategoryTheory.NatTrans.id F.toFunctor := rfl

/-- Composition of `BasedNatTrans`s, given by composition of the underlying natural transformations -/
def BasedNatTrans.comp {𝒳 𝒴 : BasedCategory 𝒮} {F G H : BasedFunctor 𝒳 𝒴} (α : BasedNatTrans F G) (β : BasedNatTrans G H) :
  BasedNatTrans F H := {
    toNatTrans := CategoryTheory.NatTrans.vcomp α.toNatTrans β.toNatTrans
    aboveId := by
      intro a S ha
      rw [CategoryTheory.NatTrans.vcomp_app, show 𝟙 S = 𝟙 S ≫ 𝟙 S by simp only [comp_id]]
      apply IsHomLift.comp (α.aboveId ha) (β.aboveId ha)
  }

@[simp]
lemma BasedNatTrans.comp_app {𝒳 𝒴 : BasedCategory 𝒮} {F G H : BasedFunctor 𝒳 𝒴} (α : BasedNatTrans F G)
    (β : BasedNatTrans G H) (x : 𝒳.cat) : (comp α β).app x = (α.app x) ≫ β.app x:= rfl

@[simp]
lemma CategoryTheory.NatTrans.id_vcomp {C D : Type _} [Category C] [Category D] {F G : C ⥤ D}
    (f : NatTrans F G) :
  NatTrans.vcomp (NatTrans.id F) f = f := by
  ext x
  simp only [vcomp_eq_comp, comp_app, id_app', id_comp]

@[simp]
lemma CategoryTheory.NatTrans.vcomp_id {C D : Type _} [Category C] [Category D] {F G : C ⥤ D}
    (f : NatTrans F G) :
  NatTrans.vcomp f (NatTrans.id G) = f := by
  ext x
  simp only [vcomp_eq_comp, comp_app, id_app', comp_id]

@[simp]
lemma BasedNatTrans.comp_toNatTrans {𝒳 𝒴 : BasedCategory 𝒮} {F G H : BasedFunctor 𝒳 𝒴}
    (α : BasedNatTrans F G) (β : BasedNatTrans G H) :
    (comp α β).toNatTrans = NatTrans.vcomp α.toNatTrans β.toNatTrans := rfl

@[simp]
lemma BasedNatTrans.id_comp {𝒳 𝒴 : BasedCategory 𝒮} {F G : BasedFunctor 𝒳 𝒴} (α : BasedNatTrans F G) :
  BasedNatTrans.comp (BasedNatTrans.id F) α = α := by
  apply BasedNatTrans.ext
  rw [BasedNatTrans.comp_toNatTrans, BasedNatTrans.id_toNatTrans, CategoryTheory.NatTrans.id_vcomp]

@[simp]
lemma BasedNatTrans.comp_id {𝒳 𝒴 : BasedCategory 𝒮} {F G : BasedFunctor 𝒳 𝒴} (α : BasedNatTrans F G) :
  BasedNatTrans.comp α (BasedNatTrans.id G) = α := by
  apply BasedNatTrans.ext
  rw [BasedNatTrans.comp_toNatTrans, BasedNatTrans.id_toNatTrans, CategoryTheory.NatTrans.vcomp_id]

lemma BasedNatTrans.comp_assoc {𝒳 𝒴 : BasedCategory 𝒮} {F G H I : BasedFunctor 𝒳 𝒴}
    (α : BasedNatTrans F G) (β : BasedNatTrans G H) (γ : BasedNatTrans H I) :
    BasedNatTrans.comp (BasedNatTrans.comp α β) γ = BasedNatTrans.comp α (BasedNatTrans.comp β γ):= by
  apply BasedNatTrans.ext
  rw [BasedNatTrans.comp_toNatTrans, BasedNatTrans.comp_toNatTrans, BasedNatTrans.comp_toNatTrans, BasedNatTrans.comp_toNatTrans, NatTrans.vcomp_eq_comp, NatTrans.vcomp_eq_comp, NatTrans.vcomp_eq_comp, NatTrans.vcomp_eq_comp, assoc]

@[simps]
instance homCategory (𝒳 𝒴 : BasedCategory 𝒮) : Category (BasedFunctor 𝒳 𝒴) where
  Hom := BasedNatTrans
  id := BasedNatTrans.id
  comp := BasedNatTrans.comp
  id_comp := BasedNatTrans.id_comp
  comp_id := BasedNatTrans.comp_id
  assoc := BasedNatTrans.comp_assoc

-- TODO: why do I need this?
@[ext]
lemma homCategory.ext {𝒳 𝒴 : BasedCategory 𝒮} {F G : BasedFunctor 𝒳 𝒴} (α β : F ⟶ G)
    (h : α.toNatTrans = β.toNatTrans) : α = β := BasedNatTrans.ext α β h

@[simps]
def BasedFunctor.associator {𝒳 𝒴 𝒵 𝒱 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒴 𝒵)
    (H : BasedFunctor 𝒵 𝒱) :
  BasedFunctor.comp (BasedFunctor.comp F G) H ≅ BasedFunctor.comp F (BasedFunctor.comp G H) where
    hom := {
      app := fun _ => 𝟙 _
      aboveId := by
        intro a S ha
        apply IsHomLift.id
        simp only [obj_proj, ha] }
    inv := {
      app := fun _ => 𝟙 _
      aboveId := by
        intro a S ha
        apply IsHomLift.id
        simp only [obj_proj, ha] }

@[simps]
def BasedFunctor.leftUnitor {𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) :
  BasedFunctor.comp (BasedFunctor.id 𝒳) F ≅ F where
    hom := {
      app := fun a => 𝟙 (F.obj a)
      naturality := by
        intros
        simp
      aboveId := by
        intro a S ha
        apply IsHomLift.id
        simp only [obj_proj, ha] }
    inv := {
      app := fun a => 𝟙 (F.obj a)
      aboveId := by
        intro a S ha
        apply IsHomLift.id
        simp only [obj_proj, ha] }

@[simps]
def BasedFunctor.rightUnitor {𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) :
  BasedFunctor.comp F (BasedFunctor.id 𝒴) ≅ F where
    hom := {
      app := fun a => 𝟙 (F.obj a)
      naturality := by
        intros
        simp
      aboveId := by
        intro a S ha
        apply IsHomLift.id
        simp only [obj_proj, ha] }
    inv := {
      app := fun a => 𝟙 (F.obj a)
      aboveId := by
        intro a S ha
        apply IsHomLift.id
        simp only [obj_proj, ha] }

@[simps!]
def BasedCategory.whiskerLeft {𝒳 𝒴 𝒵 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴)
    {G H : BasedFunctor 𝒴 𝒵} (α : G ⟶ H) : BasedFunctor.comp F G ⟶ BasedFunctor.comp F H := {
  CategoryTheory.whiskerLeft F.toFunctor α.toNatTrans with
  aboveId := by
    intro a S ha
    apply α.aboveId
    simp only [BasedFunctor.obj_proj, ha] }

@[simps!]
def BasedCategory.whiskerRight {𝒳 𝒴 𝒵 : BasedCategory 𝒮} {F G : BasedFunctor 𝒳 𝒴} (α : F ⟶ G)
    (H : BasedFunctor 𝒴 𝒵) : BasedFunctor.comp F H ⟶ BasedFunctor.comp G H := {
  CategoryTheory.whiskerRight α.toNatTrans H.toFunctor with
  aboveId := by
    intro a S ha
    apply BasedFunctor.pres_IsHomLift
    apply α.aboveId ha }

instance BasedCategory.bicategory : Bicategory (BasedCategory 𝒮) where
  Hom := BasedFunctor
  id := BasedFunctor.id
  comp := BasedFunctor.comp
  homCategory 𝒳 𝒴 := homCategory 𝒳 𝒴
  whiskerLeft := BasedCategory.whiskerLeft
  whiskerRight {𝒳 𝒴 𝒵} F G α H := BasedCategory.whiskerRight α H
  associator := BasedFunctor.associator
  leftUnitor {𝒳 𝒴} F := BasedFunctor.leftUnitor F
  rightUnitor {𝒳 𝒴} F := BasedFunctor.rightUnitor F

instance : Bicategory.Strict (BasedCategory 𝒮) where
  id_comp := BasedFunctor.id_comp
  comp_id := BasedFunctor.comp_id
  assoc := BasedFunctor.assoc

/-
def BasedCategory.prod (𝒳 𝒴 : BasedCategory 𝒮) : BasedCategory 𝒮 where

 -/
end Fibered

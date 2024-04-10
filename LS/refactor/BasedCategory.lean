import LS.refactor.Basic

import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
In this file give the type `BasedCategory 𝒮` the structure of a (strict) bicategory.

-/

universe u₁ v₁ u₂ v₂

open CategoryTheory Functor Category NatTrans Fibered

namespace Based

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/- 1-Morphisms

-/

structure Morphism (𝒳 𝒴 : BasedCategory 𝒮) extends CategoryTheory.Functor 𝒳.1 𝒴.1 where
  (w : toFunctor ⋙ 𝒴.p = 𝒳.p)

@[simps!]
protected def Morphism.id (𝒳 : BasedCategory 𝒮) : Morphism 𝒳 𝒳 :=
  { 𝟭 𝒳.1 with w := CategoryTheory.Functor.id_comp _ }

@[simps!]
def Morphism.comp {𝒳 𝒴 𝒵 : BasedCategory 𝒮} (F : Morphism 𝒳 𝒴)
    (G : Morphism 𝒴 𝒵) : Morphism 𝒳 𝒵 :=
  { F.toFunctor ⋙ G.toFunctor with w := by rw [Functor.assoc, G.w, F.w] }

@[simp]
lemma Morphism.assoc {𝒳 𝒴 𝒵 𝒯 : BasedCategory 𝒮} (F : Morphism 𝒳 𝒴) (G : Morphism 𝒴 𝒵)
    (H : Morphism 𝒵 𝒯) : Morphism.comp (Morphism.comp F G) H = Morphism.comp F (Morphism.comp G H) := rfl

@[simp]
lemma Morphism.comp_id {𝒳 𝒴 : BasedCategory 𝒮} (F : Morphism 𝒳 𝒴) : Morphism.comp (Morphism.id 𝒳) F = F := rfl

@[simp]
lemma Morphism.id_comp {𝒳 𝒴 : BasedCategory 𝒮} (F : Morphism 𝒳 𝒴) : Morphism.comp F (Morphism.id 𝒴) = F := rfl

@[simp]
lemma Morphism.obj_proj {𝒳 𝒴 : BasedCategory 𝒮} (F : Morphism 𝒳 𝒴) (a : 𝒳.1) :
    𝒴.p.obj (F.obj a) = 𝒳.p.obj a := by
  rw [←Functor.comp_obj, F.w]

lemma Morphism.IsHomLift_map{𝒳 𝒴 : BasedCategory 𝒮} (F : Morphism 𝒳 𝒴)
    {a b : 𝒳.1} (φ : a ⟶ b) : IsHomLift 𝒴 (𝒳.p.map φ) (F.map φ) where
  ObjLiftDomain := Morphism.obj_proj F a
  ObjLiftCodomain := Morphism.obj_proj F b
  HomLift := ⟨by simp [congr_hom F.w.symm]⟩

lemma Morphism.pres_IsHomLift {𝒳 𝒴 : BasedCategory 𝒮} (F : Morphism 𝒳 𝒴)
    {R S : 𝒮} {a b : 𝒳.1} {φ : a ⟶ b} {f : R ⟶ S} (hφ : IsHomLift 𝒳 f φ) : IsHomLift 𝒴 f (F.map φ) where
  ObjLiftDomain := Eq.trans (Morphism.obj_proj F a) hφ.ObjLiftDomain
  ObjLiftCodomain := Eq.trans (Morphism.obj_proj F b) hφ.ObjLiftCodomain
  HomLift := ⟨by
    rw [←Functor.comp_map, congr_hom F.w]
    simp [hφ.3.1] ⟩

lemma Morphism.HomLift_ofImage {𝒳 𝒴 : BasedCategory 𝒮} (F : Morphism 𝒳 𝒴) {S R : 𝒮} {a b : 𝒳.1}
    {φ : a ⟶ b} {f : R ⟶ S} (hφ : IsHomLift 𝒴 f (F.map φ)) : IsHomLift 𝒳 f φ where
  ObjLiftDomain := F.obj_proj a ▸ hφ.ObjLiftDomain
  ObjLiftCodomain := F.obj_proj b ▸ hφ.ObjLiftCodomain
  HomLift := ⟨by
    rw [congr_hom F.w.symm]
    simp only [Functor.comp_map, Category.assoc, eqToHom_trans, hφ.HomLift.1,
      eqToHom_trans_assoc]⟩


/-- TWOMORPHISMS -/

structure TwoMorphism {𝒳 𝒴 : BasedCategory 𝒮} (F G : Morphism 𝒳 𝒴) extends
  CategoryTheory.NatTrans F.toFunctor G.toFunctor where
  (aboveId : ∀ {a : 𝒳.carrier} {S : 𝒮} (_ : 𝒳.p.obj a = S), IsHomLift 𝒴 (𝟙 S) (toNatTrans.app a))

@[ext]
lemma TwoMorphism.ext {𝒳 𝒴 : BasedCategory 𝒮} {F G : Morphism 𝒳 𝒴} (α β : TwoMorphism F G)
  (h : α.toNatTrans = β.toNatTrans) : α = β := by
  cases α
  cases β
  simp at h
  subst h
  rfl

def TwoMorphism.id {𝒳 𝒴 : BasedCategory 𝒮} (F : Morphism 𝒳 𝒴) : TwoMorphism F F := {
  toNatTrans := CategoryTheory.NatTrans.id F.toFunctor
  aboveId := by
    intro a S ha
    constructor
    · constructor
      simp only [NatTrans.id_app', map_id, id_comp, comp_id]
    all_goals rwa [←CategoryTheory.Functor.comp_obj, F.w] }

@[simp]
lemma TwoMorphism.id_toNatTrans {𝒳 𝒴 : BasedCategory 𝒮} (F : Morphism 𝒳 𝒴) : (TwoMorphism.id F).toNatTrans = CategoryTheory.NatTrans.id F.toFunctor := rfl

def TwoMorphism.comp {𝒳 𝒴 : BasedCategory 𝒮} {F G H : Morphism 𝒳 𝒴} (α : TwoMorphism F G) (β : TwoMorphism G H) :
  TwoMorphism F H := {
    toNatTrans := CategoryTheory.NatTrans.vcomp α.toNatTrans β.toNatTrans
    aboveId := by
      intro a S ha
      rw [CategoryTheory.NatTrans.vcomp_app, show 𝟙 S = 𝟙 S ≫ 𝟙 S by simp only [comp_id]]
      apply IsHomLift_comp (α.aboveId ha) (β.aboveId ha)
  }

@[simp]
lemma TwoMorphism.comp_app {𝒳 𝒴 : BasedCategory 𝒮} {F G H : Morphism 𝒳 𝒴} (α : TwoMorphism F G)
    (β : TwoMorphism G H) (x : 𝒳.1) : (comp α β).app x = (α.app x) ≫ β.app x:= rfl

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
lemma TwoMorphism.comp_toNatTrans {𝒳 𝒴 : BasedCategory 𝒮} {F G H : Morphism 𝒳 𝒴}
    (α : TwoMorphism F G) (β : TwoMorphism G H) :
    (comp α β).toNatTrans = NatTrans.vcomp α.toNatTrans β.toNatTrans := rfl

@[simp]
lemma TwoMorphism.id_comp {𝒳 𝒴 : BasedCategory 𝒮} {F G : Morphism 𝒳 𝒴} (α : TwoMorphism F G) :
  TwoMorphism.comp (TwoMorphism.id F) α = α := by
  apply TwoMorphism.ext
  rw [TwoMorphism.comp_toNatTrans, TwoMorphism.id_toNatTrans, CategoryTheory.NatTrans.id_vcomp]

@[simp]
lemma TwoMorphism.comp_id {𝒳 𝒴 : BasedCategory 𝒮} {F G : Morphism 𝒳 𝒴} (α : TwoMorphism F G) :
  TwoMorphism.comp α (TwoMorphism.id G) = α := by
  apply TwoMorphism.ext
  rw [TwoMorphism.comp_toNatTrans, TwoMorphism.id_toNatTrans, CategoryTheory.NatTrans.vcomp_id]

lemma TwoMorphism.comp_assoc {𝒳 𝒴 : BasedCategory 𝒮} {F G H I : Morphism 𝒳 𝒴}
    (α : TwoMorphism F G) (β : TwoMorphism G H) (γ : TwoMorphism H I) :
    TwoMorphism.comp (TwoMorphism.comp α β) γ = TwoMorphism.comp α (TwoMorphism.comp β γ):= by
  apply TwoMorphism.ext
  rw [TwoMorphism.comp_toNatTrans, TwoMorphism.comp_toNatTrans, TwoMorphism.comp_toNatTrans, TwoMorphism.comp_toNatTrans, NatTrans.vcomp_eq_comp, NatTrans.vcomp_eq_comp, NatTrans.vcomp_eq_comp, NatTrans.vcomp_eq_comp, assoc]

@[simps]
instance homCategory (𝒳 𝒴 : BasedCategory 𝒮) : Category (Morphism 𝒳 𝒴) where
  Hom := TwoMorphism
  id := TwoMorphism.id
  comp := TwoMorphism.comp
  id_comp := TwoMorphism.id_comp
  comp_id := TwoMorphism.comp_id
  assoc := TwoMorphism.comp_assoc

-- TODO: why do I need this?
@[ext]
lemma homCategory.ext {𝒳 𝒴 : BasedCategory 𝒮} {F G : Morphism 𝒳 𝒴} (α β : F ⟶ G)
    (h : α.toNatTrans = β.toNatTrans) : α = β := TwoMorphism.ext α β h

@[simps]
def Morphism.associator {𝒳 𝒴 𝒵 𝒱 : BasedCategory 𝒮} (F : Morphism 𝒳 𝒴) (G : Morphism 𝒴 𝒵)
    (H : Morphism 𝒵 𝒱) :
  Morphism.comp (Morphism.comp F G) H ≅ Morphism.comp F (Morphism.comp G H) where
    hom := {
      app := fun _ => 𝟙 _
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [obj_proj, ha]
    }
    inv := {
      app := fun _ => 𝟙 _
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [obj_proj, ha]
    }

@[simps]
def Morphism.leftUnitor {𝒳 𝒴 : BasedCategory 𝒮} (F : Morphism 𝒳 𝒴) :
  Morphism.comp (Morphism.id 𝒳) F ≅ F where
    hom :=
    {
      app := fun a => 𝟙 (F.obj a)
      naturality := by
        intros
        simp
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [obj_proj, ha]
    }
    inv := {
      app := fun a => 𝟙 (F.obj a)
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [obj_proj, ha]
    }

@[simps]
def Morphism.rightUnitor {𝒳 𝒴 : BasedCategory 𝒮} (F : Morphism 𝒳 𝒴) :
  Morphism.comp F (Morphism.id 𝒴) ≅ F where
    hom :=
    {
      app := fun a => 𝟙 (F.obj a)
      naturality := by
        intros
        simp
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [obj_proj, ha]
    }
    inv := {
      app := fun a => 𝟙 (F.obj a)
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [obj_proj, ha]
    }

instance : Bicategory (BasedCategory 𝒮) where
  Hom := Morphism
  id := Morphism.id
  comp := Morphism.comp
  homCategory 𝒳 𝒴 := homCategory 𝒳 𝒴
  whiskerLeft {𝒳 𝒴 𝒵} F {G H} α := {
      whiskerLeft F.toFunctor α.toNatTrans with
      aboveId := by
        intro a S ha
        apply α.aboveId
        simp only [Morphism.obj_proj, ha]
    }

  -- TODO: weird that this has non-implicit arguments and above doesnt
  whiskerRight {𝒳 𝒴 𝒵} F G α H := {
    whiskerRight α.toNatTrans H.toFunctor with
    aboveId := by
      intro a S ha
      apply Morphism.pres_IsHomLift
      apply α.aboveId ha
  }
  associator := Morphism.associator
  leftUnitor {𝒳 𝒴} F := Morphism.leftUnitor F
  rightUnitor {𝒳 𝒴} F := Morphism.rightUnitor F

instance : Bicategory.Strict (BasedCategory 𝒮) where
  id_comp := Morphism.id_comp
  comp_id := Morphism.comp_id
  assoc := Morphism.assoc


end Based


--instance : Bicategory (Bundled IsFibered)

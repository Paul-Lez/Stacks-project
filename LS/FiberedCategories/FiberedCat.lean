/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/


import LS.FiberedCategories.BasedCategory
import LS.FiberedCategories.HasFibers

import Mathlib.CategoryTheory.Bicategory.Adjunction

/-!
# The bicategory of fibered categories

In this file we define the types `FiberCat 𝒮` and `FiberedCat 𝒮` and give them the structure
of (strict) bicategories.

`FiberCat 𝒮` extends `BasedCategory 𝒮` by additionally requiring a `HasFibers` instance.
The bicategory structure is then given by:
- Morphisms are functors of based categories that preserve the fiber structure.
- 2-morphisms are based natural transformations, the same as in `BasedCategory 𝒮`

The type `FiberedCat 𝒮` extends `FiberCat 𝒮` by additionally requiring that the objects are fibered categories.
The bicategory structure is given by:
- Morphisms are as in `FiberCat 𝒮`, but are additionally required to preserve pullbacks (in the sense of fibered categories)
- 2-morphisms are the same as in `FiberCat 𝒮` and `BasedCategory 𝒮`
-/

universe u₁ v₁ u₂ v₂

open CategoryTheory Functor Category Bicategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

namespace Fibered

/-- A `FiberCat` `𝒳` is a `BasedCategory` such that the functor `p : 𝒳 ⥤ 𝒮`
    is equipped with a `HasFibers` instance. -/
structure FiberCat (𝒮 : Type u₁) [Category.{v₁} 𝒮] extends BasedCategory 𝒮 where
  /- `HasFibers` instance for `p : 𝒳 ⥤ 𝒮`. Note that if none is provided,
      the default instance is used. -/
  hasFib : HasFibers p := by infer_instance

instance (𝒳 : FiberCat 𝒮) : HasFibers 𝒳.p := 𝒳.hasFib

/-- The `FiberCat` associated to a `BasedCategory` by taking the canonical fiber structure. -/
def BasedCategory.toFiberCat (𝒳 : BasedCategory 𝒮) : FiberCat 𝒮 :=
  { 𝒳 with }

/-- A notion of functor between `FiberCat`s. It is given by a `BasedFunctor`, `F : 𝒳 ⥤ 𝒴`,
    and a collection of functors `F.onFib S : 𝒳.hasFib.Fib S ⥤ 𝒴.hasFib.Fib S` for each `S : 𝒮`
    such that the following diagram commutes for any `a : 𝒳.hasFib.Fib S`:
    ```
    𝒳.hasFib.Fib S -- F.onFib a --> 𝒴.hasFib.ι S(F(a))
      |                                       |
      |                                       |
      v                                       v
     𝒳 ---------------- F -----------------> 𝒴

    ```
 -/
structure FiberFunctor (𝒳 𝒴 : FiberCat 𝒮) extends BasedFunctor 𝒳.toBasedCategory 𝒴.toBasedCategory where
  /- A family of functors between the fibers -/
  onFib (S : 𝒮) : 𝒳.hasFib.Fib S ⥤ 𝒴.hasFib.Fib S
  /- The functors on the fibers are compatible with the underlying functor -/
  fib_w : ∀ (S : 𝒮), (onFib S) ⋙ (𝒴.hasFib.ι S) = (𝒳.hasFib.ι S) ⋙ toFunctor := by aesop_cat

@[simp]
lemma FiberFunctor.fib_w_obj {𝒳 𝒴 : FiberCat 𝒮} (F : FiberFunctor 𝒳 𝒴) {S : 𝒮}  (a : 𝒳.hasFib.Fib S) :
    (𝒴.hasFib.ι S).obj ((F.onFib S).obj a) = (F.toFunctor).obj ((𝒳.hasFib.ι S).obj a) := by
  apply congr_obj (F.fib_w S)

/-- Composition of `FiberFunctor`s, given by composition of the underlying functors. -/
@[simps!]
def FiberFunctor.comp {𝒳 𝒴 𝒵 : FiberCat 𝒮} (F : FiberFunctor 𝒳 𝒴)
    (G : FiberFunctor 𝒴 𝒵) : FiberFunctor 𝒳 𝒵 :=
  { BasedFunctor.comp F.toBasedFunctor G.toBasedFunctor with
    onFib := fun S => F.onFib S ⋙ G.onFib S
    fib_w := by
      intro S
      rw [Functor.assoc, G.fib_w, ←Functor.assoc, F.fib_w, Functor.assoc]
      rfl
  }

/-- The identity functor as a `FiberFunctor` -/
@[simps!]
def FiberFunctor.id (𝒳 : FiberCat 𝒮) : FiberFunctor 𝒳 𝒳 :=
  { BasedFunctor.id 𝒳.toBasedCategory with
    onFib := fun S => 𝟭 (𝒳.hasFib.Fib S)
    fib_w := fun S => by simp only [Functor.id_comp, Functor.comp_id]; rfl
  }

@[simp]
lemma FiberFunctor.assoc {𝒳 𝒴 𝒵 𝒯 : FiberCat 𝒮}
    (F : FiberFunctor 𝒳 𝒴) (G : FiberFunctor 𝒴 𝒵)
    (H : FiberFunctor 𝒵 𝒯) : FiberFunctor.comp (FiberFunctor.comp F G) H =
      FiberFunctor.comp F (FiberFunctor.comp G H) := rfl

@[simp]
lemma FiberFunctor.comp_id {𝒳 𝒴 : FiberCat 𝒮}
    (F : FiberFunctor 𝒳 𝒴) : FiberFunctor.comp (FiberFunctor.id 𝒳) F = F := rfl

@[simp]
lemma FiberFunctor.id_comp {𝒳 𝒴 : FiberCat 𝒮}
    (F : FiberFunctor 𝒳 𝒴) : FiberFunctor.comp F (FiberFunctor.id 𝒴) = F := rfl

-- Might be better to move this somewhere else
@[simp]
lemma BasedFunctor.fiber_proj {𝒳 𝒴 : FiberCat 𝒮} (F : 𝒳.toBasedCategory ⟶ 𝒴.toBasedCategory)
    {S : 𝒮} (a : 𝒳.hasFib.Fib S) : 𝒴.p.obj (F.obj ((𝒳.hasFib.ι S).obj a)) = S := by
  rw [BasedFunctor.obj_proj F ((𝒳.hasFib.ι S).obj a), HasFibersObjLift a]

/-- The `FiberFunctor` induced by a `BasedFunctor` by using the canonical fiber structure -/
def BasedFunctor.toFiberFunctor {𝒳 𝒴 : BasedCategory 𝒮}
    (F : 𝒳 ⟶ 𝒴) : FiberFunctor 𝒳.toFiberCat 𝒴.toFiberCat :=
{ F with
  onFib := fun S => {
    obj := fun a => ⟨F.obj a.1, by rw [F.obj_proj, a.2]⟩
    map := @fun a b φ => ⟨F.map φ.val, BasedFunctor.pres_IsHomLift F φ.2⟩
    map_id := by
      intro a
      -- TODO THIS SHOULD ALL BE SIMP SOMEHOW..
      simp [FiberCategory_id_coe 𝒳.p S a]
      rw [←Subtype.val_inj, FiberCategory_id_coe 𝒴.p S _]
    map_comp := by
      intro x y z φ ψ
      -- THIS SHOULD ALSO ALL BE SIMP SOMEHOW...
      simp [FiberCategory_comp_coe 𝒳.p S φ ψ]
      rw [←Subtype.val_inj, FiberCategory_comp_coe 𝒴.p S _ _]
  }
  fib_w := by aesop_cat
}

/-- Category structure on `FiberFunctor` -/
@[simps!]
instance FiberFunctorCategory (𝒳 𝒴 : FiberCat 𝒮) :
    Category (FiberFunctor 𝒳 𝒴) where
  Hom F G := F.toBasedFunctor ⟶ G.toBasedFunctor
  id F := 𝟙 F.toBasedFunctor
  comp α β := BasedNatTrans.comp α β

-- Maybe this can be solved if I start using full subcat?
@[ext]
lemma FiberFunctorCategory.ext {𝒳 𝒴 : FiberCat 𝒮} {F G : FiberFunctor 𝒳 𝒴} (α β : F ⟶ G)
    (h : α.toNatTrans = β.toNatTrans) : α = β := BasedNatTrans.ext α β h

@[simps]
def FiberFunctor.associator {𝒳 𝒴 𝒵 𝒱 : FiberCat 𝒮} (F : FiberFunctor 𝒳 𝒴)
    (G : FiberFunctor 𝒴 𝒵) (H : FiberFunctor 𝒵 𝒱) :
  FiberFunctor.comp (FiberFunctor.comp F G) H ≅ FiberFunctor.comp F (FiberFunctor.comp G H) :=
{ BasedFunctor.associator F.toBasedFunctor G.toBasedFunctor H.toBasedFunctor with }

@[simps]
def FiberFunctor.leftUnitor {𝒳 𝒴 : FiberCat 𝒮} (F : FiberFunctor 𝒳 𝒴) :
  FiberFunctor.comp (FiberFunctor.id 𝒳) F ≅ F :=
{ BasedFunctor.leftUnitor F.toBasedFunctor with }

@[simps]
def FiberFunctor.rightUnitor {𝒳 𝒴 : FiberCat 𝒮} (F : FiberFunctor 𝒳 𝒴) :
  FiberFunctor.comp F (FiberFunctor.id 𝒴) ≅ F :=
{ BasedFunctor.rightUnitor F.toBasedFunctor with }

@[simps!]
def FiberFunctor.whiskerLeft {𝒳 𝒴 𝒵 : FiberCat 𝒮} (F : FiberFunctor 𝒳 𝒴)
    {G H : FiberFunctor 𝒴 𝒵} (α : G ⟶ H) :=
  BasedCategory.whiskerLeft F.toBasedFunctor α

@[simps!]
def FiberFunctor.whiskerRight {𝒳 𝒴 𝒵 : FiberCat 𝒮} {F G : FiberFunctor 𝒳 𝒴}
    (α : F ⟶ G) (H : FiberFunctor 𝒴 𝒵) :=
  BasedCategory.whiskerRight α H.toBasedFunctor

instance FiberCat.bicategory : Bicategory (FiberCat 𝒮) where
  Hom 𝒳 𝒴 := FiberFunctor 𝒳 𝒴
  id 𝒳 := FiberFunctor.id 𝒳
  comp := FiberFunctor.comp
  homCategory 𝒳 𝒴 := FiberFunctorCategory 𝒳 𝒴
  whiskerLeft {𝒳 𝒴 𝒵} F {G H} α := FiberFunctor.whiskerLeft F α
  whiskerRight {𝒳 𝒴 𝒵} {F G} α H := FiberFunctor.whiskerRight α H
  associator := FiberFunctor.associator
  leftUnitor {𝒳 𝒴} F := FiberFunctor.leftUnitor F
  rightUnitor {𝒳 𝒴} F := FiberFunctor.rightUnitor F
  comp_whiskerLeft f g η h' η₁ := by apply BasedCategory.bicategory.comp_whiskerLeft
  id_whiskerRight f g := by apply BasedCategory.bicategory.id_whiskerRight
  comp_whiskerRight η θ i := by apply BasedCategory.bicategory.comp_whiskerRight
  whiskerRight_comp η f i := by apply BasedCategory.bicategory.whiskerRight_comp
  whisker_assoc f η h η₁ h₁ := by apply BasedCategory.bicategory.whisker_assoc
  whisker_exchange η θ := BasedCategory.bicategory.whisker_exchange η θ
  pentagon f g h i := by apply BasedCategory.bicategory.pentagon
  triangle f g := by apply BasedCategory.bicategory.triangle

instance : Bicategory.Strict (FiberCat 𝒮) where
  id_comp := FiberFunctor.id_comp
  comp_id := FiberFunctor.comp_id
  assoc := FiberFunctor.assoc

/-- A `FiberedCat` is a .... -/
structure FiberedCat (𝒮 : Type u₁) [Category.{v₁} 𝒮] extends FiberCat 𝒮 where
  isFibered : IsFibered p := by infer_instance

instance (𝒳 : FiberedCat 𝒮) : IsFibered 𝒳.p := 𝒳.isFibered

structure FiberedFunctor (𝒳 𝒴 : FiberedCat 𝒮) extends FiberFunctor 𝒳.toFiberCat 𝒴.toFiberCat where
  (pullback {R S : 𝒮} {f : R ⟶ S} {φ : a ⟶ b} (_ : IsPullback 𝒳.p f φ) : IsPullback 𝒴.p f (toFunctor.map φ))

@[simps!]
def FiberedFunctor.comp {𝒳 𝒴 𝒵 : FiberedCat 𝒮} (F : FiberedFunctor 𝒳 𝒴)
    (G : FiberedFunctor 𝒴 𝒵) : FiberedFunctor 𝒳 𝒵 :=
  { FiberFunctor.comp F.toFiberFunctor G.toFiberFunctor with
    pullback := fun hφ => G.pullback (F.pullback hφ) }

@[simps!]
def FiberedFunctor.id (𝒳 : FiberedCat 𝒮) : FiberedFunctor 𝒳 𝒳 :=
  { FiberFunctor.id 𝒳.toFiberCat with
    pullback := fun hφ => by simp only [FiberFunctor.id_obj, FiberFunctor.id_map, hφ]}

@[simp]
lemma FiberedFunctor.assoc {𝒳 𝒴 𝒵 𝒯 : FiberedCat 𝒮}
    (F : FiberedFunctor 𝒳 𝒴) (G : FiberedFunctor 𝒴 𝒵)
    (H : FiberedFunctor 𝒵 𝒯) : FiberedFunctor.comp (FiberedFunctor.comp F G) H =
      FiberedFunctor.comp F (FiberedFunctor.comp G H) := rfl

@[simp]
lemma FiberedFunctor.comp_id {𝒳 𝒴 : FiberedCat 𝒮}
    (F : FiberedFunctor 𝒳 𝒴) : FiberedFunctor.comp (FiberedFunctor.id 𝒳) F = F := rfl

@[simp]
lemma FiberedFunctor.id_comp {𝒳 𝒴 : FiberedCat 𝒮}
    (F : FiberedFunctor 𝒳 𝒴) : FiberedFunctor.comp F (FiberedFunctor.id 𝒴) = F := rfl

-- TODO: same as FiberFunctorCategory, is it possible to recycle that somehow?
-- Need full subcategory of a bicategory!! (or would be nice)
@[simps!]
instance FiberedHomCategory (𝒳 𝒴 : FiberedCat 𝒮) :
    Category (FiberedFunctor 𝒳 𝒴) where
  Hom F G := F.toFiberFunctor ⟶ G.toFiberFunctor
  id F := 𝟙 F.toFiberFunctor
  comp α β := BasedNatTrans.comp α β

@[ext]
lemma FiberedHomCategory.ext {𝒳 𝒴 : FiberedCat 𝒮} {F G : FiberedFunctor 𝒳 𝒴} (α β : F ⟶ G)
    (h : α.toNatTrans = β.toNatTrans) : α = β := BasedNatTrans.ext α β h

@[simps]
def FiberedFunctor.associator {𝒳 𝒴 𝒵 𝒱 : FiberedCat 𝒮} (F : FiberedFunctor 𝒳 𝒴)
    (G : FiberedFunctor 𝒴 𝒵) (H : FiberedFunctor 𝒵 𝒱) :
  FiberedFunctor.comp (FiberedFunctor.comp F G) H ≅ FiberedFunctor.comp F (FiberedFunctor.comp G H) :=
{ FiberFunctor.associator F.toFiberFunctor G.toFiberFunctor H.toFiberFunctor with }

@[simps]
def FiberedFunctor.leftUnitor {𝒳 𝒴 : FiberedCat 𝒮} (F : FiberedFunctor 𝒳 𝒴) :
  FiberedFunctor.comp (FiberedFunctor.id 𝒳) F ≅ F :=
{ FiberFunctor.leftUnitor F.toFiberFunctor with }

@[simps]
def FiberedFunctor.rightUnitor {𝒳 𝒴 : FiberedCat 𝒮} (F : FiberedFunctor 𝒳 𝒴) :
  FiberedFunctor.comp F (FiberedFunctor.id 𝒴) ≅ F :=
{ FiberFunctor.rightUnitor F.toFiberFunctor with }

@[simps!]
def FiberedFunctor.whiskerLeft {𝒳 𝒴 𝒵 : FiberedCat 𝒮} (F : FiberedFunctor 𝒳 𝒴)
    {G H : FiberedFunctor 𝒴 𝒵} (α : G ⟶ H) :=
  BasedCategory.whiskerLeft F.toBasedFunctor α

@[simps!]
def FiberedFunctor.whiskerRight {𝒳 𝒴 𝒵 : FiberedCat 𝒮} {F G : FiberedFunctor 𝒳 𝒴}
    (α : F ⟶ G) (H : FiberedFunctor 𝒴 𝒵) :=
  BasedCategory.whiskerRight α H.toBasedFunctor

@[simps!]
instance FiberedCat.bicategory : Bicategory (FiberedCat 𝒮) where
  Hom 𝒳 𝒴 := FiberedFunctor 𝒳 𝒴
  id 𝒳 := FiberedFunctor.id 𝒳
  comp := FiberedFunctor.comp
  homCategory 𝒳 𝒴 := FiberedHomCategory 𝒳 𝒴
  whiskerLeft {𝒳 𝒴 𝒵} F {G H} α := FiberedFunctor.whiskerLeft F α
  whiskerRight {𝒳 𝒴 𝒵} {F G} α H := FiberedFunctor.whiskerRight α H
  associator := FiberedFunctor.associator
  leftUnitor {𝒳 𝒴} F := FiberedFunctor.leftUnitor F
  rightUnitor {𝒳 𝒴} F := FiberedFunctor.rightUnitor F
  comp_whiskerLeft f g η h' η₁ := by apply BasedCategory.bicategory.comp_whiskerLeft
  id_whiskerRight f g := by apply BasedCategory.bicategory.id_whiskerRight
  comp_whiskerRight η θ i := by apply BasedCategory.bicategory.comp_whiskerRight
  whiskerRight_comp η f i := by apply BasedCategory.bicategory.whiskerRight_comp
  whisker_assoc f η h η₁ h₁ := by apply BasedCategory.bicategory.whisker_assoc
  whisker_exchange η θ := BasedCategory.bicategory.whisker_exchange η θ
  pentagon f g h i := by apply BasedCategory.bicategory.pentagon
  triangle f g := by apply BasedCategory.bicategory.triangle

instance : Bicategory.Strict (FiberedCat 𝒮) where
  id_comp := FiberedFunctor.id_comp
  comp_id := FiberedFunctor.comp_id
  assoc := FiberedFunctor.assoc



-- TODO: This should be deduced using mapIso...!
@[simps]
def IsoOfBasedIso {𝒳 𝒴 : FiberedCat 𝒮} {F G : 𝒳 ⟶ 𝒴} (α : F ≅ G) : F.toFunctor ≅ G.toFunctor where
  hom := α.hom.toNatTrans
  inv := α.inv.toNatTrans
  hom_inv_id := congrArg (·.toNatTrans) α.hom_inv_id
  inv_hom_id := congrArg (·.toNatTrans) α.inv_hom_id

def EquivOfFiberFunctorEquiv {𝒳 𝒴 : FiberedCat 𝒮} (F : 𝒳 ≌ 𝒴) : 𝒳.cat ≌ 𝒴.cat :=
  CategoryTheory.Equivalence.mk F.hom.toFunctor F.inv.toFunctor (IsoOfBasedIso F.unit)
    (IsoOfBasedIso F.counit)

instance IsEquivOfFiberFunctorEquiv {𝒳 𝒴 : FiberedCat 𝒮} (F : 𝒳 ≌ 𝒴) : IsEquivalence F.hom.toFunctor := by
  change IsEquivalence (EquivOfFiberFunctorEquiv F).functor
  apply IsEquivalence.ofEquivalence

end Fibered


-- OLD CODE: recycle some of this to get API for BasedNatTrans
/- /- TWO MORPHISMS FOR HASFIBERS CLASS -/
structure FiberTwoMorphism {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [hq : HasFibers 𝒴]
    (F G : FiberMorphism 𝒳 𝒴) extends TwoMorphism F.toMorphism G.toMorphism where
  /- A family of natural transformations between the functors for each fiber  -/
  (onFib (S : 𝒮) : (F.onFib S) ⟶ (G.onFib S))
  -- TODO: use whisker notation here
  /- The family of natural transformations satisfy the following diagram for any a : hp.Fib S
  ```
  (hp.ι S ⋙ F)(a) ---------- α.app (a) ----------> (hq.ι S ⋙ G)(a)
    |                                                      |
  eqToHom                                                 eqToHom
    |                                                      |
    V                                                      V
  (F.onFib ⋙ hq.ι S)(a) --- α.onFib.app (a) ---> (G.onFib ⋙ hq.ι S)(a)

  ```
  In other words, α.app (a) = α.onFib.app (a) -/
  (fib_w (S : 𝒮) : whiskerLeft (hp.ι S) toNatTrans =
    eqToHom (F.fib_w S).symm ≫ whiskerRight (onFib S) (hq.ι S) ≫ eqToHom (G.fib_w S))

@[simps!]
def FiberTwoMorphism.comp {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [hq : HasFibers 𝒴]
    {F G H : FiberMorphism 𝒳 𝒴} (α : FiberTwoMorphism F G) (β : FiberTwoMorphism G H) :
    FiberTwoMorphism F H :=
  { TwoMorphism.comp α.toTwoMorphism β.toTwoMorphism with
    onFib := fun S => α.onFib S ≫ β.onFib S
    fib_w := by
      intro S
      simp
      sorry
      --rw [whiskerLeft_comp, whiskerRight_comp, ←category.assoc, α.fib_w, β.fib_w, category.assoc]

  }

def FiberTwoMorphism.id {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [hq : HasFibers 𝒴]
    (F : FiberMorphism 𝒳 𝒴) : FiberTwoMorphism F F :=
  { TwoMorphism.id F.toMorphism with
    onFib := fun S => 𝟙 _
    fib_w := fun S => by simp; rfl }

-- need FiberTwoMorphism.comp_app
-- By lemmas like this, I actually dont need this structure?
-- Just need to have a good API
lemma FiberTwoMorphism.fib_w_app {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [hq : HasFibers 𝒴]
    {F G: FiberMorphism 𝒳 𝒴} {α : FiberTwoMorphism F G} (S : 𝒮) (a : hp.Fib S) :
    α.app ((hp.ι S).obj a) = eqToHom (F.fib_w_obj a).symm ≫
      (hq.ι S).map ((α.onFib S).app a) ≫ eqToHom (G.fib_w_obj a) := by
  simpa using congr_app (α.fib_w S) a

@[ext]
lemma FiberTwoMorphism.ext {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [hq : HasFibers 𝒴]
    {F G : FiberMorphism 𝒳 𝒴} (α β : FiberTwoMorphism F G) (h : α.toTwoMorphism = β.toTwoMorphism) :
    α = β :=
  by
    rcases α with ⟨α, α_fib, αw⟩
    rcases β with ⟨β, β_fib, βw⟩
    simp only [mk.injEq]
    refine ⟨h, ?_⟩
    ext S a
    sorry -- NEED API FOR THIS -/

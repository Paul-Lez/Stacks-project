import LS.BasedCategory
import LS.HasFibers

/-!
# The bicategory of fibered categories

In this file we construct the bicategory of "fiber categories"

-/

universe u₁ v₁ u₂ v₂

open CategoryTheory Functor Category

variable {𝒮 : Type u₁} [Category 𝒮]

namespace Fibered

structure FiberCat (𝒮 : Type u₁) [Category 𝒮] extends BasedCategory 𝒮 where
  [hasFib : HasFibers p]

instance FiberCat.hasCoeToSort : CoeSort (FiberCat 𝒮) (Type u₂) where
  coe := fun 𝒳 => 𝒳.carrier

instance (𝒳 : FiberCat 𝒮) : HasFibers 𝒳.p := 𝒳.hasFib

/-- A notion of functor between HasFibers. It is given by a functor F : 𝒳 ⥤ 𝒴 such that F ⋙ q = p,
  and a collection of functors fiber_functor S between the fibers of p and q over S in 𝒮 such that
  .... -/
structure FiberFunctor (𝒳 𝒴 : FiberCat 𝒮) extends BasedFunctor 𝒳.toBasedCategory 𝒴.toBasedCategory where
  (onFib (S : 𝒮) : 𝒳.hasFib.Fib S ⥤ 𝒴.hasFib.Fib S)
  (fib_w : ∀ (S : 𝒮), (onFib S) ⋙ (𝒴.hasFib.ι S) = (𝒳.hasFib.ι S) ⋙ toFunctor) -- Maybe try aesop_cat by default here.

@[simp]
lemma FiberFunctor.fib_w_obj {𝒳 𝒴 : FiberCat 𝒮} (F : FiberFunctor 𝒳 𝒴) {S : 𝒮}  (a : 𝒳.hasFib.Fib S) :
    (𝒴.hasFib.ι S).obj ((F.onFib S).obj a) = (F.toFunctor).obj ((𝒳.hasFib.ι S).obj a) := by
  apply congr_obj (F.fib_w S)

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

/-- A `BasedFunctor` can be given the structure of a `FiberFunctor` -/
-- TODO: give canonical constructor from `BasedCategory` to `FiberCat`
/- def BasedFunctor.toFiberFunctor {𝒳 𝒴 : BasedCategory 𝒮}
    (F : 𝒳.toBasedCategory ⟶ 𝒴.toBasedCategory) :
  FiberFunctor 𝒳 𝒴 :=
{ F with
  onFib := fun S => {
    obj := fun a => ⟨F.obj a.1, by rw [F.obj_proj, a.2]⟩
    map := @fun a b φ => ⟨F.map φ.val, BasedFunctor.pres_IsHomLift F φ.2⟩
    map_id := by
      intro a
      -- TODO THIS SHOULD ALL BE SIMP SOMEHOW..
      simp [FiberCategory_id_coe 𝒳 S a]
      rw [←Subtype.val_inj, FiberCategory_id_coe 𝒴 S _]
    map_comp := by
      intro x y z φ ψ
      -- THIS SHOULD ALSO ALL BE SIMP SOMEHOW...
      simp [FiberCategory_comp_coe 𝒳 S φ ψ]
      rw [←Subtype.val_inj, FiberCategory_comp_coe 𝒴 S _ _]
  }
  fib_w := by aesop_cat
} -/

@[simps!]
instance FiberHomCategory (𝒳 𝒴 : FiberCat 𝒮) :
    Category (FiberFunctor 𝒳 𝒴) where
  Hom F G := F.toBasedFunctor ⟶ G.toBasedFunctor
  id F := 𝟙 F.toBasedFunctor
  comp α β := BasedNatTrans.comp α β

@[ext]
lemma FiberHomCategory.ext {𝒳 𝒴 : FiberCat 𝒮} {F G : FiberFunctor 𝒳 𝒴} (α β : F ⟶ G)
    (h : α.toNatTrans = β.toNatTrans) : α = β := BasedNatTrans.ext α β h

@[simps]
def FiberFunctor.associator {𝒳 𝒴 𝒵 𝒱 : FiberCat 𝒮} (F : FiberFunctor 𝒳 𝒴)
    (G : FiberFunctor 𝒴 𝒵) (H : FiberFunctor 𝒵 𝒱) :
  FiberFunctor.comp (FiberFunctor.comp F G) H ≅ FiberFunctor.comp F (FiberFunctor.comp G H) where
    hom := {
      app := fun _ => 𝟙 _
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [BasedFunctor.obj_proj, ha]
    }
    inv := {
      app := fun _ => 𝟙 _
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [BasedFunctor.obj_proj, ha]
    }

@[simps]
def FiberFunctor.leftUnitor {𝒳 𝒴 : FiberCat 𝒮} (F : FiberFunctor 𝒳 𝒴) :
  FiberFunctor.comp (FiberFunctor.id 𝒳) F ≅ F where
    hom :=
    {
      app := fun a => 𝟙 (F.obj a)
      naturality := by
        intros
        simp
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [BasedFunctor.obj_proj, ha]
    }
    inv := {
      app := fun a => 𝟙 (F.obj a)
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [BasedFunctor.obj_proj, ha]
    }

@[simps]
def FiberFunctor.rightUnitor {𝒳 𝒴 : FiberCat 𝒮} (F : FiberFunctor 𝒳 𝒴) :
  FiberFunctor.comp F (FiberFunctor.id 𝒴) ≅ F where
    hom :=
    {
      app := fun a => 𝟙 (F.obj a)
      naturality := by
        intros
        simp
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [BasedFunctor.obj_proj, ha]
    }
    inv := {
      app := fun a => 𝟙 (F.obj a)
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [BasedFunctor.obj_proj, ha]
    }

instance : Bicategory (FiberCat 𝒮) where
  Hom 𝒳 𝒴 := FiberFunctor 𝒳 𝒴
  id 𝒳 := FiberFunctor.id 𝒳
  comp := FiberFunctor.comp
  homCategory 𝒳 𝒴 := FiberHomCategory 𝒳 𝒴
  whiskerLeft {𝒳 𝒴 𝒵} F {G H} α := {
      whiskerLeft F.toFunctor α.toNatTrans with
      aboveId := by
        intro a S ha
        apply α.aboveId
        simp only [BasedFunctor.obj_proj, ha]
    }

  -- TODO: weird that this has non-implicit arguments and above doesnt
  whiskerRight {𝒳 𝒴 𝒵} F G α H := {
    whiskerRight α.toNatTrans H.toFunctor with
    aboveId := by
      intro a S ha
      apply BasedFunctor.pres_IsHomLift
      apply α.aboveId ha
  }
  associator := FiberFunctor.associator
  leftUnitor {𝒳 𝒴} F := FiberFunctor.leftUnitor F -- term mode doesn't work?!?
  rightUnitor {𝒳 𝒴} F := FiberFunctor.rightUnitor F

instance : Bicategory.Strict (FiberCat 𝒮) where
  id_comp := FiberFunctor.id_comp
  comp_id := FiberFunctor.comp_id
  assoc := FiberFunctor.assoc

/-- A `FiberedCat` is a .... -/
-- TODO: restructure FiberCategories file first
structure FiberedCat (𝒮 : Type u₁) [Category.{v₁} 𝒮] extends FiberCat 𝒮 where
  [isFibered : IsFibered p]

instance FiberedCat.hasCoeToSort : CoeSort (FiberedCat 𝒮) (Type u₂) where
  coe := fun 𝒳 => 𝒳.carrier

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

-- TODO: same as FiberHomCategory, is it possible to recycle that somehow?
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


-- TODO: with some API this should all follow from the above

@[simps]
def FiberedFunctor.associator {𝒳 𝒴 𝒵 𝒱 : FiberedCat 𝒮} (F : FiberedFunctor 𝒳 𝒴)
    (G : FiberedFunctor 𝒴 𝒵) (H : FiberedFunctor 𝒵 𝒱) :
  FiberedFunctor.comp (FiberedFunctor.comp F G) H ≅ FiberedFunctor.comp F (FiberedFunctor.comp G H) where
    hom := {
      app := fun _ => 𝟙 _
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [BasedFunctor.obj_proj, ha]
    }
    inv := {
      app := fun _ => 𝟙 _
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [BasedFunctor.obj_proj, ha]
    }

@[simps]
def FiberedFunctor.leftUnitor {𝒳 𝒴 : FiberedCat 𝒮} (F : FiberedFunctor 𝒳 𝒴) :
  FiberedFunctor.comp (FiberedFunctor.id 𝒳) F ≅ F where
    hom :=
    {
      app := fun a => 𝟙 (F.obj a)
      naturality := by
        intros
        simp
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [BasedFunctor.obj_proj, ha]
    }
    inv := {
      app := fun a => 𝟙 (F.obj a)
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [BasedFunctor.obj_proj, ha]
    }

@[simps]
def FiberedFunctor.rightUnitor {𝒳 𝒴 : FiberedCat 𝒮} (F : FiberedFunctor 𝒳 𝒴) :
  FiberedFunctor.comp F (FiberedFunctor.id 𝒴) ≅ F where
    hom :=
    {
      app := fun a => 𝟙 (F.obj a)
      naturality := by
        intros
        simp
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [BasedFunctor.obj_proj, ha]
    }
    inv := {
      app := fun a => 𝟙 (F.obj a)
      aboveId := by
        intro a S ha
        apply IsHomLift_id
        simp only [BasedFunctor.obj_proj, ha]
    }

instance : Bicategory (FiberedCat 𝒮) where
  Hom 𝒳 𝒴 := FiberedFunctor 𝒳 𝒴
  id 𝒳 := FiberedFunctor.id 𝒳
  comp := FiberedFunctor.comp
  homCategory 𝒳 𝒴 := FiberedHomCategory 𝒳 𝒴
  whiskerLeft {𝒳 𝒴 𝒵} F {G H} α := {
      whiskerLeft F.toFunctor α.toNatTrans with
      aboveId := by
        intro a S ha
        apply α.aboveId
        simp only [BasedFunctor.obj_proj, ha]
    }

  -- TODO: weird that this has non-implicit arguments and above doesnt
  whiskerRight {𝒳 𝒴 𝒵} F G α H := {
    whiskerRight α.toNatTrans H.toFunctor with
    aboveId := by
      intro a S ha
      apply BasedFunctor.pres_IsHomLift
      apply α.aboveId ha
  }
  associator := FiberedFunctor.associator
  leftUnitor {𝒳 𝒴} F := FiberedFunctor.leftUnitor F -- term mode doesn't work?!?
  rightUnitor {𝒳 𝒴} F := FiberedFunctor.rightUnitor F

instance : Bicategory.Strict (FiberedCat 𝒮) where
  id_comp := FiberedFunctor.id_comp
  comp_id := FiberedFunctor.comp_id
  assoc := FiberedFunctor.assoc

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

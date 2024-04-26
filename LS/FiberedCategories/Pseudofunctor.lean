import LS.FiberedCategories.HasFibers
import LS.FiberedCategories.StrictPseudofunctor
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

universe w v₁ v₂ u₁ u₂

open CategoryTheory Functor Category Fibered Opposite Discrete Bicategory

-- TODO: add @[pp_dot] in LocallyDiscrete

-- TODO: lemmas about pseudofunctors from a locally discrete bicategory (simplifies assumptions!)
variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

/-- The type of objects in the fibered category associated to a presheaf valued in types. -/
def ℱ (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) := (S : 𝒮) × (F.obj ⟨op S⟩)

@[simps]
instance ℱ.CategoryStruct : CategoryStruct (ℱ F) where
  Hom X Y := (f : X.1 ⟶ Y.1) × (X.2 ⟶ (F.map f.op.toLoc).obj Y.2)
  id X := ⟨𝟙 X.1, (F.mapId ⟨op X.1⟩).inv.app X.2⟩
  comp {_ _ Z} f g := ⟨f.1 ≫ g.1, f.2 ≫ (F.map f.1.op.toLoc).map g.2 ≫ (F.mapComp g.1.op.toLoc f.1.op.toLoc).inv.app Z.2⟩

#check Prod.ext

@[ext]
lemma ℱ.hom_ext {a b : ℱ F} (f g : a ⟶ b) (hfg₁ : f.1 = g.1)
    (hfg₂ : f.2 = g.2 ≫ eqToHom (hfg₁ ▸ rfl)) : f = g := by
  apply Sigma.ext
  exact hfg₁
  rw [←conj_eqToHom_iff_heq _ _ rfl (hfg₁ ▸ rfl)]
  simp only [hfg₂, eqToHom_refl, id_comp]

/-- The category structure on the fibered category associated to a presheaf valued in types. -/
instance : Category (ℱ F) where
  toCategoryStruct := ℱ.CategoryStruct
  id_comp {a b} f := by
    ext
    · simp
    dsimp
    rw [←assoc, ←(F.mapId ⟨op a.1⟩).inv.naturality f.2, assoc]
    rw [←whiskerLeft_app, ←NatTrans.comp_app]
    erw [map₂_right_unitor' (F:=F) f.1.op]
    nth_rw 1 [←assoc]
    erw [←CategoryTheory.whiskerLeft_comp]
    dsimp
    rw [eqToHom_app]
    simp
  comp_id := sorry
  assoc f g h := by
    ext
    · simp
    dsimp
    sorry

/-- The projection `ℱ F ⥤ 𝒮` given by projecting both objects and homs to the first factor -/
@[simps]
def ℱ.π (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) : ℱ F ⥤ 𝒮 where
  obj := fun X => X.1
  map := fun f => f.1

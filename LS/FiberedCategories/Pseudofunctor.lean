import LS.FiberedCategories.HasFibers
import LS.FiberedCategories.StrictPseudofunctor
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Functor Category Fibered Opposite Discrete Bicategory

-- TODO: add @[pp_dot] in LocallyDiscrete
section mathlib_lemmas

lemma Cat.whiskerLeft_app {C D E : Cat} (X : C) (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) :
  (F ◁ η).app X = η.app (F.obj X) := by dsimp

lemma Cat.whiskerRight_app {C D E : Cat} (X : C) {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) :
  (η ▷ H).app X = H.map (η.app X) := by dsimp

end mathlib_lemmas

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

/-- The type of objects in the fibered category associated to a presheaf valued in types. -/
def ℱ (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) := (S : 𝒮) × (F.obj ⟨op S⟩)

@[simps]
instance ℱ.CategoryStruct : CategoryStruct (ℱ F) where
  Hom X Y := (f : X.1 ⟶ Y.1) × (X.2 ⟶ (F.map f.op.toLoc).obj Y.2)
  id X := ⟨𝟙 X.1, (F.mapId ⟨op X.1⟩).inv.app X.2⟩
  comp {_ _ Z} f g := ⟨f.1 ≫ g.1, f.2 ≫ (F.map f.1.op.toLoc).map g.2 ≫ (F.mapComp g.1.op.toLoc f.1.op.toLoc).inv.app Z.2⟩

@[ext]
lemma ℱ.hom_ext {a b : ℱ F} (f g : a ⟶ b) (hfg₁ : f.1 = g.1)
    -- Is the substitution here problematic...?
    (hfg₂ : f.2 = g.2 ≫ eqToHom (hfg₁ ▸ rfl)) : f = g := by
  apply Sigma.ext
  exact hfg₁
  rw [←conj_eqToHom_iff_heq _ _ rfl (hfg₁ ▸ rfl)]
  simp only [hfg₂, eqToHom_refl, id_comp]

lemma ℱ.id_comp {a b : ℱ F} (f : a ⟶ b) : 𝟙 a ≫ f = f := by
  ext
  · simp
  dsimp
  rw [←assoc, ←(F.mapId ⟨op a.1⟩).inv.naturality f.2, assoc]
  rw [←Cat.whiskerLeft_app, ←NatTrans.comp_app]
  rw [map₂_right_unitor' (F:=F) f.1.op]
  nth_rw 1 [←assoc]
  rw [←Bicategory.whiskerLeft_comp]
  simp_rw [NatTrans.comp_app]
  rw [eqToHom_app]
  simp

lemma ℱ.comp_id {a b : ℱ F} (f : a ⟶ b) : f ≫ 𝟙 b = f := by
  ext
  · simp
  dsimp
  rw [←Cat.whiskerRight_app, ←NatTrans.comp_app]
  rw [map₂_left_unitor' (F:=F) f.1.op]
  nth_rw 1 [←assoc]
  rw [←Bicategory.comp_whiskerRight]
  simp_rw [NatTrans.comp_app]
  rw [eqToHom_app]
  simp

/-- The category structure on the fibered category associated to a presheaf valued in types. -/
instance : Category (ℱ F) where
  toCategoryStruct := ℱ.CategoryStruct
  id_comp := ℱ.id_comp
  comp_id := ℱ.comp_id
  assoc {a b c d} f g h := by
    ext
    · simp
    dsimp
    rw [assoc, assoc, ←assoc (f:=(F.mapComp g.1.op.toLoc f.1.op.toLoc).inv.app c.2)]
    rw [←(F.mapComp g.1.op.toLoc f.1.op.toLoc).inv.naturality h.2]
    rw [←Cat.whiskerLeft_app, assoc, ←NatTrans.comp_app]
    rw [map₂_associator_inv' (F:=F) h.1.op g.1.op f.1.op]
    -- End of this proof is VERY slow...
    simp
    congr
    apply eqToHom_app

/-- The projection `ℱ F ⥤ 𝒮` given by projecting both objects and homs to the first factor -/
@[simps]
def ℱ.π (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) : ℱ F ⥤ 𝒮 where
  obj := fun X => X.1
  map := fun f => f.1

-- TODO: improve comment after I know final form of this...
/-- An object of `ℱ F` lying over `S`, given by some `a : F(T)` and `S ⟶ T` -/
@[simps]
def ℱ.pullback_obj {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S) : ℱ F :=
  ⟨R, (F.map f.op.toLoc).obj a⟩

@[simps]
def ℱ.pullback_map {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S) : ℱ.pullback_obj a f ⟶ ⟨S, a⟩ :=
  ⟨f, 𝟙 _⟩

-- @[simp]
-- def ℱ.mk_map₁ {R S : 𝒮} (f : R ⟶ S) {X Y : ℱ F} (hX : X.1 = S)
--     (hY : Y.1 = R) : Y.1 ⟶ X.1 := eqToHom hY ≫ f ≫ eqToHom hX.symm

-- @[simp]
-- def ℱ.mk_map {R S : 𝒮} {f : R ⟶ S} {X Y : ℱ F} {hX : X.1 = S}
--     {hY : Y.1 = R} (hXY : Y.2 = Discrete.mk ((F.map (ℱ.mk_map₁ f hX hY).op) X.2.1)) : Y ⟶ X :=
--   ⟨ℱ.mk_map₁ f hX hY, eqToHom hXY⟩

/- API ISSUE:
  - The "equalities" we save by using HomLift etc are now put on the user when
  defining these things.
  - Need API to avoid these equalities during construction...


-/

/-- `ℱ.π` is a fibered category. -/
instance : IsFibered (ℱ.π F) where
  has_pullbacks := by
    intros a R S hS f
    -- This should be hidden by API (in `Basic.lean`)
    subst hS
    let b : ℱ F := ⟨R, (F.map f.op.toLoc).obj a.2⟩
    use b, ⟨f, 𝟙 _⟩
    exact {
      ObjLiftDomain := rfl
      ObjLiftCodomain := rfl
      HomLift := {
        w := by simp
      }
      UniversalProperty := by
        intro R' a' g f' hw φ' hφ'
        -- this subst should be hidden by API (shouldnt even be necessary?) (in `Basic.lean`)
        subst hw
        -- NEED API: to go from fiber over T to fiber over T'=T... i.e. mkmap!!
        let τ' : a'.2 ⟶ (F.map φ'.1.op.toLoc).obj a.2 := φ'.2


        sorry
    }

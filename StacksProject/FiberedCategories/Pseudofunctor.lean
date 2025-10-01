-- /-
-- Copyright (c) 2024 Calle Sönne. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Paul Lezeau, Calle Sönne
-- -/

-- import StacksProject.FiberedCategories.HasFibers
-- -- import StacksProject.FiberedCategories.StrictPseudofunctor
-- import Mathlib.CategoryTheory.Category.Cat
-- import Mathlib
-- -- import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

-- /-!
-- # Fibered category associated to a pseudofunctor

-- Given a category `𝒮` and any pseudofunctor valued in `Cat` we associate to it a fibered category
-- category `ℱ F ⥤ 𝒮`.

-- The category `ℱ F` is defined as follows:
-- * Objects: pairs `(S, a)` where `S` is an object of the base category and `a` is an object of the
--   category `F(S)`
-- * Morphisms: morphisms `(R, b) ⟶ (S, a)` are defined as pairs `(f, h)` where `f : R ⟶ S` is a
--   morphism in `𝒮` and `h : b ⟶ F(f)(a)`

-- The projection functor `ℱ F ⥤ 𝒮` is then given by projecting to the first factors, i.e.
-- * On objects, it sends `(S, a)` to `S`
-- * On morphisms, it sends `(f, h)` to `f`

-- We also provide a `HasFibers` instance `ℱ F`, such that the fiber over `S` is the category `F(S)`.

-- ## References
-- [Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by Angelo Vistoli
-- -/

-- /-
-- TODO:
-- - Fix naming
-- - (Later) splittings & functoriality
-- - Make `presheaf.lean` a special instance of the above
--   - Isomorphism between the overcategory and fibered category associated to the corresponding presheaf?
-- -/



-- universe w v₁ v₂ v₃ u₁ u₂ u₃

-- open CategoryTheory Functor Category Fibered Opposite Discrete Bicategory

-- -- TODO: add @[pp_dot] in LocallyDiscrete
-- section mathlib_lemmas

-- lemma Cat.whiskerLeft_app {C D E : Cat} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) (X : C) :
--     (F ◁ η).app X = η.app (F.obj X) :=
--   CategoryTheory.whiskerLeft_app F η X

-- lemma Cat.whiskerRight_app {C D E : Cat} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) (X : C) :
--     (η ▷ H).app X = H.map (η.app X) :=
--   CategoryTheory.whiskerRight_app η H X

-- @[simp]
-- lemma Quiver.Hom.eqToHom_toLoc {C : Type u₁} [Category.{v₁} C] {a b : C}
--     (h : a = b) : (eqToHom h).toLoc = eqToHom (congrArg LocallyDiscrete.mk h) := by
--   subst h; rfl


-- end mathlib_lemmas

-- variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

-- /-- The type of objects in the fibered category associated to a presheaf valued in types. -/
-- def ℱ (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) := (S : 𝒮) × (F.obj ⟨op S⟩)

-- @[simps]
-- instance ℱ.CategoryStruct : CategoryStruct (ℱ F) where
--   Hom X Y := (f : X.1 ⟶ Y.1) × (X.2 ⟶ (F.map f.op.toLoc).obj Y.2)
--   id X := ⟨𝟙 X.1, (F.mapId ⟨op X.1⟩).inv.app X.2⟩
--   comp {_ _ Z} f g := ⟨f.1 ≫ g.1, f.2 ≫ (F.map f.1.op.toLoc).map g.2 ≫ (F.mapComp g.1.op.toLoc f.1.op.toLoc).inv.app Z.2⟩

-- @[ext]
-- lemma ℱ.hom_ext {a b : ℱ F} (f g : a ⟶ b) (hfg₁ : f.1 = g.1)
--     -- Is the substitution here problematic...?
--     (hfg₂ : f.2 = g.2 ≫ eqToHom (hfg₁ ▸ rfl)) : f = g := by
--   apply Sigma.ext hfg₁
--   rw [←conj_eqToHom_iff_heq _ _ rfl (hfg₁ ▸ rfl)]
--   simp only [hfg₂, eqToHom_refl, id_comp]

-- -- Might not need this lemma in the end
-- lemma ℱ.hom_ext_iff {a b : ℱ F} (f g : a ⟶ b) : f = g ↔ ∃ (hfg : f.1 = g.1), f.2 = g.2 ≫ eqToHom (hfg ▸ rfl) where
--   mp := fun hfg => ⟨by rw [hfg], by simp [hfg]⟩
--   mpr := fun ⟨hfg₁, hfg₂⟩ => ℱ.hom_ext f g hfg₁ hfg₂

-- lemma ℱ.id_comp {a b : ℱ F} (f : a ⟶ b) : 𝟙 a ≫ f = f := by
--   ext
--   · simp
--   dsimp
--   rw [←assoc, ←(F.mapId ⟨op a.1⟩).inv.naturality f.2, assoc]
--   rw [←Cat.whiskerLeft_app, ←NatTrans.comp_app]
--   rw [map₂_right_unitor' (F:=F) f.1.op]
--   nth_rw 1 [←assoc]
--   rw [←Bicategory.whiskerLeft_comp]
--   simp_rw [NatTrans.comp_app]
--   rw [eqToHom_app]
--   simp

-- lemma ℱ.comp_id {a b : ℱ F} (f : a ⟶ b) : f ≫ 𝟙 b = f := by
--   ext
--   · simp
--   dsimp
--   rw [←Cat.whiskerRight_app, ←NatTrans.comp_app]
--   rw [map₂_left_unitor' (F:=F) f.1.op.toLoc]
--   nth_rw 1 [←assoc]
--   rw [←Bicategory.comp_whiskerRight]
--   simp_rw [NatTrans.comp_app]
--   rw [eqToHom_app]
--   simp

-- /-- The category structure on the fibered category associated to a presheaf valued in types. -/
-- instance : Category (ℱ F) where
--   toCategoryStruct := ℱ.CategoryStruct
--   id_comp := ℱ.id_comp
--   comp_id := ℱ.comp_id
--   assoc {a b c d} f g h := by
--     ext
--     · simp
--     dsimp
--     rw [assoc, assoc, ←assoc (f:=(F.mapComp g.1.op.toLoc f.1.op.toLoc).inv.app c.2)]
--     rw [←(F.mapComp g.1.op.toLoc f.1.op.toLoc).inv.naturality h.2]
--     rw [←Cat.whiskerLeft_app, assoc, ←NatTrans.comp_app]
--     rw [map₂_associator_inv' (F:=F) h.1.op g.1.op f.1.op]
--     -- End of this proof is VERY slow...
--     simp
--     congr
--     apply eqToHom_app

-- /-- The projection `ℱ F ⥤ 𝒮` given by projecting both objects and homs to the first factor -/
-- @[simps]
-- def ℱ.π (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) : ℱ F ⥤ 𝒮 where
--   obj := fun X => X.1
--   map := fun f => f.1

-- -- TODO: improve comment after I know final form of this...
-- /-- An object of `ℱ F` lying over `S`, given by some `a : F(T)` and `S ⟶ T` -/
-- abbrev ℱ.pullback_obj {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S) : ℱ F :=
--   ⟨R, (F.map f.op.toLoc).obj a⟩

-- abbrev ℱ.pullback_map {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S) : ℱ.pullback_obj a f ⟶ ⟨S, a⟩ :=
--   ⟨f, 𝟙 _⟩

-- lemma ℱ.pullback_IsHomLift {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S) :
--     IsHomLift (ℱ.π F) f (ℱ.pullback_map a f) where
--   ObjLiftDomain := rfl
--   ObjLiftCodomain := rfl
--   HomLift := {
--     w := by simp
--   }

-- abbrev ℱ.pullback_inducedMap {R S : 𝒮} (a : F.obj ⟨op S⟩) {f : R ⟶ S} {a' : ℱ F}
--     {φ' : a' ⟶ ⟨S, a⟩} {g : a'.1 ⟶ R} (hφ' : IsHomLift (ℱ.π F) (g ≫ f) φ') : a' ⟶ ℱ.pullback_obj a f :=
--   have : g ≫ f = φ'.1 := by simpa using IsHomLift.hom_eq hφ'
--   have : φ'.1.op.toLoc = f.op.toLoc ≫ g.op.toLoc := by simp [this.symm]
--   ⟨g, φ'.2 ≫ eqToHom (by rw [this]) ≫ (F.mapComp f.op.toLoc g.op.toLoc).hom.app a⟩

-- lemma ℱ.pullback_inducedMap_isHomLift {R S : 𝒮} (a : F.obj ⟨op S⟩) {f : R ⟶ S} {a' : ℱ F}
--     {φ' : a' ⟶ ⟨S, a⟩} {g : a'.1 ⟶ R} (hφ' : IsHomLift (ℱ.π F) (g ≫ f) φ') :
--       IsHomLift (ℱ.π F) g (ℱ.pullback_inducedMap a hφ') where
--   ObjLiftDomain := rfl
--   ObjLiftCodomain := rfl
--   HomLift := ⟨by simp⟩

-- lemma ℱ.pullback_IsPullback {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S) :
--     IsPullback (ℱ.π F) f (ℱ.pullback_map a f) := by
--   apply IsPullback.mk' (ℱ.pullback_IsHomLift a f)
--   intros a' g φ' hφ'
--   -- This should be included in API somehow...
--   have : g ≫ f = φ'.1 := by simpa using IsHomLift.hom_eq hφ'
--   use ℱ.pullback_inducedMap a hφ'
--   refine ⟨⟨ℱ.pullback_inducedMap_isHomLift a hφ', ?_⟩, ?_⟩
--   ext
--   · exact this
--   · simp
--   rintro χ' ⟨hχ', hχ'₁⟩
--   symm at hχ'₁
--   subst hχ'₁
--   -- Again this should also be included in API somehow
--   have hgχ' : g = χ'.1 := by simpa using IsHomLift.hom_eq hχ'
--   subst hgχ'
--   ext
--   · simp
--   simp

-- /-- `ℱ.π` is a fibered category. -/
-- instance : IsFibered (ℱ.π F) := by
--   apply IsFibered.mk'
--   intros a R f
--   use ℱ.pullback_obj a.2 f, ℱ.pullback_map a.2 f
--   exact ℱ.pullback_IsPullback a.2 f

-- variable (F)

-- @[simps]
-- def ℱ.ι (S : 𝒮) : F.obj ⟨op S⟩ ⥤ ℱ F where
--   obj := fun a => ⟨S, a⟩
--   map := @fun a b φ => ⟨𝟙 S, φ ≫ (F.mapId ⟨op S⟩).inv.app b⟩
--   map_id := by
--     intro a
--     dsimp
--     -- why doesnt ext work as I think it should?!
--     ext
--     · simp
--     rw [←conj_eqToHom_iff_heq _ _ rfl (by simp)]
--     simp
--   map_comp := by
--     intro a b c φ ψ
--     dsimp
--     ext
--     · simp
--     rw [←conj_eqToHom_iff_heq _ _ rfl (by simp)]
--     simp
--     nth_rw 3 [←assoc]
--     rw [←(F.mapId ⟨op S⟩).inv.naturality ψ]
--     rw [←Cat.whiskerRight_app, ←assoc (h:= eqToHom _), ←NatTrans.comp_app]
--     rw [map₂_left_unitor' (F:=F)]
--     nth_rw 2 [←assoc (h:= eqToHom _)]
--     rw [inv_hom_whiskerRight, NatTrans.comp_app, eqToHom_app]
--     simp

-- @[simps]
-- def ℱ.comp_iso (S : 𝒮) : (ℱ.ι F S) ⋙ ℱ.π F ≅ (const (F.obj ⟨op S⟩)).obj S where
--   hom := { app := fun a => 𝟙 _ }
--   inv := { app := fun a => 𝟙 _ }

-- lemma ℱ.comp_const (S : 𝒮) : (ℱ.ι F S) ⋙ ℱ.π F = (const (F.obj ⟨op S⟩)).obj S := by
--   apply Functor.ext_of_iso (ℱ.comp_iso F S) <;> simp

-- noncomputable instance (S : 𝒮) : Functor.Full (FiberInducedFunctor (ℱ.comp_const F S)) := by
--   apply fullOfExists
--   intro X Y f
--   have hf : f.1.1 = 𝟙 S := by simpa using IsHomLift.hom_eq' f.2
--   use f.1.2 ≫ eqToHom (by simp [hf]) ≫ (F.mapId ⟨op S⟩).hom.app Y
--   ext
--   · simp [hf]
--   · simp

-- instance (S : 𝒮) : Functor.Faithful (FiberInducedFunctor (ℱ.comp_const F S)) where
--   map_injective := by
--     intros a b f g heq
--     rw [←Subtype.val_inj] at heq
--     obtain ⟨_, heq₂⟩ := (ℱ.hom_ext_iff _ _).1 heq
--     dsimp at heq₂
--     rw [←CategoryTheory.NatIso.app_inv, CategoryTheory.Iso.comp_inv_eq] at heq₂
--     simpa using heq₂

-- noncomputable instance (S : 𝒮) : Functor.EssSurj (FiberInducedFunctor (ℱ.comp_const F S)) := by
--   apply essSurj_of_surj
--   intro Y
--   have hYS : Y.1.1 = S := by simpa using Y.2
--   use (hYS.symm ▸ Y.1.2)
--   apply Subtype.val_inj.1
--   apply Sigma.ext
--   · simp [hYS]
--   simp


-- noncomputable instance (S : 𝒮) : Functor.IsEquivalence (FiberInducedFunctor (ℱ.comp_const F S)) :=
--   Functor.IsEquivalence.ofFullyFaithfullyEssSurj _

-- noncomputable instance : HasFibers (ℱ.π F) where
--   Fib S := F.obj ⟨op S⟩
--   ι := ℱ.ι F
--   comp_const := ℱ.comp_const F

-- /- DEPRECATED VERSION OF EssSurj proof (bicategory hell)
--     constructor
--     exact {
--       hom := {
--         val := ⟨eqToHom hYS.symm, eqToHom (by simp)⟩
--         property := {
--           ObjLiftDomain := by simp
--           ObjLiftCodomain := hYS
--           HomLift := {
--             w := by simp
--           }
--         }

--       }
--       inv := {
--         val := ⟨eqToHom hYS, by
--           apply eqToHom (show Y.1.2 = (𝟭 (F.obj ⟨op Y.1.1⟩)).obj Y.1.2 by simp) ≫ _
--           apply (F.mapId ⟨op Y.1.1⟩).inv.app Y.1.2 ≫ _
--           apply _ ≫ (F.mapComp _ _).hom.app Y.1.2
--           apply eqToHom
--           simp
--         ⟩
--         property := {
--           ObjLiftDomain := hYS
--           ObjLiftCodomain := by simp
--           HomLift := {
--             w := by simp
--           }
--         }
--       }
--       hom_inv_id := by
--         ext
--         · simp
--         simp
--         sorry
--       inv_hom_id := sorry
--     } -/

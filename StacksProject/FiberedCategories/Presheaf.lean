-- /-
-- Copyright (c) 2024 Calle Sönne. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Paul Lezeau, Calle Sönne
-- -/

-- import StacksProject.FiberedCategories.HasFibers
-- import Mathlib.CategoryTheory.Category.Cat
-- -- import Mathlib.CategoryTheory.DiscreteCategory
-- import Mathlib

-- set_option maxHeartbeats 400000

-- /-!
-- # Fibered category associated to a presheaf

-- In this file we associate to any presheaf valued in types `F : 𝒮ᵒᵖ ⥤ Type _` a fibered
-- category `ℱ F ⥤ 𝒮`.

-- The category `ℱ F` is defined as follows:
-- * Objects: pairs `(S, a)` where `S` is an object of the base category and `a` is an element of the
--   presheaf `F` on `S`
-- * Morphisms: pairs `(f, h)` where `f` is a morphism in the base category and `h` is a proof that the
--   morphism `F.map f.op` sends `a` to `b`

-- The projection functor `ℱ F ⥤ 𝒮` is then given by projecting to the first factors, i.e.
-- * On objects, it sends `(S, a)` to `S`
-- * On morphisms, it sends `(f, h)` to `f`

-- We also provide a `HasFibers` instance `ℱ F`, such that the fiber over `S` is the discrete category
-- associated to `F(S)`.

-- ## References
-- [Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by Angelo Vistoli
-- -/

-- /-
-- TODO:
-- - Fix naming
-- - (Later) Provide a splitting for this category
-- - Functoriality!
-- - Isomorphism between the overcategory and fibered category associated to the corresponding presheaf?
-- -/

-- universe u₁ v₁ u₂ v₂ u₃ w

-- open CategoryTheory Functor Category  Opposite Discrete

-- namespace Presheaf

-- variable {𝒮 : Type u₁} [Category 𝒮] {F : 𝒮ᵒᵖ ⥤ Type u₃}

-- /-- The type of objects in the fibered category associated to a presheaf valued in types. -/
-- def ℱ (F : 𝒮ᵒᵖ ⥤ Type u₃) := (S : 𝒮) × Discrete (F.obj (op S))

-- -- TODO: rename these simp lemmas somehow
-- /-- The category structure on the fibered category associated to a presheaf valued in types. -/
-- @[simps]
-- instance : Category (ℱ F) where
--   Hom X Y := (f : X.1 ⟶ Y.1) × (X.2 ⟶ (Discrete.mk ((F.map f.op) Y.2.1)))
--   -- TODO: figure out PLift up "::" meaning
--   id X := ⟨𝟙 X.1, eqToHom (by simp only [op_id, CategoryTheory.Functor.map_id]; rfl)⟩
--   comp {X Y Z} f g :=
--     have h₁ :  (F.map f.1.op) Y.2.1 = (F.map f.1.op) ((F.map g.1.op) Z.2.1) :=
--       congrArg ((F.map f.1.op) ·) (Discrete.eq_of_hom g.2)
--     have h : (F.map f.1.op) Y.2.1 =
--         (F.map (f.1 ≫ g.1).op) Z.2.1 := Eq.trans h₁
--       (by simp only [op_comp, FunctorToTypes.map_comp_apply])
--     ⟨f.1 ≫ g.1, f.2 ≫ Discrete.eqToHom h⟩
--   id_comp := by
--     intro X Y f
--     -- TODO: make this procedure into a helper lemma?
--     simp only; ext
--     { dsimp; exact id_comp _ }
--     apply Subsingleton.helim
--     simp only [id_comp]
--   comp_id := by
--     intro X Y f
--     simp only; ext
--     { dsimp; exact comp_id _ }
--     apply Subsingleton.helim
--     simp only [comp_id]
--   assoc := by
--     intro W X Y Z f g h
--     simp only; ext
--     { dsimp; exact assoc _ _ _ }
--     apply Subsingleton.helim
--     simp only [assoc]

-- /-- The projection `ℱ F ⥤ 𝒮` given by projecting both objects and homs to the first factor -/
-- @[simps]
-- def ℱ.π (F : 𝒮ᵒᵖ ⥤ Type u₃) : ℱ F ⥤ 𝒮 where
--   obj := λ X => X.1
--   map := @λ X Y f => f.1

-- @[simp]
-- def ℱ.mk_obj {S T : 𝒮} (a : F.obj (op T)) (hST : T = S) : ℱ F :=
--   ⟨S, Discrete.mk ((F.map (eqToHom (congrArg op hST))) a)⟩

-- @[simp]
-- def ℱ.mk_map₁ {R S : 𝒮} (f : R ⟶ S) {X Y : ℱ F} (hX : X.1 = S)
--     (hY : Y.1 = R) : Y.1 ⟶ X.1 := eqToHom hY ≫ f ≫ eqToHom hX.symm

-- @[simp]
-- def ℱ.mk_map {R S : 𝒮} {f : R ⟶ S} {X Y : ℱ F} {hX : X.1 = S}
--     {hY : Y.1 = R} (hXY : Y.2 = Discrete.mk ((F.map (ℱ.mk_map₁ f hX hY).op) X.2.1)) : Y ⟶ X :=
--   ⟨ℱ.mk_map₁ f hX hY, eqToHom hXY⟩

-- @[ext]
-- lemma ℱ.map_ext {X Y : ℱ F} {f g : X ⟶ Y} (hfg : f.1 = g.1) : f = g :=
--   Sigma.ext hfg (Subsingleton.helim (by rw [hfg]) _ _)

-- -- #check ℱ.map_ext_iff

-- -- @[simp]
-- -- lemma ℱ.map_ext_iff {X Y : ℱ F} (f g : X ⟶ Y) : f = g ↔ f.1 = g.1 where
-- --   mp := fun hfg => congrArg _ hfg
-- --   mpr := fun hfg => ℱ.map_ext hfg

-- lemma ℱ.IsHomLift_eq_snd {R S : 𝒮} {f : R ⟶ S} {X Y : ℱ F} {φ : Y ⟶ X} [IsHomLift (ℱ.π F) f φ] :
--     Y.2 = Discrete.mk ((F.map (ℱ.mk_map₁ f sorry sorry).op) X.2.1) := by
--   have h : φ.1 = ℱ.mk_map₁ f sorry sorry := sorry --IsHomLift.eq_of_isHomLift (ℱ.π F) _ _
--   rw [←h]
--   ext
--   apply (Discrete.eq_of_hom φ.2)

-- lemma ℱ.mk_map_IsHomLift {R S : 𝒮} {f : R ⟶ S} {X Y : ℱ F} {hX : X.1 = S}
--     {hY : Y.1 = R} (hXY : Y.2 = Discrete.mk ((F.map (ℱ.mk_map₁ f hX hY).op) X.2.1) )
--     : IsHomLift (ℱ.π F) f (ℱ.mk_map hXY) where
--   cond := sorry
--   -- ObjLiftDomain := hY
--   -- ObjLiftCodomain := hX
--   -- HomLift := ⟨by simp⟩

-- lemma ℱ.mk_map_IsPullback {R S : 𝒮} {f : R ⟶ S} {X Y : ℱ F} {hX : X.1 = S}
--     {hY : Y.1 = R} (hXY : Y.2 = Discrete.mk ((F.map (ℱ.mk_map₁ f hX hY).op) X.2.1))
--     : IsStronglyCartesian (ℱ.π F) f (ℱ.mk_map hXY) :=
--   { ℱ.mk_map_IsHomLift hXY with
--     universal_property' := by
--       intro T g h hφ' --w φ'
--       have hZY : T.2 = Discrete.mk ((F.map (ℱ.mk_map₁ g hY sorry).op) Y.2.1) := by
--         ext
--         simp [IsHomLift_eq_snd (F := F) (f := g ≫ f) (φ := h), hXY]
--       use ℱ.mk_map hZY
--       refine ⟨⟨ℱ.mk_map_IsHomLift hZY, ?_⟩, ?_⟩
--       sorry -- { simpa [w] using (IsHomLift.hom_eq' hφ').symm}
--       intro ψ hψ
--       sorry -- simp [IsHomLift.hom_eq hψ.1]
--       }

-- /-- `ℱ.π` is a fibered category. -/
-- instance : IsFibered (ℱ.π F) where
--   exists_isCartesian' := by
--     intros X R f
--     -- subst hS
--     let Y : ℱ F := ⟨R, Discrete.mk ((F.map (op f)) X.2.1)⟩
--     have hY : Y.2 = Discrete.mk ((F.map (ℱ.mk_map₁ f rfl (show Y.1 = R from rfl)).op) X.2.1) := by
--       simp [ℱ.mk_map₁]; rfl
--     use Y, ℱ.mk_map hY
--     have := ℱ.mk_map_IsPullback hY
--     infer_instance
--   comp := by
--     intro R S T f g a b c φ ψ _ _
--     suffices (ℱ.π F).IsStronglyCartesian (f ≫ g) (φ ≫ ψ) by
--       infer_instance
--     have : (ℱ.π F).IsStronglyCartesian f φ := sorry
--     have : (ℱ.π F).IsStronglyCartesian g ψ := sorry
--     apply IsStronglyCartesian.comp

-- @[simps]
-- def ℱ.ι (F : 𝒮ᵒᵖ ⥤ Type u₃) (S : 𝒮) : Discrete (F.obj (op S)) ⥤ ℱ F where
--   obj := fun a => ⟨S, a⟩
--   map := @fun a b φ => ⟨𝟙 S, φ ≫ eqToHom (by simp only [op_id,
--     FunctorToTypes.map_id_apply, mk_as])⟩
--   map_comp := @fun a b c φ ψ => by
--     apply Sigma.ext
--     · simp
--     · apply Subsingleton.helim
--       simp

-- lemma ℱ.comp_const (F : 𝒮ᵒᵖ ⥤ Type u₃) (S : 𝒮) : (ℱ.ι F S) ⋙ ℱ.π F = (const (Discrete (F.obj (op S)))).obj S := by
--   apply Functor.ext_of_iso {
--     hom := { app := by intro _; exact 𝟙 S }
--     inv := { app := by intro _; exact 𝟙 S } }
--   all_goals simp only [comp_obj, π_obj, ι_obj_fst, const_obj_obj, implies_true]

-- noncomputable instance (S : 𝒮) : Full (Fiber.inducedFunctor (ℱ.comp_const F S)) := by
--   sorry
--   -- apply fullOfExists
--   -- intro X Y f
--   -- have hXY : X.as = Y.as := by
--   --   have h : X.as = F.map f.val.1.op Y.as := eq_of_hom f.1.2
--   --   have h' : 𝟙 S = f.val.1 := by simpa using (IsHomLift.hom_eq' f.2).symm
--   --   rw [←h'] at h
--   --   simpa using h
--   -- use (Discrete.eqToHom hXY)
--   -- ext
--   -- simpa using (IsHomLift.hom_eq' f.2).symm

-- instance (S : 𝒮) : Faithful (Fiber.inducedFunctor (ℱ.comp_const F S)) where
--   map_injective _ := Subsingleton.elim _ _

-- noncomputable instance (S : 𝒮) : EssSurj (Fiber.inducedFunctor (ℱ.comp_const F S)) where
--   mem_essImage Y := by
--     have h : Y.1.1 = S := Y.2
--     use Discrete.mk (F.map (eqToHom (congrArg op h)) Y.1.2.1)
--     constructor
--     sorry
--     -- exact {
--     --   hom := {
--     --     val := ⟨eqToHom Y.2.symm, Discrete.eqToHom (by simp)⟩
--     --     property := {
--     --       ObjLiftDomain := rfl
--     --       ObjLiftCodomain := h
--     --       HomLift := ⟨by dsimp; simp only [eqToHom_trans, eqToHom_refl, comp_id]⟩ }
--     --   }
--     --   inv := {
--     --     val := ⟨eqToHom Y.2, Discrete.eqToHom (by simp)⟩
--     --     property := {
--     --       ObjLiftDomain := h
--     --       ObjLiftCodomain := rfl
--     --       HomLift := ⟨by dsimp⟩
--     --     }
--     --   }
--     --   hom_inv_id := by ext; dsimp; sorry -- simp only [eqToHom_trans, eqToHom_refl]
--     --   inv_hom_id := by ext; dsimp; sorry -- simp only [eqToHom_trans, eqToHom_refl]
--     -- }

-- noncomputable instance (S : 𝒮) : IsEquivalence (Fiber.inducedFunctor (ℱ.comp_const F S)) :=
--   sorry --IsEquivalence.ofFullyFaithfullyEssSurj _

-- -- TODO: this should probably be given a name?
-- noncomputable instance : HasFibers (ℱ.π F) where
--   Fib S := Discrete (F.obj (op S))
--   ι := ℱ.ι F
--   comp_const := ℱ.comp_const F

/-
Copyright (c) 2024 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import LS.TwoMorphism

open CategoryTheory Functor Category Fibered

variable {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃} [Category 𝒳] [Category 𝒮]
  [Category 𝒴]


def TwoYoneda.toFun (p : 𝒳 ⥤ 𝒮) (S : 𝒮) [IsFiberedInGroupoids p] : Fibered.Morphism (Over.forget S) p ⥤ Fiber p S where
  obj := fun f => by
    apply Fiber.mk_obj (show p.obj (f.toFunctor.obj (Over.mk (𝟙 S))) = S from _)
    rw [←Functor.comp_obj, f.w, Over.forget_obj, Over.mk_left]
  map := fun f => by
    apply Fiber.mk_map _ _ (f.toIso.hom.app (Over.mk (𝟙 S))) _
    apply f.aboveId
    simp only [Over.forget_obj, Over.mk_left]
  map_id := by
    intro f
    simp only [comp_obj, Eq.ndrec, id_eq, Over.forget_obj, Over.mk_left, eq_mpr_eq_cast, cast_eq]
    apply Fiber.mk_map_id
  map_comp := by
    intro X Y Z f g
    simp only [comp_obj, Eq.ndrec, id_eq, Over.forget_obj, Over.mk_left, eq_mpr_eq_cast, cast_eq]
    rw [←Fiber.mk_map_com]
    rfl

-- Any object a in the fiber above S (i.e. a morphism a ⟶ S in 𝒮) gives rise to a fibered morphism from the forgetful functor
-- (Fiber p S ⥤ 𝒮) to p
@[simps]
noncomputable def TwoIsomorphism.Fibered_Morphism_of_fiber_obj {p : 𝒳 ⥤ 𝒮} {S : 𝒮} (hp : IsFiberedInGroupoids p) (a : Fiber p S) : Fibered.Morphism (Over.forget S) p where
  obj := fun b => PullbackObj hp.toIsFibered a.2 b.hom
  map := fun f => by
    apply IsPullbackInducedMap (p:= p) (f := (_ : Over S).hom) (g := f.left) (f' := f.left ≫ (_ : Over S).hom) (φ := PullbackMap hp.toIsFibered a.2 (_ : Over S).hom) (φ' := PullbackMap hp.toIsFibered a.2 (_ : Over S).hom) (PullbackMapIsPullback _ _ _) rfl
    rw [Over.w]
    apply (PullbackMapIsPullback _ _ _).toIsHomLift
  map_id X := by
    simp only [id_obj, const_obj_obj, id_eq, eq_mpr_eq_cast, Over.id_left, id_comp, IsPullbackInducedMap_self_eq_id]
  map_comp := by
    simp only [id_obj, const_obj_obj, id_eq, eq_mpr_eq_cast, Over.comp_left, assoc, Over.w,
      IsPullbackInducedMap_comp, implies_true]
  w := by
    apply Functor.ext ?_ ?_
    · intro X
      simp only [id_obj, const_obj_obj, Over.w, comp_obj, Over.forget_obj, PullbackObjLiftDomain]
    · intro X Y f
      simp only [id_obj, const_obj_obj, id_eq, Over.id_left, Over.comp_left, comp_obj,
        Functor.comp_map, Over.w, Over.forget_obj, Over.forget_map]
      rw [←Category.assoc, ←comp_eqToHom_iff]
      apply (IsPullbackInducedMap_IsHomLift _ _ _).HomLift.w

lemma Fiber.map_IsPullback_id {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a b : Fiber p S} (f : a ⟶ b) : IsPullback p (𝟙 S) f.val := sorry

lemma IsPullbackInducedMap_IsPullback {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
  {φ' : a' ⟶ b} (hφ' : IsHomLift p f' φ') : IsPullback p g (IsPullbackInducedMap hφ hf' hφ') := by
  sorry

noncomputable instance {p : 𝒳 ⥤ 𝒮} [IsFiberedInGroupoids p] {S : 𝒮} : Groupoid (Fiber p S) where
  inv {a b} f :=
    Fiber.mk_map b.prop a.prop (IsPullbackInducedMap (p := p) (f := 𝟙 S) (g := 𝟙 S) (f' := 𝟙 S) (hf' := by simp only [comp_id]) (Fiber.map_IsPullback_id f) (φ' := 𝟙 b.val) (IsHomLift_id b.prop)) (IsPullbackInducedMap_IsHomLift _ _ _)
  inv_comp {a b} f := by
    ext
    simp only [FiberCategory_comp_coe, FiberCategory_id_coe]
    simp_rw [Fiber.mk_map]
    apply IsPullbackInducedMap_Diagram
  comp_inv {a b} f := by
    let f'' : b.val ⟶ a.val := (IsPullbackInducedMap (p := p) (f := 𝟙 S) (g := 𝟙 S) (f' := 𝟙 S) (hf' := by simp only [comp_id]) (Fiber.map_IsPullback_id f) (φ' := 𝟙 b.val) (IsHomLift_id b.prop))
    have : IsPullback p (𝟙 S) f'' := IsPullbackInducedMap_IsPullback _ _ _
    let f' := Fiber.mk_map b.prop a.prop f'' (IsPullbackInducedMap_IsHomLift _ _ _)
    let h : a ⟶ b := Fiber.mk_map a.prop b.prop (IsPullbackInducedMap (p := p) (f := 𝟙 S) (g := 𝟙 S) (f' := 𝟙 S) (hf' := by simp only [comp_id]) this (φ' := 𝟙 a.val) (IsHomLift_id a.prop)) (IsPullbackInducedMap_IsHomLift _ _ _)
    have : f' ≫ f = 𝟙 _ := by
      ext
      simp only [FiberCategory_comp_coe, FiberCategory_id_coe, Fiber.mk_map_coe]
      rw [show f'.val = f'' by rfl]
      sorry
    ext
    simp only [FiberCategory_comp_coe, FiberCategory_id_coe]
    simp_rw [Fiber.mk_map]
    sorry


/- lemma TwoIsomorphism.Fibered_Morphism_of_fiber_obj_apply_obj {p : 𝒳 ⥤ 𝒮} {S : 𝒮} (hp : IsFiberedInGroupoids p) (a : Fiber p S) {b : Over S} : (TwoIsomorphism.Fibered_Morphism_of_fiber_obj hp a).obj a =  -/

-- Any morphism f : a ⟶ b in the fiber above S (i.e. a morphism a ⟶ b above S) gives rise to a 2-isomorphism between the fibered
-- morphisms defined above
@[simps]
noncomputable def TwoIsomorphism.TwoIsomorphism_of_fiber_morphism {p : 𝒳 ⥤ 𝒮} {S : 𝒮}
  (hp : IsFiberedInGroupoids p) {a b : Fiber p S} (f : a ⟶ b) : Fibered.TwoIsomorphism (TwoIsomorphism.Fibered_Morphism_of_fiber_obj hp a) (TwoIsomorphism.Fibered_Morphism_of_fiber_obj hp b) where
    hom := {
      app := fun x => IsPullbackNaturalityHom (p := p) (PullbackMapIsPullback hp.toIsFibered a.2 _) (PullbackMapIsPullback hp.toIsFibered b.2 _) (ψ := f.1) (HasFibersHomLift  _)
      naturality := by
        intro X Y f
        simp only [id_obj]
        apply CommSq.w
        simp only [Fibered_Morphism_of_fiber_obj_obj, id_obj, Fibered_Morphism_of_fiber_obj_map,
          const_obj_obj, Over.w]
        constructor
        sorry
    }
    inv := {
      app := fun x => sorry
        /- IsPullbackNaturalityHom (p := p) (PullbackMapIsPullback hp.toIsFibered b.2 _) (PullbackMapIsPullback hp.toIsFibered a.2 _) f.1 (HasFibersHomLift  _)  -/
      naturality := sorry
    }
    hom_inv_id := sorry
    inv_hom_id := sorry
    aboveId := sorry

-- the pseudo-inverse two yoneda functor
noncomputable def TwoYoneda.invFun (p : 𝒳 ⥤ 𝒮) (S : 𝒮) [IsFiberedInGroupoids p] : Fiber p S ⥤ Fibered.Morphism (Over.forget S) p where
  obj := fun a => TwoIsomorphism.Fibered_Morphism_of_fiber_obj (p := p) (by infer_instance) a
  map := fun f => TwoIsomorphism.TwoIsomorphism_of_fiber_morphism (p := p) (by infer_instance) f
  map_id := by
    intro X
    simp only
    apply Fibered.TwoIsomorphism.ext
    ext x
    simp only [TwoIsomorphism.Fibered_Morphism_of_fiber_obj_obj, id_obj,
      TwoIsomorphism.TwoIsomorphism_of_fiber_morphism_hom_app, FiberCategory_id_coe]
    rw [Fibered.Morphism_Cat_id_apply]
    rw [IsPullbackNaturalityHom_id]
  map_comp := by
    intro X Y Z f g
    apply Fibered.TwoIsomorphism.ext
    ext x
    simp only [IsPullbackNaturalityHom_comp]
    simp only [TwoIsomorphism.Fibered_Morphism_of_fiber_obj_obj, id_obj,
      TwoIsomorphism.TwoIsomorphism_of_fiber_morphism_hom_app, FiberCategory_comp_coe]
    simp only [id_obj, TwoIsomorphism.Fibered_Morphism_of_fiber_obj_obj, Morphism_Cat_comp_apply,
      TwoIsomorphism.TwoIsomorphism_of_fiber_morphism_hom_app]
    rw [IsPullbackNaturalityHom_comp]

noncomputable def TwoYoneda.Equivalence (p : 𝒳 ⥤ 𝒮) (S : 𝒮) [IsFiberedInGroupoids p] :
  Fibered.Morphism (Over.forget S) p  ≌ Fiber p S  where
    functor := TwoYoneda.toFun p S
    inverse := TwoYoneda.invFun p S
    unitIso := sorry
    counitIso := sorry
    functor_unitIso_comp := sorry

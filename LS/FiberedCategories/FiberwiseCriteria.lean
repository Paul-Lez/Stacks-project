/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import LS.FiberedCategories.FiberedCat

/-!
# Fiberwise criteria for functors between fibered categories
In this file we prove fiberwise criteria for a functor between fibered categories to be
either full, faithful or an equivalence.

-/

universe u₁ v₁ u₂ v₂

open CategoryTheory Functor Category Bicategory IsHomLift IsPullback

open scoped Bicategory

namespace Fibered

variable {𝒮 : Type u₁} [Category.{v₂} 𝒮]

/-- If a morphism F is faithFul, then it is also faithful fiberwise -/
lemma FiberwiseFaithfulofFaithful {𝒳 𝒴 : FiberCat 𝒮} (F : 𝒳 ⟶ 𝒴) [Functor.Faithful  F.toFunctor] :
    ∀ (S : 𝒮), Functor.Faithful  (F.onFib S) := by
  intro S
  haveI h :Functor.Faithful  ((F.onFib S) ⋙ (𝒴.hasFib.ι S)) := (F.fib_w S).symm ▸ Faithful.comp (𝒳.hasFib.ι S) F.toFunctor
  apply Functor.Faithful.of_comp _ (𝒴.hasFib.ι S)

/-- A FiberMorphism F is faithful if it is so pointwise. For proof see [Olsson] -/
lemma FaithfulofFiberwiseFaithful {𝒳 𝒴 : FiberedCat 𝒮} {F : FiberedFunctor 𝒳 𝒴}
    (hF₁ : ∀ (S : 𝒮), Functor.Faithful  (F.onFib S)) : Functor.Faithful  F.toFunctor where
  map_injective := by
    intro a b φ φ' heq
    /- We start by reducing to a setting when the domains lie in some fiber of the HasFibers.
    We do this by finding some Φ : a' ≅ a by essential surjectivity of the fiber structures,
    and then defining φ₁ := Φ.hom ≫ φ and φ₁' := Φ.hom ≫ φ'. -/
    rcases HasFibersEssSurj' (rfl (a := 𝒳.p.obj a)) with ⟨a', Φ, _⟩
    let φ₁ := Φ.hom ≫ φ
    let φ₁' := Φ.hom ≫ φ'
    suffices φ₁ = φ₁' by rwa [←CategoryTheory.Iso.cancel_iso_hom_left Φ]
    -- We also have that F(φ₁) = F(φ₁')
    have heq₁ : F.map φ₁ = F.map φ₁' := by
      simp only [F.map_comp]
      apply congrArg (F.map Φ.hom ≫ ·) heq
    /- The goal is now to factor φ₁ and φ₁' through some pullback to reduce to checking
    two morphisms τ and τ' in the fibers are equal, which will then follow from fiber-wise
    faithfulness. -/
    let h : 𝒳.p.obj a ⟶ 𝒳.p.obj b := eqToHom ((HasFibersObjLift a').symm) ≫ 𝒳.p.map φ₁
    -- Let ψ : c ⟶ b be a pullback over h such that c : Fib (p.obj a)
    rcases HasFibersPullback' rfl h with ⟨c, ψ, hψ⟩
    -- Both φ₁ and φ₁' are lifts of h
    have hφ₁ : IsHomLift 𝒳.p h φ₁ := (lift_eqToHom_comp_iff _).2 (IsHomLift.self 𝒳.p φ₁)
    have hφ₁' : IsHomLift 𝒳.p h φ₁' :=  by
      rw [lift_eqToHom_comp_iff, congr_hom F.w.symm, Functor.comp_map]
      rw [heq₁, ←Functor.comp_map, ←congr_hom F.w.symm]
      apply IsHomLift.self 𝒳.p φ₁'
    -- Let τ, τ' be the induced maps from a' to c given by φ and φ'
    rcases HasFibersFactorization hφ₁ hψ with ⟨τ, hτ⟩
    rcases HasFibersFactorization hφ₁' hψ with ⟨τ', hτ'⟩
    -- Thus, it suffices to show that τ = τ'
    suffices τ = τ' by rw [←hτ, ←hτ', this]
    have hψ' : IsPullback 𝒴.p h (F.map ψ) := F.pullback hψ
    -- F(τ) and F(τ') both solve the same pullback problem in 𝒴
    have hτ₁ : F.map ((𝒳.hasFib.ι (𝒳.p.obj a)).map τ) ≫ F.map ψ = F.map φ₁ := by rw [←Functor.map_comp, hτ]
    have hτ'₁ : F.map ((𝒳.hasFib.ι (𝒳.p.obj a)).map τ') ≫ F.map ψ = F.map φ₁ := by
      rw [←Functor.map_comp, hτ']
      apply heq₁.symm
    -- Hence we get that F(τ) = F(τ'), so we can conclude by fiberwise injectivity
    have hτ₂ := InducedMap_unique hψ' ((id_comp h).symm)
      (F.pres_IsHomLift hφ₁) (F.pres_IsHomLift (HasFibersHomLift τ)) hτ₁
    have hτ'₂ := InducedMap_unique hψ' ((id_comp h).symm)
      (F.pres_IsHomLift hφ₁) (F.pres_IsHomLift (HasFibersHomLift τ')) hτ'₁
    have heqττ' : F.map ((𝒳.hasFib.ι (𝒳.p.obj a)).map τ) = F.map ((𝒳.hasFib.ι (𝒳.p.obj a)).map τ') := by rw [hτ₂, hτ'₂]
    have heqττ'₁ : (F.onFib _).map τ = (F.onFib _).map τ' := by
      apply Functor.map_injective (𝒴.hasFib.ι (𝒳.p.obj a))
      simp_rw [←Functor.comp_map, congr_hom (F.fib_w (𝒳.p.obj a)), Functor.comp_map]
      rw [heqττ']
    apply Functor.map_injective (F.onFib (𝒳.p.obj a)) heqττ'₁

lemma PreimageIsHomLift {𝒳 𝒴 : FiberCat 𝒮} (F : 𝒳 ⟶ 𝒴) [hF₁ : Functor.Full F.toFunctor]
    {a b : 𝒳.cat} {φ : F.obj a ⟶ F.obj b} {R S : 𝒮} {f : R ⟶ S} (hφ : IsHomLift 𝒴.p f φ) :
    IsHomLift 𝒳.p f (hF₁.preimage φ) := (hF₁.witness φ ▸ F.HomLift_ofImage) hφ

/- We now show that a morphism F is full if and only if its full fiberwise -/
lemma FiberwiseFullofFull  { 𝒳 𝒴 : FiberCat 𝒮} (F : 𝒳 ⟶ 𝒴) [hF₁ : Functor.Full F.toFunctor] :
    ∀ (S : 𝒮), Functor.Full (F.onFib S) := by
  intro S
  apply fullOfExists
  intro a b φ

  let φ₁ :=  eqToHom (congr_obj (F.fib_w S) a).symm ≫ ((𝒴.hasFib.ι S).map φ)
    ≫ eqToHom (congr_obj (F.fib_w S) b)

  have hφ₁ : IsHomLift 𝒳.p (𝟙 S) (hF₁.preimage φ₁) := by
    apply PreimageIsHomLift
    simp [φ₁, HasFibersHomLift φ]

  use Classical.choose (HasFibersFull hφ₁)
  apply Functor.map_injective (𝒴.hasFib.ι S)
  -- Maybe its worth making this a standalone lemma
  rw [←Functor.comp_map, congr_hom (F.fib_w S), Functor.comp_map]
  simp [Classical.choose_spec (HasFibersFull hφ₁), φ₁]

lemma FullofFullFiberwise  { 𝒳 𝒴 : FiberedCat 𝒮} {F : 𝒳 ⟶ 𝒴} (hF₁ : ∀ (S : 𝒮), Functor.Full (F.onFib S)) :
    Functor.Full F.toFunctor := by
  apply fullOfExists
  intro a b φ

  let R := 𝒳.p.obj a
  let S := 𝒳.p.obj b

  -- Reduce to checking when domain is in a fiber
  let a' := Classical.choose (HasFibersEssSurj' (rfl (a:=R)))
  let Φ := Classical.choose (Classical.choose_spec (HasFibersEssSurj' (rfl (a := R))))
  let hΦ := Classical.choose_spec (Classical.choose_spec (HasFibersEssSurj' (rfl (a := R))))

  -- Now consider φ₁ : F.obj a' ⟶ F.obj b
  have ha' : (𝒴.hasFib.ι R).obj ((F.onFib R).obj a') = F.obj ((𝒳.hasFib.ι R).obj a') := by
    rw [←comp_obj, ←comp_obj, F.fib_w] --congr_obj comp_eq
  let φ₁ : (𝒴.hasFib.ι R).obj ((F.onFib R).obj a') ⟶ F.obj b :=
    eqToHom ha' ≫ (F.mapIso Φ).hom ≫ φ

  let h : R ⟶ S := eqToHom (F.obj_proj a).symm ≫ 𝒴.p.map φ ≫ eqToHom (F.obj_proj b)

  -- Let ψ : c ⟶ b be a pullback over h such that c : Fib R
  let c := Classical.choose (HasFibersPullback' rfl h)
  let ψ := Classical.choose (Classical.choose_spec (HasFibersPullback' rfl h))
  let hψ := Classical.choose_spec (Classical.choose_spec (HasFibersPullback' rfl h))

  have hφ₁ : IsHomLift 𝒴.p h φ₁ := by
    simp [φ₁, h]
    apply comp_lift_id_right (IsHomLift.self 𝒴.p φ) (F.pres_IsHomLift hΦ)

  -- The following could be some hF.preservesPullbacks (wrt HasFibers) API
  have hc : (𝒴.hasFib.ι R).obj ((F.onFib R).obj c) = F.obj ((𝒳.hasFib.ι R).obj c) := by
    rw [←comp_obj, ←comp_obj, F.fib_w] --
  let ψ' := eqToHom hc ≫ F.map ψ
  have hψ' : IsPullback 𝒴.p h ψ' := eqToHom_comp (F.pullback hψ) _

  -- Let τ be the induced map from a' to c given by φ₁
  let τ := Classical.choose (HasFibersFactorization hφ₁ hψ')
  let π := (hF₁ R).preimage τ

  use Φ.inv ≫ (𝒳.hasFib.ι R).map π ≫ ψ

  -- TODO GOLF THIS
  simp only [map_comp]
  rw [←Functor.comp_map, congr_hom (F.fib_w (𝒳.p.obj a)).symm]
  rw [Functor.comp_map, (hF₁ (𝒳.p.obj a)).witness]
  rw [Category.assoc, Category.assoc]
  rw [Classical.choose_spec (HasFibersFactorization hφ₁ hψ')]
  simp [φ₁]
  rw [←Category.assoc, ←Functor.mapIso_inv, ←Functor.mapIso_hom]
  rw [Iso.inv_hom_id, id_comp]


lemma FiberwiseIsEquivalenceOfEquivalence {𝒳 𝒴 : FiberedCat 𝒮} (F : 𝒳 ≌ 𝒴) :
    ∀ S : 𝒮, Functor.IsEquivalence (F.hom.onFib S) := by
  intro S
  refine @Equivalence.ofFullyFaithfullyEssSurj _ _ _ _ _ ?_ ?_ ?_
  { exact FiberwiseFullofFull F.hom.toFiberFunctor S }
  { exact FiberwiseFaithfulofFaithful F.hom.toFiberFunctor S}
  -- TODO: create this instance (+ API?)
  -- TODO: create separate lemma "FiberwiseIsEssSurjOfEssSurj"
  constructor
  intro a
  -- let `b` be the image of `a` under `F.inv`
  let b := F.inv.obj ((𝒴.hasFib.ι S).obj a)
  -- since `F.inv` is a functor of fibered categories, `b` is in the fiber of `S`
  have hb : 𝒳.p.obj b = S := by rw [F.inv.obj_proj, HasFibersObjLift]
  -- let `b'` be an object of `𝒳.HasFib.Fib S` with an isomorphism `Φ : b' ≅ b`
  let b' := Classical.choose (HasFibersEssSurj' hb)
  let Φ : (𝒳.hasFib.ι S).obj b' ≅ b := Classical.choose (Classical.choose_spec (HasFibersEssSurj' hb))
  have hΦ := Classical.choose_spec (Classical.choose_spec (HasFibersEssSurj' hb))

  -- We have that `(F.onFib R).obj b' ≅ F.obj b` in `𝒴.cat`
  let Φ' : (𝒴.hasFib.ι S).obj ((F.hom.onFib S).obj b') ≅ F.hom.obj b :=
    eqToIso (FiberFunctor.fib_w_obj _ _) ≪≫ (F.hom.toFunctor.mapIso Φ)

  let Ψ : (𝒴.hasFib.ι S).obj ((F.hom.onFib S).obj b') ≅ (𝒴.hasFib.ι S).obj a :=
    -- TODO: create API for BasedNatIso to avoid IsoOfBasedIso
    Φ' ≪≫ (IsoOfBasedIso (F.counit)).app ((𝒴.hasFib.ι S).obj a)

  have hΨ : IsHomLift 𝒴.p (𝟙 S) Ψ.hom := by
    simp only [Iso.trans_hom, Iso.app_hom, Ψ, Φ']
    apply lift_id_comp _ (F.counit.hom.aboveId (HasFibersObjLift _))
    apply lift_id_comp _ (F.hom.pres_IsHomLift hΦ)
    simp only [eqToIso.hom]
    apply eqToHom_domain_lift_id
    simp only [BasedFunctor.obj_proj, HasFibersObjLift]

  use b'
  constructor
  exact HasFibersPreimageIso Ψ hΨ

noncomputable def InvOfFiberWiseIsEquivalence.Obj {𝒳 𝒴 : FiberedCat 𝒮} {F : 𝒳 ⟶ 𝒴}
    (hF : ∀ S : 𝒮, Functor.IsEquivalence (F.onFib S)) (y : 𝒴.cat) : 𝒳.cat := by
  let S := 𝒴.p.obj y
  -- let `y'` be an object of `𝒴.hasFib.Fib S` with an isomorphism `Φ : y' ≅ y`
  let y' := Classical.choose (HasFibersEssSurj' (rfl (a:=S)))
  -- let `x` be a preimage of `y'` under `F.onFib S`
  have := Equivalence.essSurj_of_equivalence (F.onFib S)
  let x := (F.onFib S).objPreimage y'
  -- TODO: could instead use `F.onFib.inv y'`...
  exact (𝒳.hasFib.ι S).obj x

noncomputable def InvOfFiberwiseIsEquivalence.ObjIso {𝒳 𝒴 : FiberedCat 𝒮} {F : 𝒳 ⟶ 𝒴}
    (hF : ∀ S : 𝒮, Functor.IsEquivalence (F.onFib S)) (y : 𝒴.cat) :
      F.obj (InvOfFiberWiseIsEquivalence.Obj hF y) ≅ y := by
  let S := 𝒴.p.obj y
  haveI := Equivalence.essSurj_of_equivalence (F.onFib S)
  -- iso F.onFib.obj .. ≅ y'
  let Φ := (F.onFib S).objObjPreimageIso (Classical.choose (HasFibersEssSurj' (rfl (a:=S))))
  let Φ' : F.obj (InvOfFiberWiseIsEquivalence.Obj hF y) ≅ y := by
    apply eqToIso _ ≪≫ (𝒴.hasFib.ι S).mapIso Φ ≪≫
      Classical.choose (Classical.choose_spec (HasFibersEssSurj' (rfl (a:=S))))
    -- first lemma define it manually
    simp only [InvOfFiberWiseIsEquivalence.Obj, FiberFunctor.fib_w_obj]

  exact Φ'

lemma InvOfFiberwiseIsEquivalence.ObjIso_IsHomLift {𝒳 𝒴 : FiberedCat 𝒮} {F : 𝒳 ⟶ 𝒴}
      (hF : ∀ S : 𝒮, Functor.IsEquivalence (F.onFib S)) (y : 𝒴.cat) :
    IsHomLift 𝒴.p (𝟙 (𝒴.p.obj y)) (InvOfFiberwiseIsEquivalence.ObjIso hF y).hom where
      ObjLiftDomain := by rw [F.obj_proj]; apply HasFibersObjLift
      ObjLiftCodomain := rfl
      HomLift := ⟨by
        unfold ObjIso
        simp only [Iso.trans_hom, eqToIso.hom, mapIso_hom, map_comp, eqToHom_refl, comp_id]
        rw [IsHomLift.hom_eq' (HasFibersHomLift _)]
        rw [IsHomLift.hom_eq' (Classical.choose_spec (Classical.choose_spec (HasFibersEssSurj' (rfl (a:=𝒴.p.obj y)))))]
        simp only [eqToHom_map, HasFibersObjLift, eqToHom_naturality, comp_id, eqToHom_trans,
          eqToHom_refl]⟩

@[simps]
noncomputable def OfFiberwiseEquivalence.InvFunctor {𝒳 𝒴 : FiberedCat 𝒮} {F : 𝒳 ⟶ 𝒴}
    (hF : ∀ S : 𝒮, Functor.IsEquivalence (F.onFib S)) : 𝒴.cat ⥤ 𝒳.cat where
      obj y := InvOfFiberWiseIsEquivalence.Obj hF y
      map {y y'} φ := by
        -- define `φ' : .. ≅ y ⟶ y' ≅ ..`
        let φ' := (InvOfFiberwiseIsEquivalence.ObjIso hF y).hom ≫ φ ≫
          (InvOfFiberwiseIsEquivalence.ObjIso hF y').inv
        let h₁ : Functor.Full F.toFunctor := FullofFullFiberwise inferInstance
        exact F.preimage φ'

      map_id y := by
        have : Functor.Faithful  F.toFunctor := FaithfulofFiberwiseFaithful inferInstance
        simp only [id_comp, Iso.hom_inv_id, Functor.preimage_id]

      map_comp {x y z} φ ψ := by
        have : Functor.Faithful  F.toFunctor := FaithfulofFiberwiseFaithful inferInstance
        simp only [assoc, ← Functor.preimage_comp, Iso.inv_hom_id_assoc]

@[simps]
noncomputable def OfFiberwiseEquivalence.InvFunctor_w {𝒳 𝒴 : FiberedCat 𝒮} {F : 𝒳 ⟶ 𝒴}
    (hF : ∀ S : 𝒮, Functor.IsEquivalence (F.onFib S)) :
      (OfFiberwiseEquivalence.InvFunctor hF) ⋙ 𝒳.p ≅ 𝒴.p where
        hom := {
          app := fun y => eqToHom (HasFibersObjLift _)
          naturality := by
            intros y y' φ
            simp only [Functor.comp_map]
            rw [IsHomLift.hom_eq (F.IsHomLift_map ((InvFunctor hF).map φ))]
            -- This all should be factored out
            simp only [comp_obj, InvFunctor_obj, InvFunctor_map, assoc,
              image_preimage, map_comp, eqToHom_trans]
            rw [IsHomLift.hom_eq' (InvOfFiberwiseIsEquivalence.ObjIso_IsHomLift hF y)]
            -- TODO: maybe I should restate this lemma better
            have := (lift_id_inv (InvOfFiberwiseIsEquivalence.ObjIso_IsHomLift hF y'))
            simp only [IsIso.Iso.inv_hom] at this

            rw [IsHomLift.hom_eq' this]
            simp only [InvFunctor_obj, eqToHom_refl, comp_id, id_comp, eqToHom_trans,
              eqToHom_trans_assoc, comp_obj]
        }
        inv := {
          app := fun y => eqToHom (HasFibersObjLift _).symm
          naturality := sorry -- same as above
        }

lemma PreimageIsPullback {𝒳 𝒴 : FiberCat 𝒮} (F : 𝒳 ⟶ 𝒴) [Functor.Full F.toFunctor]
    [Functor.Faithful  F.toFunctor] {a b : 𝒳.cat} {φ : F.obj a ⟶ F.obj b} {R S : 𝒮} {f : R ⟶ S}
    (hφ : IsPullback 𝒴.p f φ) : IsPullback 𝒳.p f (F.preimage φ) :=
    { PreimageIsHomLift F hφ.toIsHomLift with
      UniversalProperty := by
        intro R' a' g f' hgf φ' hφ'
        have hFφ' := F.pres_IsHomLift hφ'
        let ψ := InducedMap hφ hgf hFφ'
        use F.preimage ψ
        refine ⟨⟨?_, ?_⟩, ?_⟩
        { apply PreimageIsHomLift
          apply (InducedMap_IsHomLift hφ hgf hFφ') }
        { apply F.map_injective
          simp
          apply InducedMap_Diagram hφ hgf hFφ'}

        simp only [and_imp]
        intro χ hχ hχ_comp
        apply F.map_injective
        rw [F.image_preimage]
        apply InducedMap_unique hφ hgf hFφ'
        apply F.pres_IsHomLift hχ
        simpa using congrArg F.map hχ_comp }

@[simps!]
noncomputable def InvOfFiberwiseIsEquivalence {𝒳 𝒴 : FiberedCat 𝒮} (F : 𝒳 ⟶ 𝒴)
    (hF : ∀ S : 𝒮, Functor.IsEquivalence (F.onFib S)) : 𝒴 ⟶ 𝒳 :=
{ OfFiberwiseEquivalence.InvFunctor hF with
  w := by
    apply Functor.ext_of_iso (OfFiberwiseEquivalence.InvFunctor_w hF)
    { exact fun y => OfFiberwiseEquivalence.InvFunctor_w_hom_app hF y }

  -- TODO: do I need these? Should functoriality be defined differently?
  onFib := fun S => (hF S).inverse -- maybe use more complicated defn to make it easier
  fib_w := by
    intro S
    sorry

  pullback := by
    intro a b R S f φ hφ
    let h₁ : Functor.Full F.toFunctor := FullofFullFiberwise inferInstance
    have h₂ : Functor.Faithful  F.toFunctor := FaithfulofFiberwiseFaithful inferInstance
    simp only [OfFiberwiseEquivalence.InvFunctor_map]
    apply PreimageIsPullback _
    rw [show f = 𝟙 R ≫ f ≫ 𝟙 S by simp]
    apply IsPullback.comp
    apply of_isIso
    rw [←hφ.ObjLiftDomain]
    apply InvOfFiberwiseIsEquivalence.ObjIso_IsHomLift
    apply IsPullback.comp hφ
    apply of_isIso
    -- TODO: maybe I should restate this lemma better
    have := (lift_id_inv (InvOfFiberwiseIsEquivalence.ObjIso_IsHomLift hF b))
    simp only [IsIso.Iso.inv_hom] at this
    rw [←hφ.ObjLiftCodomain]
    apply this
  }

noncomputable def EquivalenceOfFiberwiseIsEquivalence {𝒳 𝒴 : FiberedCat 𝒮} (F : 𝒳 ⟶ 𝒴)
    (hF : ∀ S : 𝒮, Functor.IsEquivalence (F.onFib S)) : 𝒳 ≌ 𝒴 where
  hom := F
  inv := InvOfFiberwiseIsEquivalence F hF
  -- unit is from last part of Olssons proof
  unit := {
    hom := {
      app := by
        intro x
        let hF₁ : Functor.Full F.toFunctor := FullofFullFiberwise inferInstance
        apply F.preimage
        -- TODO: 𝟙 notation doesnt work here for some reason...
        let h := (FiberedFunctor.id 𝒳).obj
        exact (InvOfFiberwiseIsEquivalence.ObjIso hF (F.obj ((FiberedFunctor.id 𝒳).obj x))).inv

      naturality := by
        intros
        have : Functor.Faithful  F.toFunctor := FaithfulofFiberwiseFaithful inferInstance
        apply F.map_injective
        simp
      aboveId := by
        intro x S hx
        let h₁ : Functor.Full F.toFunctor := FullofFullFiberwise inferInstance
        simp only
        apply PreimageIsHomLift
        -- TODO: I should restate this lemma better
        have := (lift_id_inv (InvOfFiberwiseIsEquivalence.ObjIso_IsHomLift hF (F.obj ((FiberedFunctor.id 𝒳).obj x))))
        simp only [IsIso.Iso.inv_hom] at this
        rw [←hx, ←F.obj_proj x]
        exact this
    }
    inv := {
      app := by
        intro x
        let hF₁ : Functor.Full F.toFunctor := FullofFullFiberwise inferInstance
        apply F.preimage
        -- TODO: 𝟙 notation doesnt work here for some reason...
        let h := (FiberedFunctor.id 𝒳).obj
        exact (InvOfFiberwiseIsEquivalence.ObjIso hF (F.obj ((FiberedFunctor.id 𝒳).obj x))).hom
      naturality := sorry -- same as above
      aboveId := sorry -- same as above
    }
    hom_inv_id := by
      simp
      ext x
      -- TODO: should make these two lines into some sort of simp lemma,
      -- then some proofs will get automated
      have : Functor.Faithful  F.toFunctor := FaithfulofFiberwiseFaithful inferInstance
      apply F.map_injective
      simp
    inv_hom_id := sorry -- same as above
  }
  counit := {
    hom := {
      app := fun y => (InvOfFiberwiseIsEquivalence.ObjIso hF y).hom
      aboveId := by
        intro y S hy
        rw [←hy]
        apply InvOfFiberwiseIsEquivalence.ObjIso_IsHomLift hF y
    }
    inv := {
      app := fun y => (InvOfFiberwiseIsEquivalence.ObjIso hF y).inv
      aboveId := by
        intro y S hy
        -- TODO: restate lemma giving this
        have := (lift_id_inv (InvOfFiberwiseIsEquivalence.ObjIso_IsHomLift hF y))
        simp only [IsIso.Iso.inv_hom] at this
        rw [←hy]
        apply this
    }
  }
  left_triangle := sorry




end Fibered

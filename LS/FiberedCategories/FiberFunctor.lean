/-
Copyright (c) 2023 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/

import LS.HasFibers

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃} [Category 𝒳] [Category 𝒮] [Category 𝒴]

namespace Fibered

structure Morphism (p : 𝒳 ⥤ 𝒮) (q : 𝒴 ⥤ 𝒮) extends CategoryTheory.Functor 𝒳 𝒴 where
  (w : toFunctor ⋙ q = p)

protected def Morphism.id (p : 𝒳 ⥤ 𝒮) : Morphism p p :=
  { 𝟭 𝒳 with w := CategoryTheory.Functor.id_comp _ }

/-- A notion of functor between HasFibers. It is given by a functor F : 𝒳 ⥤ 𝒴 such that F ⋙ q = p,
  and a collection of functors fiber_functor S between the fibers of p and q over S in 𝒮 such that
  .... -/
class IsFiberMorphism {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [hp : HasFibers p] [hq : HasFibers q] (F : Morphism p q) where
  (fiber_functor (S : 𝒮) : hp.Fib S ⥤ hq.Fib S)
  (comp_eq : ∀ (S : 𝒮), (fiber_functor S) ⋙ (hq.ι S) = (hp.ι S) ⋙ F.toFunctor) -- TRY AESOP_CAT BY DEFAULT HERE?

/-- A notion of functor between FiberedStructs. It is furthermore required to preserve pullbacks  -/
class IsFiberedMorphism {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [IsFibered p] [hp : HasFibers p]
    [IsFibered q] [hq : HasFibers q] (F : Morphism p q) extends IsFiberMorphism F where
  (preservesPullbacks {R S : 𝒮} {f : R ⟶ S} {φ : a ⟶ b} (_ : IsPullback p f φ) : IsPullback q f (F.map φ))

@[simp]
lemma Morphism.obj_proj {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (F : Morphism p q) (a : 𝒳) : q.obj (F.obj a) = p.obj a := by
  rw [←comp_obj, F.w]

@[simp]
lemma Morphism.fiber_proj {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [hp : HasFibers p]
    (F : Morphism p q) {S : 𝒮} (a : hp.Fib S) : q.obj (F.obj ((hp.ι S).obj a)) = S := by
  rw [Morphism.obj_proj F ((hp.ι S).obj a), HasFibersObjLift]

-- lemma IsFiberMorphism.congr_hom {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [hp : HasFibers p] [hq : HasFibers q]
--     (F : Morphism p q) [hF : IsFiberMorphism F] {S : 𝒮} {a b : hp.Fib S} (φ : a ⟶ b ):
--     (hq.ι S).map ((hF.fiber_functor S).map φ) = F.map ((hp.ι S).map φ) := by
--     rw [←comp_obj, congr_obj (hF.comp_eq S), comp_obj]

-- TODO: this one is probably not needed
lemma Morphism.IsHomLift_map  {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (F : Morphism p q)
    {a b : 𝒳} (φ : a ⟶ b) : IsHomLift q (p.map φ) (F.map φ) where
  ObjLiftDomain := Morphism.obj_proj F a
  ObjLiftCodomain := Morphism.obj_proj F b
  HomLift := ⟨by simp [congr_hom F.w.symm]⟩

lemma Morphism.pres_IsHomLift  {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (F : Morphism p q)
    {R S : 𝒮} {a b : 𝒳} {φ : a ⟶ b} {f : R ⟶ S} (hφ : IsHomLift p f φ) : IsHomLift q f (F.map φ) where
  ObjLiftDomain := Eq.trans (Morphism.obj_proj F a) hφ.ObjLiftDomain
  ObjLiftCodomain := Eq.trans (Morphism.obj_proj F b) hφ.ObjLiftCodomain
  HomLift := ⟨by
    rw [←Functor.comp_map, congr_hom F.w]
    simp [hφ.3.1] ⟩

lemma Morphism.HomLift_ofImage  {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (F : Morphism p q) {S R : 𝒮} {a b : 𝒳}
    {φ : a ⟶ b} {f : R ⟶ S} (hφ : IsHomLift q f (F.map φ)) : IsHomLift p f φ where
  ObjLiftDomain := F.obj_proj a ▸ hφ.ObjLiftDomain
  ObjLiftCodomain := F.obj_proj b ▸ hφ.ObjLiftCodomain
  HomLift := ⟨by
    rw [congr_hom F.w.symm]
    simp only [Functor.comp_map, assoc, eqToHom_trans, hφ.HomLift.1, eqToHom_trans_assoc]⟩

@[default_instance]
instance Morphism.IsFiber_canonical {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (F : Morphism p q) :
    IsFiberMorphism F where
  fiber_functor := fun S => {
    obj := fun a => ⟨F.obj a.1, by rw [F.obj_proj, a.2]⟩
    map := @fun a b φ => ⟨F.map φ.val, Morphism.pres_IsHomLift F φ.2⟩
    map_id := by
      intro a
      -- TODO THIS SHOULD ALL BE SIMP SOMEHOW..
      simp [FiberCategory_id_coe p S a]
      rw [←Subtype.val_inj, FiberCategory_id_coe q S _]
    map_comp := by
      intro x y z φ ψ
      -- THIS SHOULD ALSO ALL BE SIMP SOMEHOW...
      simp [FiberCategory_comp_coe p S φ ψ]
      rw [←Subtype.val_inj, FiberCategory_comp_coe q S _ _]
  }
  comp_eq := by aesop_cat

/-- If a morphism F is faithFul, then it is also faithful fiberwise -/
lemma FiberwiseFaithfulofFaithful  {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [hp : HasFibers p] [hq : HasFibers q]
    (F : Morphism p q) [hF : IsFiberMorphism F] [Faithful F.toFunctor] : ∀ (S : 𝒮),
    Faithful (hF.fiber_functor S) := by
    intro S
    haveI h : Faithful ((hF.fiber_functor S) ⋙ (hq.ι S)) := (hF.comp_eq S).symm ▸ Faithful.comp (hp.ι S) F.toFunctor
    apply Faithful.of_comp _ (hq.ι S)

/-- A FiberMorphism F is faithful if it is so pointwise. For proof see [Olsson] -/
lemma FaithfulofFiberwiseFaithful {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [IsFibered p] [hp : HasFibers p]
    [IsFibered q] [hq : HasFibers q] {F : Morphism p q} [hF : IsFiberedMorphism F]
    (hF₁ : ∀ (S : 𝒮), Faithful (hF.fiber_functor S)) : Faithful F.toFunctor where
  map_injective := by
    intro a b φ φ' heq
    /- We start by reducing to a setting when the domains lie in some fiber of the HasFibers.
    We do this by finding some Φ : a' ≅ a by essential surjectivity of the fiber structures,
    and then defining φ₁ := Φ.hom ≫ φ and φ₁' := Φ.hom ≫ φ'. -/
    rcases HasFibersEssSurj' (rfl (a := p.obj a)) with ⟨a', Φ, _⟩
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
    let h : p.obj a ⟶ p.obj b := eqToHom ((HasFibersObjLift a').symm) ≫ p.map φ₁
    -- Let ψ : c ⟶ b be a pullback over h such that c : Fib (p.obj a)
    rcases HasFibersPullback' rfl h with ⟨c, ψ, hψ⟩
    -- Both φ₁ and φ₁' are lifts of h
    have hφ₁ : IsHomLift p h φ₁ := (IsHomLift_eqToHom_comp' _).2 (IsHomLift_self p φ₁)
    have hφ₁' : IsHomLift p h φ₁' :=  by
      rw [IsHomLift_eqToHom_comp', congr_hom F.w.symm, Functor.comp_map]
      rw [heq₁, ←Functor.comp_map, ←congr_hom F.w.symm]
      apply IsHomLift_self p φ₁'
    -- Let τ, τ' be the induced maps from a' to c given by φ and φ'
    rcases HasFibersFactorization hφ₁ hψ with ⟨τ, hτ⟩
    rcases HasFibersFactorization hφ₁' hψ with ⟨τ', hτ'⟩
    -- Thus, it suffices to show that τ = τ'
    suffices τ = τ' by rw [←hτ, ←hτ', this]
    have hψ' : IsPullback q h (F.map ψ) := hF.preservesPullbacks hψ
    -- F(τ) and F(τ') both solve the same pullback problem in 𝒴
    have hτ₁ : F.map ((hp.ι (p.obj a)).map τ) ≫ F.map ψ = F.map φ₁ := by rw [←Functor.map_comp, hτ]
    have hτ'₁ : F.map ((hp.ι (p.obj a)).map τ') ≫ F.map ψ = F.map φ₁ := by
      rw [←Functor.map_comp, hτ']
      apply heq₁.symm
    -- Hence we get that F(τ) = F(τ'), so we can conclude by fiberwise injectivity
    have hτ₂ := IsPullbackInducedMap_unique hψ' ((id_comp h).symm)
      (Morphism.pres_IsHomLift F hφ₁) (Morphism.pres_IsHomLift F (HasFibersHomLift τ)) hτ₁
    have hτ'₂ := IsPullbackInducedMap_unique hψ' ((id_comp h).symm)
      (Morphism.pres_IsHomLift F hφ₁) (Morphism.pres_IsHomLift F (HasFibersHomLift τ')) hτ'₁
    have heqττ' : F.map ((hp.ι (p.obj a)).map τ) = F.map ((hp.ι (p.obj a)).map τ') := by rw [hτ₂, hτ'₂]
    have heqττ'₁ : (hF.fiber_functor _).map τ = (hF.fiber_functor _).map τ' := by
      apply Functor.map_injective (hq.ι (p.obj a))
      simp_rw [←Functor.comp_map, congr_hom (hF.comp_eq (p.obj a)), Functor.comp_map]
      rw [heqττ']
    apply Functor.map_injective (hF.fiber_functor (p.obj a)) heqττ'₁

lemma PreimageIsHomLift {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (F : Morphism p q) [hF₁ : Full F.toFunctor]
    {a b : 𝒳} {φ : F.obj a ⟶ F.obj b} {R S : 𝒮} {f : R ⟶ S} (hφ : IsHomLift q f φ) :
    IsHomLift p f (hF₁.preimage φ) := (hF₁.witness φ ▸ Morphism.HomLift_ofImage F) hφ

/- We now show that a morphism F is full if and only if its full fiberwise -/
lemma FiberwiseFullofFull  {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [hp : HasFibers p] [hq : HasFibers q]
    (F : Morphism p q) [hF : IsFiberMorphism F] [hF₁ : Full F.toFunctor] : ∀ (S : 𝒮),
    Full (hF.fiber_functor S) := by
  intro S
  apply fullOfExists
  intro a b φ

  let φ₁ :=  eqToHom (congr_obj (hF.comp_eq S) a).symm ≫ ((hq.ι S).map φ)
    ≫ eqToHom (congr_obj (hF.comp_eq S) b)

  have hφ₁ : IsHomLift p (𝟙 S) (hF₁.preimage φ₁) := by
    apply PreimageIsHomLift
    simp [φ₁, HasFibersHomLift φ]

  use Classical.choose (HasFibersFull hφ₁)
  apply Functor.map_injective (hq.ι S)
  -- Maybe its worth making this a standalone lemma
  rw [←Functor.comp_map, congr_hom (hF.comp_eq S), Functor.comp_map]
  simp [Classical.choose_spec (HasFibersFull hφ₁), φ₁]

lemma FullofFullFiberwise  {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [IsFibered p] [hp : HasFibers p]  [IsFibered q] [hq : HasFibers q]
    {F : Morphism p q} [hF : IsFiberedMorphism F] (hF₁ : ∀ (S : 𝒮), Full (hF.fiber_functor S)) :
    Full F.toFunctor := by
  apply fullOfExists
  intro a b φ

  let R := p.obj a
  let S := p.obj b

  -- Reduce to checking when domain is in a fiber
  let a' := Classical.choose (HasFibersEssSurj' (rfl (a:=R)))
  let Φ := Classical.choose (Classical.choose_spec (HasFibersEssSurj' (rfl (a := R))))
  let hΦ := Classical.choose_spec (Classical.choose_spec (HasFibersEssSurj' (rfl (a := R))))

  -- Now consider φ₁ : F.obj a' ⟶ F.obj b
  have ha' : (hq.ι R).obj ((hF.fiber_functor R).obj a') = F.obj ((hp.ι R).obj a') := by
    rw [←comp_obj, ←comp_obj, hF.comp_eq] --congr_obj comp_eq
  let φ₁ : (hq.ι R).obj ((hF.fiber_functor R).obj a') ⟶ F.obj b :=
    eqToHom ha' ≫ (F.mapIso Φ).hom ≫ φ

  let h : R ⟶ S := eqToHom (Morphism.obj_proj F a).symm ≫ q.map φ ≫ eqToHom (Morphism.obj_proj F b)

  -- Let ψ : c ⟶ b be a pullback over h such that c : Fib R
  let c := Classical.choose (HasFibersPullback' rfl h)
  let ψ := Classical.choose (Classical.choose_spec (HasFibersPullback' rfl h))
  let hψ := Classical.choose_spec (Classical.choose_spec (HasFibersPullback' rfl h))

  have hφ₁ : IsHomLift q h φ₁ := by
    simp [φ₁, h]
    apply IsHomLift_of_IsHomLiftId_comp (IsHomLift_self q φ) (Morphism.pres_IsHomLift F hΦ)

  -- The following could be some hF.preservesPullbacks (wrt HasFibers) API
  have hc : (hq.ι R).obj ((hF.fiber_functor R).obj c) = F.obj ((hp.ι R).obj c) := by
    rw [←comp_obj, ←comp_obj, hF.comp_eq] --
  let ψ' := eqToHom hc ≫ F.map ψ
  have hψ' : IsPullback q h ψ' := IsPullback_eqToHom_comp (hF.preservesPullbacks hψ) _

  -- Let τ be the induced map from a' to c given by φ₁
  let τ := Classical.choose (HasFibersFactorization hφ₁ hψ')
  let π := (hF₁ R).preimage τ

  use Φ.inv ≫ (hp.ι R).map π ≫ ψ

  -- TODO GOLF THIS
  simp only [map_comp]
  rw [←Functor.comp_map, congr_hom (hF.comp_eq (p.obj a)).symm]
  rw [Functor.comp_map, (hF₁ (p.obj a)).witness]
  rw [Category.assoc, Category.assoc]
  rw [Classical.choose_spec (HasFibersFactorization hφ₁ hψ')]
  simp [φ₁]
  rw [←Category.assoc, ←Functor.mapIso_inv, ←Functor.mapIso_hom]
  rw [Iso.inv_hom_id, id_comp]

/-
Copyright (c) 2023 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/

import LS.FiberStructures

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃} [Category 𝒳] [Category 𝒮] [Category 𝒴]

namespace Fibered

/-
TODO:
Introduce Fibered.Morphism (or alt. notation) as in TwoMorphism and state lemmas in this generality
THEN make FiberFunctor/FiberedFunctor structures extending this -/

/-- A notion of functor between FiberStructs. It is given by a functor F : 𝒳 ⥤ 𝒴 such that F ⋙ q = p,
  and a collection of functors fiber_functor S between the fibers of p and q over S in 𝒮 such that
  .... -/
structure FiberFunctor (F : 𝒳 ⥤ 𝒴) (p : 𝒳 ⥤ 𝒮) (q : 𝒴 ⥤ 𝒮) [hp : FiberStruct p] [hq : FiberStruct q] where
  (base_preserving : F ⋙ q = p)
  (fiber_functor (S : 𝒮) : hp.Fib S ⥤ hq.Fib S)
  (comp_eq : ∀ (S : 𝒮), (fiber_functor S) ⋙ (hq.ι S) = (hp.ι S) ⋙ F)

/-- A notion of functor between FiberedStructs. It is furthermore required to preserve pullbacks  -/
structure FiberedFunctor (F : 𝒳 ⥤ 𝒴) (p : 𝒳 ⥤ 𝒮) (q : 𝒴 ⥤ 𝒮) [hp : FiberedStruct p] [hq : FiberedStruct q]
  extends FiberFunctor F p q where
  (preservesPullbacks {R S : 𝒮} {f : R ⟶ S} {φ : a ⟶ b} (_ : IsPullback p f φ) : IsPullback q f (F.map φ))

-- HERE NEED TO DEFINE THE "STANDARD ONE"

/-
def IsFiberedFunctorOnFiber (p : 𝒳 ⥤ 𝒮) (q : 𝒴 ⥤ 𝒮) (F : 𝒳 ⥤ 𝒴) [IsFibered p]
  [IsFibered q] [hF : IsFiberedFunctor p q F] (S : 𝒮) : Fiber p S ⥤ Fiber q S where
    -- THIS SHOULD HAVE BEEN PUT IN AN API
    obj := fun ⟨a, ha⟩ => ⟨F.obj a, show q.obj (F.obj a) = S by rwa [←comp_obj, hF.1]⟩
    map := by
      intro a b φ
      refine ⟨F.map φ.val, ?_⟩
      have h₁ := (IsFiberedFunctorMap p q F φ.1).1
      rw [comp_eqToHom_iff] at h₁
      rw [h₁]
      have h₂ := φ.2
      rw [comp_eqToHom_iff] at h₂
      rw [h₂]
      simp only [eqToHom_trans]
    map_id :=
      by
        intro x
        apply Subtype.val_inj.1
        simp only [Eq.ndrec, id_eq, eq_mpr_eq_cast, cast_eq, eq_mp_eq_cast]
        sorry
        --have : (𝟙 x).1 = 𝟙 x.1 := rfl
    map_comp :=
      by
        intro x y z f g
        apply Subtype.val_inj.1
        simp
        sorry

-/

@[simp]
lemma FiberFunctorObj {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [hp : FiberStruct p]
  [hq : FiberStruct q] (hF : FiberFunctor F p q) (a : 𝒳) : q.obj (F.obj a) = p.obj a := by
  rw [←comp_obj, hF.base_preserving]

@[simp]
lemma FiberFunctorObjFiber {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [hp : FiberStruct p]
  [hq : FiberStruct q] {hF : FiberFunctor F p q} {S : 𝒮} (a : hp.Fib S) :
  q.obj (F.obj ((hp.ι S).obj a)) = S := by
  rw [FiberFunctorObj hF ((hp.ι S).obj a), FiberStructObjLift]

/-- TODO -/
lemma FiberFunctorHomLift {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [hp : FiberStruct p]
  [hq : FiberStruct q] (hF : FiberFunctor F p q) {a b : 𝒳} (φ : a ⟶ b) :
  IsHomLift q (p.map φ) (F.map φ) where
    ObjLiftDomain := FiberFunctorObj hF a
    ObjLiftCodomain := FiberFunctorObj hF b
    HomLift := ⟨by
      have h₁ := hF.base_preserving
      subst h₁ -- TODO WHY DO I NEED THIS?? rw and simp_only fails...
      simp only [comp_obj, eqToHom_refl, comp_id, Functor.comp_map, id_comp]⟩

lemma FiberFunctorPresHomLift {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [hp : FiberStruct p]
  [hq : FiberStruct q] (hF : FiberFunctor F p q) {R S : 𝒮} {a b : 𝒳} {φ : a ⟶ b}
  {f : R ⟶ S} (hφ : IsHomLift p f φ) : IsHomLift q f (F.map φ) where
    ObjLiftDomain := Eq.trans (FiberFunctorObj hF a) hφ.ObjLiftDomain
    ObjLiftCodomain := Eq.trans (FiberFunctorObj hF b) hφ.ObjLiftCodomain
    HomLift := ⟨by
      -- TODO MAKE PROOF CLEANER
      have h₁ := hφ.3.1
      have h₂ := hF.base_preserving
      subst h₂
      simpa using h₁ ⟩

lemma FiberFunctorIsHomLiftOfImage {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [hp : FiberStruct p]
  [hq : FiberStruct q] (hF : FiberFunctor F p q) {S R : 𝒮} {a b : 𝒳} {φ : a ⟶ b}
  {f : R ⟶ S} (hφ : IsHomLift q f (F.map φ)) : IsHomLift p f φ where
    -- TODO API?
    ObjLiftDomain := by
      rw [←hF.base_preserving, comp_obj]
      exact hφ.ObjLiftDomain
    ObjLiftCodomain := by
      rw [←hF.base_preserving, comp_obj]
      exact hφ.ObjLiftCodomain
    HomLift := by
      constructor
      rw [Functor.congr_hom hF.base_preserving.symm]
      simp only [Functor.comp_map, assoc, eqToHom_trans, hφ.HomLift.1, eqToHom_trans_assoc]

-- NEED MORE COMMSQUARES API....
-- ALSO NEED MORE API FOR PULLING BACK TO FIBERS

/-- If a FiberFunctor F is faithful, then it is also faithful pointwise -/
lemma FiberStructFaithfulofFaithful {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [hp : FiberStruct p]
  [hq : FiberStruct q] (hF : FiberFunctor F p q) [Faithful F] : ∀ (S : 𝒮),
  Faithful (hF.fiber_functor S) := by
  intro S
  haveI h : Faithful ((hF.fiber_functor S) ⋙ (hq.ι S)) := (hF.comp_eq S).symm ▸ Faithful.comp (hp.ι S) F
  apply Faithful.of_comp _ (hq.ι S)

/-- A FiberFunctor F is faithful if it is so pointwise -/
lemma FaithfulofFaithfulFiberStruct {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {hp : FiberedStruct p}
  {hq : FiberedStruct q} {hF : FiberedFunctor F p q} (hF₁ : ∀ (S : 𝒮), Faithful (hF.fiber_functor S)) :
  Faithful F := by
  constructor
  intro a b φ φ' heq

  -- Reduce to checking when domain is in a fiber
  rcases FiberStructEssSurj' (rfl (a := p.obj a)) with ⟨a', Φ, hΦ⟩
  let φ₁ := Φ.hom ≫ φ
  let φ₁' := Φ.hom ≫ φ'
  suffices φ₁ = φ₁' by rwa [←CategoryTheory.Iso.cancel_iso_hom_left Φ]
  have heq₁ : F.map φ₁ = F.map φ₁' := by
    simp only [F.map_comp]
    apply (CategoryTheory.Iso.cancel_iso_hom_left (F.mapIso Φ) _ _).2 heq

  let h : p.obj a ⟶ p.obj b := eqToHom ((FiberStructObjLift a').symm) ≫ p.map φ₁

  -- Let ψ : c ⟶ b be a pullback over h such that c : Fib (p.obj a)
  rcases FiberStructPullback' hp rfl h with ⟨c, ψ, hψ⟩

  have hφ₁ : IsHomLift p h φ₁ := IsHomLift_eqToHom_comp' (IsHomLift_self p φ₁) _

  have h₁ : h = eqToHom ((FiberStructObjLift a').symm) ≫ p.map φ₁' := by
    rw [Functor.congr_hom hF.base_preserving.symm]
    rw [Functor.comp_map, ←heq₁, ←Functor.comp_map]
    rw [←Functor.congr_hom hF.base_preserving.symm]

  have hφ₁' : IsHomLift p h φ₁' := h₁ ▸ IsHomLift_eqToHom_comp' (IsHomLift_self p φ₁') _

  -- Let τ, τ' be the induced maps from b to c given by φ and φ'
  rcases FiberStructFactorization hφ₁ hψ with ⟨τ, hτ⟩
  rcases FiberStructFactorization hφ₁' hψ with ⟨τ', hτ'⟩

  -- It suffices to show that τ = τ'
  suffices τ = τ' by rw [←hτ, ←hτ', this]

  -- 1. Show that F.map ψ is a pullback
  have hψ' : IsPullback q h (F.map ψ) := hF.preservesPullbacks hψ

  -- τ and τ' both solve the same pullback problem
  have hτ₁ : F.map ((hp.ι (p.obj a)).map τ) ≫ F.map ψ = F.map φ₁ := by rw [←Functor.map_comp, hτ]
  have hτ'₁ : F.map ((hp.ι (p.obj a)).map τ') ≫ F.map ψ = F.map φ₁ := by
    rw [←Functor.map_comp, hτ']
    apply heq₁.symm

  have hτ_homlift := FiberFunctorPresHomLift hF.1 (FiberStructHomLift τ)
  have hτ'_homlift := FiberFunctorPresHomLift hF.1 (FiberStructHomLift τ')

  have hτ₂ := IsPullbackInducedMap_unique hψ' (show h = 𝟙 (p.obj a) ≫ h by simp)
    (FiberFunctorPresHomLift hF.1 hφ₁) hτ_homlift hτ₁

  have hτ'₂ := IsPullbackInducedMap_unique hψ' (show h = 𝟙 (p.obj a) ≫ h by simp)
    (FiberFunctorPresHomLift hF.1 hφ₁) hτ'_homlift hτ'₁

  -- Hence F.map τ = F.map τ'
  have heqττ' : F.map ((hp.ι (p.obj a)).map τ) = F.map ((hp.ι (p.obj a)).map τ') := by rw [hτ₂, hτ'₂]

  have heqττ'₁ : (hF.fiber_functor _).map τ = (hF.fiber_functor _).map τ' := by
    apply Functor.map_injective (hq.ι (p.obj a))
    simp_rw [←Functor.comp_map, Functor.congr_hom (hF.comp_eq (p.obj a)), Functor.comp_map]
    rw [heqττ']

  apply Functor.map_injective (hF.fiber_functor (p.obj a)) heqττ'₁

lemma PreimageIsHomLift {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [hp : FiberStruct p]
  [hq : FiberStruct q] (hF : FiberFunctor F p q) [hF₁ : Full F] {a b : 𝒳}
  (φ : F.obj a ⟶ F.obj b) : IsHomLift p (q.map φ) (hF₁.preimage φ) := by sorry

lemma FiberFunctorsFullofFull {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [hp : FiberStruct p]
  [hq : FiberStruct q] (hF : FiberFunctor F p q) [hF₁ : Full F] : ∀ (S : 𝒮),
  Full (hF.fiber_functor S) := fun S => {

    preimage := by
      intro a b φ

      -- TYPE THEORY HELL :D (rewrtite to use one equality on each side...)
      let φ₁ := eqToHom (comp_obj _ _ a) ≫ ((hq.ι S).map φ) ≫ eqToHom (comp_obj _ _ b).symm

      let φ₂  := eqToHom (congr_obj (hF.comp_eq S) a).symm ≫ φ₁ ≫ eqToHom (congr_obj (hF.comp_eq S) b)

      let φ₃ := eqToHom (comp_obj _ _ a) ≫ φ₂ ≫ eqToHom (comp_obj _ _ b).symm

      have hφ₃ : IsHomLift p (𝟙 S) (hF₁.preimage φ₃) := by
        apply FiberFunctorIsHomLiftOfImage hF
        rw [hF₁.witness φ₃]
        simp only [φ₃, φ₂, φ₁, FiberStructHomLift φ, eqToHom_refl, comp_id,
          id_comp, IsHomLift_eqToHom_comp, IsHomLift_comp_eqToHom]

      use Classical.choose (FiberStructFull hφ₃)

    witness := by
      intro a b φ
      apply Functor.map_injective (hq.ι S)
      simp only [comp_obj, eqToHom_refl, comp_id, id_comp, eq_mp_eq_cast]
      rw [←Functor.comp_map, Functor.congr_hom (hF.comp_eq S), Functor.comp_map]
      rw [Classical.choose_spec (FiberStructFull _)]
      simp
      -- TODO: THE FOLLOWING WAS ALREADY PROVED ABOVE CAN I RECYCLE THE PROOF?
      apply FiberFunctorIsHomLiftOfImage hF
      rw [hF₁.witness _]
      simp only [FiberStructHomLift φ, eqToHom_refl, comp_id,
          id_comp, IsHomLift_eqToHom_comp, IsHomLift_comp_eqToHom]
      }

lemma FullofFullFiberStruct {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {hp : FiberedStruct p}
  {hq : FiberedStruct q} {hF : FiberedFunctor F p q} (hF₁ : ∀ (S : 𝒮), Full (hF.fiber_functor S)) :
  Full F where
    preimage := by
      intro a b φ

      let R := p.obj a
      let S := p.obj b

      -- Reduce to checking when domain is in a fiber
      -- TODO TRICKY AS THIS IS BY NO MEANS UNIQUE (actually might not matter?)
      let a' := Classical.choose (FiberStructEssSurj' (rfl (a:=R)))
      let Φ := Classical.choose (Classical.choose_spec (FiberStructEssSurj' (rfl (a := R))))
      let hΦ := Classical.choose_spec (Classical.choose_spec (FiberStructEssSurj' (rfl (a := R))))

      let h : R ⟶ S := eqToHom (FiberFunctorObj hF.1 a).symm ≫ q.map φ ≫ eqToHom (FiberFunctorObj hF.1 b)

      -- Let ψ : c ⟶ b be a pullback over h such that c : Fib R
      let c := Classical.choose (FiberStructPullback' hp rfl h)
      let ψ := Classical.choose (Classical.choose_spec (FiberStructPullback' hp rfl h))
      let hψ := Classical.choose_spec (Classical.choose_spec (FiberStructPullback' hp rfl h))

      -- Now consider φ₁ : F.obj a' ⟶ F.obj b
      have ha' : (hq.ι R).obj ((hF.fiber_functor R).obj a') = F.obj ((hp.ι R).obj a') := by
        rw [←comp_obj, ←comp_obj, hF.comp_eq]
      let φ₁ : (hq.ι R).obj ((hF.fiber_functor R).obj a') ⟶ F.obj b :=
        eqToHom ha' ≫ (F.mapIso Φ).hom ≫ φ

      have hφ₁ : IsHomLift q h φ₁ := by
        have H := IsHomLift_self q φ₁

        simp only [φ₁, F.mapIso_hom]
        apply IsHomLift_eqToHom_comp' _
        apply IsHomLift_comp_eqToHom' _
        apply IsHomLift_comp_eqToHom _

        have h₁ := FiberFunctorPresHomLift hF.1 hΦ
        -- API FOR THIS? Comp w/ homlift id is homlift
        sorry

      -- TODO: define "FromFiberObj" and "FromFiberHom" and use them to formulate FiberStructFactorization
      have hc : (hq.ι R).obj ((hF.fiber_functor R).obj c) = F.obj ((hp.ι R).obj c) := by
        rw [←comp_obj, ←comp_obj, hF.comp_eq]
      let ψ' := eqToHom hc ≫ F.map ψ

      -- NEED: IsPullback comp eqToHom...!
      have hψ' : IsPullback q h ψ' := by
        have := hF.preservesPullbacks hψ
        sorry -- hF.preservesPullbacks hψ + compiso pullback

      -- Let τ be the induced map from a' to c given by φ₁
      let τ := Classical.choose (FiberStructFactorization hφ₁ hψ')
      have hτ := Classical.choose_spec (FiberStructFactorization hφ₁ hψ')

      let π := (hF₁ R).preimage τ

      exact Φ.inv ≫ (hp.ι R).map π ≫ ψ


    witness := by
      intro a b φ
      simp only [map_comp] -- hF.comp_eq, (hF₁ (p.obj a)).witness]
      rw [←Functor.comp_map, Functor.congr_hom (hF.comp_eq (p.obj a)).symm]
      rw [Functor.comp_map, (hF₁ (p.obj a)).witness]
      -- NEED API FOR THIS....

      rw [Category.assoc, Category.assoc]
      -- TODO: need way to get rid of extra goals here (problably via better API)
      -- Maybe OK once sorries above have been resolved?
      rw [Classical.choose_spec (FiberStructFactorization _ _)]
      simp
      rw [←Category.assoc, ←Functor.mapIso_inv, ←Functor.mapIso_hom]
      rw [Iso.inv_hom_id, id_comp]
      all_goals sorry


/-
TODO:
2. Full if fibers are full
3. Equivalence iff equivalence on fibers
  -- NOTE THIS REQUIRES NEW DEFINITION OF EQUIVALENCE!!! (inverse needs to also preserve fibers. Immediate?)
-/

-- class IsFiberedNatTrans (p : 𝒳 ⥤ 𝒮) (q : 𝒴 ⥤ 𝒮) [hp : IsFibered p] [hq : IsFibered q] {F : 𝒳 ⥤ 𝒴}
--   {G : 𝒳 ⥤ 𝒴} [IsFiberedFunctor p q F] [IsFiberedFunctor p q G] (α : F ⟶ G) : Prop where
--   (pointwiseInFiber : ∀ (a : 𝒳), q.map (α.app a) = eqToHom (IsFiberedFunctorPresFiberObj p q F G a))

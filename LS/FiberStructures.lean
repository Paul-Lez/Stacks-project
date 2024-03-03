/-
Copyright (c) 2023 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/

import LS.FiberedCategories'

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category 𝒳] [Category 𝒮]

namespace Fibered


-- MISSING MATHLIB LEMMA

/-- If the two inner squares below commute, then so does the outer square.
```
  W ---f---> X ---f'--> X'
  |          |          |
  g          h          h'
  |          |          |
  v          v          v
  Y ---i---> Z ---i'--> Z'

```
-/
lemma CommSqComp {W X X' Y Z Z' : 𝒮} {f : W ⟶ X} {f' : X ⟶ X'} {g : W ⟶ Y} {h : X ⟶ Z} {h' : X' ⟶ Z'}
  {i : Y ⟶ Z} {i' : Z ⟶ Z'} (hsq₁ : CommSq f g h i) (hsq₂ : CommSq f' h h' i') : CommSq (f ≫ f') g h' (i ≫ i') :=
  ⟨by rw [←assoc, assoc, ←hsq₁.w, hsq₂.w, assoc]⟩

-- First we define the fibers of a given fibered category
-- def Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮) := (a : 𝒳) × (p.obj a ≅ S)
def Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮) := {a : 𝒳 // p.obj a = S}

-- a lies in the fiber of p.obj a
def FiberSelf {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fiber p S := ⟨a, ha⟩

-- TODO DO I EVEN NEED?
@[simp]
lemma FiberSelfCoe (p : 𝒳 ⥤ 𝒮) (a : 𝒳) : (FiberSelf (p:=p) (a:=a) rfl).1 = a := rfl

instance FiberCategory (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : Category (Fiber p S) where
  -- TODO: Is this the best implementation? IsHomLift allows us to use the api,
  -- but then we need to "reprove" p.obj a = S and p.obj b = S...
  -- Maybe just CommSq directly?
  Hom a b := {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}
  id a := ⟨𝟙 a.1, IsHomLift_id a.2⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val, by apply (comp_id (𝟙 S)) ▸ IsHomLift_comp φ.2 ψ.2⟩

def FiberInclusion (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : (Fiber p S) ⥤ 𝒳 where
  obj a := a.1
  map φ := φ.1

instance FiberInclusionFaithful (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : Faithful (FiberInclusion p S) where
  map_injective := Subtype.val_inj.1

-- Next define induced map from "arbitrary fiber" to "canonical fiber"

def FiberInducedFunctor {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type _} [Category C]
  {F : C ⥤ 𝒳} (hF : F ⋙ p = (const C).obj S) : C ⥤ Fiber p S where
    obj := fun x => ⟨F.obj x, by simp only [←comp_obj, hF, const_obj_obj]⟩
    map := fun φ => ⟨F.map φ, {
      ObjLiftDomain := by simp only [←comp_obj, hF, const_obj_obj]
      ObjLiftCodomain := by simp only [←comp_obj, hF, const_obj_obj]
      HomLift := ⟨by simpa using (eqToIso hF).hom.naturality φ⟩
    }⟩

def FiberInducedFunctorNat {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type _} [Category C] {F : C ⥤ 𝒳}
  (hF : F ⋙ p = (const C).obj S) : F ≅ (FiberInducedFunctor hF) ⋙ (FiberInclusion p S) where
    hom := { app := fun a => 𝟙 (F.obj a) }
    inv := { app := fun a => 𝟙 ((FiberInducedFunctor hF ⋙ FiberInclusion p S).obj a) }

-- TODO UPDATE MATHLIB + USE EXT OF ISO

lemma FiberInducedFunctorComp {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type _} [Category C] {F : C ⥤ 𝒳}
  (hF : F ⋙ p = (const C).obj S) : F = (FiberInducedFunctor hF) ⋙ (FiberInclusion p S) := sorry

-- We define an extrinsic notion of fibers, which we call FiberStruct
-- Fibered family. TODO: make into a class? Then could infer "canonical fibers" if none are given...
structure FiberStruct (p : 𝒳 ⥤ 𝒮) where
  Fib (S : 𝒮) : Type _
  [isCategory (S : 𝒮) : Category (Fib S)]
  (ι (S : 𝒮) : (Fib S) ⥤ 𝒳)
  (comp_const (S : 𝒮) : (ι S) ⋙ p = (const (Fib S)).obj S)
  -- NOTE THESE TWO DONT SAY ANYTHING ABOUT THE MAPS!
  --(comp_const (S : 𝒮) : ∀ (a : Fib S), (ι S ⋙ p).obj a = S)
  --(comp_const (S : 𝒮) : ∀ (a : Fib S), p.obj ((ι S).obj a) = S)
  [equiv (S : 𝒮) : IsEquivalence (FiberInducedFunctor (comp_const S))]

instance {p : 𝒳 ⥤ 𝒮} (hp : FiberStruct p) {S : 𝒮} : Category (hp.Fib S) := hp.isCategory S

instance {p : 𝒳 ⥤ 𝒮} (hp : FiberStruct p) {S : 𝒮} : IsEquivalence (FiberInducedFunctor (hp.comp_const S)) := hp.equiv S

instance {p : 𝒳 ⥤ 𝒮} (hp : FiberStruct p) {S : 𝒮} : EssSurj (FiberInducedFunctor (hp.comp_const S)) :=
  Equivalence.essSurj_of_equivalence (FiberInducedFunctor (hp.comp_const S))

--instance {p : 𝒳 ⥤ 𝒮} (hp : FiberStruct p) {S : 𝒮} : Full (FiberInducedFunctor (hp.comp_const S)) := inferInstance

instance {p : 𝒳 ⥤ 𝒮} (hp : FiberStruct p) {S : 𝒮} : Faithful (hp.ι S) :=
  Faithful.of_iso (FiberInducedFunctorNat (hp.comp_const S)).symm

lemma FiberStructObjLift {p : 𝒳 ⥤ 𝒮} {hp : FiberStruct p} {S : 𝒮} (a : hp.Fib S) : p.obj ((hp.ι S).obj a) = S :=
  by simp only [←comp_obj, hp.comp_const, const_obj_obj]

lemma FiberStructHomLift {p : 𝒳 ⥤ 𝒮} {hp : FiberStruct p} {S : 𝒮} {a b : hp.Fib S}
  (φ : a ⟶ b) : IsHomLift p (𝟙 S) ((hp.ι S).map φ) where
  ObjLiftDomain := FiberStructObjLift a
  ObjLiftCodomain := FiberStructObjLift b
  HomLift := ⟨by
    rw [←Functor.comp_map, Functor.congr_hom (hp.comp_const S)] -- Can easily be replaced if we decide to work up to iso
    simp only [comp_obj, const_obj_obj, const_obj_map, id_comp, eqToHom_trans, comp_id]⟩

lemma FiberStructFull {p : 𝒳 ⥤ 𝒮} {hp : FiberStruct p} {S : 𝒮} {a b : hp.Fib S} {φ : (hp.ι S).obj a ⟶ (hp.ι S).obj b}
  (hφ : IsHomLift p (𝟙 S) φ) : ∃ (ψ : a ⟶ b), (hp.ι S).map ψ = φ := by
  -- TODO IMPROVE PROOF... Only 5 last lines should be necessary
  let a' : Fiber p S := ⟨(hp.ι S).obj a, FiberStructObjLift a⟩
  let b' : Fiber p S := ⟨(hp.ι S).obj b, FiberStructObjLift b⟩
  let φ' : a' ⟶ b' := ⟨φ, hφ⟩ -- TODO TURN INTO API ABOVE

  let c : Fiber p S := (FiberInducedFunctor (hp.comp_const S)).obj a
  let d : Fiber p S := (FiberInducedFunctor (hp.comp_const S)).obj b
  let ψ : c ⟶ d := φ'

  use (Full.preimage ψ)

  rw [←NatIso.naturality_2 (FiberInducedFunctorNat (hp.comp_const S))]
  unfold FiberInducedFunctorNat
  simp only [comp_obj, Functor.comp_map, Full.witness, comp_id, id_comp]
  rfl

lemma FiberStructEssSurj {p : 𝒳 ⥤ 𝒮} (hp : FiberStruct p) {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
  ∃ (b : hp.Fib S) (φ : (hp.ι S).obj b ⟶ a), IsIso φ ∧ IsHomLift p (𝟙 S) φ := by
  -- This will be easy to inline
  use Functor.objPreimage (FiberInducedFunctor (hp.comp_const S)) (FiberSelf ha)
  let Φ := Functor.objObjPreimageIso (FiberInducedFunctor (hp.comp_const S)) (FiberSelf ha)
  use (FiberInclusion p S).map Φ.hom
  refine ⟨inferInstance, Φ.hom.2⟩

lemma FiberStructEssSurj' {p : 𝒳 ⥤ 𝒮} (hp : FiberStruct p) {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
  ∃ (b : hp.Fib S) (φ : (hp.ι S).obj b ≅ a), IsHomLift p (𝟙 S) φ.hom := by
  -- This will be easy to inline
  use Functor.objPreimage (FiberInducedFunctor (hp.comp_const S)) (FiberSelf ha)
  let Φ := Functor.objObjPreimageIso (FiberInducedFunctor (hp.comp_const S)) (FiberSelf ha)
  refine ⟨(FiberInclusion p S).mapIso Φ, Φ.hom.2⟩

-- MIGHT NOT NEED....
def FiberStructMap {p : 𝒳 ⥤ 𝒮} {hp : FiberStruct p} {R S : 𝒮} {a : hp.Fib S}
  {b : hp.Fib R} (φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a) : R ⟶ S :=
    eqToHom (FiberStructObjLift b).symm ≫ (p.map φ) ≫ eqToHom (FiberStructObjLift a)
--    ((hp.comp_const R).app b).inv ≫ (p.map φ) ≫ ((hp.comp_const S).app a).hom

structure FiberedStruct (p : 𝒳 ⥤ 𝒮) extends FiberStruct p where
  [isFibered : IsFibered p]

-- TODO NEEDED FOR NOW...?
instance {p : 𝒳 ⥤ 𝒮} (hp : FiberedStruct p) {S : 𝒮} : Category (hp.Fib S) := hp.isCategory S
instance {p : 𝒳 ⥤ 𝒮} (hp : FiberedStruct p) {S : 𝒮} : IsEquivalence (FiberInducedFunctor (hp.comp_const S)) := hp.equiv S
instance {p : 𝒳 ⥤ 𝒮} (hp : FiberedStruct p) {S : 𝒮} : Faithful (FiberInducedFunctor (hp.comp_const S)) := inferInstance

lemma FiberStructPullback {p : 𝒳 ⥤ 𝒮} {hp : FiberedStruct p} {R S : 𝒮} (a : hp.Fib S)
  (f : R ⟶ S) : ∃ (b : hp.Fib R) (φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a), IsPullback p f φ := by
    rcases hp.isFibered.has_pullbacks (FiberStructObjLift a) f with ⟨b, φ, hφ⟩
    rcases FiberStructEssSurj hp.1 hφ.ObjLiftDomain with ⟨b', ψ, hψ⟩
    use b', ψ ≫ φ
    rw [←id_comp f]
    exact IsPullback_comp (IsPullbackofIso hψ.2 hψ.1) hφ

lemma FiberStructPullback' {p : 𝒳 ⥤ 𝒮} (hp : FiberedStruct p) {R S : 𝒮} {a : 𝒳}
  (ha : p.obj a = S) (f : R ⟶ S) : ∃ (b : hp.Fib R) (φ : (hp.ι R).obj b ⟶ a),
    IsPullback p f φ := by
  rcases hp.isFibered.has_pullbacks ha f with ⟨b, φ, hφ⟩
  rcases FiberStructEssSurj hp.1 hφ.ObjLiftDomain with ⟨b', ψ, hψ⟩
  use b', ψ ≫ φ
  rw [←id_comp f]
  exact IsPullback_comp (IsPullbackofIso hψ.2 hψ.1) hφ

-- Given a pullback, can choose the induced map to lie in the fiber?
-- TODO UNIQUENESS
lemma FiberStructFactorization {p : 𝒳 ⥤ 𝒮} {hp : FiberedStruct p} {R S : 𝒮}
  {a : hp.Fib S} {b b' : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a}
  (hφ : IsHomLift p f φ) {ψ : (hp.ι R).obj b' ⟶ (hp.ι S).obj a} (hψ : IsPullback p f ψ) :
    ∃ (τ : b ⟶ b'), (hp.ι R).map τ ≫ ψ = φ := by
  -- By fullness, we can pull back τ to the fiber over R
  rcases FiberStructFull (IsPullbackInducedMap_IsHomLift hψ (id_comp f).symm hφ) with ⟨τ, hτ⟩
  use τ
  rw [hτ]
  exact (IsPullbackInducedMap_Diagram hψ (id_comp f).symm hφ)

-- TODO REPLACE ABOVE WITH THIS
lemma FiberStructFactorization' {p : 𝒳 ⥤ 𝒮} {hp : FiberedStruct p} {R S : 𝒮}
  {a : 𝒳} {b b' : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ a}
  (hφ : IsHomLift p f φ) {ψ : (hp.ι R).obj b' ⟶ a} (hψ : IsPullback p f ψ) :
    ∃ (τ : b ⟶ b'), (hp.ι R).map τ ≫ ψ = φ := by
  -- By fullness, we can pull back τ to the fiber over R
  rcases FiberStructFull (IsPullbackInducedMap_IsHomLift hψ (id_comp f).symm hφ) with ⟨τ, hτ⟩
  use τ
  rw [hτ]
  exact (IsPullbackInducedMap_Diagram hψ (id_comp f).symm hφ)


lemma fiber_factorization {p : 𝒳 ⥤ 𝒮} (hp : FiberedStruct p) {R S : 𝒮}
  {a : hp.Fib S} {b : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a}
  (hφ : IsHomLift p f φ) : ∃ (b' : hp.Fib R)
  (τ : b ⟶ b') (ψ : (hp.ι R).obj b' ⟶ (hp.ι S).obj a), IsPullback p f ψ ∧ (((hp.ι R).map τ) ≫ ψ = φ) := by
    rcases (FiberStructPullback a f) with ⟨b', ψ, hψ⟩
    rcases FiberStructFactorization hφ hψ with ⟨τ, hτ⟩
    use b', τ, ψ, hψ

variable {𝒴 : Type u₃} [Category 𝒴]

structure FiberFunctor (F : 𝒳 ⥤ 𝒴) {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (hp : FiberStruct p) (hq : FiberStruct q) where
  -- TODO: miiiight follow from next axiom...
  (base_preserving : F ⋙ q = p)
  (fiber_functor (S : 𝒮) : hp.Fib S ⥤ hq.Fib S)
  (comp_eq : ∀ (S : 𝒮), (fiber_functor S) ⋙ (hq.ι S) = (hp.ι S) ⋙ F)

structure FiberedFunctor (F : 𝒳 ⥤ 𝒴) {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (hp : FiberedStruct p) (hq : FiberedStruct q)
  extends FiberFunctor F hp.toFiberStruct hq.toFiberStruct where
  (preservesPullbacks {R S : 𝒮} {f : R ⟶ S} {φ : a ⟶ b} (_ : IsPullback p f φ) : IsPullback q f (F.map φ))

@[simp]
lemma FiberFunctorObj {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {hp : FiberStruct p}
  {hq : FiberStruct q} (hF : FiberFunctor F hp hq) (a : 𝒳) : q.obj (F.obj a) = p.obj a := by
  rw [←comp_obj, hF.base_preserving]

lemma FiberFunctorHomLift {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {hp : FiberStruct p}
  {hq : FiberStruct q} (hF : FiberFunctor F hp hq) {S : 𝒮} {a b : 𝒳} (φ : a ⟶ b) :
  IsHomLift q (p.map φ) (F.map φ) where
    ObjLiftDomain := FiberFunctorObj hF a
    ObjLiftCodomain := FiberFunctorObj hF b
    HomLift := ⟨by
      have h₁ := hF.base_preserving
      subst h₁ -- TODO WHY DO I NEED THIS?? rw and simp_only fails...
      simp only [comp_obj, eqToHom_refl, comp_id, Functor.comp_map, id_comp]⟩

lemma FiberFunctorPresHomLift {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {hp : FiberStruct p}
  {hq : FiberStruct q} (hF : FiberFunctor F hp hq) {R S : 𝒮} {a b : 𝒳} {φ : a ⟶ b}
  {f : R ⟶ S} (hφ : IsHomLift p f φ) : IsHomLift q f (F.map φ) where
    ObjLiftDomain := Eq.trans (FiberFunctorObj hF a) hφ.ObjLiftDomain
    ObjLiftCodomain := Eq.trans (FiberFunctorObj hF b) hφ.ObjLiftCodomain
    HomLift := ⟨by
      -- TODO MAKE PROOF CLEANER
      have h₁ := hφ.3.1
      have h₂ := hF.base_preserving
      subst h₂
      simpa using h₁ ⟩

lemma FiberFunctorIsHomLiftOfImage {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {hp : FiberStruct p}
  {hq : FiberStruct q} (hF : FiberFunctor F hp hq) {S R : 𝒮} {a b : 𝒳} {φ : a ⟶ b}
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

lemma FiberStructFaithfulofFaithful {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {hp : FiberStruct p}
  {hq : FiberStruct q} (hF : FiberFunctor F hp hq) [Faithful F] : ∀ (S : 𝒮),
  Faithful (hF.fiber_functor S) := by
  intro S
  haveI h : Faithful ((hF.fiber_functor S) ⋙ (hq.ι S)) := (hF.comp_eq S).symm ▸ Faithful.comp (hp.ι S) F
  apply Faithful.of_comp _ (hq.ι S)

lemma FaithfulofFaithfulFiberStruct {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {hp : FiberedStruct p}
  {hq : FiberedStruct q} {hF : FiberedFunctor F hp hq} (hF₁ : ∀ (S : 𝒮), Faithful (hF.fiber_functor S)) :
  Faithful F := by
  constructor
  intro a b φ φ' heq

  -- Reduce to checking when domain is in a fiber
  rcases FiberStructEssSurj' hp.1 (rfl (a := p.obj a)) with ⟨a', Φ, hΦ⟩
  let φ₁ := Φ.hom ≫ φ
  let φ₁' := Φ.hom ≫ φ'
  suffices φ₁ = φ₁' by rwa [←CategoryTheory.Iso.cancel_iso_hom_left Φ]
  have heq₁ : F.map φ₁ = F.map φ₁' := by
    simp only [map_comp]
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
  rcases FiberStructFactorization' hφ₁ hψ with ⟨τ, hτ⟩
  rcases FiberStructFactorization' hφ₁' hψ with ⟨τ', hτ'⟩

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

lemma FiberFunctorsFullofFull {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {hp : FiberStruct p}
  {hq : FiberStruct q} (hF : FiberFunctor F hp hq) [hF₁ : Full F] : ∀ (S : 𝒮),
  Full (hF.fiber_functor S) := fun S => {
    preimage := by
      intro a b φ

      -- TYPE THEORY HELL :D
      let φ₁ := eqToHom (comp_obj _ _ a) ≫ ((hq.ι S).map φ) ≫ eqToHom (comp_obj _ _ b).symm

      let φ₂  := eqToHom (congr_obj (hF.comp_eq S) a).symm ≫ φ₁ ≫ eqToHom (congr_obj (hF.comp_eq S) b)

      let φ₃ := eqToHom (comp_obj _ _ a) ≫ φ₂ ≫ eqToHom (comp_obj _ _ b).symm

      have hφ₃ : IsHomLift p (𝟙 S) (hF₁.preimage φ₃) := by
        apply FiberFunctorIsHomLiftOfImage hF
        rw [hF₁.witness φ₃]
        simp only [FiberStructHomLift φ, eqToHom_refl, comp_id,
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

/-
TODO:
2. Full if fibers are full
3. Equivalence iff equivalence on fibers (easy from fullness + fully faithfulness)
-/


end Fibered

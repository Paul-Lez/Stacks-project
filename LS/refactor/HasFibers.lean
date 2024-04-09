/-
Copyright (c) 2023 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/

import LS.refactor.IsFibered
import Mathlib.CategoryTheory.Functor.Const

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category

variable {𝒮 : Type u₁} [Category 𝒮]

namespace Fibered

/-- Fiber 𝒳 S is the type of elements of 𝒳 mapping to S via 𝒳.p  -/
def Fiber (𝒳 : BasedCategory 𝒮) (S : 𝒮) := {a : 𝒳.1 // 𝒳.p.obj a = S}

/-- We can turn Fiber 𝒳 S into a category by taking the morphisms to be those lying over 𝟙 S -/
@[simps]
instance FiberCategory (𝒳 : BasedCategory 𝒮) (S : 𝒮) : Category (Fiber 𝒳 S) where
  Hom a b := {φ : a.1 ⟶ b.1 // IsHomLift 𝒳 (𝟙 S) φ}
  id a := ⟨𝟙 a.1, IsHomLift_id a.2⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val, by apply (comp_id (𝟙 S)) ▸ IsHomLift_comp φ.2 ψ.2⟩

def Fiber.mk_obj {𝒳 : BasedCategory 𝒮} {S : 𝒮} {a : 𝒳.1} (ha : 𝒳.p.obj a = S) : Fiber 𝒳 S := ⟨a, ha⟩

def Fiber.mk_map {𝒳 : BasedCategory 𝒮} {S : 𝒮} {a b : 𝒳.1} (ha : 𝒳.p.obj a = S) (hb : 𝒳.p.obj b = S)
    (φ : a ⟶ b) (hφ : IsHomLift 𝒳 (𝟙 S) φ := by aesop_cat) : Fiber.mk_obj ha ⟶ Fiber.mk_obj hb :=
  ⟨φ, hφ⟩

@[simp]
lemma Fiber.mk_map_id {𝒳 : BasedCategory 𝒮} {S : 𝒮} {a : 𝒳.1} (ha : 𝒳.p.obj a = S) :
    Fiber.mk_map ha ha (𝟙 a) = 𝟙 (Fiber.mk_obj ha) := rfl

@[simp]
lemma Fiber.mk_obj_coe (𝒳 : BasedCategory 𝒮) (a : 𝒳.1) : (Fiber.mk_obj (a:=a) rfl).1 = a := rfl

/-- The functor including Fiber 𝒳 S into 𝒳 -/
@[simps]
def FiberInclusion (𝒳 : BasedCategory 𝒮) (S : 𝒮) : (Fiber 𝒳 S) ⥤ 𝒳.1 where
  obj a := a.1
  map φ := φ.1

instance FiberInclusionFaithful (𝒳 : BasedCategory 𝒮) (S : 𝒮) : Faithful (FiberInclusion 𝒳 S) where
  map_injective := Subtype.val_inj.1

@[ext]
lemma Fiber.hom_ext {𝒳 : BasedCategory 𝒮} {S : 𝒮} {a b : Fiber 𝒳 S} (φ ψ : a ⟶ b) : φ.1 = ψ.1 → φ = ψ := Subtype.ext

@[simp]
lemma Fiber.val_comp {𝒳 : BasedCategory 𝒮} {S : 𝒮} {a b c : Fiber 𝒳 S} (φ : a ⟶ b)
    (ψ : b ⟶ c) : (φ ≫ ψ).1 = φ.1 ≫ ψ.1 := rfl

lemma Fiber.mk_map_com {𝒳 : BasedCategory 𝒮} {S : 𝒮} {a b c : 𝒳.1} (ha : 𝒳.p.obj a = S) (hb : 𝒳.p.obj b = S)
    (hc : 𝒳.p.obj c = S) (φ : a ⟶ b) (ψ : b ⟶ c) (hφ : IsHomLift 𝒳 (𝟙 S) φ)
    (hψ : IsHomLift 𝒳 (𝟙 S) ψ) : Fiber.mk_map ha hc (φ ≫ ψ) (IsHomLift_id_comp hφ hψ) =
    Fiber.mk_map ha hb φ hφ ≫ Fiber.mk_map hb hc ψ hψ := rfl

/-- Given a functor F : C ⥤ 𝒳 mapping constantly to some S in the base,
  we get an induced functor C ⥤ Fiber 𝒳 S -/
@[simps]
def FiberInducedFunctor {𝒳 : BasedCategory 𝒮} {S : 𝒮} {C : Type _} [Category C]
  {F : C ⥤ 𝒳.1} (hF : F ⋙ 𝒳.p = (const C).obj S) : C ⥤ Fiber 𝒳 S where
    obj := fun x => ⟨F.obj x, by simp only [←comp_obj, hF, const_obj_obj]⟩
    map := fun φ => ⟨F.map φ, {
      ObjLiftDomain := by simp only [←comp_obj, hF, const_obj_obj]
      ObjLiftCodomain := by simp only [←comp_obj, hF, const_obj_obj]
      HomLift := ⟨by simpa using (eqToIso hF).hom.naturality φ⟩
    }⟩

/-- The natural transformation between F : C ⥤ 𝒳 and .... -/
def FiberInducedFunctorNat {𝒳 : BasedCategory 𝒮} {S : 𝒮} {C : Type _} [Category C] {F : C ⥤ 𝒳.1}
  (hF : F ⋙ 𝒳.p = (const C).obj S) : F ≅ (FiberInducedFunctor hF) ⋙ (FiberInclusion 𝒳 S) where
    hom := { app := fun a => 𝟙 (F.obj a) }
    inv := { app := fun a => 𝟙 ((FiberInducedFunctor hF ⋙ FiberInclusion 𝒳 S).obj a) }

lemma FiberInducedFunctorComp {𝒳 : BasedCategory 𝒮} {S : 𝒮} {C : Type _} [Category C] {F : C ⥤ 𝒳.1}
  (hF : F ⋙ 𝒳.p = (const C).obj S) : F = (FiberInducedFunctor hF) ⋙ (FiberInclusion 𝒳 S) :=
  Functor.ext_of_iso (FiberInducedFunctorNat hF) (fun x => by rfl) (fun x => by rfl)

/-- HasFibers is an exttrinsic notion of fibers on a functor 𝒳.p : 𝒳 ⥤ 𝒮. It is given by a collection
of categories Fib S for every S in 𝒮 (the fiber categories), equiped with functors ι : Fib S ⥤ 𝒳
which map constantly to S on the base such that the induced functor Fib S ⥤ Fiber 𝒳 S is an equivalence. -/
class HasFibers (𝒳 : BasedCategory 𝒮) where
  Fib (S : 𝒮) : Type _
  [isCategory (S : 𝒮) : Category (Fib S)]
  (ι (S : 𝒮) : (Fib S) ⥤ 𝒳.1)
  (comp_const (S : 𝒮) : (ι S) ⋙ 𝒳.p = (const (Fib S)).obj S)
  [equiv (S : 𝒮) : IsEquivalence (FiberInducedFunctor (comp_const S))]

instance {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] {S : 𝒮} : Category (hp.Fib S) := hp.isCategory S

instance {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] {S : 𝒮} : IsEquivalence (FiberInducedFunctor (hp.comp_const S)) := hp.equiv S

instance {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] {S : 𝒮} : EssSurj (FiberInducedFunctor (hp.comp_const S)) :=
  Equivalence.essSurj_of_equivalence (FiberInducedFunctor (hp.comp_const S))

instance {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] {S : 𝒮} : Faithful (hp.ι S) :=
  Faithful.of_iso (FiberInducedFunctorNat (hp.comp_const S)).symm

-- BASIC API CONSTRUCTIONS
def HasFibersProj {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] {S R : 𝒮} {a : hp.Fib S} {b : hp.Fib R}
  (φ : (hp.ι S).obj a ⟶ (hp.ι R).obj b) : S ⟶ R := sorry

@[simp]
lemma HasFibersObjLift {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] {S : 𝒮} (a : hp.Fib S) : 𝒳.p.obj ((hp.ι S).obj a) = S :=
  by simp only [←comp_obj, hp.comp_const, const_obj_obj]

/-- For any homomorphism φ in a fiber Fib S, its image under ι S lies over 𝟙 S -/
lemma HasFibersHomLift {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] {S : 𝒮} {a b : hp.Fib S}
  (φ : a ⟶ b) : IsHomLift 𝒳 (𝟙 S) ((hp.ι S).map φ) where
  ObjLiftDomain := HasFibersObjLift a
  ObjLiftCodomain := HasFibersObjLift b
  HomLift := ⟨by
    rw [←Functor.comp_map, Functor.congr_hom (hp.comp_const S)] -- Can easily be replaced if we decide to work up to iso
    simp only [comp_obj, const_obj_obj, const_obj_map, id_comp, eqToHom_trans, comp_id]⟩

/- Now we define the standard/canonical fiber associated to a fibered category.
When the user does not wish to supply specific fiber categories, this will be the default choice. -/
def Fiber.comp_const_nat (𝒳 : BasedCategory 𝒮) (S : 𝒮) : (FiberInclusion 𝒳 S) ⋙ 𝒳.p ≅ (const (Fiber 𝒳 S)).obj S where
  hom := {
    app := fun x => eqToHom x.prop
    naturality := fun x y φ => by simpa using φ.prop.3.1}
  inv := {
    app := fun x => eqToHom (x.prop).symm
    naturality := fun x y φ => by
      -- TODO OPTIMIZE PROOF (could be solved by simp!!). probably need extra api to simplify
      simp only [const_obj_obj, comp_obj, FiberInclusion_obj, const_obj_map, id_comp, Functor.comp_map, FiberInclusion_map]
      rw [←eqToHom_comp_iff, comp_eqToHom_iff, φ.2.3.1, comp_id]
      }

lemma Fiber.comp_const (𝒳 : BasedCategory 𝒮) (S : 𝒮) : (FiberInclusion 𝒳 S) ⋙ 𝒳.p = (const (Fiber 𝒳 S)).obj S := by
  -- TODO OPTIMIZE PROOF
  apply Functor.ext_of_iso (Fiber.comp_const_nat 𝒳 S)
  intro x
  simp only [comp_const_nat]
  intro x
  simp only [comp_obj, FiberInclusion_obj, x.2, const_obj_obj]

@[default_instance]
instance HasFibers.canonical (𝒳 : BasedCategory 𝒮) : HasFibers 𝒳 where
  Fib := Fiber 𝒳
  ι := FiberInclusion 𝒳
  comp_const := Fiber.comp_const 𝒳
  equiv := fun S =>
  {
    inverse :=  𝟭 (Fiber 𝒳 S)
    unitIso := {
      hom := { app := fun x => ⟨𝟙 x.1, IsHomLift_id x.2⟩ }
      inv := { app := fun x => ⟨𝟙 x.1, IsHomLift_id x.2⟩ } }
    counitIso := {
      hom := { app := fun x => ⟨𝟙 x.1, IsHomLift_id x.2⟩}
      inv := { app := fun x => ⟨𝟙 x.1, IsHomLift_id x.2⟩} }
  }

/-- A version of fullness of the functor Fib S ⥤ Fiber 𝒳 S that can be used inside the category 𝒳 -/
lemma HasFibersFull {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] {S : 𝒮} {a b : hp.Fib S} {φ : (hp.ι S).obj a ⟶ (hp.ι S).obj b}
  (hφ : IsHomLift 𝒳 (𝟙 S) φ) : ∃ (ψ : a ⟶ b), (hp.ι S).map ψ = φ := by
  -- TODO IMPROVE PROOF... Only 5 last lines should be necessary
  let a' : Fiber 𝒳 S := ⟨(hp.ι S).obj a, HasFibersObjLift a⟩
  let b' : Fiber 𝒳 S := ⟨(hp.ι S).obj b, HasFibersObjLift b⟩
  let φ' : a' ⟶ b' := ⟨φ, hφ⟩ -- TODO TURN INTO API ABOVE

  let c : Fiber 𝒳 S := (FiberInducedFunctor (hp.comp_const S)).obj a
  let d : Fiber 𝒳 S := (FiberInducedFunctor (hp.comp_const S)).obj b
  let ψ : c ⟶ d := φ'

  use (Full.preimage ψ)

  rw [←NatIso.naturality_2 (FiberInducedFunctorNat (hp.comp_const S))]
  unfold FiberInducedFunctorNat
  simp only [comp_obj, Functor.comp_map, Full.witness, comp_id, id_comp]
  rfl

/-- A version of essential surjectivity of the functor Fib S ⥤ Fiber 𝒳 S that can be used inside the category 𝒳 -/
lemma HasFibersEssSurj {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] {S : 𝒮} {a : 𝒳.1} (ha : 𝒳.p.obj a = S) :
  ∃ (b : hp.Fib S) (φ : (hp.ι S).obj b ⟶ a), IsIso φ ∧ IsHomLift 𝒳 (𝟙 S) φ := by
  -- This will be easy to inline
  use Functor.objPreimage (FiberInducedFunctor (hp.comp_const S)) (Fiber.mk_obj ha)
  let Φ := Functor.objObjPreimageIso (FiberInducedFunctor (hp.comp_const S)) (Fiber.mk_obj ha)
  use (FiberInclusion 𝒳 S).map Φ.hom
  refine ⟨inferInstance, Φ.hom.2⟩

lemma HasFibersEssSurj' {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] {S : 𝒮} {a : 𝒳.1} (ha : 𝒳.p.obj a = S) :
    ∃ (b : hp.Fib S) (φ : (hp.ι S).obj b ≅ a), IsHomLift 𝒳 (𝟙 S) φ.hom := by
  -- This will be easy to inline
  use Functor.objPreimage (FiberInducedFunctor (hp.comp_const S)) (Fiber.mk_obj ha)
  let Φ := Functor.objObjPreimageIso (FiberInducedFunctor (hp.comp_const S)) (Fiber.mk_obj ha)
  refine ⟨(FiberInclusion 𝒳 S).mapIso Φ, Φ.hom.2⟩

-- MIGHT NOT NEED....
def HasFibersMap {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] {R S : 𝒮} {a : hp.Fib S}
    {b : hp.Fib R} (φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a) : R ⟶ S :=
  eqToHom (HasFibersObjLift b).symm ≫ (𝒳.p.map φ) ≫ eqToHom (HasFibersObjLift a)

/-- Given a HasFibers and a diagram
```
           a
           -
           |
           v
  R --f--> S
```
with a in Fib S, we can take a pullback b = `R ×_S a` in Fib R -/
lemma HasFibersPullback {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [IsFibered 𝒳] {R S : 𝒮} (a : hp.Fib S)
    (f : R ⟶ S) : ∃ (b : hp.Fib R) (φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a), IsPullback 𝒳 f φ := by
  rcases IsFibered.has_pullbacks (HasFibersObjLift a) f with ⟨b, φ, hφ⟩
  rcases HasFibersEssSurj hφ.ObjLiftDomain with ⟨b', ψ, hψ⟩
  use b', ψ ≫ φ
  rw [←id_comp f]
  exact IsPullback_comp (IsPullbackofIso hψ.2 hψ.1) hφ

-- TODO MAYBE REPLACE THE ABOVE WITH THIS LEMMA
lemma HasFibersPullback' {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [IsFibered 𝒳] {R S : 𝒮} {a : 𝒳.1}
    (ha : 𝒳.p.obj a = S) (f : R ⟶ S) : ∃ (b : hp.Fib R) (φ : (hp.ι R).obj b ⟶ a),
      IsPullback 𝒳 f φ := by
  rcases IsFibered.has_pullbacks ha f with ⟨b, φ, hφ⟩
  rcases HasFibersEssSurj hφ.ObjLiftDomain with ⟨b', ψ, hψ⟩
  use b', ψ ≫ φ
  rw [←id_comp f]
  exact IsPullback_comp (IsPullbackofIso hψ.2 hψ.1) hφ

/-- Given a fibered category p, b' b in Fib R, an a pullback ψ : b ⟶ a in 𝒳, i.e.
```
b'       b --ψ--> a
|        |        |
v        v        v
R ====== R --f--> S
```
Then the induced map τ : b' ⟶ b to lies in the fiber over R -/
lemma HasFibersFactorization {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [IsFibered 𝒳] {R S : 𝒮}
    {a : 𝒳.1} {b b' : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ a}
    (hφ : IsHomLift 𝒳 f φ) {ψ : (hp.ι R).obj b' ⟶ a} (hψ : IsPullback 𝒳 f ψ) :
      ∃ (τ : b ⟶ b'), (hp.ι R).map τ ≫ ψ = φ := by
  -- By fullness, we can pull back τ to the fiber over R
  rcases HasFibersFull (IsPullbackInducedMap_IsHomLift hψ (id_comp f).symm hφ) with ⟨τ, hτ⟩
  use τ
  rw [hτ]
  exact (IsPullbackInducedMap_Diagram hψ (id_comp f).symm hφ)

noncomputable def HasFibersInducedMap {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [IsFibered 𝒳] {R S : 𝒮}
    {a : 𝒳.1} {b b' : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ a}
    (hφ : IsHomLift 𝒳 f φ) {ψ : (hp.ι R).obj b' ⟶ a} (hψ : IsPullback 𝒳 f ψ) : b ⟶ b' :=
  Classical.choose (HasFibersFactorization hφ hψ)

-- TODO FORMULATE...
/- lemma HasFibersFactorizationUnique {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [IsFibered 𝒳] {R S : 𝒮}
  {a : 𝒳.1} {b b' : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ a}
  (hφ : IsHomLift 𝒳 f φ) {ψ : (hp.ι R).obj b' ⟶ a} (hψ : IsPullback 𝒳.p f ψ) : -/


-- TODO: In this lemma, should maybe just require that a lies over S (not necc in the fiber)
/-- Given a in Fib S, b in Fib R, and a diagram
```
  b --φ--> a
  -        -
  |        |
  v        v
  R --f--> S
```
It can be factorized as
```
  b --τ--> b'--ψ--> a
  -        -        -
  |        |        |
  v        v        v
  R ====== R --f--> S
```
with ψ a pullback of f and τ a map in Fib R -/
lemma fiber_factorization {𝒳 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [IsFibered 𝒳] {R S : 𝒮}
    {a : hp.Fib S} {b : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a}
    (hφ : IsHomLift 𝒳 f φ) : ∃ (b' : hp.Fib R) (τ : b ⟶ b') (ψ : (hp.ι R).obj b' ⟶ (hp.ι S).obj a),
      IsPullback 𝒳 f ψ ∧ (((hp.ι R).map τ) ≫ ψ = φ) := by
  rcases (HasFibersPullback a f) with ⟨b', ψ, hψ⟩
  rcases HasFibersFactorization hφ hψ with ⟨τ, hτ⟩
  use b', τ, ψ, hψ

end Fibered

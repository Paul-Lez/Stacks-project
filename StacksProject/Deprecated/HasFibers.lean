/-
Copyright (c) 2023 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/

import StacksProject.FiberedCategories.Basic
import Mathlib.CategoryTheory.Functor.Const

/-!
# Fibers of functors
In this file we develop the theory of fibers of functors. Given a functor `p : 𝒳 ⥤ 𝒮`, we define
the fiber categories `Fiber p S` for every `S : 𝒮` as follows:
- An object in `Fiber p S` is a pair `(a, ha)` where `a : 𝒳` and `ha : p.obj a = S`.
- A morphism in `Fiber p S` is a morphism `φ : a ⟶ b` in 𝒳 such that `p.map φ = 𝟙 S`.

We also introduce a typeclass `HasFibers` for a functor `p : 𝒳 ⥤ 𝒮`, consisting of:
- A collection of categories `Fib S` for every `S` in `𝒮` (the fiber categories)
- Functors `ι : Fib S ⥤ 𝒳` such that `ι ⋙ p = const (Fib S) S
- The induced functor `Fib S ⥤ Fiber p S` is an equivalence.

The reason for introducing this typeclass is that in practice, when working with fibered categories
one often already has a collection of categories `Fib S` for every `S` that are equivalent to the fibers
`Fiber p S`. One would then like to use these categories `Fib S` directly, instead of working through this
equivalence of categories. By developing an API for the `HasFibers` typeclass, this will be possible.
For example, we develop the following lemmas:
- `HasFibersEssSurj` any object `a : 𝒳` lying over some `S : 𝒮` is isomorphic to the image of some `a' : Fib S`
- `HasFibersPullback` allows one to take pullbacks such that the codomain lies in one of the fibers `Fib S`.
- `HasFibersFactorization` (TODO: maybe call it `HasFibersInducedMap`, and the next `HasFibersFactorization`)
- `fiber_factorization` any morphism in `𝒳` can be factored as a morphism in some fiber `Fib S` followed by
  a pullback. (TODO: rename this lemma)

Here is an example of when this typeclass is useful. Suppose we have a presheaf of types `F : 𝒮ᵒᵖ ⥤ Type _`.
The associated fibered category then has objects `(S, a)` where `S : 𝒮` and `a` is an element of `F(S)`.
The fiber category `Fiber p S` is then equivalent to the discrete category `Fib S` with objects `a` in `F(S)`.
In this case, the `HasFibers` instance is given by the categories `F(S)` and the functor `ι` sends
`a : F(S)` to `(S, a)` in the fibered category. See `Presheaf.lean` for more details.
-/

-- TODO: port this to use `BasedCategory` later.
-- FiberCat should then be defined in this file, move out any `IsFibered` propoerties to `FiberedCat.lean`

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category IsPullback

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category 𝒳] [Category 𝒮]

-- TODO: should it be this namespace?
namespace Fibered

/-- Fiber p S is the type of elements of 𝒳 mapping to S via p  -/
def Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮) := {a : 𝒳 // p.obj a = S}

/-- We can turn Fiber p S into a category by taking the morphisms to be those lying over 𝟙 S -/
@[simps]
instance FiberCategory (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : Category (Fiber p S) where
  Hom a b := {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}
  id a := ⟨𝟙 a.1, IsHomLift.id a.2⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val, by apply (comp_id (𝟙 S)) ▸ IsHomLift.comp φ.2 ψ.2⟩

def Fiber.mk_obj {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fiber p S := ⟨a, ha⟩

@[simps?]
def Fiber.mk_map {p :𝒳 ⥤ 𝒮} {S : 𝒮} {a b : 𝒳} (ha : p.obj a = S) (hb : p.obj b = S) (φ : a ⟶ b) (hφ : IsHomLift p (𝟙 S) φ := by aesop_cat) : Fiber.mk_obj ha ⟶ Fiber.mk_obj hb := ⟨φ, hφ⟩

@[simp]
lemma Fiber.mk_map_id {p :𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fiber.mk_map ha ha (𝟙 a) = 𝟙 (Fiber.mk_obj ha) := rfl

@[simp]
lemma Fiber.mk_obj_coe (p : 𝒳 ⥤ 𝒮) (a : 𝒳) : (Fiber.mk_obj (p:=p) (a:=a) rfl).1 = a := rfl

/-- The functor including Fiber p S into 𝒳 -/
@[simps]
def FiberInclusion (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : (Fiber p S) ⥤ 𝒳 where
  obj a := a.1
  map φ := φ.1

instance FiberInclusionFaithful (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : Functor.Faithful (FiberInclusion p S) where
  map_injective := Subtype.val_inj.1

@[ext]
lemma Fiber.hom_ext {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a b : Fiber p S} (φ ψ : a ⟶ b) : φ.1 = ψ.1 → φ = ψ := Subtype.ext

@[simp]
lemma Fiber.val_comp {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a b c : Fiber p S} (φ : a ⟶ b)
    (ψ : b ⟶ c) : (φ ≫ ψ).1 = φ.1 ≫ ψ.1 := rfl

lemma Fiber.mk_map_com {p :𝒳 ⥤ 𝒮} {S : 𝒮} {a b c : 𝒳} (ha : p.obj a = S) (hb : p.obj b = S)
    (hc : p.obj c = S) (φ : a ⟶ b) (ψ : b ⟶ c) (hφ : IsHomLift p (𝟙 S) φ)
    (hψ : IsHomLift p (𝟙 S) ψ) : Fiber.mk_map ha hc (φ ≫ ψ) (IsHomLift.lift_id_comp hφ hψ) =
    Fiber.mk_map ha hb φ hφ ≫ Fiber.mk_map hb hc ψ hψ := rfl

/-- Given a functor F : C ⥤ 𝒳 mapping constantly to some S in the base,
  we get an induced functor C ⥤ Fiber p S -/
@[simps]
def FiberInducedFunctor {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type _} [Category C]
  {F : C ⥤ 𝒳} (hF : F ⋙ p = (const C).obj S) : C ⥤ Fiber p S where
    obj := fun x => ⟨F.obj x, by simp only [←comp_obj, hF, const_obj_obj]⟩
    map := fun φ => ⟨F.map φ, {
      ObjLiftDomain := by simp only [←comp_obj, hF, const_obj_obj]
      ObjLiftCodomain := by simp only [←comp_obj, hF, const_obj_obj]
      HomLift := ⟨by simpa using (eqToIso hF).hom.naturality φ⟩
    }⟩

/-- The natural transformation between F : C ⥤ 𝒳 and .... -/
def FiberInducedFunctorNat {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type _} [Category C] {F : C ⥤ 𝒳}
  (hF : F ⋙ p = (const C).obj S) : F ≅ (FiberInducedFunctor hF) ⋙ (FiberInclusion p S) where
    hom := { app := fun a => 𝟙 (F.obj a) }
    inv := { app := fun a => 𝟙 ((FiberInducedFunctor hF ⋙ FiberInclusion p S).obj a) }

lemma FiberInducedFunctorComp {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type _} [Category C] {F : C ⥤ 𝒳}
  (hF : F ⋙ p = (const C).obj S) : F = (FiberInducedFunctor hF) ⋙ (FiberInclusion p S) :=
  Functor.ext_of_iso (FiberInducedFunctorNat hF) (fun x => by rfl) (fun x => by rfl)

/-- HasFibers is an exttrinsic notion of fibers on a functor p : 𝒳 ⥤ 𝒮. It is given by a collection
of categories Fib S for every S in 𝒮 (the fiber categories), equiped with functors ι : Fib S ⥤ 𝒳
which map constantly to S on the base such that the induced functor Fib S ⥤ Fiber p S is an equivalence. -/
class HasFibers (p : 𝒳 ⥤ 𝒮) where
  Fib (S : 𝒮) : Type _
  [isCategory (S : 𝒮) : Category (Fib S)]
  (ι (S : 𝒮) : (Fib S) ⥤ 𝒳)
  (comp_const (S : 𝒮) : (ι S) ⋙ p = (const (Fib S)).obj S)
  [equiv (S : 𝒮) : Functor.IsEquivalence (FiberInducedFunctor (comp_const S))]

instance {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} : Category (hp.Fib S) := hp.isCategory S

@[simps!]
def HasFibers.InducedFunctor (p : 𝒳 ⥤ 𝒮) [hp : HasFibers p] (S : 𝒮) : hp.Fib S ⥤ Fiber p S :=
  FiberInducedFunctor (hp.comp_const S)

def HasFibers.InducedFunctorNat {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] (S : 𝒮) :
    hp.ι S ≅ (hp.InducedFunctor S) ⋙ (FiberInclusion p S) :=
  FiberInducedFunctorNat (hp.comp_const S)

lemma HasFibers.InducedFunctorComp {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] (S : 𝒮) :
    hp.ι S = (hp.InducedFunctor S) ⋙ (FiberInclusion p S) :=
  FiberInducedFunctorComp (hp.comp_const S)

-- TODO: state these in terms of InducedFunctor
instance {p : 𝒳 ⥤ 𝒮} [HasFibers p] {S : 𝒮} : Functor.IsEquivalence (HasFibers.InducedFunctor p S) :=
  HasFibers.equiv S

instance {p : 𝒳 ⥤ 𝒮} [HasFibers p] {S : 𝒮} : Functor.EssSurj (HasFibers.InducedFunctor p S) :=
  Equivalence.essSurj_of_equivalence (HasFibers.InducedFunctor p S)

instance {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} : Functor.Faithful (hp.ι S) :=
  Functor.Faithful.of_iso (hp.InducedFunctorNat S).symm

-- BASIC API CONSTRUCTIONS
def HasFibersProj {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S R : 𝒮} {a : hp.Fib S} {b : hp.Fib R}
  (φ : (hp.ι S).obj a ⟶ (hp.ι R).obj b) : S ⟶ R := sorry

@[simp]
lemma HasFibersObjLift {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} (a : hp.Fib S) : p.obj ((hp.ι S).obj a) = S :=
  by simp only [←comp_obj, hp.comp_const, const_obj_obj]

/-- For any homomorphism φ in a fiber Fib S, its image under ι S lies over 𝟙 S -/
lemma HasFibersHomLift {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} {a b : hp.Fib S}
  (φ : a ⟶ b) : IsHomLift p (𝟙 S) ((hp.ι S).map φ) where
  ObjLiftDomain := HasFibersObjLift a
  ObjLiftCodomain := HasFibersObjLift b
  HomLift := ⟨by
    rw [←Functor.comp_map, Functor.congr_hom (hp.comp_const S)] -- Can easily be replaced if we decide to work up to iso
    simp only [comp_obj, const_obj_obj, const_obj_map, id_comp, eqToHom_trans, comp_id]⟩

/- Now we define the standard/canonical fiber associated to a fibered category.
When the user does not wish to supply specific fiber categories, this will be the default choice. -/
def Fiber.comp_const_nat (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : (FiberInclusion p S) ⋙ p ≅ (const (Fiber p S)).obj S where
  hom := {
    app := fun x => eqToHom x.prop
    naturality := fun x y φ => by simpa using φ.prop.3.1}
  inv := {
    app := fun x => eqToHom (x.prop).symm
    naturality := fun x y φ => by
      -- TODO OPTIMIZE PROOF (could be solved by simp!!). probably need extra api to simplify
      simp only [const_obj_obj, comp_obj, FiberInclusion_obj, const_obj_map, id_comp, Functor.comp_map, FiberInclusion_map]
      rw [←eqToHom_comp_iff, comp_eqToHom_iff, φ.2.3.1, comp_id] }

lemma Fiber.comp_const (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : (FiberInclusion p S) ⋙ p = (const (Fiber p S)).obj S := by
  -- TODO OPTIMIZE PROOF
  apply Functor.ext_of_iso (Fiber.comp_const_nat p S)
  intro x
  simp only [comp_const_nat]
  intro x
  simp only [comp_obj, FiberInclusion_obj, x.2, const_obj_obj]

@[default_instance]
instance HasFibers.canonical (p : 𝒳 ⥤ 𝒮) : HasFibers p where
  Fib := Fiber p
  ι := FiberInclusion p
  comp_const := Fiber.comp_const p
  equiv := fun S => {
    inverse :=  𝟭 (Fiber p S)
    unitIso := {
      hom := { app := fun x => ⟨𝟙 x.1, IsHomLift.id x.2⟩ }
      inv := { app := fun x => ⟨𝟙 x.1, IsHomLift.id x.2⟩ } }
    counitIso := {
      hom := { app := fun x => ⟨𝟙 x.1, IsHomLift.id x.2⟩}
      inv := { app := fun x => ⟨𝟙 x.1, IsHomLift.id x.2⟩} } }

/-- A version of fullness of the functor `Fib S ⥤ Fiber p S` that can be used inside the category `𝒳` -/
lemma HasFibersFull {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} {a b : hp.Fib S} {φ : (hp.ι S).obj a ⟶ (hp.ι S).obj b}
  (hφ : IsHomLift p (𝟙 S) φ) : ∃ (ψ : a ⟶ b), (hp.ι S).map ψ = φ := by

  let a' : Fiber p S := (HasFibers.InducedFunctor p S).obj a
  let b' : Fiber p S := (HasFibers.InducedFunctor p S).obj b
  let ψ : a' ⟶ b' := ⟨φ, hφ⟩
  use (Full.preimage ψ)

  rw [←NatIso.naturality_2 (FiberInducedFunctorNat (hp.comp_const S))]
  -- TODO: this should all be simp after appropriate `@[simp]s`
  unfold FiberInducedFunctorNat
  simp only [comp_obj, Functor.comp_map, Full.witness, comp_id, id_comp]
  rfl

/-- Any isomorphism `Φ : (hp.ι S).obj a ≅ (hp.ι S).obj b` lying over `𝟙 S` can be lifted to an isomorphism in `Fib S` -/
def HasFibersPreimageIso {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} {a b : hp.Fib S}
    (Φ : (hp.ι S).obj a ≅ (hp.ι S).obj b) (hΦ : IsHomLift p (𝟙 S) Φ.hom) : a ≅ b := by
  let a' : Fiber p S := (HasFibers.InducedFunctor p S).obj a
  let b' : Fiber p S := (HasFibers.InducedFunctor p S).obj b
  let Φ' : a' ≅ b' := {
    hom := ⟨Φ.hom, hΦ⟩
    inv := ⟨Φ.inv, by simpa using IsHomLift.lift_id_inv hΦ⟩ -- TODO: this could be improved..
  }
  exact ((hp.InducedFunctor S).preimageIso Φ')


/-- A version of essential surjectivity of the functor `Fib S ⥤ Fiber p S` that can be used inside the category `𝒳` -/
lemma HasFibersEssSurj {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
  ∃ (b : hp.Fib S) (φ : (hp.ι S).obj b ⟶ a), IsIso φ ∧ IsHomLift p (𝟙 S) φ := by
  -- This will be easy to inline
  use Functor.objPreimage (HasFibers.InducedFunctor p S) (Fiber.mk_obj ha)
  let Φ := Functor.objObjPreimageIso (HasFibers.InducedFunctor p S) (Fiber.mk_obj ha)
  use (FiberInclusion p S).map Φ.hom
  refine ⟨inferInstance, Φ.hom.2⟩

lemma HasFibersEssSurj' {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    ∃ (b : hp.Fib S) (φ : (hp.ι S).obj b ≅ a), IsHomLift p (𝟙 S) φ.hom := by
  -- This will be easy to inline
  use Functor.objPreimage (HasFibers.InducedFunctor p S) (Fiber.mk_obj ha)
  let Φ := Functor.objObjPreimageIso (HasFibers.InducedFunctor p S) (Fiber.mk_obj ha)
  refine ⟨(FiberInclusion p S).mapIso Φ, Φ.hom.2⟩

-- MIGHT NOT NEED....
def HasFibersMap {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {R S : 𝒮} {a : hp.Fib S}
    {b : hp.Fib R} (φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a) : R ⟶ S :=
  eqToHom (HasFibersObjLift b).symm ≫ (p.map φ) ≫ eqToHom (HasFibersObjLift a)

/-- Given a `HasFibers` instance and a diagram
```
           a
           -
           |
           v
  R --f--> S
```
with a in Fib S, we can take a pullback b = `R ×_S a` in Fib R -/
lemma HasFibersPullback {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] [IsFibered p] {R S : 𝒮} (a : hp.Fib S)
    (f : R ⟶ S) : ∃ (b : hp.Fib R) (φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a), IsPullback p f φ := by
  rcases IsFibered.has_pullbacks (HasFibersObjLift a) f with ⟨b, φ, hφ⟩
  rcases HasFibersEssSurj hφ.ObjLiftDomain with ⟨b', ψ, ⟨_, hψ⟩⟩
  use b', ψ ≫ φ
  rw [←id_comp f]
  exact IsPullback.comp (IsPullback.of_isIso hψ) hφ

-- TODO MAYBE REPLACE THE ABOVE WITH THIS LEMMA
lemma HasFibersPullback' {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] [IsFibered p] {R S : 𝒮} {a : 𝒳}
    (ha : p.obj a = S) (f : R ⟶ S) : ∃ (b : hp.Fib R) (φ : (hp.ι R).obj b ⟶ a),
      IsPullback p f φ := by
  rcases IsFibered.has_pullbacks ha f with ⟨b, φ, hφ⟩
  rcases HasFibersEssSurj hφ.ObjLiftDomain with ⟨b', ψ, ⟨_, hψ⟩⟩
  use b', ψ ≫ φ
  rw [←id_comp f]
  exact IsPullback.comp (IsPullback.of_isIso hψ) hφ

/-- Given a fibered category p, b' b in Fib R, an a pullback ψ : b ⟶ a in 𝒳, i.e.
```
b'       b --ψ--> a
|        |        |
v        v        v
R ====== R --f--> S
```
Then the induced map τ : b' ⟶ b to lies in the fiber over R -/
lemma HasFibersFactorization {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] [IsFibered p] {R S : 𝒮}
    {a : 𝒳} {b b' : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ a}
    (hφ : IsHomLift p f φ) {ψ : (hp.ι R).obj b' ⟶ a} (hψ : IsPullback p f ψ) :
      ∃ (τ : b ⟶ b'), (hp.ι R).map τ ≫ ψ = φ := by
  -- By fullness, we can pull back τ to the fiber over R
  rcases HasFibersFull (InducedMap_IsHomLift hψ (id_comp f).symm hφ) with ⟨τ, hτ⟩
  use τ
  rw [hτ]
  exact (InducedMap_Diagram hψ (id_comp f).symm hφ)

noncomputable def HasFibersInducedMap {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] [IsFibered p] {R S : 𝒮}
    {a : 𝒳} {b b' : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ a}
    (hφ : IsHomLift p f φ) {ψ : (hp.ι R).obj b' ⟶ a} (hψ : IsPullback p f ψ) : b ⟶ b' :=
  Classical.choose (HasFibersFactorization hφ hψ)

-- TODO FORMULATE...
/- lemma HasFibersFactorizationUnique {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] [IsFibered p] {R S : 𝒮}
  {a : 𝒳} {b b' : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ a}
  (hφ : IsHomLift p f φ) {ψ : (hp.ι R).obj b' ⟶ a} (hψ : IsPullback p f ψ) : -/


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
lemma fiber_factorization {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] [IsFibered p] {R S : 𝒮}
    {a : hp.Fib S} {b : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a}
    (hφ : IsHomLift p f φ) : ∃ (b' : hp.Fib R) (τ : b ⟶ b') (ψ : (hp.ι R).obj b' ⟶ (hp.ι S).obj a),
      IsPullback p f ψ ∧ (((hp.ι R).map τ) ≫ ψ = φ) := by
  rcases (HasFibersPullback a f) with ⟨b', ψ, hψ⟩
  rcases HasFibersFactorization hφ hψ with ⟨τ, hτ⟩
  use b', τ, ψ, hψ

end Fibered

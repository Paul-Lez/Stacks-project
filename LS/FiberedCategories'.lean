/-
Copyright (c) 2023 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/

import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Functor.Const
-- TO GET HAS PULLBACKS, FIGURE OUT WHAT TO IMPORT LATER
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks

--import Mathlib.CategoryTheory.Limits
/-!

# Fibered categories

This file defines fibered categories.

## Implementation
-/


universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category 𝒳] [Category 𝒮]

namespace Fibered

/--
MORE FLEXIBLE API
-/

def HomLift' {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
 (ha : p.obj a = R) (hb : p.obj b = S) : Prop :=
  CommSq (p.map φ) (eqToHom ha) (eqToHom hb) f

/-- The proposition that an arrow a --φ--> b lifts an arrow R --f--> S in 𝒮 via p. This is
often drawn as:
```
  a --φ--> b
  -        -
  |        |
  v        v
  R --f--> S
``` -/
class IsHomLift (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) : Prop where
  (ObjLiftDomain : p.obj a = R)
  (ObjLiftCodomain : p.obj b = S)
  (HomLift : CommSq (p.map φ) (eqToHom ObjLiftDomain) (eqToHom ObjLiftCodomain) f)

lemma IsHomLift_id {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a : 𝒳} (ha : p.obj a = R) : IsHomLift p (𝟙 R) (𝟙 a) where
  ObjLiftDomain := ha
  ObjLiftCodomain := ha
  HomLift := ⟨by simp only [map_id, id_comp, comp_id]⟩

instance IsHomLift_self (p : 𝒳 ⥤ 𝒮) : IsHomLift p (p.map φ) φ where
  ObjLiftDomain := rfl
  ObjLiftCodomain := rfl
  HomLift := ⟨by simp only [eqToHom_refl, comp_id, id_comp]⟩

/-- If a --φ--> b lifts R --f--> S, then if φ is an isomorphism, so is f. -/
lemma IsIsoofIsHomliftisIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hlift : IsHomLift p f φ) (hφ : IsIso φ) : IsIso f := by
  rcases hlift with ⟨domain, _, ⟨homlift⟩⟩
  rw [←eqToHom_comp_iff domain.symm] at homlift
  rw [←homlift]
  exact IsIso.comp_isIso

lemma IsHomLift_inv {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hlift : IsHomLift p f φ) (hφ : IsIso φ) (hf : IsIso f) : IsHomLift p (inv f) (inv φ) where
    ObjLiftDomain := hlift.2
    ObjLiftCodomain := hlift.1
    HomLift := by
      constructor
      simp only [map_inv, IsIso.eq_comp_inv, assoc, IsIso.inv_comp_eq]
      exact hlift.3.1.symm

lemma IsHomLift_comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S}
  {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c} (hφ : IsHomLift p f φ)
  (hψ : IsHomLift p g ψ) : IsHomLift p (f ≫ g) (φ ≫ ψ) where
    ObjLiftDomain := hφ.1
    ObjLiftCodomain := hψ.2
    HomLift := by
      constructor
      rw [←Category.assoc, ←hφ.3.1]
      simp only [map_comp, assoc, hψ.3.1]

/-- The proposition that a lift
```
  a --φ--> b
  -        -
  |        |
  v        v
  R --f--> S
```
is a pullback.
-/
class IsPullback (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) extends IsHomLift p f φ : Prop where
  (UniversalProperty {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S}
    (_ : f' = g ≫ f) {φ' : a' ⟶ b} (_ : IsHomLift p f' φ') :
      ∃! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ')

/-- Given a diagram:
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that φ is a pullback, and an arrow φ' : a' ⟶ b,
the induced map is the map a' ⟶ a obtained from the
universal property of φ. -/
noncomputable def IsPullbackInducedMap {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
  {φ' : a' ⟶ b} (hφ' : IsHomLift p f' φ') : a' ⟶ a :=
  Classical.choose $ hφ.UniversalProperty hf' hφ'

lemma IsPullbackInducedMap_IsHomLift {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
  {φ' : a' ⟶ b} (hφ' : IsHomLift p f' φ') : IsHomLift p g (IsPullbackInducedMap hφ hf' hφ') :=
  (Classical.choose_spec (hφ.UniversalProperty hf' hφ')).1.1

@[simp]
lemma IsPullbackInducedMap_Diagram {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
  {φ' : a' ⟶ b} (hφ' : IsHomLift p f' φ') : (IsPullbackInducedMap hφ hf' hφ') ≫ φ = φ' :=
  (Classical.choose_spec (hφ.UniversalProperty hf' hφ')).1.2

/-- Given a diagram:
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
with φ a pullback. Then for any arrow φ' : a' ⟶ b, and ψ : a' ⟶ a such that
g ≫ ψ = φ'. Then ψ equals the induced pullback map. -/
lemma IsPullbackInducedMap_unique {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
  {φ' : a' ⟶ b} (hφ' : IsHomLift p f' φ') {ψ : a' ⟶ a} (hψ : IsHomLift p g ψ)
  (hcomp : ψ ≫ φ = φ') : ψ = IsPullbackInducedMap hφ hf' hφ' :=
  (Classical.choose_spec (hφ.UniversalProperty hf' hφ')).2 ψ ⟨hψ, hcomp⟩

@[simp]
lemma IsPullbackInducedMap_self_eq_id {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback p f φ) : 𝟙 a = IsPullbackInducedMap hφ (show f = 𝟙 R ≫ f by simp) hφ.toIsHomLift :=
  IsPullbackInducedMap_unique hφ (show f = 𝟙 R ≫ f by simp) hφ.toIsHomLift (IsHomLift_id hφ.ObjLiftDomain) (id_comp _)

/-- TODO IS THIS PARTICULAR STATEMENT OPTIMAL? Assumes "big" squares are commutative...
```


``` -/
@[simp]
lemma IsPullbackInducedMap_comp {p : 𝒳 ⥤ 𝒮}
  {R R' R'' S: 𝒮} {a a' a'' b : 𝒳}
  {f : R ⟶ S} {f' : R' ⟶ S} {f'' : R'' ⟶ S} {g : R' ⟶ R} {h : R'' ⟶ R'}
  (H : f' = g ≫ f) (H' : f'' = h ≫ f') {φ : a ⟶ b} {φ' : a' ⟶ b} {φ'' : a'' ⟶ b}
  (hφ : IsPullback p f φ) (hφ' : IsPullback p f' φ') (hφ'' : IsHomLift p f'' φ'') :
  IsPullbackInducedMap hφ' H' hφ'' ≫ IsPullbackInducedMap hφ H hφ'.toIsHomLift
  = IsPullbackInducedMap hφ (show f'' = (h ≫ g) ≫ f by rwa [assoc, ←H]) hφ'' := by
  apply IsPullbackInducedMap_unique
  · apply IsHomLift_comp
    apply IsPullbackInducedMap_IsHomLift
    apply IsPullbackInducedMap_IsHomLift
  · simp only [assoc, IsPullbackInducedMap_Diagram]

/-- Given two pullback squares
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
Then also the composite φ ≫ ψ is a pullback square. -/
lemma IsPullback_comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c: 𝒳} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b}
  {ψ : b ⟶ c} (hφ : IsPullback p f φ) (hψ : IsPullback p g ψ) : IsPullback p (f ≫ g) (φ ≫ ψ) where
    toIsHomLift := IsHomLift_comp hφ.toIsHomLift hψ.toIsHomLift
    UniversalProperty := by
      intro U d h i hi_comp τ hi
      rw [←assoc] at hi_comp
      let π := IsPullbackInducedMap hφ rfl (IsPullbackInducedMap_IsHomLift hψ hi_comp hi)
      existsi π
      refine ⟨⟨IsPullbackInducedMap_IsHomLift hφ rfl (IsPullbackInducedMap_IsHomLift hψ hi_comp hi), ?_⟩, ?_⟩
      · rw [←(IsPullbackInducedMap_Diagram hψ hi_comp hi)]
        rw [←(IsPullbackInducedMap_Diagram hφ rfl (IsPullbackInducedMap_IsHomLift hψ hi_comp hi)), assoc]
      intro π' hπ'
      apply IsPullbackInducedMap_unique hφ _ _ hπ'.1
      apply IsPullbackInducedMap_unique hψ _ _ (IsHomLift_comp hπ'.1 hφ.toIsHomLift)
      simpa only [assoc] using hπ'.2

/-- Given two commutative squares
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
such that the composite φ ≫ ψ is a pullback, then so is φ. -/
lemma IsPullback_of_comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c: 𝒳} {f : R ⟶ S} {g : S ⟶ T}
  {φ : a ⟶ b} {ψ : b ⟶ c} (hψ : IsPullback p g ψ) (hcomp : IsPullback p (f ≫ g) (φ ≫ ψ))
  (hφ : IsHomLift p f φ) : IsPullback p f φ where
    toIsHomLift := hφ
    UniversalProperty := by
      intro U d h i hi_comp τ hi
      have h₁ : IsHomLift p (i ≫ g) (τ ≫ ψ) := IsHomLift_comp hi hψ.toIsHomLift
      have h₂ : i ≫ g = h ≫ f ≫ g := by rw [hi_comp, assoc]
      let π := IsPullbackInducedMap hcomp h₂ h₁
      existsi π
      refine ⟨⟨IsPullbackInducedMap_IsHomLift hcomp h₂ h₁, ?_⟩,?_⟩
      · have h₃ := IsHomLift_comp (IsPullbackInducedMap_IsHomLift hcomp h₂ h₁) hφ
        rw [←assoc] at h₂
        rw [IsPullbackInducedMap_unique hψ h₂ h₁ (by rwa [←hi_comp]) rfl]
        apply IsPullbackInducedMap_unique hψ h₂ h₁ h₃ _
        rw [assoc] at h₂
        rw [assoc, (IsPullbackInducedMap_Diagram hcomp h₂ h₁)]
      intro π' hπ'
      apply IsPullbackInducedMap_unique _ _ _ hπ'.1 (by rw [←hπ'.2, assoc])

lemma IsPullbackofIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳}
  {f : R ⟶ S} {φ : a ⟶ b} (hlift : IsHomLift p f φ) (hφ : IsIso φ) : IsPullback p f φ where
    toIsHomLift := hlift
    UniversalProperty := by
      intros R' a' g f' hf' φ' hφ'
      existsi φ' ≫ inv φ
      constructor
      · simp only [assoc, IsIso.inv_hom_id, comp_id, and_true]
        have hf : IsIso f := IsIsoofIsHomliftisIso hlift hφ
        have h₁ := IsHomLift_comp hφ' (IsHomLift_inv hlift hφ hf)
        simp only [hf', assoc, IsIso.hom_inv_id, comp_id] at h₁
        exact h₁
      intro ψ hψ
      simp only [IsIso.eq_comp_inv, hψ.2]

-- NEED TO CHECK PROOFS FROM HERE ONWARDS
lemma IsPullbackIsoofIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback p f φ) (hf : IsIso f): IsIso φ :=
  by
    constructor
    set φ' := IsPullbackInducedMap hφ (IsIso.inv_hom_id f).symm (IsHomLift_id _)
    existsi φ'
    refine ⟨?_, IsPullbackInducedMap_Diagram hφ (IsIso.inv_hom_id f).symm (IsHomLift_id hφ.ObjLiftCodomain)⟩
    have h₁ : IsHomLift p (𝟙 R) (φ ≫ φ') := {
      ObjLiftDomain := hφ.ObjLiftDomain
      ObjLiftCodomain := hφ.ObjLiftDomain
      HomLift := by
        constructor
        simp only [map_comp, assoc, comp_id]
        have h₁ := hφ.HomLift.1
        rw [comp_eqToHom_iff] at h₁
        rw [h₁]
        have h₂ := (IsPullbackInducedMap_IsHomLift hφ (IsIso.inv_hom_id f).symm (IsHomLift_id hφ.ObjLiftCodomain)).HomLift.1
        rw [comp_eqToHom_iff] at h₂
        rw [h₂]
        simp only [assoc, eqToHom_trans, eqToHom_refl, comp_id, eqToHom_trans_assoc, id_comp, IsIso.hom_inv_id]
        -- TODO TEMPORARY:
        apply hφ.ObjLiftCodomain
    }
    have h₂ : IsHomLift p f (φ ≫ φ' ≫ φ) := by
      rw [IsPullbackInducedMap_Diagram hφ (IsIso.inv_hom_id f).symm (IsHomLift_id hφ.ObjLiftCodomain), comp_id]
      apply hφ.toIsHomLift
    rw [IsPullbackInducedMap_unique hφ (show f = 𝟙 R ≫ f by simp) h₂ h₁ (by apply Category.assoc)]
    apply (IsPullbackInducedMap_unique hφ (show f = 𝟙 R ≫ f by simp) _ (IsHomLift_id hφ.ObjLiftDomain) _).symm
    rw [IsPullbackInducedMap_Diagram hφ (IsIso.inv_hom_id f).symm (IsHomLift_id hφ.ObjLiftCodomain)]
    simp only [id_comp, comp_id]

-- TODO: Keep this as a separate lemma...?
noncomputable def IsPullbackInducedMapIsoofIso {p : 𝒳 ⥤ 𝒮}
  {R R' S : 𝒮} {a a' b : 𝒳} {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ≅ R}
  (H : f' = g.hom ≫ f) {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback p f φ) (hφ' : IsPullback p f' φ') : a' ≅ a where
    hom := IsPullbackInducedMap hφ H hφ'.toIsHomLift
    inv := IsPullbackInducedMap hφ' (show g.inv ≫ g.hom ≫ f = g.inv ≫ f' by simp [H])
      -- TODO DO THIS BETTER.....
      (by
          rw [←assoc, g.inv_hom_id, id_comp]
          exact hφ.toIsHomLift)
    -- TODO SIMP SHOULD DO AUTOMATICALLY.....
    hom_inv_id := by
      simp only [Iso.inv_hom_id_assoc, IsPullbackInducedMap_comp, Iso.hom_inv_id, ←IsPullbackInducedMap_self_eq_id]
    inv_hom_id := by
      simp only [Iso.inv_hom_id_assoc, IsPullbackInducedMap_comp, Iso.inv_hom_id, ←IsPullbackInducedMap_self_eq_id]

noncomputable def IsPullbackIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a' a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  {φ' : a' ⟶ b} (hφ : IsPullback p f φ) (hφ' : IsPullback p f φ') : a' ≅ a :=
  IsPullbackInducedMapIsoofIso (show f = (Iso.refl R).hom ≫ f by simp) hφ hφ'

/-
Naturality API: TODO IS IT NEEDED, minimal for now.

-/
-- TODO: make ψ non-explicit... Need to fix Stacks2 first for this
noncomputable def IsPullbackNaturalityHom {p : 𝒳 ⥤ 𝒮}
  {R S : 𝒮} {a a' b b' : 𝒳} {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b'}
  (hφ : IsPullback p f φ) (hφ' : IsPullback p f φ')
  (ψ : b ⟶ b') (hψ : IsHomLift p (𝟙 S) ψ) : a ⟶ a' :=
  IsPullbackInducedMap hφ' (show (f ≫ 𝟙 S = 𝟙 R ≫ f) by simp) (IsHomLift_comp hφ.toIsHomLift hψ)


/-- Definition of a Fibered category. -/
class IsFibered (p : 𝒳 ⥤ 𝒮) : Prop where
  (has_pullbacks {a : 𝒳} {R S : 𝒮} (_ : p.obj a = S) (f : R ⟶ S) :
    ∃ (b : 𝒳) (φ : b ⟶ a), IsPullback p f φ)

/-
API FOR FIBERED CATEGORIES
-/

noncomputable def PullbackObj {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p) {R S : 𝒮}
  {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : 𝒳 :=
  Classical.choose (hp.1 ha f)

noncomputable def PullbackMap {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : PullbackObj hp ha f ⟶ a :=
  Classical.choose (Classical.choose_spec (hp.1 ha f))

lemma PullbackMapIsPullback {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : IsPullback p f (PullbackMap hp ha f) :=
  Classical.choose_spec (Classical.choose_spec (hp.1 ha f))

lemma PullbackObjLiftDomain {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : p.obj (PullbackObj hp ha f) = R := (PullbackMapIsPullback hp ha f).ObjLiftDomain

-- TODO make more readable? Then need more API. Might need to split up PullbackMapIsPullback
noncomputable def pullback_comp_iso_pullback_pullback' {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ R) :
  PullbackObj hp ha (g ≫ f) ≅ PullbackObj hp (PullbackObjLiftDomain hp ha f) g :=
  IsPullbackIso (IsPullback_comp (PullbackMapIsPullback hp (PullbackObjLiftDomain hp ha f) g) (PullbackMapIsPullback hp ha f))
      (PullbackMapIsPullback hp ha (g ≫ f))

/-
Given a diagram
    ``R × T ≅ T × R ----> R
                |       f |
                |    g    |
                T ------> S
and a : 𝒳 above S, we have a canonical isomorphism a|_R×T ≅ a|_T×R -/
noncomputable def PullbackPullbackIso'' {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ S)
  [Limits.HasPullback f g] :
    PullbackObj hp ha (@Limits.pullback.fst _ _ _ _ _ f g _≫ f)
      ≅ PullbackObj hp ha (@Limits.pullback.fst _ _ _ _ _ g f
        (Limits.hasPullback_symmetry f g) ≫ g) :=
  by
    have lem₁ : IsPullback p (@Limits.pullback.fst _ _ _ _ _ f g _≫ f)
      (PullbackMap hp ha (@Limits.pullback.fst _ _ _ _ _ f g _≫ f))
    · apply PullbackMapIsPullback hp ha (@Limits.pullback.fst _ _ _ _ _ f g _≫ f)
    have lem₂ : IsPullback p (@Limits.pullback.fst _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) ≫ g)
      (PullbackMap hp ha (@Limits.pullback.fst _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) ≫ g))
    · apply PullbackMapIsPullback hp ha
    have H : (Limits.pullbackSymmetry f g).hom ≫ (@Limits.pullback.fst _ _ _ _ _ g f
      (Limits.hasPullback_symmetry f g) ≫ g) = (@Limits.pullback.fst _ _ _ _ _ f g _≫ f)
    · rw [Limits.pullbackSymmetry_hom_comp_fst_assoc, Limits.pullback.condition]
    exact IsPullbackInducedMapIsoofIso H.symm lem₂ lem₁

noncomputable def pullback_iso_pullback'  {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ S)
  [CategoryTheory.Limits.HasPullback f g] :
  PullbackObj hp (PullbackObjLiftDomain hp ha f) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _)
    ≅ PullbackObj hp (PullbackObjLiftDomain hp ha g) (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f g _)
    :=
    Iso.trans (pullback_comp_iso_pullback_pullback' hp ha f (@Limits.pullback.fst _ _ _ _ _ f g _)).symm
    (by
      have lem₃ := pullback_comp_iso_pullback_pullback' hp ha g (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f g _)
      rwa [←Limits.pullback.condition] at lem₃)

noncomputable def PullbackPullbackIso''' {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = R) (f : R ⟶ S) (g : T ⟶ S)
  [Limits.HasPullback f g] :
    PullbackObj hp ha (@Limits.pullback.fst _ _ _ _ _ f g _) ≅
      PullbackObj hp ha (@Limits.pullback.snd _ _ _ _ _ g f (Limits.hasPullback_symmetry f g)) :=
by
  --For now this is a tactic "proof" to make it more readable. This will be easy to inline!
  have lem₁ : IsPullback p (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _)
    (PullbackMap hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _))
  · apply PullbackMapIsPullback hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _)
  have lem₂ : IsPullback p (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) )
    (PullbackMap hp ha (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) ))
  · apply PullbackMapIsPullback hp ha
  apply IsPullbackInducedMapIsoofIso (Limits.pullbackSymmetry_hom_comp_snd f g).symm lem₂ lem₁


end Fibered

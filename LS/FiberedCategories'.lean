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

instance IsHomLift_self (p : 𝒳 ⥤ 𝒮) {a b : 𝒳} (φ : a ⟶ b) : IsHomLift p (p.map φ) φ where
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
    inv := IsPullbackInducedMap hφ' (show g.inv ≫ g.hom ≫ f = g.inv ≫ f' by simp only [Iso.inv_hom_id_assoc, H])
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
  IsPullbackInducedMapIsoofIso (show f = (Iso.refl R).hom ≫ f by simp only [Iso.refl_hom, id_comp]) hφ hφ'

/-
Naturality API: TODO IS IT NEEDED, minimal for now.

-/
-- TODO: make ψ non-explicit... Need to fix Stacks2 first for this
noncomputable def IsPullbackNaturalityHom {p : 𝒳 ⥤ 𝒮}
  {R S : 𝒮} {a a' b b' : 𝒳} {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b'}
  (hφ : IsPullback p f φ) (hφ' : IsPullback p f φ')
  (ψ : b ⟶ b') (hψ : IsHomLift p (𝟙 S) ψ) : a ⟶ a' :=
  IsPullbackInducedMap hφ' (show (f ≫ 𝟙 S = 𝟙 R ≫ f) by simp only [comp_id, id_comp])
    (IsHomLift_comp hφ.toIsHomLift hψ)


/-- Definition of a Fibered category. -/
class IsFibered (p : 𝒳 ⥤ 𝒮) : Prop where
  (has_pullbacks {a : 𝒳} {R S : 𝒮} (_ : p.obj a = S) (f : R ⟶ S) :
    ∃ (b : 𝒳) (φ : b ⟶ a), IsPullback p f φ)

/- API FOR FIBERED CATEGORIES -/

/-- Given a Fibered category p : 𝒳 ⥤ 𝒫, and a diagram
```
           a
           -
           |
           v
  R --f--> S
```
we have a pullback `R ×_S a` -/
noncomputable def PullbackObj {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p) {R S : 𝒮}
  {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : 𝒳 :=
  Classical.choose (hp.1 ha f)

/-- Given a Fibered category p : 𝒳 ⥤ 𝒫, and a diagram
```
          a
          -
          |
          v
R --f--> S
```
we get a map R ×_S b ⟶ a -/
noncomputable def PullbackMap {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : PullbackObj hp ha f ⟶ a :=
  Classical.choose (Classical.choose_spec (hp.1 ha f))

lemma PullbackMapIsPullback {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : IsPullback p f (PullbackMap hp ha f) :=
  Classical.choose_spec (Classical.choose_spec (hp.1 ha f))

lemma PullbackObjLiftDomain {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : p.obj (PullbackObj hp ha f) = R := (PullbackMapIsPullback hp ha f).ObjLiftDomain

/-- Given a diagram
```
                  a
                  -
                  |
                  v
T --g--> R --f--> S
```
we have an isomorphism T ×_S a ≅ T ×_R (R ×_S a) -/
noncomputable def PullbackCompIsoPullbackPullback {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ R) :
  PullbackObj hp ha (g ≫ f) ≅ PullbackObj hp (PullbackObjLiftDomain hp ha f) g :=
  IsPullbackIso (IsPullback_comp (PullbackMapIsPullback hp (PullbackObjLiftDomain hp ha f) g)
    (PullbackMapIsPullback hp ha f))
      (PullbackMapIsPullback hp ha (g ≫ f))

/-- Given a diagram in 𝒫
```
R × T ≅ T × R ----> R
          |       f |
          |    g    |
          T ------> S
```
and a : 𝒳 above S, we have a canonical isomorphism a|_R×T ≅ a|_T×R -/
noncomputable def PullbackPullbackIso'' {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ S)
  [Limits.HasPullback f g] :
    PullbackObj hp ha (Limits.pullback.fst (f := f) (g := g) ≫ f)
      ≅ PullbackObj hp ha (@Limits.pullback.fst _ _ _ _ _ g f
        (Limits.hasPullback_symmetry f g) ≫ g) :=
  by
    have lem₁ : IsPullback p (Limits.pullback.fst (f := f) (g := g) ≫ f)
      (PullbackMap hp ha (Limits.pullback.fst (f := f) (g := g) ≫ f))
    · apply PullbackMapIsPullback hp ha (Limits.pullback.fst (f := f) (g := g) ≫ f)
    have lem₂ : IsPullback p (@Limits.pullback.fst _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) ≫ g)
      (PullbackMap hp ha (@Limits.pullback.fst _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) ≫ g))
    · apply PullbackMapIsPullback hp ha
    have H : (Limits.pullbackSymmetry f g).hom ≫ (@Limits.pullback.fst _ _ _ _ _ g f
      (Limits.hasPullback_symmetry f g) ≫ g) = (Limits.pullback.fst (f := f) (g := g) ≫ f)
    · rw [Limits.pullbackSymmetry_hom_comp_fst_assoc, Limits.pullback.condition]
    exact IsPullbackInducedMapIsoofIso H.symm lem₂ lem₁

/-- Given a diagram in 𝒫
```
R × T ≅ T × R ----> R
          |       f |
          |    g    |
          T ------> S
```

-/
noncomputable def pullback_iso_pullback'  {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ S)
  [Limits.HasPullback f g] :
  PullbackObj hp (PullbackObjLiftDomain hp ha f) (Limits.pullback.fst (f := f) (g := g))
    ≅ PullbackObj hp (PullbackObjLiftDomain hp ha g) (Limits.pullback.snd (f := f) (g := g))
    :=
    Iso.trans (PullbackCompIsoPullbackPullback hp ha f (Limits.pullback.fst (f := f) (g := g))).symm
    (by
      have lem₃ := PullbackCompIsoPullbackPullback hp ha g (Limits.pullback.snd (f := f) (g := g))
      rwa [←Limits.pullback.condition] at lem₃)

/-- Given a diagram in 𝒫
```
R × T ≅ T × R ----> R
          |       f |
          |    g    |
          T ------> S
```

-/
noncomputable def PullbackPullbackIso''' {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = R) (f : R ⟶ S) (g : T ⟶ S)
  [Limits.HasPullback f g] :
    PullbackObj hp ha (Limits.pullback.fst (f := f) (g := g)) ≅
      PullbackObj hp ha (@Limits.pullback.snd _ _ _ _ _ g f (Limits.hasPullback_symmetry f g)) :=
by
  --For now this is a tactic "proof" to make it more readable. This will be easy to inline!
  have lem₁ : IsPullback p (Limits.pullback.fst (f := f) (g := g))
    (PullbackMap hp ha (Limits.pullback.fst (f := f) (g := g)))
  · apply PullbackMapIsPullback hp ha (Limits.pullback.fst (f := f) (g := g))
  have lem₂ : IsPullback p (@Limits.pullback.snd _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) )
    (PullbackMap hp ha (@Limits.pullback.snd _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) ))
  · apply PullbackMapIsPullback hp ha
  apply IsPullbackInducedMapIsoofIso (Limits.pullbackSymmetry_hom_comp_snd f g).symm lem₂ lem₁

-- ====================================================================
-- From here and onwards this is work in progress not needed for Stacks
-- ====================================================================

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

-- We define an intrinsic notion of fibers, which we call FiberStruct
-- Fibered family
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

instance {p : 𝒳 ⥤ 𝒮} (hp : FiberStruct p) {S : 𝒮} : Faithful (hp.ι S) :=
  Faithful.of_iso (FiberInducedFunctorNat (hp.comp_const S)).symm

lemma FiberStructFull {p : 𝒳 ⥤ 𝒮} {hp : FiberStruct p} {S : 𝒮} {a b : hp.Fib S} {φ : (hp.ι S).obj a ⟶ (hp.ι S).obj b}
  (hφ : IsHomLift p (𝟙 S) φ) : ∃ (ψ : a ⟶ b), (hp.ι S).map ψ = φ := by
  -- Step 1: move φ to the "canonical" fiber over S
    -- Move ι a, ι b to the fiber over S by using FiberInducedFunctorNat (somehow (can possibly rewrite?))
    -- THIS SHOULD BE IN API "FiberHomLift" or sth
  -- rw [FiberInducedFunctorComp (hp.comp_const S)] at hφ.........
  -- Step 2: use fullness of ι S to pull back φ
  sorry

lemma FiberStructEssSurj {p : 𝒳 ⥤ 𝒮} {hp : FiberStruct p} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
  ∃ (b : hp.Fib S) (φ : (hp.ι S).obj b ⟶ a), IsIso φ ∧ IsHomLift p (𝟙 S) φ := by
  -- This will be easy to inline
  use Functor.objPreimage (FiberInducedFunctor (hp.comp_const S)) (FiberSelf ha)
  let Φ := Functor.objObjPreimageIso (FiberInducedFunctor (hp.comp_const S)) (FiberSelf ha)
  use (FiberInclusion p S).map Φ.hom
  refine ⟨inferInstance, Φ.hom.2⟩

lemma FiberStructObjLift {p : 𝒳 ⥤ 𝒮} {hp : FiberStruct p} {S : 𝒮} (a : hp.Fib S) : p.obj ((hp.ι S).obj a) = S :=
  by simp only [←comp_obj, hp.comp_const, const_obj_obj]

-- MIGHT NOT NEED....
def FiberStructMap {p : 𝒳 ⥤ 𝒮} {hp : FiberStruct p} {R S : 𝒮} {a : hp.Fib S}
  {b : hp.Fib R} (φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a) : R ⟶ S :=
    eqToHom (FiberStructObjLift b).symm ≫ (p.map φ) ≫ eqToHom (FiberStructObjLift a)
--    ((hp.comp_const R).app b).inv ≫ (p.map φ) ≫ ((hp.comp_const S).app a).hom

structure FiberedStruct (p : 𝒳 ⥤ 𝒮) extends FiberStruct p where
  [isFibered : IsFibered p]

lemma FiberStructPullback {p : 𝒳 ⥤ 𝒮} {hp : FiberedStruct p} {R S : 𝒮} (a : hp.Fib S)
  (f : R ⟶ S) : ∃ (b : hp.Fib R) (φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a), IsPullback p f φ := by
    rcases hp.isFibered.has_pullbacks (FiberStructObjLift a) f with ⟨b, φ, hφ⟩
    rcases FiberStructEssSurj hφ.ObjLiftDomain with ⟨b', ψ, hψ⟩
    use b', ψ ≫ φ
    rw [←id_comp f]
    exact IsPullback_comp (IsPullbackofIso hψ.2 hψ.1) hφ

lemma fiber_factorization {p : 𝒳 ⥤ 𝒮} (hp : FiberedStruct p) {R S : 𝒮}
  {a : hp.Fib S} {b : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a}
  (hφ : IsHomLift p f φ) : ∃ (b' : hp.Fib R)
  (τ : b ⟶ b') (ψ : (hp.ι R).obj b' ⟶ (hp.ι S).obj a), IsPullback p f ψ ∧ (((hp.ι R).map τ) ≫ ψ = φ) := by
    rcases (FiberStructPullback a f) with ⟨b', ψ, hψ⟩
    -- Let τ' be the canonical map from b to b', from the universal property of ψ (CAN REMOVE! (but makes things clearer for now))
    let τ' := IsPullbackInducedMap hψ (id_comp f).symm hφ
    -- By fullness, we can pull back τ to the fiber over R
    rcases FiberStructFull (IsPullbackInducedMap_IsHomLift hψ (id_comp f).symm hφ) with ⟨τ, hτ⟩
    use b', τ, ψ, hψ
    rw [hτ]
    exact (IsPullbackInducedMap_Diagram hψ (id_comp f).symm hφ)

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

-- NEED MORE COMMSQUARES API....
-- ALSO NEED MORE API FOR PULLING BACK TO FIBERS

lemma FiberFunctorFaithful {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {hp : FiberStruct p}
  {hq : FiberStruct q} (hF : FiberFunctor F hp hq) [Faithful F] : ∀ (S : 𝒮),
  Faithful (hF.fiber_functor S) := by
  intro S
  haveI h : Faithful ((hF.fiber_functor S) ⋙ (hq.ι S)) := (hF.comp_eq S).symm ▸ Faithful.comp (hp.ι S) F
  apply Faithful.of_comp _ (hq.ι S)

lemma FiberFunctorFaithful' {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {hp : FiberStruct p}
  {hq : FiberStruct q} {hF : FiberFunctor F hp hq} (hF₁ : ∀ (S : 𝒮), Faithful (hF.fiber_functor S)) :
  Faithful F := by
  constructor
  intro a b φ φ' hφφ'

  let h := p.map φ
  -- STEP 1: WLOG USE CANONICAL FIBER STRUCTURE!
    -- Wlog check faithful of composition --> check 2nd one is faithful
  -- Now proceed as normal...

  sorry

    -- 1. Fix "q.map φ" on the base.
    -- 2. factorize as a pullback over it
    -- 3. universal property should reduce to checking on the fiber
    -- 4. This is known!

#exit

lemma FiberFunctorsFull_of_Full {F : 𝒳 ⥤ 𝒴} {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {hp : FiberStruct p}
  {hq : FiberStruct q} (hF : FiberFunctor F hp hq) [hF₁ : Full F] : ∀ (S : 𝒮),
  Full (hF.fiber_functor S) := fun S => {
    preimage := by
      intro a b φ


      let φ₁ := ((hq.ι S).map φ)

      -- BIG ISSUE
     -- rw [←comp_obj, ←comp_obj, hF.comp_eq, comp_obj, comp_obj] at φ₁

      let φ₁ := eqToHom (comp_obj _ _ a) ≫ ((hq.ι S).map φ) ≫ eqToHom (comp_obj _ _ b).symm
      simp only [hF.comp_eq] at φ₁
      simp only [comp_obj] at φ₁
      let φ₂ := hF₁.preimage φ₁

      have hφ₂ : IsHomLift p (𝟙 S) φ₂ := {
        ObjLiftDomain := by simp only [←comp_obj, hp.comp_const]
        ObjLiftCodomain := by simp only [←comp_obj, hp.comp_const]
        HomLift := by

          constructor
          sorry
      }
      use Classical.choose (hp.full S a b φ₂ hφ₂)

    witness := by
      intro a b φ
      haveI h := (hq.faithful S)
      apply Functor.map_injective (hq.ι S)
      simp only [comp_obj, eqToHom_refl, comp_id, id_comp, eq_mp_eq_cast]
      rw [←Functor.comp_map]
      have h₁ := (hF.comp_eq S)
      --subst h₁
      sorry -- type theory helll..... :(




      -- (hq.ι S).obj
      --simp only [comp_obj, eqToHom_refl, comp_id, id_comp, eq_mp_eq_cast]

  }

/-
TODO:
2. Fully faithfull iff fully faithful!
3. Equivalence iff equivalence on fibers
-/


end Fibered

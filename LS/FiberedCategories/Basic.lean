/-
Copyright (c) 2024 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import LS.FiberedCategories.HomLift

/-!

# Fibered categories

This file defines what it means for a functor `p : 𝒳 ⥤ 𝒮` to be fibered`.

## Main definitions

- `IsHomLift p f φ` expresses that a morphism `φ` in `𝒳` is a lift of a morphism `f` in `𝒮`
along the functor `p`. This class is introduced to deal with the issues related to equalities of
morphisms in a category.
- `IsPullback p f φ` expresses that `φ` is a pullback of `f` along `p`.
- `IsFibered p` expresses that `p` gives `𝒳` the structure of a fibered category over `𝒮`,
i.e. that for every morphism `f` in `𝒮` and every object `a` in `𝒳` there is a pullback of `f`
with domain `a`.

## Implementation

-/

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category IsHomLift

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category 𝒳] [Category 𝒮]

namespace Fibered

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

/-- Definition of a Fibered category. -/
class IsFibered (p : 𝒳 ⥤ 𝒮) : Prop where
  (has_pullbacks {a : 𝒳} {R S : 𝒮} (_ : p.obj a = S) (f : R ⟶ S) :
    ∃ (b : 𝒳) (φ : b ⟶ a), IsPullback p f φ)

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
  (hφ : IsPullback p f φ) : IsPullbackInducedMap hφ (id_comp f).symm hφ.toIsHomLift = 𝟙 a:=
  (IsPullbackInducedMap_unique hφ (id_comp f).symm hφ.toIsHomLift (IsHomLift.id hφ.ObjLiftDomain) (id_comp _)).symm

-- TODO: make this standard .mk (TODO: make h hypthesis use explicit notation)
lemma IsPullback.mk' {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : b ⟶ a}
    (hφ : IsHomLift p f φ) (h : ∀ {a' : 𝒳} {g : p.obj a' ⟶ R} {φ' : a' ⟶ a},
      IsHomLift p (g ≫ f) φ' → ∃! χ : a' ⟶ b, IsHomLift p g χ ∧ χ ≫ φ = φ') :
        IsPullback p f φ where
  toIsHomLift := hφ
  UniversalProperty := by
    intro R' a' g f' hf' φ' hφ'
    have := hφ'.ObjLiftDomain.symm
    subst this
    subst hf'
    apply @h a' g φ' hφ'

lemma IsFibered.mk' {p : 𝒳 ⥤ 𝒮} (h : ∀ (a : 𝒳) (R : 𝒮) (f : R ⟶ p.obj a),
    ∃ (b : 𝒳) (φ : b ⟶ a), IsPullback p f φ) : IsFibered p where
  has_pullbacks := @fun a R S ha f => by subst ha; apply h a R f


/-- TODO: is this particular statement optional? Assumes "big" squares are commutative...
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
  · apply IsHomLift.comp
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
  toIsHomLift := IsHomLift.comp hφ.toIsHomLift hψ.toIsHomLift
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
    apply IsPullbackInducedMap_unique hψ _ _ (IsHomLift.comp hπ'.1 hφ.toIsHomLift)
    simpa only [assoc] using hπ'.2

/-- Given two commutative squares
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
such that the composite φ ≫ ψ and ψ are pullbacks, then so is φ. -/
lemma IsPullback_of_comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c: 𝒳} {f : R ⟶ S} {g : S ⟶ T}
  {φ : a ⟶ b} {ψ : b ⟶ c} (hψ : IsPullback p g ψ) (hcomp : IsPullback p (f ≫ g) (φ ≫ ψ))
  (hφ : IsHomLift p f φ) : IsPullback p f φ where
  toIsHomLift := hφ
  UniversalProperty := by
    intro U d h i hi_comp τ hi
    have h₁ : IsHomLift p (i ≫ g) (τ ≫ ψ) := IsHomLift.comp hi hψ.toIsHomLift
    have h₂ : i ≫ g = h ≫ f ≫ g := by rw [hi_comp, assoc]
    let π := IsPullbackInducedMap hcomp h₂ h₁
    existsi π
    refine ⟨⟨IsPullbackInducedMap_IsHomLift hcomp h₂ h₁, ?_⟩,?_⟩
    · have h₃ := IsHomLift.comp (IsPullbackInducedMap_IsHomLift hcomp h₂ h₁) hφ
      rw [←assoc] at h₂
      rw [IsPullbackInducedMap_unique hψ h₂ h₁ (by rwa [←hi_comp]) rfl]
      apply IsPullbackInducedMap_unique hψ h₂ h₁ h₃ _
      rw [assoc] at h₂
      rw [assoc, (IsPullbackInducedMap_Diagram hcomp h₂ h₁)]
    intro π' hπ'
    apply IsPullbackInducedMap_unique _ _ _ hπ'.1 (by rw [←hπ'.2, assoc])

lemma IsPullbackofIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳}
  {f : R ⟶ S} {φ : a ⟶ b} (hlift : IsHomLift p f φ) [IsIso φ] : IsPullback p f φ where
    toIsHomLift := hlift
    UniversalProperty := by
      intros R' a' g f' hf' φ' hφ'
      existsi φ' ≫ inv φ
      constructor
      · simp only [assoc, IsIso.inv_hom_id, comp_id, and_true]
        -- TODO: make these two lines into a lemma somehow?
        haveI := IsIso_of_lift_IsIso hlift
        have h₁ := IsHomLift.comp hφ' (IsHomLift.inv hlift)
        simp only [hf', assoc, IsIso.hom_inv_id, comp_id] at h₁
        exact h₁
      intro ψ hψ
      simp only [IsIso.eq_comp_inv, hψ.2]

/- eqToHom interactions -/
lemma IsPullback_eqToHom {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hba : b = a) {S : 𝒮} (hS : p.obj a = S) :
    IsPullback p (𝟙 S) (eqToHom hba) :=
  IsPullbackofIso (eqToHom_codomain_lift_id hba hS)

lemma IsPullback_eqToHom' {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hba : b = a) {S : 𝒮} (hS : p.obj b = S) :
    IsPullback p (𝟙 S) (eqToHom hba) :=
  IsPullbackofIso (eqToHom_domain_lift_id hba hS)

lemma IsPullback_eqToHom_comp {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b c : 𝒳} {f : R ⟶ S}
    {φ : b ⟶ a} (hφ : IsPullback p f φ) (hc : c = b) : IsPullback p f (eqToHom hc ≫ φ) :=
  id_comp f ▸ IsPullback_comp (IsPullback_eqToHom hc hφ.ObjLiftDomain) hφ

lemma IsPullback_comp_eqToHom {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b c : 𝒳} {f : R ⟶ S}
    {φ : b ⟶ a} (hφ : IsPullback p f φ) (hc : a = c) : IsPullback p f (φ ≫ eqToHom hc) :=
  comp_id f ▸ IsPullback_comp hφ (IsPullback_eqToHom' hc hφ.ObjLiftCodomain)

-- NEED TO CHECK PROOFS FROM HERE ONWARDS
lemma IsPullbackIsoofIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback p f φ) (hf : IsIso f): IsIso φ := by
  constructor
  set φ' := IsPullbackInducedMap hφ (IsIso.inv_hom_id f).symm (IsHomLift.id hφ.ObjLiftCodomain)
  existsi φ'
  refine ⟨?_, IsPullbackInducedMap_Diagram hφ (IsIso.inv_hom_id f).symm (IsHomLift.id hφ.ObjLiftCodomain)⟩
  have h₁ : IsHomLift p (𝟙 R) (φ ≫ φ') := {
    ObjLiftDomain := hφ.ObjLiftDomain
    ObjLiftCodomain := hφ.ObjLiftDomain
    HomLift := by
      constructor
      simp only [map_comp, assoc, comp_id]
      have h₁ := hφ.HomLift.1
      rw [comp_eqToHom_iff] at h₁
      rw [h₁]
      have h₂ := (IsPullbackInducedMap_IsHomLift hφ (IsIso.inv_hom_id f).symm (IsHomLift.id hφ.ObjLiftCodomain)).HomLift.1
      rw [comp_eqToHom_iff] at h₂
      rw [h₂]
      simp only [assoc, eqToHom_trans, eqToHom_refl, comp_id, eqToHom_trans_assoc, id_comp, IsIso.hom_inv_id] }
  have h₂ : IsHomLift p f (φ ≫ φ' ≫ φ) := by
    rw [IsPullbackInducedMap_Diagram hφ (IsIso.inv_hom_id f).symm (IsHomLift.id hφ.ObjLiftCodomain), comp_id]
    apply hφ.toIsHomLift
  rw [IsPullbackInducedMap_unique hφ (show f = 𝟙 R ≫ f by simp) h₂ h₁ (by apply Category.assoc)]
  apply (IsPullbackInducedMap_unique hφ (show f = 𝟙 R ≫ f by simp) _ (IsHomLift.id hφ.ObjLiftDomain) _).symm
  rw [IsPullbackInducedMap_Diagram hφ (IsIso.inv_hom_id f).symm (IsHomLift.id hφ.ObjLiftCodomain)]
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
    hom_inv_id := by
      simp only [Iso.inv_hom_id_assoc, IsPullbackInducedMap_comp, Iso.hom_inv_id, IsPullbackInducedMap_self_eq_id]
    inv_hom_id := by
      simp only [Iso.inv_hom_id_assoc, IsPullbackInducedMap_comp, Iso.inv_hom_id, IsPullbackInducedMap_self_eq_id]

noncomputable def IsPullbackIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a' a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  {φ' : a' ⟶ b} (hφ : IsPullback p f φ) (hφ' : IsPullback p f φ') : a' ≅ a :=
  IsPullbackInducedMapIsoofIso (show f = (Iso.refl R).hom ≫ f by simp only [Iso.refl_hom, id_comp]) hφ hφ'

/-- Given a diagram

      a ⟶  b
            |         above     R ⟶ S
            |
      a' ⟶ b'

`IsPullbackNaturalityHom` is induced map `a ⟶ a'`
-/
noncomputable def IsPullbackNaturalityHom {p : 𝒳 ⥤ 𝒮}
  {R S : 𝒮} {a a' b b' : 𝒳} {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b'}
  (hφ : IsPullback p f φ) (hφ' : IsPullback p f φ')
  {ψ : b ⟶ b'} (hψ : IsHomLift p (𝟙 S) ψ) : a ⟶ a' :=
  IsPullbackInducedMap hφ' (show (f ≫ 𝟙 S = 𝟙 R ≫ f) by simp only [comp_id, id_comp])
    (IsHomLift.comp hφ.toIsHomLift hψ)

/--The natural map `IsPullbackNaturalityHom : a ⟶ a'` lies above the identity -/
lemma IsPullbackNaturalityHom_IsHomLift {p : 𝒳 ⥤ 𝒮}
  {R S : 𝒮} {a a' b b' : 𝒳} {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b'}
  (hφ : IsPullback p f φ) (hφ' : IsPullback p f φ')
  {ψ : b ⟶ b'} (hψ : IsHomLift p (𝟙 S) ψ) :
  IsHomLift p (𝟙 R) (IsPullbackNaturalityHom hφ hφ' hψ) := IsPullbackInducedMap_IsHomLift _ _ _

/--The natural map `IsPullbackNaturalityHom : a ⟶ a'` makes the following diagram commute
      a ⟶  b
      |     |
      |     |
      a' ⟶ b'   -/
lemma IsPullbackNaturalityHom_CommSq {p : 𝒳 ⥤ 𝒮}
  {R S : 𝒮} {a a' b b' : 𝒳} {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b'}
  (hφ : IsPullback p f φ) (hφ' : IsPullback p f φ')
  {ψ : b ⟶ b'} (hψ : IsHomLift p (𝟙 S) ψ) :
  CommSq (IsPullbackNaturalityHom hφ hφ' hψ) φ φ' ψ where
    w := IsPullbackInducedMap_Diagram hφ' _ _

/--The map `IsPullbackNaturalityHom : a ⟶ a'` is the unique map `a ⟶ a'` above the identity that makes the following diagram commute
      a  ⟶ b
      |     |
      |     |
      a' ⟶ b'    -/
lemma IsPullbackNaturalityHom_uniqueness {p : 𝒳 ⥤ 𝒮}
  {R S : 𝒮} {a a' b b' : 𝒳} {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b'}
  (hφ : IsPullback p f φ) (hφ' : IsPullback p f φ')
  {ψ : b ⟶ b'} (hψ : IsHomLift p (𝟙 S) ψ)
  {μ : a ⟶ a'} (hμ : IsHomLift p (𝟙 R) μ)
  (hμ' : CommSq μ φ φ' ψ) : μ = IsPullbackNaturalityHom hφ hφ' hψ := IsPullbackInducedMap_unique _ _ _ hμ hμ'.w

/--If we have a diagram
      a  ⟶ b
            ||
            ||
      a  ⟶ b
then the induced map `IsPullbackNaturalityHom : a ⟶ a'` is just the identity -/
@[simp]
lemma IsPullbackNaturalityHom_id {p : 𝒳 ⥤ 𝒮}
  {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback p f φ) : IsPullbackNaturalityHom hφ hφ (IsHomLift.id hφ.toIsHomLift.ObjLiftCodomain) = 𝟙 a := by
  apply (IsPullbackNaturalityHom_uniqueness _ _ _ (IsHomLift.id hφ.ObjLiftDomain) _).symm
  constructor
  aesop

/--The construction of `IsPullbackNaturalityHom` preserves compositions. More precisely if we have
      a  ⟶ b
            |
            |
      a' ⟶ b'               above         R ⟶ S
            |
            |
      a''⟶ b''
then the diagram a ⟶ a' that arise by taking induced maps `IsPullbackNaturalityHom` commutes
                  \   |
                    \ |
                    a''                                                                     -/
@[simp]
lemma IsPullbackNaturalityHom_comp {p : 𝒳 ⥤ 𝒮}
  {R S : 𝒮} {a a' a'' b b' b'' : 𝒳} {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b'} {φ'' : a'' ⟶ b''}
  (hφ : IsPullback p f φ) (hφ' : IsPullback p f φ')
  (hφ'' : IsPullback p f φ'')
  {ψ : b ⟶ b'} (hψ : IsHomLift p (𝟙 S) ψ)
  {ψ' : b' ⟶ b''} (hψ' : IsHomLift p (𝟙 S) ψ') :
  IsPullbackNaturalityHom hφ hφ'' (lift_id_comp hψ hψ') = IsPullbackNaturalityHom hφ hφ' hψ ≫ IsPullbackNaturalityHom hφ' hφ'' hψ' := (IsPullbackNaturalityHom_uniqueness _ _ _ (lift_id_comp (IsPullbackNaturalityHom_IsHomLift _ _ _)
    (IsPullbackNaturalityHom_IsHomLift _ _ _)) (CommSq.horiz_comp (IsPullbackNaturalityHom_CommSq _ _ _) (IsPullbackNaturalityHom_CommSq _ _ _))).symm


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
  {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ S) [Limits.HasPullback f g] :
  PullbackObj hp ha (Limits.pullback.fst (f := f) (g := g) ≫ f)
    ≅ PullbackObj hp ha (@Limits.pullback.fst (f := g) (g := f) (Limits.hasPullback_symmetry f g) ≫ g) := by
  have lem₁ : IsPullback p (Limits.pullback.fst (f := f) (g := g) ≫ f)
    (PullbackMap hp ha (Limits.pullback.fst (f := f) (g := g) ≫ f)) := by
    apply PullbackMapIsPullback hp ha (Limits.pullback.fst (f := f) (g := g) ≫ f)
  have lem₂ : IsPullback p (@Limits.pullback.fst (f := g) (g := f) (Limits.hasPullback_symmetry f g)  ≫ g)
    (PullbackMap hp ha (@Limits.pullback.fst (f := g) (g := f) (Limits.hasPullback_symmetry f g) ≫ g)) := by
    apply PullbackMapIsPullback hp ha
  have H : (Limits.pullbackSymmetry f g).hom ≫ (@Limits.pullback.fst (f := g) (g := f)
    (Limits.hasPullback_symmetry f g) ≫ g) = (Limits.pullback.fst (f := f) (g := g) ≫ f) :=
    by rw [Limits.pullbackSymmetry_hom_comp_fst_assoc, Limits.pullback.condition]
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
    ≅ PullbackObj hp (PullbackObjLiftDomain hp ha g) (Limits.pullback.snd (f := f) (g := g)) :=
  Iso.trans (PullbackCompIsoPullbackPullback hp ha f (Limits.pullback.fst (f := f) (g := g))).symm (by
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
  {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = R) (f : R ⟶ S) (g : T ⟶ S) [Limits.HasPullback f g] :
  PullbackObj hp ha (Limits.pullback.fst (f := f) (g := g)) ≅
    PullbackObj hp ha (@Limits.pullback.snd _ _ _ _ _ g f (Limits.hasPullback_symmetry f g)) := by
  --For now this is a tactic "proof" to make it more readable. This will be easy to inline!
  have lem₁ : IsPullback p (Limits.pullback.fst (f := f) (g := g))
    (PullbackMap hp ha (Limits.pullback.fst (f := f) (g := g))) :=
    by apply PullbackMapIsPullback hp ha (Limits.pullback.fst (f := f) (g := g))
  have lem₂ : IsPullback p (@Limits.pullback.snd _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) )
    (PullbackMap hp ha (@Limits.pullback.snd _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) )) := by
    apply PullbackMapIsPullback hp ha
  apply IsPullbackInducedMapIsoofIso (Limits.pullbackSymmetry_hom_comp_snd f g).symm lem₂ lem₁


end Fibered

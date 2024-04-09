import LS.refactor.Basic

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category

namespace Fibered

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]


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
class IsPullback (𝒳 : BasedCategory 𝒮) {R S : 𝒮} {a b : 𝒳.1} (f : R ⟶ S) (φ : a ⟶ b)
    extends IsHomLift 𝒳 f φ : Prop where
  (UniversalProperty {R' : 𝒮} {a' : 𝒳.1} {g : R' ⟶ R} {f' : R' ⟶ S}
    (_ : f' = g ≫ f) {φ' : a' ⟶ b} (_ : IsHomLift 𝒳 f' φ') :
      ∃! χ : a' ⟶ a, IsHomLift 𝒳 g χ ∧ χ ≫ φ = φ')

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
noncomputable def IsPullbackInducedMap {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b : 𝒳.1} {f : R ⟶ S}
    {φ : a ⟶ b} (hφ : IsPullback 𝒳 f φ) {R' : 𝒮} {a' : 𝒳.1} {g : R' ⟶ R} {f' : R' ⟶ S}
    (hf' : f' = g ≫ f) {φ' : a' ⟶ b} (hφ' : IsHomLift 𝒳 f' φ') : a' ⟶ a :=
  Classical.choose $ hφ.UniversalProperty hf' hφ'

lemma IsPullbackInducedMap_IsHomLift {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b : 𝒳.1} {f : R ⟶ S}
    {φ : a ⟶ b} (hφ : IsPullback 𝒳 f φ) {R' : 𝒮} {a' : 𝒳.1} {g : R' ⟶ R} {f' : R' ⟶ S}
    (hf' : f' = g ≫ f) {φ' : a' ⟶ b} (hφ' : IsHomLift 𝒳 f' φ') :
    IsHomLift 𝒳 g (IsPullbackInducedMap hφ hf' hφ') :=
  (Classical.choose_spec (hφ.UniversalProperty hf' hφ')).1.1

@[simp]
lemma IsPullbackInducedMap_Diagram {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b : 𝒳.1} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsPullback 𝒳 f φ) {R' : 𝒮} {a' : 𝒳.1} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    {φ' : a' ⟶ b} (hφ' : IsHomLift 𝒳 f' φ') : (IsPullbackInducedMap hφ hf' hφ') ≫ φ = φ' :=
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
lemma IsPullbackInducedMap_unique {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b : 𝒳.1} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsPullback 𝒳 f φ) {R' : 𝒮} {a' : 𝒳.1} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    {φ' : a' ⟶ b} (hφ' : IsHomLift 𝒳 f' φ') {ψ : a' ⟶ a} (hψ : IsHomLift 𝒳 g ψ)
    (hcomp : ψ ≫ φ = φ') : ψ = IsPullbackInducedMap hφ hf' hφ' :=
  (Classical.choose_spec (hφ.UniversalProperty hf' hφ')).2 ψ ⟨hψ, hcomp⟩

@[simp]
lemma IsPullbackInducedMap_self_eq_id {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b : 𝒳.1} {f : R ⟶ S}
    {φ : a ⟶ b} (hφ : IsPullback 𝒳 f φ) : IsPullbackInducedMap hφ (id_comp f).symm hφ.toIsHomLift = 𝟙 a :=
  (IsPullbackInducedMap_unique hφ (id_comp f).symm hφ.toIsHomLift (IsHomLift_id hφ.ObjLiftDomain) (id_comp _)).symm

/-- TODO IS THIS PARTICULAR STATEMENT OPTIMAL? Assumes "big" squares are commutative...
```


``` -/
@[simp]
lemma IsPullbackInducedMap_comp {𝒳 : BasedCategory 𝒮} {R R' R'' S: 𝒮} {a a' a'' b : 𝒳.1}
    {f : R ⟶ S} {f' : R' ⟶ S} {f'' : R'' ⟶ S} {g : R' ⟶ R} {h : R'' ⟶ R'}
    (H : f' = g ≫ f) (H' : f'' = h ≫ f') {φ : a ⟶ b} {φ' : a' ⟶ b} {φ'' : a'' ⟶ b}
    (hφ : IsPullback 𝒳 f φ) (hφ' : IsPullback 𝒳 f' φ') (hφ'' : IsHomLift 𝒳 f'' φ'') :
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
lemma IsPullback_comp {𝒳 : BasedCategory 𝒮} {R S T : 𝒮} {a b c : 𝒳.1} {f : R ⟶ S} {g : S ⟶ T}
    {φ : a ⟶ b} {ψ : b ⟶ c} (hφ : IsPullback 𝒳 f φ) (hψ : IsPullback 𝒳 g ψ) :
    IsPullback 𝒳 (f ≫ g) (φ ≫ ψ) where
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
such that the composite φ ≫ ψ and ψ are pullbacks, then so is φ. -/
lemma IsPullback_of_comp {𝒳 : BasedCategory 𝒮} {R S T : 𝒮} {a b c : 𝒳.1} {f : R ⟶ S} {g : S ⟶ T}
  {φ : a ⟶ b} {ψ : b ⟶ c} (hψ : IsPullback 𝒳 g ψ) (hcomp : IsPullback 𝒳 (f ≫ g) (φ ≫ ψ))
  (hφ : IsHomLift 𝒳 f φ) : IsPullback 𝒳 f φ where
    toIsHomLift := hφ
    UniversalProperty := by
      intro U d h i hi_comp τ hi
      have h₁ : IsHomLift 𝒳 (i ≫ g) (τ ≫ ψ) := IsHomLift_comp hi hψ.toIsHomLift
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

lemma IsPullbackofIso {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b : 𝒳.1}
  {f : R ⟶ S} {φ : a ⟶ b} (hlift : IsHomLift 𝒳 f φ) (hφ : IsIso φ) : IsPullback 𝒳 f φ where
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

/- eqToHom interactions -/
lemma IsPullback_eqToHom {𝒳 : BasedCategory 𝒮} {a b : 𝒳.1} (hba : b = a) {S : 𝒮} (hS : 𝒳.p.obj a = S) :
    IsPullback 𝒳 (𝟙 S) (eqToHom hba) :=
  IsPullbackofIso (IsHomLift_id_eqToHom hba hS) inferInstance

lemma IsPullback_eqToHom' {𝒳 : BasedCategory 𝒮} {a b : 𝒳.1} (hba : b = a) {S : 𝒮} (hS : 𝒳.p.obj b = S) :
    IsPullback 𝒳 (𝟙 S) (eqToHom hba) :=
  IsPullbackofIso (IsHomLift_id_eqToHom' hba hS) inferInstance

lemma IsPullback_eqToHom_comp {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b c : 𝒳.1} {f : R ⟶ S}
    {φ : b ⟶ a} (hφ : IsPullback 𝒳 f φ) (hc : c = b) : IsPullback 𝒳 f (eqToHom hc ≫ φ) :=
  id_comp f ▸ IsPullback_comp (IsPullback_eqToHom hc hφ.ObjLiftDomain) hφ

lemma IsPullback_comp_eqToHom {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b c : 𝒳.1} {f : R ⟶ S}
    {φ : b ⟶ a} (hφ : IsPullback 𝒳 f φ) (hc : a = c) : IsPullback 𝒳 f (φ ≫ eqToHom hc) :=
  comp_id f ▸ IsPullback_comp hφ (IsPullback_eqToHom' hc hφ.ObjLiftCodomain)

-- NEED TO CHECK PROOFS FROM HERE ONWARDS
lemma IsPullbackIsoofIso {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b : 𝒳.1} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback 𝒳 f φ) (hf : IsIso f): IsIso φ :=
  by
    constructor
    set φ' := IsPullbackInducedMap hφ (IsIso.inv_hom_id f).symm (IsHomLift_id hφ.ObjLiftCodomain)
    existsi φ'
    refine ⟨?_, IsPullbackInducedMap_Diagram hφ (IsIso.inv_hom_id f).symm (IsHomLift_id hφ.ObjLiftCodomain)⟩
    have h₁ : IsHomLift 𝒳 (𝟙 R) (φ ≫ φ') := {
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
    }
    have h₂ : IsHomLift 𝒳 f (φ ≫ φ' ≫ φ) := by
      rw [IsPullbackInducedMap_Diagram hφ (IsIso.inv_hom_id f).symm (IsHomLift_id hφ.ObjLiftCodomain), comp_id]
      apply hφ.toIsHomLift
    rw [IsPullbackInducedMap_unique hφ (show f = 𝟙 R ≫ f by simp) h₂ h₁ (by apply Category.assoc)]
    apply (IsPullbackInducedMap_unique hφ (show f = 𝟙 R ≫ f by simp) _ (IsHomLift_id hφ.ObjLiftDomain) _).symm
    rw [IsPullbackInducedMap_Diagram hφ (IsIso.inv_hom_id f).symm (IsHomLift_id hφ.ObjLiftCodomain)]
    simp only [id_comp, comp_id]

-- TODO: Keep this as a separate lemma...?
noncomputable def IsPullbackInducedMapIsoofIso {𝒳 : BasedCategory 𝒮}
  {R R' S : 𝒮} {a a' b : 𝒳.1} {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ≅ R}
  (H : f' = g.hom ≫ f) {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback 𝒳 f φ) (hφ' : IsPullback 𝒳 f' φ') : a' ≅ a where
    hom := IsPullbackInducedMap hφ H hφ'.toIsHomLift
    inv := IsPullbackInducedMap hφ' (show g.inv ≫ g.hom ≫ f = g.inv ≫ f' by simp only [Iso.inv_hom_id_assoc, H])
      -- TODO DO THIS BETTER.....
      (by
          rw [←assoc, g.inv_hom_id, id_comp]
          exact hφ.toIsHomLift)
    -- TODO SIMP SHOULD DO AUTOMATICALLY.....
    hom_inv_id := by
      simp only [Iso.inv_hom_id_assoc, IsPullbackInducedMap_comp, Iso.hom_inv_id, IsPullbackInducedMap_self_eq_id]
    inv_hom_id := by
      simp only [Iso.inv_hom_id_assoc, IsPullbackInducedMap_comp, Iso.inv_hom_id, IsPullbackInducedMap_self_eq_id]

noncomputable def IsPullbackIso {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a' a b : 𝒳.1} {f : R ⟶ S} {φ : a ⟶ b}
  {φ' : a' ⟶ b} (hφ : IsPullback 𝒳 f φ) (hφ' : IsPullback 𝒳 f φ') : a' ≅ a :=
  IsPullbackInducedMapIsoofIso (show f = (Iso.refl R).hom ≫ f by simp only [Iso.refl_hom, id_comp]) hφ hφ'

/-
Naturality API: TODO IS IT NEEDED, minimal for now.

-/
-- TODO: make ψ non-explicit... Need to fix Stacks2 first for this
noncomputable def IsPullbackNaturalityHom {𝒳 : BasedCategory 𝒮}
  {R S : 𝒮} {a a' b b' : 𝒳.1} {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b'}
  (hφ : IsPullback 𝒳 f φ) (hφ' : IsPullback 𝒳 f φ')
  (ψ : b ⟶ b') (hψ : IsHomLift 𝒳 (𝟙 S) ψ) : a ⟶ a' :=
  IsPullbackInducedMap hφ' (show (f ≫ 𝟙 S = 𝟙 R ≫ f) by simp only [comp_id, id_comp])
    (IsHomLift_comp hφ.toIsHomLift hψ)


/-- Definition of a Fibered category. -/
class IsFibered (𝒳 : BasedCategory 𝒮) : Prop where
  (has_pullbacks {a : 𝒳.1} {R S : 𝒮} (_ : 𝒳.p.obj a = S) (f : R ⟶ S) :
    ∃ (b : 𝒳.1) (φ : b ⟶ a), IsPullback 𝒳 f φ)

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
noncomputable def PullbackObj {𝒳 : BasedCategory 𝒮} (hp : IsFibered 𝒳) {R S : 𝒮}
  {a : 𝒳.1} (ha : 𝒳.p.obj a = S) (f : R ⟶ S) : 𝒳.1 :=
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
noncomputable def PullbackMap {𝒳 : BasedCategory 𝒮} (hp : IsFibered 𝒳)
  {R S : 𝒮} {a : 𝒳.1} (ha : 𝒳.p.obj a = S) (f : R ⟶ S) : PullbackObj hp ha f ⟶ a :=
  Classical.choose (Classical.choose_spec (hp.1 ha f))

lemma PullbackMapIsPullback {𝒳 : BasedCategory 𝒮} (hp : IsFibered 𝒳)
  {R S : 𝒮} {a : 𝒳.1} (ha : 𝒳.p.obj a = S) (f : R ⟶ S) : IsPullback 𝒳 f (PullbackMap hp ha f) :=
  Classical.choose_spec (Classical.choose_spec (hp.1 ha f))

lemma PullbackObjLiftDomain {𝒳 : BasedCategory 𝒮} (hp : IsFibered 𝒳)
  {R S : 𝒮} {a : 𝒳.1} (ha : 𝒳.p.obj a = S) (f : R ⟶ S) : 𝒳.p.obj (PullbackObj hp ha f) = R := (PullbackMapIsPullback hp ha f).ObjLiftDomain

/-- Given a diagram
```
                  a
                  -
                  |
                  v
T --g--> R --f--> S
```
we have an isomorphism T ×_S a ≅ T ×_R (R ×_S a) -/
noncomputable def PullbackCompIsoPullbackPullback {𝒳 : BasedCategory 𝒮} (hp : IsFibered 𝒳)
  {R S T : 𝒮} {a : 𝒳.1} (ha : 𝒳.p.obj a = S) (f : R ⟶ S) (g : T ⟶ R) :
  PullbackObj hp ha (g ≫ f) ≅ PullbackObj hp (PullbackObjLiftDomain hp ha f) g :=
  IsPullbackIso (IsPullback_comp (PullbackMapIsPullback hp (PullbackObjLiftDomain hp ha f) g)
    (PullbackMapIsPullback hp ha f))
      (PullbackMapIsPullback hp ha (g ≫ f))

end Fibered

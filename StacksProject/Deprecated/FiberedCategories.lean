/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
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

/--
MORE FLEXIBLE API
-/

def HomLift' {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
 (ha : p.obj a = R) (hb : p.obj b = S) : Prop :=
  CommSq (p.map φ) (eqToHom ha) (eqToHom hb) f

lemma HomLift'_id {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a : 𝒳} (ha : p.obj a = R) : HomLift' (𝟙 R) (𝟙 a) ha ha := by
  constructor ; simp only [map_id, id_comp, comp_id]

lemma HomLift'_self (p : 𝒳 ⥤ 𝒮) {a b : 𝒳} (φ : a ⟶ b) : HomLift' (p.map φ) φ rfl rfl :=
  ⟨by simp only [eqToHom_refl, comp_id, id_comp]⟩

-- TODO make instance somehow
lemma IsIsoofHomlift'Iso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {ha : p.obj a = R} {hb : p.obj b = S}
  {f : R ⟶ S} {φ : a ⟶ b} (hlift : HomLift' f φ ha hb) (hφ : IsIso φ) : IsIso f := by
  rcases hlift with ⟨hlift⟩
  rw [←eqToHom_comp_iff ha.symm] at hlift
  rw [←hlift]
  exact IsIso.comp_isIso

-- TODO INFER IsIso f SOMEHOW
lemma HomLift'_inv {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {ha : p.obj a = R} {hb : p.obj b = S}
  {f : R ⟶ S} {φ : a ⟶ b} (hlift : HomLift' f φ ha hb) (hφ : IsIso φ) (hf : IsIso f) :
  HomLift' (inv f) (inv φ) hb ha :=
  by
    constructor
    simp only [map_inv, IsIso.eq_comp_inv, assoc, IsIso.inv_comp_eq]
    exact hlift.1.symm

lemma HomLift'_comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c : 𝒳} {ha : p.obj a = R} {hb : p.obj b = S}
  {hc : p.obj c = T} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c} (hφ : HomLift' f φ ha hb)
  (hψ : HomLift' g ψ hb hc) : HomLift' (f ≫ g) (φ ≫ ψ) ha hc :=
  by
    constructor
    rw [←Category.assoc, ←hφ.1]
    simp only [map_comp, assoc, hψ.1]

class IsPullback' (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) : Prop where
  (ObjLiftDomain : p.obj a = R)
  (ObjLiftCodomain : p.obj b = S)
  (HomLift : HomLift' f φ ObjLiftDomain ObjLiftCodomain)
  (UniversalProperty {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (_ : f' = g ≫ f)
  {ha' : p.obj a' = R'} {φ' : a' ⟶ b} (_ : HomLift' f' φ' ha' ObjLiftCodomain) :
    ∃! χ : a' ⟶ a, HomLift' g χ ha' ObjLiftDomain ∧ χ ≫ φ = φ')

/--
Given:
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S

With φ a pullback and φ' : a' ⟶ b, gets the induced map from a' to a from the universal property.
-/

-- TODO IsPullback' should be in []??
noncomputable def IsPullback'InducedMap {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback' p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
  {ha' : p.obj a' = R'} {φ' : a' ⟶ b} (hφ' : HomLift' f' φ' ha' hφ.ObjLiftCodomain) : a' ⟶ a :=
  Classical.choose $ hφ.UniversalProperty hf' hφ'

lemma IsPullback'InducedMap_HomLift {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback' p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
  {ha' : p.obj a' = R'} {φ' : a' ⟶ b} (hφ' : HomLift' f' φ' ha' hφ.ObjLiftCodomain) :
  HomLift' g (IsPullback'InducedMap hφ hf' hφ') ha' hφ.ObjLiftDomain :=
  (Classical.choose_spec (hφ.UniversalProperty hf' hφ')).1.1

@[simp]
lemma IsPullback'InducedMap_Diagram {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback' p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
  {ha' : p.obj a' = R'} {φ' : a' ⟶ b} (hφ' : HomLift' f' φ' ha' hφ.ObjLiftCodomain) :
  (IsPullback'InducedMap hφ hf' hφ') ≫ φ = φ' :=
  (Classical.choose_spec (hφ.UniversalProperty hf' hφ')).1.2


/--
Given:
a' --ψ-->a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S

With φ a pullback φ' : a' ⟶ b, s.t. ψ ≫ φ = φ'. Then ψ is the induced Pullback map

-/
lemma IsPullback'InducedMap_unique {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback' p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
  {ha' : p.obj a' = R'} {φ' : a' ⟶ b} (hφ' : HomLift' f' φ' ha' hφ.ObjLiftCodomain)
  {ψ : a' ⟶ a} (hψ : HomLift' g ψ ha' hφ.ObjLiftDomain) (hcomp : ψ ≫ φ = φ'):
  ψ = IsPullback'InducedMap hφ hf' hφ' :=
  (Classical.choose_spec (hφ.UniversalProperty hf' hφ')).2 ψ ⟨hψ, hcomp⟩

@[simp]
lemma IsPullback'InducedMap_self_eq_id {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback' p f φ) : 𝟙 a = IsPullback'InducedMap hφ (show f = 𝟙 R ≫ f by simp) hφ.HomLift :=
  IsPullback'InducedMap_unique hφ (show f = 𝟙 R ≫ f by simp) hφ.HomLift (HomLift'_id _) (id_comp _)

@[simp]
lemma IsPullback'InducedMap_comp {p : 𝒳 ⥤ 𝒮}
  {R R' R'' S: 𝒮} {a a' a'' b : 𝒳} (ha'' : p.obj a'' = R'')
  {f : R ⟶ S} {f' : R' ⟶ S} {f'' : R'' ⟶ S} {g : R' ⟶ R} {h : R'' ⟶ R'}
  (H : f' = g ≫ f) (H' : f'' = h ≫ f') {φ : a ⟶ b} {φ' : a' ⟶ b} {φ'' : a'' ⟶ b}
  (hφ : IsPullback' p f φ) (hφ' : IsPullback' p f' φ') (hφ'' : HomLift' f'' φ'' ha'' hφ.2) :
  -- hφ'' MIGHT JUST NEED TO BE HOMLIFT
  IsPullback'InducedMap hφ' H' hφ'' ≫ IsPullback'InducedMap hφ H hφ'.HomLift
  = IsPullback'InducedMap hφ (show f'' = (h ≫ g) ≫ f by rwa [assoc, ←H]) hφ'' := by
  apply IsPullback'InducedMap_unique
  · apply HomLift'_comp
    apply IsPullback'InducedMap_HomLift
    apply IsPullback'InducedMap_HomLift
  · simp only [assoc, IsPullback'InducedMap_Diagram]

--lemma IsPullback'InducedMap_comp

def IsPullback'_comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c: 𝒳} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b}
  {ψ : b ⟶ c} (hφ : IsPullback' p f φ) (hψ : IsPullback' p g ψ) : IsPullback' p (f ≫ g) (φ ≫ ψ) where
    ObjLiftDomain := hφ.ObjLiftDomain
    ObjLiftCodomain := hψ.ObjLiftCodomain
    HomLift := HomLift'_comp hφ.HomLift hψ.HomLift
    UniversalProperty := by
      intro U d h i hi_comp hd τ hi
      rw [←assoc] at hi_comp
      set τ' := IsPullback'InducedMap hψ hi_comp hi
      set π := IsPullback'InducedMap hφ rfl (IsPullback'InducedMap_HomLift hψ hi_comp hi)
      existsi π
      refine ⟨⟨IsPullback'InducedMap_HomLift hφ rfl (IsPullback'InducedMap_HomLift hψ hi_comp hi), ?_⟩, ?_⟩
      · rw [←(IsPullback'InducedMap_Diagram hψ hi_comp hi)]
        rw [←(IsPullback'InducedMap_Diagram hφ rfl (IsPullback'InducedMap_HomLift hψ hi_comp hi)), assoc]
      intro π' hπ'
      apply IsPullback'InducedMap_unique hφ _ _ hπ'.1
      apply IsPullback'InducedMap_unique hψ _ _ (HomLift'_comp hπ'.1 hφ.HomLift)
      simpa only [assoc] using hπ'.2

def IsPullback'_of_comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c: 𝒳} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b}
  {ψ : b ⟶ c} (hψ : IsPullback' p g ψ) (hcomp : IsPullback' p (f ≫ g) (φ ≫ ψ))
  (hφ : HomLift' f φ hcomp.1 hψ.1) : IsPullback' p f φ where
    ObjLiftDomain := hcomp.ObjLiftDomain
    ObjLiftCodomain := hψ.ObjLiftDomain
    HomLift := hφ
    UniversalProperty := by
      intro U d h i hi_comp hd τ hi
      have h₁ := HomLift'_comp hi hψ.HomLift
      have h₂ : i ≫ g = h ≫ f ≫ g := by rw [hi_comp, assoc]
      set π := IsPullback'InducedMap hcomp h₂ h₁ with hπ
      existsi π
      refine ⟨⟨IsPullback'InducedMap_HomLift hcomp h₂ h₁, ?_⟩,?_⟩
      · have h₃ := IsPullback'InducedMap_HomLift hcomp h₂ h₁
        rw [←assoc] at h₂
        have h₄ := HomLift'_comp h₃ hφ
        have h₅ : τ = IsPullback'InducedMap hψ h₂ h₁ :=
          IsPullback'InducedMap_unique hψ h₂ h₁ (by rwa [←hi_comp]) rfl
        rw [h₅]
        apply IsPullback'InducedMap_unique hψ h₂ h₁ h₄ _
        rw [assoc] at h₂
        rw [assoc, (IsPullback'InducedMap_Diagram hcomp h₂ h₁)]
      intro π' hπ'
      apply IsPullback'InducedMap_unique _ _ _ hπ'.1 (by rw [←hπ'.2, assoc])

lemma IsPullback'ofIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {ha : p.obj a = R} {hb : p.obj b = S}
  {f : R ⟶ S} {φ : a ⟶ b} (hlift : HomLift' f φ ha hb) (hφ : IsIso φ) : IsPullback' p f φ where
    ObjLiftDomain := ha
    ObjLiftCodomain := hb
    HomLift := hlift
    UniversalProperty := by
      intros R' a' g f' hf' ha' φ' hφ'
      existsi φ' ≫ inv φ
      constructor
      · simp only [assoc, IsIso.inv_hom_id, comp_id, and_true]
        -- TODO THIS SHOULD BE INFERED...
        haveI hhh : IsIso f := IsIsoofHomlift'Iso hlift hφ
        have h₁ := HomLift'_comp hφ' (HomLift'_inv hlift hφ hhh)
        simp only [hf', assoc, IsIso.hom_inv_id, comp_id] at h₁
        exact h₁
      intro ψ hψ
      simp only [IsIso.eq_comp_inv, hψ.2]

lemma IsPullback'IsoofIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback' p f φ) (hf : IsIso f): IsIso φ :=
  by
    constructor
    set φ' := IsPullback'InducedMap hφ (IsIso.inv_hom_id f).symm (HomLift'_id _)
    existsi φ'
    refine ⟨?_, IsPullback'InducedMap_Diagram hφ (IsIso.inv_hom_id f).symm (HomLift'_id _)⟩
    have h₁ : HomLift' (𝟙 R) (φ ≫ φ') hφ.1 hφ.1 := by
      constructor
      simp only [map_comp, assoc, comp_id]
      have h₁ := hφ.3.1
      rw [comp_eqToHom_iff] at h₁
      rw [h₁]
      have h₂ := (IsPullback'InducedMap_HomLift hφ (IsIso.inv_hom_id f).symm (HomLift'_id _)).1
      rw [comp_eqToHom_iff] at h₂
      rw [h₂]
      simp only [assoc, eqToHom_trans, eqToHom_refl, comp_id, eqToHom_trans_assoc, id_comp, IsIso.hom_inv_id]
    have h₂ : HomLift' f (φ ≫ φ' ≫ φ) hφ.1 hφ.2 := by
      rw [IsPullback'InducedMap_Diagram hφ (IsIso.inv_hom_id f).symm (HomLift'_id _), comp_id]
      apply hφ.3
    rw [IsPullback'InducedMap_unique hφ (show f = 𝟙 R ≫ f by simp) h₂ h₁ (by apply Category.assoc)]
    apply (IsPullback'InducedMap_unique hφ (show f = 𝟙 R ≫ f by simp) _ (HomLift'_id hφ.1) _).symm
    rw [IsPullback'InducedMap_Diagram hφ (IsIso.inv_hom_id f).symm (HomLift'_id _)]
    simp only [id_comp, comp_id]

-- TODO: Keep this as a separate lemma...?
noncomputable def IsPullback'InducedMapIsoofIso {p : 𝒳 ⥤ 𝒮}
  {R R' S : 𝒮} {a a' b : 𝒳} {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ≅ R}
  (H : f' = g.hom ≫ f) {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback' p f φ) (hφ' : IsPullback' p f' φ') : a' ≅ a where
    hom := IsPullback'InducedMap hφ H hφ'.HomLift
    inv := IsPullback'InducedMap hφ' (show g.inv ≫ g.hom ≫ f = g.inv ≫ f' by simp [H])
      -- TODO DO THIS BETTER.....
      (by
          rw [←assoc, g.inv_hom_id, id_comp]
          exact hφ.HomLift)
    -- TODO SIMP SHOULD DO AUTOMATICALLY.....
    hom_inv_id := by
      simp only [Iso.inv_hom_id_assoc, IsPullback'InducedMap_comp, Iso.hom_inv_id, ←IsPullback'InducedMap_self_eq_id]
    inv_hom_id := by
      simp only [Iso.inv_hom_id_assoc, IsPullback'InducedMap_comp, Iso.inv_hom_id, ←IsPullback'InducedMap_self_eq_id]

noncomputable def IsPullback'Iso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a' a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  {φ' : a' ⟶ b} (hφ : IsPullback' p f φ) (hφ' : IsPullback' p f φ') : a' ≅ a :=
  IsPullback'InducedMapIsoofIso (show f = (Iso.refl R).hom ≫ f by simp) hφ hφ'

/-
Naturality API: TODO IS IT NEEDED, minimal for now.

-/

-- TODO: make ψ non-explicit... Need to fix Stacks2 first for this
noncomputable def IsPullback'NaturalityHom {p : 𝒳 ⥤ 𝒮}
  {R S : 𝒮} {a a' b b' : 𝒳} {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b'}
  (hφ : IsPullback' p f φ) (hφ' : IsPullback' p f φ')
  (ψ : b ⟶ b') (hψ : HomLift' (𝟙 S) ψ hφ.2 hφ'.2) : a ⟶ a' :=
  IsPullback'InducedMap hφ' (show (f ≫ 𝟙 S = 𝟙 R ≫ f) by simp) (HomLift'_comp hφ.3 hψ)


/-- Definition of a Fibered category. -/
class IsFibered (p : 𝒳 ⥤ 𝒮) : Prop where
  (has_pullbacks {a : 𝒳} {R S : 𝒮} (_ : p.obj a = S) (f : R ⟶ S) :
    ∃ (b : 𝒳) (φ : b ⟶ a), IsPullback' p f φ)

/-
API FOR FIBERED CATEGORIES
-/

noncomputable def PullbackObj' {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p) {R S : 𝒮}
  {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : 𝒳 :=
  Classical.choose (hp.1 ha f)

noncomputable def PullbackMap' {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : PullbackObj' hp ha f ⟶ a :=
  Classical.choose (Classical.choose_spec (hp.1 ha f))

lemma PullbackMap'IsPullback {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : IsPullback' p f (PullbackMap' hp ha f) :=
  Classical.choose_spec (Classical.choose_spec (hp.1 ha f))

lemma PullbackObjLiftDomain {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : p.obj (PullbackObj' hp ha f) = R := (PullbackMap'IsPullback hp ha f).1

-- TODO make more readable? Then need more API. Might need to split up PullbackMap'IsPullback
noncomputable def pullback_comp_iso_pullback_pullback' {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ R) :
  PullbackObj' hp ha (g ≫ f) ≅ PullbackObj' hp (PullbackObjLiftDomain hp ha f) g :=
  IsPullback'Iso (IsPullback'_comp (PullbackMap'IsPullback hp (PullbackObjLiftDomain hp ha f) g) (PullbackMap'IsPullback hp ha f))
      (PullbackMap'IsPullback hp ha (g ≫ f))

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
    PullbackObj' hp ha (@Limits.pullback.fst _ _ _ _ _ f g _ ≫ f)
      ≅ PullbackObj' hp ha (@Limits.pullback.fst _ _ _ _ _ g f
        (Limits.hasPullback_symmetry f g) ≫ g) :=
  by
    have lem₁ : IsPullback' p (@Limits.pullback.fst _ _ _ _ _ f g _≫ f)
      (PullbackMap' hp ha (@Limits.pullback.fst _ _ _ _ _ f g _≫ f))
    · apply PullbackMap'IsPullback hp ha (@Limits.pullback.fst _ _ _ _ _ f g _≫ f)
    have lem₂ : IsPullback' p (@Limits.pullback.fst _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) ≫ g)
      (PullbackMap' hp ha (@Limits.pullback.fst _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) ≫ g))
    · apply PullbackMap'IsPullback hp ha
    have H : (Limits.pullbackSymmetry f g).hom ≫ (@Limits.pullback.fst _ _ _ _ _ g f
      (Limits.hasPullback_symmetry f g) ≫ g) = (@Limits.pullback.fst _ _ _ _ _ f g _≫ f)
    · rw [Limits.pullbackSymmetry_hom_comp_fst_assoc, Limits.pullback.condition]
    exact IsPullback'InducedMapIsoofIso H.symm lem₂ lem₁

noncomputable def pullback_iso_pullback'  {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ S)
  [CategoryTheory.Limits.HasPullback f g] :
  PullbackObj' hp (PullbackObjLiftDomain hp ha f) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _)
    ≅ PullbackObj' hp (PullbackObjLiftDomain hp ha g) (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f g _)
    :=
    Iso.trans (pullback_comp_iso_pullback_pullback' hp ha f (@Limits.pullback.fst _ _ _ _ _ f g _)).symm
    (by
      have lem₃ := pullback_comp_iso_pullback_pullback' hp ha g (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f g _)
      rwa [←Limits.pullback.condition] at lem₃)

noncomputable def PullbackPullbackIso''' {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
  {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = R) (f : R ⟶ S) (g : T ⟶ S)
  [Limits.HasPullback f g] :
    PullbackObj' hp ha (@Limits.pullback.fst _ _ _ _ _ f g _) ≅
      PullbackObj' hp ha (@Limits.pullback.snd _ _ _ _ _ g f (Limits.hasPullback_symmetry f g)) :=
by
  --For now this is a tactic "proof" to make it more readable. This will be easy to inline!
  have lem₁ : IsPullback' p (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _)
    (PullbackMap' hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _))
  · apply PullbackMap'IsPullback hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _)
  have lem₂ : IsPullback' p (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) )
    (PullbackMap' hp ha (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ g f (Limits.hasPullback_symmetry f g) ))
  · apply PullbackMap'IsPullback hp ha
  apply IsPullback'InducedMapIsoofIso (Limits.pullbackSymmetry_hom_comp_snd f g).symm lem₂ lem₁

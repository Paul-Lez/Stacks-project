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

-- TODO move variable D later
variable {S : Type u₁} {C : Type u₂} {D : Type u₃} [Category S] [Category C] [Category D]

/-
Defining when an arrow is cartesian (see Olssons book)
Strongly cartesian in the stacks project

-/

class IsCartesian (p : C ⥤ S) {x y : C} (φ : y ⟶ x) : Prop where
  (isCartesian {z : C} {ψ : z ⟶ x} {f : p.obj z ⟶ p.obj y} (hy : f ≫ (p.map φ) = p.map ψ) :
    ∃! (χ : z ⟶ y), (χ ≫ φ = ψ) ∧ f = p.map χ)

/--
The composition of two cartesian arrows is cartesian
-/
lemma IsCartesian.comp (p : C ⥤ S) {x y z : C} (ψ : z ⟶ y) (φ : y ⟶ x)
  [hψ : IsCartesian p ψ] [hφ : IsCartesian p φ] : IsCartesian p (ψ ≫ φ) :=
  by
    constructor
    intro a τ f hfcomp
    rcases hφ with ⟨hφ⟩
    rw [map_comp, ←assoc] at hfcomp
    rcases hφ hfcomp with ⟨τ', ⟨hφcomp, hφproj⟩, τ'_unique⟩
    rcases hψ with ⟨hψ⟩
    rcases hψ hφproj with ⟨π, ⟨hcomp2, hproj2⟩, π_unique⟩
    existsi π
    refine ⟨⟨?_, hproj2⟩, ?_⟩
    · rw [←assoc, hcomp2]
      exact hφcomp
    rintro π' ⟨hπ'comp, hπ'proj⟩
    apply π_unique
    refine ⟨?_, hπ'proj⟩
    apply τ'_unique
    constructor
    · rw [assoc]
      exact hπ'comp
    simp only [hπ'proj, map_comp]

/--
Given a cartesian morphism ψ ≫ φ such that φ is cartesian, then so must ψ be. (TODO: make iff)
-/
lemma IsCartesian.comp_of_cartesian (p : C ⥤ S) {x y z : C} (ψ : z ⟶ y) (φ : y ⟶ x) [hφ : IsCartesian p φ]
  [hcomp : IsCartesian p (ψ ≫ φ)] : IsCartesian p ψ :=
  by
    constructor
    intro a τ f hfcomp
    rcases hcomp with ⟨hcomp⟩
    have h1 : f ≫ p.map (ψ ≫ φ) = p.map (τ ≫ φ) :=
      by rw [map_comp, ←assoc, hfcomp, map_comp]
    rcases hcomp h1 with ⟨π, ⟨hπcomp, hπproj⟩, π_unique⟩
    existsi π
    refine ⟨⟨?_, hπproj⟩, ?_⟩
    · have h2 : (f ≫ p.map ψ) ≫ p.map φ = p.map (τ ≫ φ) :=
        by simp only [hπproj, assoc, ←hπcomp, map_comp]
      rcases hφ with ⟨hφ⟩
      rcases hφ h2 with ⟨τ', ⟨_, hτ'proj⟩, τ'_unique⟩
      rw [τ'_unique τ ⟨rfl, hfcomp⟩]
      apply τ'_unique
      aesop -- TODO REPLACE?
    rintro π' ⟨hπ'comp, hπ'proj⟩
    apply π_unique
    refine ⟨?_, hπ'proj⟩
    simp only [←hπ'comp, assoc]

/--
Isomorphisms are cartesian.
-/
lemma iso_iscartesian (p : C ⥤ S) {x y : C} (φ : y ⟶ x) [IsIso φ] : IsCartesian p φ :=
  by
    constructor
    intros z ψ f hy
    existsi ψ ≫ inv φ
    constructor
    · constructor
      · simp only [assoc, IsIso.inv_hom_id, comp_id]
      simp only [map_comp, map_inv, IsIso.eq_comp_inv, hy]
    intro ψ' hψ'
    simp only [IsIso.eq_comp_inv, hψ'.1]

/--
A cartesian arrow such that its projection is an isomorphism, must also be an isomorphism.
-/
lemma isiso_of_cartesian (p : C ⥤ S) {x y : C} (φ : y ⟶ x) [hiso : IsIso (p.map φ)]
  [hcart : IsCartesian p φ] : IsIso φ :=
  by
    constructor
    rcases hcart with ⟨hcart⟩
    have heq : inv (p.map φ) ≫ p.map φ = p.map (𝟙 x) :=
      by simp only [IsIso.inv_hom_id, map_id]
    rcases (hcart heq) with ⟨φinv, ⟨hcomp, hproj⟩, _⟩
    existsi φinv
    refine ⟨?_, hcomp⟩
    have heq2 : p.map (φ ≫ φinv) ≫ p.map φ = p.map (φ) :=
      by
        simp only [map_comp]
        rw [←hproj]
        simp only [IsIso.hom_inv_id, id_comp]
    rcases (hcart heq2) with ⟨φ', _, hunique2⟩
    have hh : 𝟙 y = φ' :=
      by
        apply hunique2
        simp only [id_comp, map_comp, map_id, true_and]
        rw [←hproj]
        simp only [IsIso.hom_inv_id]
    rw [hh]
    apply hunique2
    simp only [assoc, hcomp, comp_id, map_comp, and_self]


variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category 𝒳] [Category 𝒮]
/--
MORE FLEXIBLE API
-/

def HomLift' {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
 (ha : p.obj a = R) (hb : p.obj b = S) : Prop :=
  CommSq (p.map φ) (eqToHom ha) (eqToHom hb) f

lemma HomLift'_id {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a : 𝒳} (ha : p.obj a = R) : HomLift' (𝟙 R) (𝟙 a) ha ha :=
  by
    constructor
    simp only [map_id, id_comp, comp_id]

def HomLift'_self (p : 𝒳 ⥤ 𝒮) {a b : 𝒳} (φ : a ⟶ b) : HomLift' (p.map φ) φ rfl rfl :=
  ⟨by simp only [eqToHom_refl, comp_id, id_comp]⟩

-- TODO make instance somehow
lemma IsIsoofHomlift'Iso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {ha : p.obj a = R} {hb : p.obj b = S}
  {f : R ⟶ S} {φ : a ⟶ b} (hlift : HomLift' f φ ha hb) (hφ : IsIso φ) : IsIso f :=
  by
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
  (UniversalProperty {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
  {ha' : p.obj a' = R'} {φ' : a' ⟶ b} (hφ' : HomLift' f' φ' ha' ObjLiftCodomain) :
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
  = IsPullback'InducedMap hφ (show f'' = (h ≫ g) ≫ f by rwa [assoc, ←H]) hφ'' := sorry

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
      simp only [assoc]
      exact hπ'.2

--noncomputable def IsPullbackNaturalityHom

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
    UniversalProperty :=
    by
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
    have h₁ : HomLift' (𝟙 R) (φ ≫ φ') hφ.1 hφ.1 :=
      by
        constructor
        simp only [map_comp, assoc, comp_id]
        have h₁ := hφ.3.1
        rw [comp_eqToHom_iff] at h₁
        rw [h₁]
        have h₂ := (IsPullback'InducedMap_HomLift hφ (IsIso.inv_hom_id f).symm (HomLift'_id _)).1
        rw [comp_eqToHom_iff] at h₂
        rw [h₂]
        simp only [assoc, eqToHom_trans, eqToHom_refl, comp_id, eqToHom_trans_assoc, id_comp, IsIso.hom_inv_id]
    have h₂ : HomLift' f (φ ≫ φ' ≫ φ) hφ.1 hφ.2 :=
      by
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


/-
TODO:
Naturality (Do we really need this? Maybe not if we work w/ isos instead of ids on base)
-/

/-- Definition of a Fibered category. -/
class IsFibered (p : 𝒳 ⥤ 𝒮) : Prop where
  (has_pullbacks {a : 𝒳} {R S : 𝒮} (ha : p.obj a = S) (f : R ⟶ S) :
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
    PullbackObj' hp ha (@Limits.pullback.fst _ _ _ _ _ f g _≫ f)
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

def Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮) := {a : 𝒳 // p.obj a = S}

def Fiber.self (p : 𝒳 ⥤ 𝒮) (a : 𝒳) : Fiber p (p.obj a) := ⟨a, rfl⟩

-- TODO DO I EVEN NEED?
@[simp]
lemma Fiber.self_coe (p : 𝒳 ⥤ 𝒮) (a : 𝒳) : (Fiber.self p a).val = a := rfl

instance Fiber.category (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : Category (Fiber p S) where
  Hom a b := {φ : a.val ⟶ b.val // (p.map φ) ≫ (eqToHom b.prop) = (eqToHom a.prop)}
  id a := ⟨𝟙 a.val,
    by
      simp only [map_id, id_comp, comp_id]⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val,
    by
      simp only [map_comp, assoc, comp_id]
      rw [ψ.prop, φ.prop]⟩

def Fiber.functor (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : (Fiber p S) ⥤ 𝒳 where
  obj := Subtype.val
  map := Subtype.val

/-
class HasFibers (p : 𝒳 ⥤ 𝒮) where
  Fib (S : 𝒮) : Type v₁
  [isCategory : Category (Fib (S : 𝒮))]
  (fiber_equiv (S : 𝒮)  : Fib S ≌ Fiber p S) -/

-- def HasFibers.functor (p : C ⥤ S) (s : S) [hp : HasFibers p] := (hp.fiber_equiv s).functor

/-
def Fiber.comp_const (p : C ⥤ S) (s : S) : (Fiber.functor p s) ⋙ p ≅ (const (Fiber p s)).obj s where
  hom := {
    app :=
    by
      intro x
      exact eqToHom x.prop
    naturality :=
    by
      intros x y f
      simp only [comp_obj, const_obj_obj, Functor.comp_map, const_obj_map, comp_id]
      exact f.prop
  }
  inv := {
    app :=
    by
      intro x
      exact eqToHom (x.prop).symm
    naturality :=
    by
      intros x y f
      simp only [const_obj_obj, comp_obj, const_obj_map, id_comp, Functor.comp_map]
      rw [←(eqToHom_comp_iff x.prop), comp_eqToHom_iff]
      exact f.prop.symm
  }


class HasFibers (p : C ⥤ S) where
  Fib (s : S) : Type v₁
  [isCategory : Category (Fib s)]
  (fiber_functor (s : S) : (Fib s) ⥤ C)
  (comp_const (s : S) : fiber_functor s ⋙ p ≅ (const (Fib s)).obj s)
  (has_pullbacks {s t : S} {x : Fib s}  (f : t ⟶ s) :
    ∃ (y : Fib t) (φ : (fiber_functor t).obj y ⟶ (fiber_functor s).obj x),
      CommSq (p.map φ) ((comp_const t).hom.app y) ((comp_const s).hom.app x) f ∧ IsCartesian p φ)

instance canonical_fiber (p : C ⥤ S) [hp : IsFibered p] : HasFibers p where
  Fib :=
    by
      intro s
      exact Fiber p s
  fiber_functor :=
   by
    intro s
    exact Fiber.functor p s
  comp_const :=
    by
      intro s
      exact Fiber.comp_const p s
  has_pullbacks :=
    by
      intro s t x f
      rcases hp with ⟨hp⟩
      rcases hp (f ≫ eqToHom (x.prop.symm)) with ⟨y, φ , hy, h_lift, h_cart⟩
      existsi ⟨y, hy⟩
      existsi φ
      constructor
      constructor
      rcases h_lift with ⟨h_lift⟩
      rw [←assoc, ←comp_eqToHom_iff x.prop, comp_id] at h_lift
      exact h_lift
      exact h_cart
-/

lemma fiber_factorization {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p) {a b : 𝒳} (ψ : b ⟶ a) :
  ∃ (c : Fiber p (p.obj b)) (τ : Fiber.self p b ⟶ c) (φ : c.val ⟶ a),
    IsPullback' p (p.map ψ) φ ∧ (τ.val ≫ φ = ψ) :=
  by
    rcases hp.1 rfl (p.map ψ) with ⟨c', φ, hφ⟩
    existsi ⟨c', hφ.1⟩
    have h₃ : p.map ψ = 𝟙 (p.obj b)  ≫ p.map ψ := by simp only [id_comp]
    set τ' := IsPullback'InducedMap hφ h₃ (HomLift'_self p ψ)
    existsi ⟨τ', ?_⟩
    · rw [(IsPullback'InducedMap_HomLift hφ h₃ (HomLift'_self p ψ)).1]
      simp only [Fiber.self_coe, eqToHom_refl, comp_id]
    existsi φ
    refine ⟨hφ, by simp only [IsPullback'InducedMap_Diagram]⟩

class Functor.IsBasePreserving (p : C ⥤ S) (q : D ⥤ S) (F : C ⥤ D)
  [IsFibered p] [IsFibered q] : Prop where
  (basePreserving : F ⋙ q = p)
  (preservesCartesian (φ : y ⟶ x) [IsCartesian p φ] : IsCartesian q (F.map φ))

lemma samefiber (p : C ⥤ S) (q : D ⥤ S) (F : C ⥤ D) (G : C ⥤ D)
  [IsFibered p] [IsFibered q] [hF : Functor.IsBasePreserving p q F] [hG : Functor.IsBasePreserving p q G]
  (x : C) : q.obj (F.obj x) = q.obj (G.obj x) :=
  by
    rcases hF with ⟨hFcomm, _⟩
    rcases hG with ⟨hGcomm, _⟩
    rw [←comp_obj, ←comp_obj, hFcomm, hGcomm]

-- To make into a category I first have to define the type of Fibered categories....
--instance IsFibered.category (p : C ⥤ D) [IsFibered p] : Category p where sorry

class NatTrans.IsBasePreserving (p : C ⥤ S) (q : D ⥤ S) [IsFibered p] [IsFibered q] {F : C ⥤ D}
  (G : C ⥤ D) [Functor.IsBasePreserving p q F] [Functor.IsBasePreserving p q G] (α : F ⟶ G) : Prop where
  (pointwiseInFiber : ∀ (x : C), q.map (α.app x) = eqToHom (samefiber p q F G x))

-- TODO DEFINE COERCION
--def NatTrans.lift (p : C ⥤ S) (q : D ⥤ S) [IsFibered p] [IsFibered q] {F : C ⥤ D}
--  (G : C ⥤ D) [Functor.IsBasePreserving p q F] [Functor.IsBasePreserving p q G] (α : F ⟶ G)
--  [NatTrans.IsBasePreserving p q α] (x : C) :

/-
-- TODO BREAK UP INTO SMALLER PIECES
lemma IsFiberedInGroupoids_iff (p : C ⥤ S) : IsFiberedInGroupoids p ↔
  (IsFibered p ∧ (∀ (s : S) {x y : (Fiber p s)} (φ : x ⟶ y), IsIso φ)) :=
  by
    constructor
    · rintro ⟨hfiber, hlift⟩
      refine ⟨⟨?_⟩, ?_⟩
      · intro x s f
        rcases hlift f with ⟨z, ψ, hz, hcomm⟩
        existsi z
        existsi ψ
        existsi hz
        refine ⟨hcomm, hfiber ψ⟩
      intro s x y ψ
      haveI hiso : IsIso (p.map ψ.val) :=
        by
          have hψ := ψ.prop
          rw [comp_eqToHom_iff, eqToHom_trans] at hψ
          rw [hψ]
          sorry -- TODO SHOULD BE FINE ALREADY? This instance exists in EqToHom...
      haveI hψiso : IsIso (ψ.val) := isiso_of_cartesian p ψ.val
      sorry -- Need iso is in fiber... separate lemma (after better definition of fibers)
    rintro ⟨hfiber, hiso⟩
    constructor
    · intro x y φ
      rcases fiber_factorization p φ with ⟨z, ψ, τ, hτ, hcomp⟩
      rw [←hcomp]
      haveI hiso := hiso (p.obj y) ψ
      haveI : IsCartesian p ψ.val :=
        by
          haveI : IsIso ψ.val := sorry -- TODO INSTANCE SHOULD ALREADY EXIST
          exact iso_iscartesian p ψ.val
      apply IsCartesian.comp
    intro x Y f
    rcases hfiber with ⟨hfiber⟩
    rcases hfiber f with ⟨y, φ, hy, hcomm, hcart⟩
    existsi y
    existsi φ
    existsi hy
    exact hcomm
-/

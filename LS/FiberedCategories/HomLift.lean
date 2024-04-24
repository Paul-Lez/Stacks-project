/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks

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

/-
TODO:
-- TODO: naming... Open a namespace!
-- TODO: naming of variables, make it more consistent.
-/

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category 𝒳] [Category 𝒮]

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

/-- For any arrow `φ : a ⟶ b` in `𝒳`, `φ` lifts the arrow `p.map φ` in the base `𝒮`-/
@[simp]
lemma IsHomLift_self (p : 𝒳 ⥤ 𝒮) {a b : 𝒳} (φ : a ⟶ b) : IsHomLift p (p.map φ) φ where
  ObjLiftDomain := rfl
  ObjLiftCodomain := rfl
  HomLift := ⟨by simp only [eqToHom_refl, comp_id, id_comp]⟩

@[simp]
lemma IsHomLift_id {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a : 𝒳} (ha : p.obj a = R) : IsHomLift p (𝟙 R) (𝟙 a) :=
  ha ▸ (p.map_id _ ▸ IsHomLift_self p (𝟙 a))

lemma IsHomLift_congr {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsHomLift p f φ) : eqToHom hφ.ObjLiftDomain.symm ≫ p.map φ ≫ eqToHom hφ.ObjLiftCodomain = f :=
  (eqToHom_comp_iff hφ.ObjLiftDomain.symm _ _).2 hφ.HomLift.w


lemma IsHomLift_congr' {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsHomLift p f φ) : eqToHom hφ.ObjLiftDomain ≫ f ≫ eqToHom hφ.ObjLiftCodomain.symm = p.map φ := by
  rw [←assoc, comp_eqToHom_iff hφ.ObjLiftCodomain.symm _ _]
  exact hφ.HomLift.w.symm

/-- If `φ : a ⟶ b` lifts `f : R ⟶ S` and `φ` is an isomorphism, then so is `f`. -/
-- TODO: Iso version of this?
lemma IsIsoofIsHomliftisIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
  (hlift : IsHomLift p f φ) [IsIso φ] : IsIso f := by
  rcases hlift with ⟨domain, _, ⟨homlift⟩⟩
  rw [←eqToHom_comp_iff domain.symm] at homlift
  rw [←homlift]
  exact IsIso.comp_isIso

/-- If `φ : a ⟶ b` lifts `f : R ⟶ S` and both are isomorphisms, then `φ⁻¹` lifts `f⁻¹`. -/
lemma IsHomLift_inv {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hlift : IsHomLift p f φ) [IsIso φ] [IsIso f] : IsHomLift p (inv f) (inv φ) where
  ObjLiftDomain := hlift.2
  ObjLiftCodomain := hlift.1
  HomLift := by
    constructor
    simp only [map_inv, IsIso.eq_comp_inv, assoc, IsIso.inv_comp_eq]
    exact hlift.3.1.symm

/-- If `φ : a ⟶ b` is an isomorphism, and lifts `𝟙 S` for some `S : 𝒮`, then `φ⁻¹` also lifts `𝟙 S` -/
lemma IsHomLift_inv_id {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a b : 𝒳} {φ : a ⟶ b} [IsIso φ]
    (hlift : IsHomLift p (𝟙 S) φ) : IsHomLift p (𝟙 S) (inv φ) :=
  (IsIso.inv_id (X:=S)) ▸ IsHomLift_inv hlift

-- TODO MOVE THIS UP SOMEWHAT
lemma IsHomLift_comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S}
  {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c} (hφ : IsHomLift p f φ)
  (hψ : IsHomLift p g ψ) : IsHomLift p (f ≫ g) (φ ≫ ψ) where
    ObjLiftDomain := hφ.1
    ObjLiftCodomain := hψ.2
    HomLift := by
      -- TODO: could use composition of CommSq (once mathlib is updated)
      constructor
      rw [←Category.assoc, ←hφ.3.1]
      simp only [map_comp, assoc, hψ.3.1]

/-- If `φ : a ⟶ b` and `ψ : b ⟶ c` lift `𝟙 S`, then so does `φ ≫ ψ` -/
lemma IsHomLift_id_comp {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a b c : 𝒳} {φ : a ⟶ b} {ψ : b ⟶ c} (hφ : IsHomLift p (𝟙 R) φ)
  (hψ : IsHomLift p (𝟙 R) ψ) : IsHomLift p (𝟙 R) (φ ≫ ψ) := by
  have := IsHomLift_comp hφ hψ
  rw [comp_id] at this
  exact this

-- TODO: figure out naming scheme for these (or just comment better? e.g. IsHomLift_id_eqToHom_domain)
lemma IsHomLift_id_eqToHom {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hba : b = a) {S : 𝒮}
    (hS : p.obj a = S) : IsHomLift p (𝟙 S) (eqToHom hba) where
      ObjLiftDomain := hba ▸ hS
      ObjLiftCodomain := hS
      HomLift := ⟨by simp only [eqToHom_map, eqToHom_trans, comp_id]⟩

lemma IsHomLift_id_eqToHom' {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hba : b = a) {S : 𝒮}
    (hS : p.obj b = S) : IsHomLift p (𝟙 S) (eqToHom hba) where
      ObjLiftDomain := hS
      ObjLiftCodomain := hba ▸ hS
      HomLift := ⟨by simp only [eqToHom_map, eqToHom_trans, comp_id]⟩

lemma IsHomLift_eqToHom_id {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S)
    {a : 𝒳} (ha : p.obj a = S) : IsHomLift p (eqToHom hRS) (𝟙 a) where
      ObjLiftDomain := hRS ▸ ha
      ObjLiftCodomain := ha
      HomLift := ⟨by simp only [map_id, id_comp, eqToHom_trans]⟩

lemma IsHomLift_eqToHom_id' {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S)
    {a : 𝒳} (ha : p.obj a = R) : IsHomLift p (eqToHom hRS) (𝟙 a) where
      ObjLiftDomain := ha
      ObjLiftCodomain := hRS ▸ ha
      HomLift := ⟨by simp only [map_id, id_comp, eqToHom_trans]⟩


@[simp]
lemma IsHomLift_comp_eqToHom {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b c: 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} {hca : c = a} : IsHomLift p f (eqToHom hca ≫ φ) ↔ IsHomLift p f φ where
  mp := by intro hφ'; subst hca; simpa using hφ'
  mpr := fun hφ => id_comp f ▸ IsHomLift_comp (IsHomLift_id_eqToHom hca hφ.ObjLiftDomain) hφ

@[simp]
lemma IsHomLift_eqToHom_comp {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b c: 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} {hbc : b = c} : IsHomLift p f (φ ≫ eqToHom hbc) ↔ IsHomLift p f φ where
  mp := by intro hφ'; subst hbc; simpa using hφ'
  mpr := fun hφ => comp_id f ▸ IsHomLift_comp hφ (IsHomLift_id_eqToHom' hbc hφ.ObjLiftCodomain)

@[simp]
lemma IsHomLift_eqToHom_comp' {p : 𝒳 ⥤ 𝒮} {R S T: 𝒮} {a b : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} (hTR : T = R) : IsHomLift p ((eqToHom hTR) ≫ f) φ ↔ IsHomLift p f φ where
  mp := by intro hφ'; subst hTR; simpa using hφ'
  mpr := fun hφ => id_comp φ ▸ IsHomLift_comp (IsHomLift_eqToHom_id hTR hφ.ObjLiftDomain) hφ

@[simp]
lemma IsHomLift_comp_eqToHom' {p : 𝒳 ⥤ 𝒮} {R S T: 𝒮} {a b : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} (hST : S = T) : IsHomLift p (f ≫ (eqToHom hST)) φ ↔ IsHomLift p f φ where
  mp := by intro hφ'; subst hST; simpa using hφ'
  mpr := fun hφ => comp_id φ ▸ IsHomLift_comp hφ (IsHomLift_eqToHom_id' hST hφ.ObjLiftCodomain)

-- TODO: move this elsewhere in this file (probably up a bit, to belong with the `id` lemmas...!)
/-- If `φ : a ⟶ b` lifts `f` and `ψ : b ⟶ c` lifts `𝟙 T`, then `φ  ≫ ψ` lifts `f` -/
lemma IsHomLift_of_IsHomLiftId_comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S}
    {φ : b ⟶ a} (hφ : IsHomLift p f φ) {ψ : c ⟶ b} (hψ : IsHomLift p (𝟙 T) ψ) :
    IsHomLift p f (ψ ≫ φ) where
  ObjLiftDomain := by
    rw [←hφ.ObjLiftDomain, hψ.ObjLiftCodomain, hψ.ObjLiftDomain]
  ObjLiftCodomain := hφ.ObjLiftCodomain
  HomLift := ⟨by
    have : p.map ψ = eqToHom (_ : p.obj c = p.obj b) := by simpa [comp_eqToHom_iff] using hψ.3.1
    rw [map_comp, assoc, hφ.3.1, this, eqToHom_trans_assoc] ⟩

/-- If `φ : a ⟶ b` lifts `𝟙 S` and `ψ : b ⟶ c` lifts `f`, then `φ  ≫ ψ` lifts `f` -/
lemma IsHomLift_of_comp_IsHomLiftId {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b c : 𝒳} {f : R ⟶ S}
    {φ : b ⟶ a} (hφ : IsHomLift p f φ) {ψ : a ⟶ c} (hψ : IsHomLift p (𝟙 S) ψ) :
    IsHomLift p f (φ ≫ ψ) where
  ObjLiftDomain := hφ.ObjLiftDomain
  ObjLiftCodomain := by
    rw [←hφ.ObjLiftCodomain, hψ.ObjLiftDomain, hψ.ObjLiftCodomain]
  HomLift := ⟨by
    have : p.map ψ = eqToHom (_ : p.obj a = p.obj c) := by simpa [comp_eqToHom_iff] using hψ.3.1
    rw [map_comp, assoc, this, eqToHom_trans, hφ.3.1] ⟩

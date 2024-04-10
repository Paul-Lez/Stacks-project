import Mathlib.CategoryTheory.CommSq

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category

/-
TODO:
- Is there a way to make the notation {a : 𝒳} work? (possibly by making BasedCategory into a typeclass (BasedOver?))

-/

namespace Fibered

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]


structure BasedCategory (𝒮 : Type u₁) [Category.{v₁} 𝒮] where
  (carrier : Type u₂) -- TODO: other types also OK?
  [isCat : Category.{v₂} carrier]
  (p : carrier ⥤ 𝒮)

-- TODO: can this be done automatically?
instance (𝒳 : BasedCategory 𝒮) : Category 𝒳.carrier := 𝒳.isCat

/-- The proposition that an arrow a --φ--> b in 𝒳 lifts an arrow R --f--> S in 𝒮 via p. This is
often drawn as:
```
  a --φ--> b
  -        -
  |        |
  v        v
  R --f--> S
``` -/
class IsHomLift (𝒳 : BasedCategory 𝒮) {R S : 𝒮} {a b : 𝒳.1} (f : R ⟶ S) (φ : a ⟶ b) : Prop where
  (ObjLiftDomain : 𝒳.p.obj a = R)
  (ObjLiftCodomain : 𝒳.p.obj b = S)
  (HomLift : CommSq (𝒳.p.map φ) (eqToHom ObjLiftDomain) (eqToHom ObjLiftCodomain) f)

@[simp]
lemma IsHomLift_id {𝒳 : BasedCategory 𝒮} {R : 𝒮} {a : 𝒳.1} (ha : 𝒳.p.obj a = R) : IsHomLift 𝒳 (𝟙 R) (𝟙 a) where
  ObjLiftDomain := ha
  ObjLiftCodomain := ha
  HomLift := ⟨by simp only [map_id, id_comp, comp_id]⟩

@[simp]
lemma IsHomLift_self (𝒳 : BasedCategory 𝒮) {a b : 𝒳.1} (φ : a ⟶ b) : IsHomLift 𝒳 (𝒳.p.map φ) φ where
  ObjLiftDomain := rfl
  ObjLiftCodomain := rfl
  HomLift := ⟨by simp only [eqToHom_refl, comp_id, id_comp]⟩

lemma IsHomLift_congr {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b : 𝒳.1} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsHomLift 𝒳 f φ) : eqToHom hφ.ObjLiftDomain.symm ≫ 𝒳.p.map φ ≫ eqToHom hφ.ObjLiftCodomain = f :=
  (eqToHom_comp_iff hφ.ObjLiftDomain.symm _ _).2 hφ.HomLift.w


lemma IsHomLift_congr' {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b : 𝒳.1} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsHomLift 𝒳 f φ) : eqToHom hφ.ObjLiftDomain ≫ f ≫ eqToHom hφ.ObjLiftCodomain.symm = 𝒳.p.map φ := by
  rw [←assoc, comp_eqToHom_iff hφ.ObjLiftCodomain.symm _ _]
  exact hφ.HomLift.w.symm

/-- If a --φ--> b lifts R --f--> S, then if φ is an isomorphism, so is f. -/
lemma IsIsoofIsHomliftisIso {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b : 𝒳.1} {f : R ⟶ S} {φ : a ⟶ b}
  (hlift : IsHomLift 𝒳 f φ) (hφ : IsIso φ) : IsIso f := by
  rcases hlift with ⟨domain, _, ⟨homlift⟩⟩
  rw [←eqToHom_comp_iff domain.symm] at homlift
  rw [←homlift]
  exact IsIso.comp_isIso

lemma IsHomLift_inv {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b : 𝒳.1} {f : R ⟶ S} {φ : a ⟶ b}
  (hlift : IsHomLift 𝒳 f φ) (hφ : IsIso φ) (hf : IsIso f) : IsHomLift 𝒳 (inv f) (inv φ) where
    ObjLiftDomain := hlift.2
    ObjLiftCodomain := hlift.1
    HomLift := by
      constructor
      simp only [map_inv, IsIso.eq_comp_inv, assoc, IsIso.inv_comp_eq]
      exact hlift.3.1.symm

lemma IsHomLift_comp {𝒳 : BasedCategory 𝒮} {R S T : 𝒮} {a b c : 𝒳.1} {f : R ⟶ S}
  {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c} (hφ : IsHomLift 𝒳 f φ)
  (hψ : IsHomLift 𝒳 g ψ) : IsHomLift 𝒳 (f ≫ g) (φ ≫ ψ) where
    ObjLiftDomain := hφ.1
    ObjLiftCodomain := hψ.2
    HomLift := by
      constructor
      rw [←Category.assoc, ←hφ.3.1]
      simp only [map_comp, assoc, hψ.3.1]

lemma IsHomLift_id_comp {𝒳 : BasedCategory 𝒮} {R : 𝒮} {a b c : 𝒳.1} {φ : a ⟶ b} {ψ : b ⟶ c} (hφ : IsHomLift 𝒳 (𝟙 R) φ)
  (hψ : IsHomLift 𝒳 (𝟙 R) ψ) : IsHomLift 𝒳 (𝟙 R) (φ ≫ ψ) := by
  have := IsHomLift_comp hφ hψ
  rw [comp_id] at this
  exact this

lemma IsHomLift_id_eqToHom {𝒳 : BasedCategory 𝒮} {a b : 𝒳.1} (hba : b = a) {S : 𝒮}
    (hS : 𝒳.p.obj a = S) : IsHomLift 𝒳 (𝟙 S) (eqToHom hba) where
      ObjLiftDomain := hba ▸ hS
      ObjLiftCodomain := hS
      HomLift := ⟨by simp only [eqToHom_map, eqToHom_trans, comp_id]⟩

lemma IsHomLift_id_eqToHom' {𝒳 : BasedCategory 𝒮} {a b : 𝒳.1} (hba : b = a) {S : 𝒮}
    (hS : 𝒳.p.obj b = S) : IsHomLift 𝒳 (𝟙 S) (eqToHom hba) where
      ObjLiftDomain := hS
      ObjLiftCodomain := hba ▸ hS
      HomLift := ⟨by simp only [eqToHom_map, eqToHom_trans, comp_id]⟩

lemma IsHomLift_eqToHom_id {𝒳 : BasedCategory 𝒮} {R S : 𝒮} (hRS : R = S)
    {a : 𝒳.1} (ha : 𝒳.p.obj a = S) : IsHomLift 𝒳 (eqToHom hRS) (𝟙 a) where
      ObjLiftDomain := hRS ▸ ha
      ObjLiftCodomain := ha
      HomLift := ⟨by simp only [map_id, id_comp, eqToHom_trans]⟩

lemma IsHomLift_eqToHom_id' {𝒳 : BasedCategory 𝒮} {R S : 𝒮} (hRS : R = S)
    {a : 𝒳.1} (ha : 𝒳.p.obj a = R) : IsHomLift 𝒳 (eqToHom hRS) (𝟙 a) where
      ObjLiftDomain := ha
      ObjLiftCodomain := hRS ▸ ha
      HomLift := ⟨by simp only [map_id, id_comp, eqToHom_trans]⟩

@[simp]
lemma IsHomLift_comp_eqToHom {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b c: 𝒳.1} {f : R ⟶ S}
    {φ : a ⟶ b} {hca : c = a} : IsHomLift 𝒳 f (eqToHom hca ≫ φ) ↔ IsHomLift 𝒳 f φ where
  mp := by intro hφ'; subst hca; simpa using hφ'
  mpr := fun hφ => id_comp f ▸ IsHomLift_comp (IsHomLift_id_eqToHom hca hφ.ObjLiftDomain) hφ

@[simp]
lemma IsHomLift_eqToHom_comp {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b c: 𝒳.1} {f : R ⟶ S}
    {φ : a ⟶ b} {hbc : b = c} : IsHomLift 𝒳 f (φ ≫ eqToHom hbc) ↔ IsHomLift 𝒳 f φ where
  mp := by intro hφ'; subst hbc; simpa using hφ'
  mpr := fun hφ => comp_id f ▸ IsHomLift_comp hφ (IsHomLift_id_eqToHom' hbc hφ.ObjLiftCodomain)

@[simp]
lemma IsHomLift_eqToHom_comp' {𝒳 : BasedCategory 𝒮} {R S T: 𝒮} {a b : 𝒳.1} {f : R ⟶ S}
    {φ : a ⟶ b} (hTR : T = R) : IsHomLift 𝒳 ((eqToHom hTR) ≫ f) φ ↔ IsHomLift 𝒳 f φ where
  mp := by intro hφ'; subst hTR; simpa using hφ'
  mpr := fun hφ => id_comp φ ▸ IsHomLift_comp (IsHomLift_eqToHom_id hTR hφ.ObjLiftDomain) hφ

@[simp]
lemma IsHomLift_comp_eqToHom' {𝒳 : BasedCategory 𝒮} {R S T: 𝒮} {a b : 𝒳.1} {f : R ⟶ S}
    {φ : a ⟶ b} (hST : S = T) : IsHomLift 𝒳 (f ≫ (eqToHom hST)) φ ↔ IsHomLift 𝒳 f φ where
  mp := by intro hφ'; subst hST; simpa using hφ'
  mpr := fun hφ => comp_id φ ▸ IsHomLift_comp hφ (IsHomLift_eqToHom_id' hST hφ.ObjLiftCodomain)

lemma IsHomLift_of_IsHomLiftId_comp {𝒳 : BasedCategory 𝒮} {R S T : 𝒮} {a b c : 𝒳.1} {f : R ⟶ S}
    {φ : b ⟶ a} (hφ : IsHomLift 𝒳 f φ) {ψ : c ⟶ b} (hψ : IsHomLift 𝒳 (𝟙 T) ψ) :
    IsHomLift 𝒳 f (ψ ≫ φ) where
  ObjLiftDomain := by
    rw [←hφ.ObjLiftDomain, hψ.ObjLiftCodomain, hψ.ObjLiftDomain]
  ObjLiftCodomain := hφ.ObjLiftCodomain
  HomLift := ⟨by
    have : 𝒳.p.map ψ = eqToHom (_ : 𝒳.p.obj c = 𝒳.p.obj b) := by simpa [comp_eqToHom_iff] using hψ.3.1
    rw [map_comp, assoc, hφ.3.1, this, eqToHom_trans_assoc] ⟩

lemma IsHomLift_of_comp_IsHomLiftId {𝒳 : BasedCategory 𝒮} {R S : 𝒮} {a b c : 𝒳.1} {f : R ⟶ S}
    {φ : b ⟶ a} (hφ : IsHomLift 𝒳 f φ) {ψ : a ⟶ c} (hψ : IsHomLift 𝒳 (𝟙 S) ψ) :
    IsHomLift 𝒳 f (φ ≫ ψ) where
  ObjLiftDomain := hφ.ObjLiftDomain
  ObjLiftCodomain := by
    rw [←hφ.ObjLiftCodomain, hψ.ObjLiftDomain, hψ.ObjLiftCodomain]
  HomLift := ⟨by
    have : 𝒳.p.map ψ = eqToHom (_ : 𝒳.p.obj a = 𝒳.p.obj c) := by simpa [comp_eqToHom_iff] using hψ.3.1
    rw [map_comp, assoc, this, eqToHom_trans, hφ.3.1] ⟩

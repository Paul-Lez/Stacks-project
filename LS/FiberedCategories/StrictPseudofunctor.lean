import Mathlib.CategoryTheory.Bicategory.Functor
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/- This file contains lemmas that (in some form) should be PRd to CategoryTheory/Bicategory
These are not directly related to stacks / fibered categories
-/

namespace CategoryTheory

open Category Bicategory

namespace Pseudofunctor

universe w₁ w₂ v₁ v₂ u₁ u₂


variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable (F : Pseudofunctor B C)

lemma map₂_eqToHom {a b : B} {f g : a ⟶ b} (h : f = g) :
    F.map₂ (eqToHom h) = eqToHom (F.congr_map h) := by
  subst h; simp only [eqToHom_refl, map₂_id]

end Pseudofunctor

open CategoryTheory Bicategory Discrete LocallyDiscrete

universe w₂ v v₁ v₂ u u₁ u₂

variable {I : Type u₁} [Category.{v₁} I] {B : Type u₂} [Bicategory.{w₂, v₂} B] [Strict B]
variable {F : Pseudofunctor (LocallyDiscrete I) B}

-- These should be stated in terms of strict bicategories

-- Pseudofunctors from locally discrete categories to strict bicategories
lemma map₂_left_unitor' {a b : I} (f : a ⟶ b) : (F.mapComp (𝟙 a).toLoc f.toLoc).inv =
    (F.mapId ⟨a⟩).hom ▷ F.map f.toLoc ≫ eqToHom (by simp) := by
  have h := F.map₂_left_unitor f.toLoc
  simp at h
  rw [F.map₂_eqToHom, ←Iso.inv_comp_eq, comp_eqToHom_iff] at h
  simp at h
  apply h

lemma map₂_right_unitor' {a b : I} (f : a ⟶ b) : (F.mapComp f.toLoc (𝟙 b).toLoc).inv =
    F.map f.toLoc ◁ (F.mapId ⟨b⟩).hom ≫ eqToHom (by simp) := by
  have h := F.map₂_right_unitor f.toLoc
  simp at h
  rw [F.map₂_eqToHom, ←Iso.inv_comp_eq, comp_eqToHom_iff] at h
  simp at h
  apply h

lemma map₂_associator' {a b c d : I} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f.toLoc (g.toLoc ≫ h.toLoc)).hom ≫ (F.map f.toLoc) ◁ (F.mapComp g.toLoc h.toLoc).hom
    = eqToHom (by simp) ≫ (F.mapComp (f.toLoc ≫ g.toLoc) h.toLoc).hom ≫
    (F.mapComp f.toLoc g.toLoc).hom ▷ F.map h.toLoc ≫ eqToHom (by simp)
    := by
  have h := F.map₂_associator f.toLoc g.toLoc h.toLoc
  simp at h
  rw [F.map₂_eqToHom, ←Iso.inv_comp_eq] at h
  -- TODO: rewrite thing as inv then move to LHS (+ restate lemma to use this notation instead!)
  sorry

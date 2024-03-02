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
def Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮) := (a : 𝒳) × (p.obj a ≅ S)
--{a : 𝒳 // ∃ φ : p.obj a ⟶ S, IsIso φ}

-- a lies in the fiber of p.obj a
def FiberSelf (p : 𝒳 ⥤ 𝒮) (a : 𝒳) : Fiber p (p.obj a) := ⟨a, eqToIso rfl⟩

-- TODO DO I EVEN NEED?
@[simp]
lemma FiberSelfCoe (p : 𝒳 ⥤ 𝒮) (a : 𝒳) : (FiberSelf p a).1 = a := rfl

instance FiberCategory (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : Category (Fiber p S) where
  -- TODO NEED BETTER DEFINITION, CommSq?
  Hom a b := {φ : a.1 ⟶ b.1 // CommSq (p.map φ) a.2.hom b.2.hom (eqToHom rfl)}
  id a := ⟨𝟙 a.1, ⟨by simp only [map_id, id_comp, eqToHom_refl, comp_id]⟩⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val,
    by
      have := CommSqComp φ.2 ψ.2
      simp only [eqToHom_refl, ←map_comp, comp_id] at this
      exact this⟩

def FiberFunctor (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : (Fiber p S) ⥤ 𝒳 where
  obj := Sigma.fst
  map := Subtype.val

-- Next define induced map from "arbitrary fiber" to "canonical fiber"

def FiberUniversalFunctor {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type _} [Category C]
  {F : C ⥤ 𝒳} (α : F ⋙ p ≅ (const C).obj S) : C ⥤ Fiber p S where
    obj := fun x => ⟨F.obj x, α.app x⟩
    map := fun φ => ⟨F.map φ, ⟨α.hom.naturality _⟩⟩

-- We define an intrinsic notion of fibers, which we call FiberStruct
-- Fibered family
structure FiberStruct (p : 𝒳 ⥤ 𝒮) where
  Fib (S : 𝒮) : Type _
  [isCategory (S : 𝒮) : Category (Fib S)]
  (ι (S : 𝒮) : (Fib S) ⥤ 𝒳)
  (comp_const (S : 𝒮) : (ι S) ⋙ p ≅ (const (Fib S)).obj S)
  --(comp_const (S : 𝒮) : ∀ (x : Fib S), (fiber_functor S ⋙ p).obj x = S) <--- USE THIS INSTEAD
  (equiv (S : 𝒮) : IsEquivalence (FiberUniversalFunctor (comp_const S)))

instance HasFibersCategory {p : 𝒳 ⥤ 𝒮} (hp : FiberStruct p) {S : 𝒮} : Category (hp.Fib S) := hp.isCategory S

-- lemma FiberStructPullback {p : 𝒳 ⥤ 𝒮} [IsFibered p] {hp : FiberStruct p} {R S : 𝒮} (a : hp.Fib S)
--   (f : R ⟶ S) : ∃ (b : hp.Fib R) (φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a), IsPullback p f φ := by
--     sorry -- TODO USE IDENTITY INSTEAD OF ISOS....

def FiberStructProj {p : 𝒳 ⥤ 𝒮} (hp : FiberStruct p) {R S : 𝒮} (a : hp.Fib S)
  (b : hp.Fib R) (φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a) : R ⟶ S :=
    ((hp.comp_const R).app b).inv ≫ (p.map φ) ≫ ((hp.comp_const S).app a).hom


--class FiberedStruct (p : 𝒳 ⥤ 𝒮) extends FiberStruct where
--  (has_pullbacks {S R : 𝒫} (a : Fib S) (f : R ⟶ S) :
--    ∃ (b : Fib R) (φ : (fiber_functor R).obj b ⟶ (fiber_functor S).obj a), IsPullback p f φ))

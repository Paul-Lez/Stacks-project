import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Functor.Const


universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category

variable {S : Type u₁} {C : Type u₂} {D : Type u₃} [Category S] [Category C] [Category D]

namespace ObjLift

def ObjLift (p : C ⥤ S) (U : S) (x : C) : Prop := p.obj x = U

lemma LiftImage (p : C ⥤ S) (x : C) : ObjLift p (p.obj x) x := rfl

lemma eq {p : C ⥤ S} {U : S} {x : C} (h : ObjLift p U x) : p.obj x = U := h

def toIso {p : C ⥤ S} {U : S} {x : C} (hx : ObjLift p U x) : p.obj x ≅ U := eqToIso hx

def toHom {p : C ⥤ S} {U : S} {x : C} (hx : ObjLift p U x) : p.obj x ⟶ U := eqToHom hx

end ObjLift

open ObjLift

def HomLift (p : C ⥤ S) {x y : C} {U V : S} (f : U ⟶ V)
(φ : x ⟶ y) (h₁ : ObjLift p U x)
(h₂ : ObjLift p V y) : Prop := CommSq (p.map φ) (toHom h₁) (toHom h₂) f

--lemma HomLiftOpp (p : C ⥤ S) {x y : C} {U V : S} (f : U ⟶ V) (φ : x ⟶ y) (h₁ : ObjLift p U x)
--  (h₂ : ObjLift p V y) : (HomLift p f φ h₁ h₂) ↔ (Homlift p.op f.op φ.op ((ObjLiftOpp p U x).1
--   h₁) ((ObjLiftOpp p V y).1 h₂)) :=
--by sorry

/-
Defining when an arrow is cartesian (see Olssons book)
Strongly cartesian in the stacks project
-/

class IsCartesian (p : C ⥤ S) {x y : C} (φ : y ⟶ x) : Prop where
  (isCartesian {z : C} {ψ : z ⟶ x} {f : p.obj z ⟶ p.obj y} (hy : f ≫ (p.map φ) = p.map ψ) :
    ∃! (χ : z ⟶ y), (χ ≫ φ = ψ) ∧ f = p.map χ)

#check Iso

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
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [←assoc, hcomp2]
      exact hφcomp
    · exact hproj2
    rintro π' ⟨hπ'comp, hπ'proj⟩
    apply π_unique
    refine ⟨?_, hπ'proj⟩
    apply τ'_unique
    constructor
    · rw [assoc]
      exact hπ'comp
    simp only [hπ'proj, map_comp]

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

lemma isiso_of_cartesian (p : C ⥤ S) {x y : C} (φ : y ⟶ x) [hiso : IsIso (p.map φ)]
  [hcart : IsCartesian p φ] : IsIso φ :=
  by
    constructor
    rcases hcart with ⟨hcart⟩
    have heq : inv (p.map φ) ≫ p.map φ = p.map (𝟙 x) :=
      by simp only [IsIso.inv_hom_id, map_id]
    rcases (hcart heq) with ⟨φinv, ⟨hcomp, hproj⟩, hunique⟩
    existsi φinv
    refine ⟨?_, hcomp⟩
    sorry -- TODO AFTER MOVING PAULS API OVER HERE... Or need to use is_iscartesian


class IsFibered (p : C ⥤ S) : Prop where
  (cartesian_lift {x : C} {Y : S} (f : Y ⟶ p.obj x) :
    ∃ (y : C) (φ : y ⟶ x) (hy : p.obj y = Y),
      CommSq (p.map φ) (eqToHom hy) (𝟙 (p.obj x)) f ∧ IsCartesian p φ)

def Fiber (p : C ⥤ S) (s : S) := {x : C // p.obj x = s}

def Fiber.self (p : C ⥤ S) (x : C) : Fiber p (p.obj x) := ⟨x, rfl⟩

-- TODO DO I EVEN NEED?
lemma Fiber.self_coe (p : C ⥤ S) (x : C) : (Fiber.self p x).val = x := rfl

instance Fiber.category (p : C ⥤ S) (s : S) : Category (Fiber p s) where
  Hom x y := {φ : x.val ⟶ y.val // (p.map φ) ≫ (eqToHom y.prop) = (eqToHom x.prop)}
  id x := ⟨𝟙 x.val,
    by
      simp only [map_id, id_comp, comp_id]⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val,
    by
      simp only [map_comp, assoc, comp_id]
      rw [ψ.prop, φ.prop]⟩

#check Subtype.val

def Fiber.functor (p : C ⥤ S) (s : S) : (Fiber p s) ⥤ C where
  obj := Subtype.val
  map := Subtype.val

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

lemma fiber_factorization (p : C ⥤ S) [hp : IsFibered p] (x y : C) (ψ : y ⟶ x) :
  ∃ (z : Fiber p (p.obj y)) (τ : Fiber.self p y ⟶ z) (φ : z.val ⟶ x), IsCartesian p φ ∧
    (τ.val ≫ φ = ψ) :=
  by
    rcases hp with ⟨hp⟩
    rcases hp (p.map ψ) with ⟨z', φ, hproj_eq, ⟨hproj, ⟨hcart⟩⟩⟩
    existsi ⟨z', hproj_eq⟩
    have h1 : eqToHom hproj_eq.symm ≫ p.map φ = p.map ψ :=
      by
        rcases hproj with ⟨hproj⟩
        simp only [comp_id] at hproj
        simp only [hproj, eqToHom_trans_assoc, eqToHom_refl, id_comp]
    rcases (hcart h1) with ⟨τ', ⟨hcomp, hproj⟩, τ'_unique⟩
    existsi ⟨τ', by simp only [←hproj, eqToHom_trans, eqToHom_refl]⟩
    existsi φ
    refine ⟨⟨hcart⟩, hcomp⟩


--instance PreimageFibers (p : C ⥤ S) : HasFibers p where
--  fiber s := Fiber p s
--  fiber_functor := sorry
--  comp_const := sorry

class FiberedCategoryMorphism (p : C ⥤ S) (q : D ⥤ S) (F : C ⥤ D)
  [IsFibered p] [IsFibered q] : Prop where
  (basePreserving : F ⋙ q = p)
  (preservesCartesian (φ : y ⟶ x) [IsCartesian p φ] : IsCartesian q (F.map φ))






--class IsFiberedInGroupoids (p : C ⥤ S) : Prop where
--  (liftHom {x : C} {Y : S} (f : Y ⟶ p.obj x) :
--    ∃ (y : C) (φ : y ⟶ x) (hx : p.obj y = Y),
--      CommSq (p.map φ) (eqToHom hx) (𝟙 (p.obj x)) f)
--  (isCartesian {x y z : C} {φ : y ⟶ x} {ψ : z ⟶ x} {f : p.obj z ⟶ p.obj y}
--  (hy : f ≫ (p.map φ) = p.map ψ) :
--    ∃! (χ : z ⟶ y), CommSq f (𝟙 (p.obj z)) (𝟙 (p.obj y)) (p.map χ))

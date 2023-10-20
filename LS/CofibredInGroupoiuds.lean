import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.CommSq


universe u₁ v₁ u₂ v₂ w

open CategoryTheory Functor Opposite

variable {S : Type u₁} {C : Type u₂} [Category S] [Category C]

def ObjLift (p : C ⥤ S) (U : S) (x : C) : Prop := p.obj x = U

lemma ObjLift_image (p : C ⥤ S) (x : C) : ObjLift p (p.obj x) x := rfl

lemma eq_of_ObjLift {p : C ⥤ S} {U : S} {x : C} (h : ObjLift p U x) : p.obj x = U := h

lemma ObjLiftOpp (p : C ⥤ S) (U : S) (x : C) : ObjLift p U x ↔ ObjLift p.op (op U) (op x) :=
by
  constructor
  intro h
  have h1 : p.op.obj (op x) = op U :=
    by
      rw [op_obj, op_inj_iff]
      exact h
  exact h1
  intro h
  have h1 : p.obj x = U :=
    by
      rw [←op_inj_iff, ←op_obj]
      exact h
  exact h1

--lemma eqToHom (U V : C) (h : U = V) : U ≅ V := by rw [h]

def HomLift (p : C ⥤ S) {x y : C} {U V : S} (f : p.obj x ⟶ p.obj y) (φ : x ⟶ y) (h₁ : ObjLift p U x)
  (h₂ : ObjLift p V y) : Prop := CommSq (p.map φ) (𝟙 (p.obj x)) (𝟙 (p.obj y)) f

--lemma HomLiftOpp (p : C ⥤ S) {x y : C} {U V : S} (f : U ⟶ V) (φ : x ⟶ y) (h₁ : ObjLift p U x)
--  (h₂ : ObjLift p V y) : (HomLift p f φ h₁ h₂) ↔ (Homlift p.op f.op φ.op ((ObjLiftOpp p U x).1
--   h₁) ((ObjLiftOpp p V y).1 h₂)) :=
--by sorry

class IsFiberedInGroupoids (p : C ⥤ S) : Prop where
  (LiftHom {y : C} {X : S} (f : X ⟶ p.obj y) : 
    ∃ (x : C) (φ : x ⟶ y) (hx : p.obj x = X), 
      CommSq (p.map φ) (eqToHom hx) (𝟙 (p.obj y)) f)
  (IsCartesian {x y z : C} {φ : y ⟶ x} {ψ : z ⟶ x} {f : p.obj z ⟶ p.obj y}
  (hy : f ≫ (p.map φ) = p.map ψ) :
    ∃! (χ : z ⟶ y), CommSq f (𝟙 (p.obj z)) (𝟙 (p.obj y)) (p.map χ))

class IsCofiberedInGroupoids (p : C ⥤ S) : Prop where
  (LiftHom {x : C} {Y : S} (f : p.obj x ⟶ Y) : 
    ∃ (y : C) (φ : x ⟶ y) (hy : Y = p.obj y), 
      CommSq f (𝟙 (p.obj x)) (eqToHom hy) (p.map φ))
  (IsCoCartesian { x y z : C} {φ : x ⟶ y} {ψ : x ⟶ z} {f : p.obj y ⟶ p.obj z}
  (hy : (p.map φ) ≫ f = p.map ψ) :
    ∃! (χ : y ⟶ z), CommSq (p.map χ) (𝟙 (p.obj y)) (𝟙 (p.obj z)) f)
  
-- TODO possibly rewrite proof after making CofiberedInGroupoids "symm" wrt FiberedInGroupoids

lemma IsCofiberedInGroupoidsOpp (p : C ⥤ S) [hp : IsCofiberedInGroupoids p] : IsFiberedInGroupoids p.op :=
by
  rcases hp with ⟨hlift, hcart⟩
  constructor
  · intro y X f
    rcases hlift f.unop with ⟨x, φ, unop_obj_lift, unop_hom_lift⟩
    existsi op x
    existsi op φ
    rw [←op_inj_iff, ←op_obj, op_unop] at unop_obj_lift
    existsi unop_obj_lift.symm
    rw [op_map]
    have h1 : Quiver.Hom.unop (op φ) = φ := by rfl
    rw [h1]
    have h2 := CommSq.op unop_hom_lift
    simp at h2
    exact h2
  intro x y z φ ψ f h_comp
  rw [op_map, ←(Quiver.Hom.op_unop f), ←op_comp, op_map] at h_comp
  have h2 := Quiver.Hom.op_inj h_comp
  rcases hcart h2 with ⟨χ, χ_comm, χ_unique⟩
  let χ_op := χ.op
  simp at χ_op
  existsi χ_op
  constructor
  · simp
    apply CommSq.op
    simp
    exact χ_comm
  intro g g_comm
  have h1 := χ_unique (g.unop)
  have h2 := CommSq.unop g_comm
  simp at h2
  have h3 := h1 h2
  apply Quiver.Hom.unop_inj
  exact h3

/-
POSSIBLE TODO:
1. Define Fiber category + show its a groupoid
2. Show cats fibered in groupoids form a 2-category
3. Define cat MOR(F, Gz)

-/
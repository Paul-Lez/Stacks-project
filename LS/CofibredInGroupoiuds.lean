import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.CommSq


universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Opposite

variable {S : Type u₁} {C : Type u₂} {D : Type u₃} [Category S] [Category C] [Category D]

namespace ObjLift

def ObjLift (p : C ⥤ S) (U : S) (x : C) : Prop := p.obj x = U

lemma LiftImage (p : C ⥤ S) (x : C) : ObjLift p (p.obj x) x := rfl

lemma eq {p : C ⥤ S} {U : S} {x : C} (h : ObjLift p U x) : p.obj x = U := h

lemma Opp (p : C ⥤ S) (U : S) (x : C) : ObjLift p U x ↔ ObjLift p.op (op U) (op x) :=
by rw [ObjLift, ObjLift, op_obj, unop_op, op_inj_iff]

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
  (IsCoCartesian {x y z : C} {φ : x ⟶ y} {ψ : x ⟶ z} {f : p.obj y ⟶ p.obj z}
  (hy : (p.map φ) ≫ f = p.map ψ) :
    ∃! (χ : y ⟶ z), CommSq (p.map χ) (𝟙 (p.obj y)) (𝟙 (p.obj z)) f)

--def lift

-- TODO possibly rewrite proof after making CofiberedInGroupoids "symm" wrt FiberedInGroupoids

lemma IsCofiberedInGroupoidsOpp (p : C ⥤ S) [hp : IsCofiberedInGroupoids p] :
  IsFiberedInGroupoids p.op :=
by
  rcases hp with ⟨hlift, hcart⟩
  refine ⟨fun f => ?_, fun h_comp => ?_⟩
  · rcases hlift f.unop with ⟨x, φ, unop_obj_lift, unop_hom_lift⟩
    existsi op x, op φ
    rw [←op_inj_iff, ←op_obj, op_unop] at unop_obj_lift
    existsi unop_obj_lift.symm
    simpa only [op_obj, unop_op, op_unop, eqToHom_op, op_id, Quiver.Hom.op_unop] using CommSq.op unop_hom_lift
  rcases hcart (Quiver.Hom.op_inj h_comp) with ⟨χ, χ_comm, χ_unique⟩
  refine ⟨χ.op, ⟨?_, fun g g_comm => Quiver.Hom.unop_inj ((χ_unique (g.unop)) (CommSq.unop g_comm))⟩⟩
  simpa only [op_obj, op_map, Quiver.Hom.unop_op, op_obj, Quiver.Hom.op_unop, op_id] using CommSq.op χ_comm

/-
POSSIBLE TODO:
1. Define Fiber category + show its a groupoid
2. Show cats fibered in groupoids form a 2-category
3. Define cat MOR(F, G)

-/
namespace IsFiberedInGroupoidHom

-- Define morphisms for categories fibred in groupoids
def IsFiberedInGroupoidHom (p : C ⥤ S) (q : D ⥤ S) (F : C ⥤ D) : Prop := F.comp q = p

lemma IsFiberedInGroupoidHom.Id (p : C ⥤ S) : IsFiberedInGroupoidHom p p (Functor.id C) := rfl

lemma comp (p : C ⥤ S) (q : D ⥤ S) (f : C ⥤ D) (h : IsFiberedInGroupoidHom p q f) :
  f.comp q = p := h

lemma ProjEq {p : C ⥤ S} {q : D ⥤ S} {f g : C ⥤ D}
  (h : IsFiberedInGroupoidHom p q f) (h' : IsFiberedInGroupoidHom p q g) (a : C) :
   q.obj (f.obj a) = q.obj (g.obj a) :=
by rw [←Functor.comp_obj, ←Functor.comp_obj, h, h']

lemma IsObjLift_left {p : C ⥤ S} {q : D ⥤ S} {f : C ⥤ D}
  (hf : IsFiberedInGroupoidHom p q f) (a : C) : ObjLift p (q.obj $ f.obj a) a :=
by rw [←Functor.comp_obj, hf] ; apply ObjLift.LiftImage

lemma IsObjLift_right {p : C ⥤ S} {q : D ⥤ S} {f : C ⥤ D}
  (hf : IsFiberedInGroupoidHom p q f) (a : C) : ObjLift q (p.obj a) (f.obj a) :=
by rw [←hf] ; apply ObjLift.LiftImage

end IsFiberedInGroupoidHom

open ObjLift IsFiberedInGroupoidHom

def IsFiberedInGroupoid2HomProp {p : C ⥤ S} {q : D ⥤ S} (f g : C ⥤ D)
  (hf : IsFiberedInGroupoidHom p q f) (hg : IsFiberedInGroupoidHom p q g) (α : f ⟶ g) : Prop := ∀ (a : C),
  HomLift q (eqToHom (ProjEq hf hg a)) (CategoryTheory.NatTrans.app α a) (LiftImage q (f.obj a)) (LiftImage q (g.obj a))


--#check IsFiberedInGroupoid2HomProp


/- variable (J : GrothendieckTopology S)

class Stack {p : C ⥤ S} (hp : IsFiberedInGroupoids p) : Prop where
  (GlueMorphism : ∀ (S : J.sieves) (a b : C) {pb : S → C} {pbm : ∀ (s : S), (pb s → b)},
      ) -/


--def IsFiberedInGroupoid2CommSq

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

lemma toHom_eq_eqToHom {p : C ⥤ S} {U : S} {x : C} (hx : ObjLift p U x) :
  toHom hx = eqToHom hx := rfl

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
  (hy : f ≫ (p.map φ) = p.map ψ) : ∃! (χ : z ⟶ y), CommSq f (𝟙 (p.obj z)) (𝟙 (p.obj y)) (p.map χ))

def IsPullback (p : C ⥤ S) {x y : C} {X : S} (f : X ⟶ p.obj y)
  (φ : x ⟶ y) (hx : ObjLift p X x) : Prop :=  CommSq (p.map φ) (eqToHom hx) (𝟙 (p.obj y)) f

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


variable (J : GrothendieckTopology S)

variable {𝒳 𝒮 : Type u₁} [Category 𝒳] [Category 𝒮]

lemma LiftHom' {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {b : 𝒳} (hb : ObjLift p S b) (f : R ⟶ S) :
  ∃ (a : 𝒳) (ha : ObjLift p R a) (φ : a ⟶ b), HomLift p f φ ha hb :=
by
  set f' : R ⟶ p.obj b := f ≫ eqToHom hb.symm with hf'
  rcases hp.LiftHom f' with ⟨a, φ', h, hφ'⟩
  existsi a, h, φ'
  rw [HomLift]
  constructor
  rcases hφ' with ⟨hφ⟩
  simp only [hf', Category.comp_id] at hφ
  simp only [hφ, toHom_eq_eqToHom, toHom_eq_eqToHom, comp_eqToHom_iff, eqToHom_comp_iff, comp_eqToHom_iff, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans, Category.comp_id]

/-
(IsCartesian {x y z : C} {φ : y ⟶ x} {ψ : z ⟶ x} {f : p.obj z ⟶ p.obj y}
  (hy : f ≫ (p.map φ) = p.map ψ) :
    ∃! (χ : z ⟶ y), CommSq f (𝟙 (p.obj z)) (𝟙 (p.obj y)) (p.map χ))
-/


/- lemma  (p : 𝒳 ⥤ 𝒮) (hp : IsFiberedInGroupoids p)
  (R S T : 𝒮) (a b c : 𝒳) (ha : ObjLift p R a) (hb : ObjLift p S b) (hc : ObjLift p T c)
  (f : R ⟶ S) (g : S ⟶ T) (ψ : b ⟶ c)
  (ρ : a ⟶ c)  -/



lemma PullbackUniversalProperty {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  (R S T : 𝒮) (a b c : 𝒳) (ha : ObjLift p R a) (hb : ObjLift p S b) (hc : ObjLift p T c)
  (f : R ⟶ S) (g : S ⟶ T) (ψ : b ⟶ c)
  (ρ : a ⟶ c)
  (HCS : HomLift p g ψ hb hc)
  (HCS' : HomLift p (f ≫ g) ρ ha hc) :
  ∃! φ : a ⟶ b, HomLift p f φ ha hb ∧ ρ = φ ≫ ψ :=
by
  set f' : p.obj a ⟶ p.obj b := eqToHom ha ≫ f ≫ eqToHom hb.symm with hf'
  set g' : p.obj b ⟶ p.obj c := eqToHom hb ≫ g ≫ eqToHom hc.symm with hg'
  set temp := p.map ψ
  have : f' ≫ p.map ψ = p.map ρ
  · sorry
  rcases hp.IsCartesian this with ⟨χ, hχ⟩
  existsi χ
  constructor
  · simp only
    constructor
    · rw [HomLift]
      constructor
      rcases hχ.left with ⟨h⟩
      simp only [Category.comp_id, Category.id_comp] at h
      rw [←h]
      simp only [Category.assoc, comp_eqToHom_iff, eqToHom_comp_iff, eqToHom_trans, toHom_eq_eqToHom,
        eqToHom_refl, Category.comp_id, eqToHom_trans_assoc, Category.id_comp]
    · sorry
  · intros y hy
    apply hχ.right
    rw [HomLift] at hy
    rcases hy.left with ⟨hy'⟩
    constructor
    rw [hf']
    sorry

  --rcases HomLift' hp hb f with ⟨a, ha, φ, hφ⟩
  --existsi φ



/- lemma test {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  (S T : 𝒮) (a a' b : C) (ha : ObjLift p S a) (ha' : ObjLift p S a') -/


/- lemma test {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  (S : 𝒮) (I : J.sieves S) (a : 𝒳) (ha : ObjLift p S a) : -/


def Gluing_Prop {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  (S : 𝒮) (I : J.sieves S) (a b : 𝒳) (ha : ObjLift p S a)
  (hb : ObjLift p S b)
  {pb : I → 𝒳}
  {pbm : ∀ (s : I), (pb s → b)}
  {hpb : ∀ s : I, ObjLift p s (pb s) }
  {hpbm : ∀ i : I, HomLift p s (pbm s) (hpb s) hb}
  : true := sorry




/- class Stack {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p) : Prop where
  (GlueMorphism : ∀ (S : 𝒮) (I : J.sieves S) (a b : 𝒳) (ha : ObjLift p S a)
  (hb : ObjLift p S b)
  {pb : I → 𝒳}
  {pbm : ∀ (s : I), (pb s → b)}
  {hpb : ∀ s : I, ObjLift p s (pb s) }
  {hpbm : ∀ i : I, HomLift p s (pbm s) 1

  }, true)   -/


--def IsFiberedInGroupoid2CommSq

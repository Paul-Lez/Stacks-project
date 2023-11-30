import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Sites.Grothendieck
import LS.FiberedCategories


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

lemma HomLift_comp (p : C ⥤ S) {x y z: C} {U V W : S} (f : U ⟶ V) (g : V ⟶ W)
(φ : x ⟶ y) (ψ : y ⟶ z) (h₁ : ObjLift p U x)
(h₂ : ObjLift p V y) (h₃ : ObjLift p W z) (h₄ : HomLift p f φ h₁ h₂) (h₅ : HomLift p g ψ h₂ h₃) :
  HomLift p (f ≫ g) (φ ≫ ψ) h₁ h₃ := sorry

--lemma HomLiftOpp (p : C ⥤ S) {x y : C} {U V : S} (f : U ⟶ V) (φ : x ⟶ y) (h₁ : ObjLift p U x)
--  (h₂ : ObjLift p V y) : (HomLift p f φ h₁ h₂) ↔ (Homlift p.op f.op φ.op ((ObjLiftOpp p U x).1
--   h₁) ((ObjLiftOpp p V y).1 h₂)) :=
--by sorry

class IsFiberedInGroupoids (p : C ⥤ S) : Prop where
  (LiftHom {y : C} {X : S} (f : X ⟶ p.obj y) :
    ∃ (x : C) (φ : x ⟶ y) (hx : p.obj x = X),
      CommSq (p.map φ) (eqToHom hx) (𝟙 (p.obj y)) f)
  (IsCartesian {x y : C} (φ : y ⟶ x) :  IsCartesian p φ)

/- def IsPullback (p : C ⥤ S) {x y : C} {X : S} (f : X ⟶ p.obj y)
  (φ : x ⟶ y) (hx : ObjLift p X x) : Prop :=  CommSq (p.map φ) (eqToHom hx) (𝟙 (p.obj y)) f -/

lemma IsFiberedInGroupoids.id : IsFiberedInGroupoids (Functor.id S) :=
by
  constructor
  · intros y X f
    existsi X, f
    simp only [id_obj, Functor.id_map, eqToHom_refl, exists_prop, true_and, Category.comp_id, Category.id_comp]
    constructor
    simp only [Category.comp_id, Category.id_comp]
  intros x y φ
  constructor
  intros z ψ f h
  existsi f
  simp only [id_obj, Functor.id_map, and_true, and_imp]
  simp only [id_obj, Functor.id_map] at h
  refine ⟨h, ?_⟩
  intros y _ hyy
  exact hyy.symm

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

-- 2-morphisms of categories fibered in groupoids
def IsFiberedInGroupoid2HomProp {p : C ⥤ S} {q : D ⥤ S} (f g : C ⥤ D)
  (hf : IsFiberedInGroupoidHom p q f) (hg : IsFiberedInGroupoidHom p q g) (α : f ⟶ g) : Prop := ∀ (a : C),
  HomLift q (eqToHom (ProjEq hf hg a)) (CategoryTheory.NatTrans.app α a) (LiftImage q (f.obj a)) (LiftImage q (g.obj a))

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category 𝒳] [Category 𝒮]

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

/- The following code is designed to help work with a specific choice of a pullback, which makes life easier -/
noncomputable def PullbackObj {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {b : 𝒳} (hb : ObjLift p S b) (f : R ⟶ S) : 𝒳 :=
Classical.choose (LiftHom' hp hb f)

lemma PullbackObjLift {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {b : 𝒳} (hb : ObjLift p S b) (f : R ⟶ S) : ObjLift p R (PullbackObj hp hb f) :=
Classical.choose (Classical.choose_spec (LiftHom' hp hb f))

noncomputable def PullbackMap {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {b : 𝒳} (hb : ObjLift p S b) (f : R ⟶ S) : PullbackObj hp hb f ⟶ b :=
Classical.choose $ Classical.choose_spec (Classical.choose_spec (LiftHom' hp hb f))

lemma PullbackHomLift {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {b : 𝒳} (hb : ObjLift p S b) (f : R ⟶ S) :
  HomLift p f (PullbackMap hp hb f) (PullbackObjLift hp hb f) hb :=
Classical.choose_spec $ Classical.choose_spec (Classical.choose_spec (LiftHom' hp hb f))

def IsPullback {p : 𝒳 ⥤ 𝒮}
  {R S : 𝒮} {a b : 𝒳} (hb : ObjLift p S b) (f : R ⟶ S) (φ : a ⟶ b) : Prop := ∃ ha : ObjLift p R a,
  HomLift p f φ ha hb

def IsPullbackObjLift {p : 𝒳 ⥤ 𝒮}
  {R S : 𝒮} {a b : 𝒳} {hb : ObjLift p S b} {f : R ⟶ S} {φ : a ⟶ b} (hφ : IsPullback hb f φ) :
  ObjLift p R a :=
Classical.choose hφ

lemma PullbackIsPullback {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {b : 𝒳} (hb : ObjLift p S b) (f : R ⟶ S) :
    IsPullback hb f (PullbackMap hp hb f) := by
  use (PullbackObjLift hp hb f) ; exact PullbackHomLift hp hb f

lemma IsPullback_HomLift {p : 𝒳 ⥤ 𝒮}
  {R S : 𝒮} {a b : 𝒳} {φ : a ⟶ b} {hb : ObjLift p S b} {f : R ⟶ S} (hφ : IsPullback hb f φ) :
  HomLift p f φ (IsPullbackObjLift hφ) hb :=
Classical.choose_spec hφ

lemma PullbackUniversalPropertyExistsUnique {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a b c : 𝒳} {ha : ObjLift p R a} {hb : ObjLift p S b} {hc : ObjLift p T c}
  {f : R ⟶ S} {g : S ⟶ T} {ψ : b ⟶ c}
  {ρ : a ⟶ c}
  (HCS : HomLift p g ψ hb hc)
  (HCS' : HomLift p (f ≫ g) ρ ha hc) :
  ∃! φ : a ⟶ b, HomLift p f φ ha hb ∧ ρ = φ ≫ ψ :=
by
  set f' : p.obj a ⟶ p.obj b := eqToHom ha ≫ f ≫ eqToHom hb.symm with hf'
  set g' : p.obj b ⟶ p.obj c := eqToHom hb ≫ g ≫ eqToHom hc.symm
  set temp := p.map ψ
  have : f' ≫ p.map ψ = p.map ρ
  · rcases HCS' with ⟨HCS'⟩
    rw [toHom_eq_eqToHom, comp_eqToHom_iff] at HCS' -- TODO: what does toHom do???
    rw [HCS']
    rw [toHom_eq_eqToHom]
    rcases HCS with ⟨HCS⟩
    rw [toHom_eq_eqToHom, comp_eqToHom_iff] at HCS
    rw [HCS]
    rw [toHom_eq_eqToHom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rcases (hp.IsCartesian ψ).isCartesian this with ⟨χ, hχ⟩
  existsi χ
  constructor
  · simp only
    constructor
    · rw [HomLift]
      constructor
      rcases hχ.left with ⟨_, h⟩
      rw [←h, hf']
      simp only [Category.assoc, comp_eqToHom_iff, eqToHom_comp_iff, eqToHom_trans, toHom_eq_eqToHom,
        eqToHom_refl, Category.comp_id, eqToHom_trans_assoc, Category.id_comp]
    · exact hχ.left.1.symm
  · intros y hy
    apply hχ.right
    rw [HomLift] at hy
    rcases hy.left with ⟨hy'⟩
    constructor
    exact hy.2.symm
    rw [hf']
    rw [toHom_eq_eqToHom, toHom_eq_eqToHom] at hy' -- TODO: toHom stuff
    rw [←Category.assoc, ←hy']
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

noncomputable def PullbackUniversalPropertyMap {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a b c : 𝒳} {ha : ObjLift p R a} {hb : ObjLift p S b} {hc : ObjLift p T c}
  {f : R ⟶ S} {g : S ⟶ T} {ψ : b ⟶ c}
  {ρ : a ⟶ c}
  (HCS : HomLift p g ψ hb hc)
  (HCS' : HomLift p (f ≫ g) ρ ha hc) : a ⟶ b :=
Classical.choose (PullbackUniversalPropertyExistsUnique hp HCS HCS')

@[simp]
lemma PullbackUniversalPropertyDiagram {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a b c : 𝒳} {ha : ObjLift p R a} {hb : ObjLift p S b} {hc : ObjLift p T c}
  {f : R ⟶ S} {g : S ⟶ T} {ψ : b ⟶ c}
  {ρ : a ⟶ c}
  (HCS : HomLift p g ψ hb hc)
  (HCS' : HomLift p (f ≫ g) ρ ha hc) :
    PullbackUniversalPropertyMap hp HCS HCS' ≫ ψ = ρ :=
(Classical.choose_spec (PullbackUniversalPropertyExistsUnique hp HCS HCS')).left.right.symm

lemma PullbackUniversalPropertyMap_HomLift {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a b c : 𝒳} {ha : ObjLift p R a} {hb : ObjLift p S b} {hc : ObjLift p T c}
  {f : R ⟶ S} {g : S ⟶ T} {ψ : b ⟶ c}
  {ρ : a ⟶ c}
  (HCS : HomLift p g ψ hb hc)
  (HCS' : HomLift p (f ≫ g) ρ ha hc) :
  HomLift p f (PullbackUniversalPropertyMap hp HCS HCS') ha hb :=
(Classical.choose_spec (PullbackUniversalPropertyExistsUnique hp HCS HCS')).left.left

lemma PullbackUniversalMap_unique {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a b c : 𝒳} {ha : ObjLift p R a} {hb : ObjLift p S b} {hc : ObjLift p T c}
  {f : R ⟶ S} {g : S ⟶ T} {ψ : b ⟶ c}
  {ρ : a ⟶ c} {φ : a ⟶ b} (hφ : φ ≫ ψ = ρ) (hφ' : HomLift p f φ ha hb)
  (HCS : HomLift p g ψ hb hc)
  (HCS' : HomLift p (f ≫ g) ρ ha hc) : φ = PullbackUniversalPropertyMap hp HCS HCS' :=
(Classical.choose_spec (PullbackUniversalPropertyExistsUnique hp HCS HCS')).right _ ⟨hφ', hφ.symm⟩

-- In this section we prove various properties about the naturality of pullbacks
section Pullback_Induced_maps

noncomputable def IsPullbackInducedMap {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {a a' b : 𝒳} {hb : ObjLift p S b}
  {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ⟶ R}
  (H : g ≫ f = f') {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback hb f φ) (hφ' : IsPullback hb f' φ') : a' ⟶ a :=
PullbackUniversalPropertyMap hp (IsPullback_HomLift hφ)
  (IsPullback_HomLift (show IsPullback hb (g ≫ f ) φ' by rwa [←H] at hφ'))

@[simp]
lemma IsPullbackInducedMap_self_eq_id {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {a b : 𝒳} (hb : ObjLift p S b) {f : R ⟶ S} {φ : a ⟶ b}
  (hφ : IsPullback hb f φ) : IsPullbackInducedMap hp (show 𝟙 R ≫ f = f by simp) hφ hφ = 𝟙 a := by
apply (PullbackUniversalMap_unique _ _ _ _ _).symm
· simp only [Category.id_comp]
· rw [HomLift]
  constructor
  simp only [map_id, Category.id_comp, Category.comp_id]

lemma IsPullbackInducedMap_eq_PullbackUniversalPropertyMap {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {a a' b : 𝒳} (hb : ObjLift p S b)
  {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ⟶ R}
  (H : g ≫ f = f') {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback hb f φ) (hφ' : IsPullback hb f' φ') :
  IsPullbackInducedMap hp H hφ hφ' = PullbackUniversalPropertyMap hp (IsPullback_HomLift hφ)
  (IsPullback_HomLift (show IsPullback hb (g ≫ f ) φ' by rwa [←H] at hφ')) := rfl

def IsPullbackNaturalityHom {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {a a' b b' : 𝒳} {hb : ObjLift p S b} {hb' : ObjLift p S b'}
  {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b'}
  (hφ : IsPullback hb f φ) (hφ' : IsPullback hb' f φ')
  (ψ : b ⟶ b') (hψ : HomLift p (𝟙 S) ψ hb hb')
  : a ⟶ a' := sorry

@[simp]
lemma IsPullbackInducedMapDiagram {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {a a' b : 𝒳} (hb : ObjLift p S b)
  {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ⟶ R}
  (H : g ≫ f = f') {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback hb f φ) (hφ' : IsPullback hb f' φ') :
  IsPullbackInducedMap hp H hφ hφ' ≫ φ = φ' := by
  rw [IsPullbackInducedMap_eq_PullbackUniversalPropertyMap, PullbackUniversalPropertyDiagram]

lemma IsPullbackInducedMap_HomLift {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {a a' b : 𝒳} (hb : ObjLift p S b)
  {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ⟶ R}
  (H : g ≫ f = f') {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback hb f φ) (hφ' : IsPullback hb f' φ') :
  HomLift p g (IsPullbackInducedMap hp H hφ hφ') (IsPullbackObjLift hφ') (IsPullbackObjLift hφ) :=
sorry

lemma IsPullbackInducedMap_unique {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {a a' b : 𝒳} (hb : ObjLift p S b)
  {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ⟶ R}
  (H : g ≫ f = f') {φ : a ⟶ b} {φ' : a' ⟶ b} {ψ : a' ⟶ a}
  {hφ : IsPullback hb f φ} {hφ' : IsPullback hb f' φ'}
  (hψ : HomLift p g ψ (IsPullbackObjLift hφ') (IsPullbackObjLift hφ))
  (hψ' : ψ ≫ φ = φ') : ψ = IsPullbackInducedMap hp H hφ hφ' := sorry

@[simp]
lemma IsPullbackInducedMap_comp {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' R'' S: 𝒮} {a a' a'' b : 𝒳} (hb : ObjLift p S b)
  {f : R ⟶ S} {f' : R' ⟶ S} {f'' : R'' ⟶ S} {g : R' ⟶ R} {h : R'' ⟶ R'}
  (H : g ≫ f = f') (H' : h ≫ f' = f'') {φ : a ⟶ b} {φ' : a' ⟶ b} {φ'' : a'' ⟶ b}
  (hφ : IsPullback hb f φ) (hφ' : IsPullback hb f' φ') (hφ'' : IsPullback hb f'' φ''):
  IsPullbackInducedMap hp H' hφ' hφ'' ≫ IsPullbackInducedMap hp H hφ hφ'
  = IsPullbackInducedMap hp (show (h ≫ g) ≫ f = f'' by rwa [Category.assoc, H]) hφ hφ'' := by
  apply IsPullbackInducedMap_unique hp
  · apply HomLift_comp
    · apply IsPullbackInducedMap_HomLift
    · apply IsPullbackInducedMap_HomLift
  · simp only [Category.assoc, IsPullbackInducedMapDiagram]

noncomputable def IsPullbackIsoOfIso {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {a a' b : 𝒳} (hb : ObjLift p S b)
  {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ≅ R}
  (H : g.hom ≫ f = f') {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback hb f φ) (hφ' : IsPullback hb f' φ') : a' ≅ a where
    hom := IsPullbackInducedMap hp H hφ hφ'
    inv :=  IsPullbackInducedMap hp (show g.symm.hom ≫ f' = f by sorry) hφ' hφ
    hom_inv_id := by simp
    inv_hom_id := by simp

def IsPullbackNaturalityIso {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {a a' b b' : 𝒳} {hb : ObjLift p S b} {hb' : ObjLift p S b'}
  {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b'}
  (hφ : IsPullback hb f φ) (hφ' : IsPullback hb' f φ')
  (ψ : b ≅ b') (hψ : HomLift p (𝟙 S) ψ.hom hb hb') : a ≅ a' := sorry

lemma IsPullbackIsoOfIso_hom {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {a a' b : 𝒳} (hb : ObjLift p S b)
  {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ≅ R}
  (H : g.hom ≫ f = f') {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback hb f φ) (hφ' : IsPullback hb f' φ') :
(IsPullbackIsoOfIso hp hb H hφ hφ').hom = IsPullbackInducedMap hp hb H hφ hφ' := rfl

def IsPullbackIso {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {a a' b : 𝒳} {hb : ObjLift p S b} {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b}
   (hφ : IsPullback hb f φ) (hφ' : IsPullback hb f φ') : a ≅ a' where
     hom := _ --IsPullbackNaturalityHom hp
     inv := _
     hom_inv_id := _
     inv_hom_id := _

def PullbackObjIsoOfIso {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {b : 𝒳} (hb : ObjLift p S b)
  (f : R ⟶ S) (f' : R' ⟶ S)
  (g : R' ≅ R)
  (H : g.hom ≫ f = f') : PullbackObj hp hb f' ≅ PullbackObj hp hb f := sorry

lemma PullbackUniqueₐ {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  (R S T : 𝒮) (a b c : 𝒳) (ha : ObjLift p R a) (hb : ObjLift p S b) (hc : ObjLift p T c)
  (f : R ⟶ S) (g : S ⟶ T) (ψ : b ⟶ c)
  (ρ : a ⟶ c) (φ φ' : a ⟶ b)
  (HCSψ : HomLift p g ψ hb hc)
  (HCSρ : HomLift p (f ≫ g) ρ ha hc)
  (HCSφ : HomLift p f φ ha hb)
  (HCSφ' : HomLift p f φ' ha hb)
  (hφ : φ ≫ ψ = ρ)
  (hφ' : φ' ≫ ψ = ρ) : φ = φ' := by
  obtain ⟨φ'', _, h'⟩ := PullbackUniversalPropertyExistsUnique hp HCSψ HCSρ
  rw [h' φ ⟨HCSφ, hφ.symm⟩, h' φ' ⟨HCSφ', hφ'.symm⟩]

lemma PullbackIsoExists {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {a a' b : 𝒳} {ha : ObjLift p R a} {ha' : ObjLift p R a'} {hb : ObjLift p S b}
  {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b}
  (HL : HomLift p f φ ha hb)
  (HL' : HomLift p f φ' ha' hb)
  : ∃! ψ : a ≅ a', ψ.hom ≫ φ' = φ :=
by sorry

noncomputable def PullbackIso {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {a a' b : 𝒳} {ha : ObjLift p R a} {ha' : ObjLift p R a'} {hb : ObjLift p S b}
  {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b}
  (HL : HomLift p f φ ha hb)
  (HL' : HomLift p f φ' ha' hb) : a ≅ a' :=
Classical.choice $ nonempty_of_exists (ExistsUnique.exists
  (PullbackIsoExists hp HL HL'))

lemma PullbackIsoComm  {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {a a' b : 𝒳} {ha : ObjLift p R a} {ha' : ObjLift p R a'} {hb : ObjLift p S b}
  {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b}
  (HL : HomLift p f φ ha hb)
  (HL' : HomLift p f φ' ha' hb) : (PullbackIso hp HL HL').hom ≫ φ' = φ :=
by sorry

lemma PullbackIsoUnique {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {a a' b : 𝒳} {ha : ObjLift p R a} {ha' : ObjLift p R a'} {hb : ObjLift p S b}
  {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b}
  (HL : HomLift p f φ ha hb)
  (HL' : HomLift p f φ' ha' hb)
  {f : a ⟶ a'}  (hf : f ≫ φ' = φ) : f = (PullbackIso hp HL HL').hom
:= sorry

attribute [local instance] CategoryTheory.Limits.hasPullback_symmetry

/- Given a diagram
      R × T ≅ T × R ----> R
                |       f |
                |    g    |
                T ------> S
and a : 𝒳 above S, we have a canonical isomorphism a|_R×T ≅ a|_T×R -/
noncomputable def PullbackPullbackIso {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a : 𝒳} (ha : ObjLift p S a) (f : R ⟶ S) (g : T ⟶ S)
  [CategoryTheory.Limits.HasPullback f g] :
  PullbackObj hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _≫ f)
    ≅ PullbackObj hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ g f
      (CategoryTheory.Limits.hasPullback_symmetry f g) ≫ g) := by
  have lem₁ : IsPullback ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _≫ f)  (PullbackMap hp ha
    (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _≫ f))
  · apply PullbackIsPullback hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _≫ f)
  have lem₂ : IsPullback ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ g f _≫ g)  (PullbackMap hp ha
    (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ g f (CategoryTheory.Limits.hasPullback_symmetry f g) ≫ g))
  · apply PullbackIsPullback hp ha
  have H : (Limits.pullbackSymmetry f g).hom ≫ (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ g f (CategoryTheory.Limits.hasPullback_symmetry f g) ≫ g) = (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _≫ f)
  · rw [Limits.pullbackSymmetry_hom_comp_fst_assoc, Limits.pullback.condition]
  apply IsPullbackIsoOfIso hp ha H lem₂ lem₁

def pullback_comp_iso_pullback_pullback {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a : 𝒳} (ha : ObjLift p S a) (f : R ⟶ S) (g : T ⟶ R) :
  PullbackObj hp ha (g ≫ f) ≅ PullbackObj hp (PullbackObjLift hp ha f) g :=
sorry

def pullback_iso_pullback  {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a : 𝒳} (ha : ObjLift p S a) (f : R ⟶ S) (g : T ⟶ S)
  [CategoryTheory.Limits.HasPullback f g] :
  PullbackObj hp (PullbackObjLift hp ha f) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _)
    ≅ PullbackObj hp (PullbackObjLift hp ha g) (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f g
      _) := sorry

/- Given a diagram
      R × T ≅ T × R ----> R
                |       f |
                |    g    |
                T ------> S
and a : 𝒳 above R, we have a canonical isomorphism a|_R×T ≅ a|_T×R -/
noncomputable def PullbackPullbackIso' {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a : 𝒳} (ha : ObjLift p R a) (f : R ⟶ S) (g : T ⟶ S)
  [CategoryTheory.Limits.HasPullback f g] :
    PullbackObj hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _) ≅
      PullbackObj hp ha (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ g f _) :=
by
  --For now this is a tactic "proof" to make it more readable. This will be easy to inline!
  have lem₁ : IsPullback ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _)  (PullbackMap hp ha
    (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _))
  · apply PullbackIsPullback hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _)
  have lem₂ : IsPullback ha (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ g f _)  (PullbackMap hp ha
    (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ g f _))
  · apply PullbackIsPullback hp ha
  apply IsPullbackIsoOfIso hp ha (Limits.pullbackSymmetry_hom_comp_snd _ _) lem₂ lem₁

end Pullback_Induced_maps

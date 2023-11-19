import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Sites.Grothendieck


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
  (IsCartesian {x y z : C} {φ : y ⟶ x} {ψ : z ⟶ x} {f : p.obj z ⟶ p.obj y} :
    f ≫ (p.map φ) = p.map ψ →  ∃! (χ : z ⟶ y), CommSq f (𝟙 (p.obj z)) (𝟙 (p.obj y)) (p.map χ))

/- def IsPullback (p : C ⥤ S) {x y : C} {X : S} (f : X ⟶ p.obj y)
  (φ : x ⟶ y) (hx : ObjLift p X x) : Prop :=  CommSq (p.map φ) (eqToHom hx) (𝟙 (p.obj y)) f -/

class IsCofiberedInGroupoids (p : C ⥤ S) : Prop where
  (LiftHom {x : C} {Y : S} (f : p.obj x ⟶ Y) :
    ∃ (y : C) (φ : x ⟶ y) (hy : Y = p.obj y),
      CommSq f (𝟙 (p.obj x)) (eqToHom hy) (p.map φ))
  (IsCoCartesian {x y z : C} {φ : x ⟶ y} {ψ : x ⟶ z} {f : p.obj y ⟶ p.obj z} :
    (p.map φ) ≫ f = p.map ψ → ∃! (χ : y ⟶ z), CommSq (p.map χ) (𝟙 (p.obj y)) (𝟙 (p.obj z)) f)

lemma IsFiberedInGroupoids.id : IsFiberedInGroupoids (Functor.id S) :=
by
  constructor
  · intros y X f
    existsi X, f
    simp only [id_obj, Functor.id_map, eqToHom_refl, exists_prop, true_and, Category.comp_id, Category.id_comp]
    constructor
    simp only [Category.comp_id, Category.id_comp]
  · intros x y z φ ψ f h
    existsi f
    constructor
    simp only [id_obj, Functor.id_map]
    constructor
    simp only [Category.comp_id, Category.id_comp]
    intros y hy
    simp only [id_obj, Functor.id_map] at hy
    obtain ⟨w⟩ := hy
    simp only [Category.comp_id, Category.id_comp] at w
    exact w.symm

--def lift

-- TODO possibly rewrite proof after making CofiberedInGroupoids "symm" wrt FiberedInGroupoids

lemma IsCofiberedInGroupoidsOpp (p : C ⥤ S) (hp : IsCofiberedInGroupoids p) :
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

lemma IsFiberedInGroupoidsOpp (p : C ⥤ S) (hp : IsFiberedInGroupoids p):
  IsCofiberedInGroupoids p.op :=
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

lemma IsFiberedInGroupoids_iff_Op (p : C ⥤ S) : IsFiberedInGroupoids p ↔ IsCofiberedInGroupoids p.op :=
by
  refine ⟨fun hp => IsFiberedInGroupoidsOpp p hp, fun hp =>  sorry --apply IsCofiberedInGroupoidsOpp p hp}
  ⟩

lemma IsCoiberedInGroupoids.id : IsCofiberedInGroupoids (Functor.id Sᵒᵖ) :=
by simpa [show Functor.id Sᵒᵖ = (Functor.id S).op from rfl, ←IsFiberedInGroupoids_iff_Op]
  using IsFiberedInGroupoids.id
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
  {R S : 𝒮} {a b : 𝒳} (hb : ObjLift p S b) (f : R ⟶ S) (φ : a ⟶ b) (hφ : IsPullback hb f φ) : ObjLift p R a := sorry

lemma PullbackIsPullback {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {b : 𝒳} (hb : ObjLift p S b) (f : R ⟶ S) :
    IsPullback hb f (PullbackMap hp hb f) := sorry

def IsPullbackIso {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S : 𝒮} {a a' b : 𝒳} {hb : ObjLift p S b} {f : R ⟶ S} {φ : a ⟶ b} {φ' : a' ⟶ b}
   (hφ : IsPullback hb f φ) (hφ' : IsPullback hb f φ') : a ≅ a' :=
by sorry



/- def IsPullbackInducedMapExists {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a a' b b' : 𝒳} (hb : ObjLift p S b)
  (hb' : ObjLift p S b') (f : R ⟶ S) (φ : a ⟶ b) (φ' : a' ⟶ b') (ψ : a' ⟶ a)
  (hφ : IsPullbackDef hb f φ) (hφ' : IsPullbackDef hb' f φ') : ∃    -/

lemma PullbackUniversalPropertyExistsUnique {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a b c : 𝒳} {ha : ObjLift p R a} {hb : ObjLift p S b} {hc : ObjLift p T c}
  {f : R ⟶ S} {g : S ⟶ T} {ψ : b ⟶ c}
  {ρ : a ⟶ c}
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

def PullbackUniversalPropertyMap {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a b c : 𝒳} {ha : ObjLift p R a} {hb : ObjLift p S b} {hc : ObjLift p T c}
  {f : R ⟶ S} {g : S ⟶ T} {ψ : b ⟶ c}
  {ρ : a ⟶ c}
  (HCS : HomLift p g ψ hb hc)
  (HCS' : HomLift p (f ≫ g) ρ ha hc) : a ⟶ b :=
sorry

lemma PullbackUniversalPropertyDiagram {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a b c : 𝒳} {ha : ObjLift p R a} {hb : ObjLift p S b} {hc : ObjLift p T c}
  {f : R ⟶ S} {g : S ⟶ T} {ψ : b ⟶ c}
  {ρ : a ⟶ c}
  (HCS : HomLift p g ψ hb hc)
  (HCS' : HomLift p (f ≫ g) ρ ha hc) :
    PullbackUniversalPropertyMap hp HCS HCS' ≫ ψ = ρ := sorry

def PullbackObjInducedMap {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {b : 𝒳} /- {ha : ObjLift p R a} {ha' : ObjLift p R a'} -/ (hb : ObjLift p S b)
  (f : R ⟶ S) (f' : R' ⟶ S)
  {g : R' ⟶ R}
  (H : g ≫ f = f')
  --{φ : a ⟶ b} {φ' : a' ⟶ b}
  --(HL : HomLift p f φ ha hb) (HL' : HomLift p f φ' ha' hb)
  : PullbackObj hp hb f' ⟶ PullbackObj hp hb f :=
sorry

def IsPullbackInducedMap {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {a a' b : 𝒳} (hb : ObjLift p S b)
  {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ⟶ R}
  (H : g ≫ f = f') {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback hb f φ) (hφ' : IsPullback hb f' φ') : a' ⟶ a :=
by sorry

lemma IsPullbackInducedMapDiagram {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {a a' b : 𝒳} (hb : ObjLift p S b)
  {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ⟶ R}
  (H : g ≫ f = f') {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback hb f φ) (hφ' : IsPullback hb f' φ') :
IsPullbackInducedMap hp hb H hφ hφ' ≫ φ = φ' := sorry

def IsPullbackIsoOfIso {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {a a' b : 𝒳} (hb : ObjLift p S b)
  {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ≅ R}
  (H : g.hom ≫ f = f') {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback hb f φ) (hφ' : IsPullback hb f' φ') : a' ≅ a := sorry

lemma IsPullbackIsoOfIso_hom {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {a a' b : 𝒳} (hb : ObjLift p S b)
  {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ≅ R}
  (H : g.hom ≫ f = f') {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback hb f φ) (hφ' : IsPullback hb f' φ') :
  (IsPullbackIsoOfIso hp hb H hφ hφ').hom = IsPullbackInducedMap hp hb H hφ hφ' := sorry

def PullbackObjIsoOfIso {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {b : 𝒳} (hb : ObjLift p S b)
  (f : R ⟶ S) (f' : R' ⟶ S)
  (g : R' ≅ R)
  (H : g.hom ≫ f = f') : PullbackObj hp hb f' ≅ PullbackObj hp hb f := sorry

lemma PullbackIso_of_Iso_hom {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {b : 𝒳} (hb : ObjLift p S b)
  (f : R ⟶ S) (f' : R' ⟶ S)
  (g : R' ≅ R)
  (H : g.hom ≫ f = f') : (PullbackObjIsoOfIso hp hb f f' g H).hom = PullbackObjInducedMap hp hb f f' H := sorry

lemma PullbackUniqueₐ {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  (R S T : 𝒮) (a b c : 𝒳) (ha : ObjLift p R a) (hb : ObjLift p S b) (hc : ObjLift p T c)
  (f : R ⟶ S) (g : S ⟶ T) (ψ : b ⟶ c)
  (ρ : a ⟶ c) (φ φ' : a ⟶ b)
  (HCSψ : HomLift p g ψ hb hc)
  (HCSρ : HomLift p (f ≫ g) ρ ha hc)
  (HCSφ : HomLift p f φ ha hb)
  (HCSφ' : HomLift p f φ' ha hb)
  (hφ : φ ≫ ψ = ρ)
  (hφ' : φ' ≫ ψ = ρ) : φ = φ' :=
by
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
def PullbackPullbackIso {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a : 𝒳} (ha : ObjLift p S a) (f : R ⟶ S) (g : T ⟶ S)
  [CategoryTheory.Limits.HasPullback f g] :
  PullbackObj hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _≫ f)
    ≅ PullbackObj hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ g f
      (CategoryTheory.Limits.hasPullback_symmetry f g) ≫ g) :=
by
  have lem₁ : IsPullback ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _≫ f)  (PullbackMap hp ha
    (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _≫ f))
  · apply PullbackIsPullback hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _≫ f)
  have lem₂ : IsPullback ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ g f _≫ g)  (PullbackMap hp ha
    (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ g f (CategoryTheory.Limits.hasPullback_symmetry f g) ≫ g))
  · apply PullbackIsPullback hp ha
  have H : (Limits.pullbackSymmetry f g).hom ≫ (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ g f (CategoryTheory.Limits.hasPullback_symmetry f g) ≫ g) = (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _≫ f)
  · rw [Limits.pullbackSymmetry_hom_comp_fst_assoc, Limits.pullback.condition]
  apply IsPullbackIsoOfIso hp ha H lem₂ lem₁

/- Given a diagram
      R × T ≅ T × R ----> R
                |       f |
                |    g    |
                T ------> S
and a : 𝒳 above R, we have a canonical isomorphism a|_R×T ≅ a|_T×R -/
def PullbackPullbackIso' {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a : 𝒳} (ha : ObjLift p R a) (f : R ⟶ S) (g : T ⟶ S)
  [CategoryTheory.Limits.HasPullback f g] :
    PullbackObj hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _) ≅
      PullbackObj hp ha (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ g f _) :=
by
  have lem₁ : IsPullback ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _)  (PullbackMap hp ha
    (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _))
  · apply PullbackIsPullback hp ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _)
  have lem₂ : IsPullback ha (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _)  (PullbackMap hp ha
    (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ g f _))
  have H : (Limits.pullbackSymmetry f g).hom ≫ (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f g _)
    =  (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ g f _)
  · sorry
  apply IsPullbackIsoOfIso hp ha _ lem₂ lem₁
  · exact Iso.refl _
  · simp only [Iso.refl_hom, Category.id_comp]

def pullbackfibredprod {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R R' S : 𝒮} {a a' b : 𝒳} (ha : ObjLift p R a) (ha' : ObjLift p R' a') (hb : ObjLift p S b)
  {f : R ⟶ S} {f' : R' ⟶ S} [CategoryTheory.Limits.HasPullback f f'] :
  PullbackObj hp (PullbackObjLift hp hb f) (show Limits.pullback f f' ⟶ R from CategoryTheory.Limits.pullback.fst) ≅
    PullbackObj hp (PullbackObjLift hp hb f') (show Limits.pullback f f' ⟶ R' from CategoryTheory.Limits.pullback.snd)
    := sorry

variable (J : GrothendieckTopology 𝒮) (S Y : 𝒮) (I : Sieve S) (hI : I ∈ J.sieves S) (f : Y ⟶ S) (hf : I f)

def pullback_family_iso  {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  (S : 𝒮) (I : Sieve S) (hI : I ∈ J.sieves S)
  (hI' : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'), CategoryTheory.Limits.HasPullback f f')
  (a b : 𝒳) (ha : ObjLift p S a) (hb : ObjLift p S b)
  (φ : ∀ (Y : 𝒮) (f : Y ⟶ S) (hf : I f), PullbackObj hp ha f ⟶ b) : ∀ (Y Y' : 𝒮) (f : Y ⟶ S) (f' : Y' ⟶ S) (hf : I f) (hf' : I f'),
  PullbackObj hp (PullbackObjLift hp ha f) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf')) ≅
  PullbackObj hp (PullbackObjLift hp ha f') (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f f' (hI' hf hf')) :=
fun (Y Y' : 𝒮) (f : Y ⟶ S) (f' : Y' ⟶ S) (hf : I f) (hf' : I f') =>
by
  haveI := hI' hf hf'
  apply pullbackfibredprod hp (PullbackObjLift hp ha f) (PullbackObjLift hp ha f')

-- *** Morphisms glue ***
def Pullback_family {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  (S : 𝒮) (I : Sieve S) (hI : I ∈ J.sieves S)
  (hI' : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    CategoryTheory.Limits.HasPullback f f')
  (a b : 𝒳) (ha : ObjLift p S a) (hb : ObjLift p S b)
  (φ : ∀ (Y : 𝒮) (f : Y ⟶ S) (hf : I f), PullbackObj hp ha f ⟶ b) : Prop :=
∀ (Y Y' : 𝒮) (f : Y ⟶ S) (f' : Y' ⟶ S) (hf : I f) (hf' : I f'),
  (PullbackMap hp (PullbackObjLift hp ha f) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf')) ≫ (φ Y f hf))
  = (pullback_family_iso J hp S I hI hI' a b ha hb φ Y Y' f f' hf hf').hom ≫
    (PullbackMap hp (PullbackObjLift hp ha f') (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f f' (hI' hf hf')) ≫ (φ Y' f' hf'))

/- Todo: define the natural morphism
  `PullbackObj hp hb (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf') ≫ f) ⟶`
    `PullbackObj hp (ha hf) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf'))`
    Eventually this should maybe be inlined/reduced to more elementary definition -/
def objects_glue' {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  (S : 𝒮) (I : Sieve S) (hI : I ∈ J.sieves S) [Limits.HasPullbacks 𝒮]
  (hI' : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'), CategoryTheory.Limits.HasPullback f f')
  (a : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), 𝒳)
  (ha : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), ObjLift p Y (a hf))
  (α : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    PullbackObj hp (ha hf) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf'))
    ≅ PullbackObj hp (ha hf') (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f f' (hI' hf hf')))
  (hα : ∀ (Y Y' Y''': 𝒮) (f : Y ⟶ S) (f' : Y' ⟶ S) (f'' : Y'' ⟶ S) (hf : I f) (hf' : I f')
    (hf'' : I f''), true) -- fixme (Cocyle condition)
  (hα' : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    HomLift p (𝟙 (@CategoryTheory.Limits.pullback _ _ _ _ _ f f' (hI' hf hf'))) (α hf hf').hom sorry sorry):
  ∀ (Y Y' : 𝒮) (f : Y ⟶ S) (f' : Y' ⟶ S) (hf : I f) (hf' : I f') (b : 𝒳) (hb : ObjLift p S b),
  PullbackObj hp hb (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf') ≫ f) ⟶
    PullbackObj hp (ha hf) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf')) :=
by sorry
/-   intros Y Y' f f' hf hf' b hb
  have HCS := HomLift f
  apply PullbackUniversalPropertyMap -/

def CocyleCondition {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  (S : 𝒮) (I : Sieve S) (hI : I ∈ J.sieves S) [Limits.HasPullbacks 𝒮]
  (hI' : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    CategoryTheory.Limits.HasPullback f f')
  (a : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), 𝒳)
  (ha : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), ObjLift p Y (a hf))
  (α : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    PullbackObj hp (ha hf) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf'))
    ≅ PullbackObj hp (ha hf') (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f f' (hI' hf hf'))) : Prop :=
   ∀ (Y Y' Y'': 𝒮) (f : Y ⟶ S) (f' : Y' ⟶ S) (f'' : Y'' ⟶ S) (hf : I f) (hf' : I f')
    (hf'' : I f''), true


-- *** Ojects glue ***:
def objects_glue {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  (S : 𝒮) (I : Sieve S) (hI : I ∈ J.sieves S) [Limits.HasPullbacks 𝒮]
  (hI' : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    CategoryTheory.Limits.HasPullback f f')
  (a : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), 𝒳)
  (ha : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), ObjLift p Y (a hf))
  (α : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    PullbackObj hp (ha hf) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf'))
    ≅ PullbackObj hp (ha hf') (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f f' (hI' hf hf')))
  (hα : ∀ (Y Y' Y''': 𝒮) (f : Y ⟶ S) (f' : Y' ⟶ S) (f'' : Y'' ⟶ S) (hf : I f) (hf' : I f')
    (hf'' : I f''), true) -- fixme (Cocyle condition)
  (hα' : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    HomLift p (𝟙 (@CategoryTheory.Limits.pullback _ _ _ _ _ f f' (hI' hf hf'))) (α hf hf').hom
    (PullbackObjLift _ _ _) (PullbackObjLift _ _ _))
  : Prop := ∃ (b : 𝒳) (hb : ObjLift p S b)
      (φ : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), PullbackObj hp hb f ≅ a hf)
      (hφ : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), HomLift p (𝟙 Y) (φ hf).hom (PullbackObjLift hp hb f) (ha hf)),
     ∀ (Y Y' : 𝒮) (f : Y ⟶ S) (f' : Y' ⟶ S) (hf : I f) (hf' : I f'),
    CommSq (show PullbackObj hp hb (CategoryTheory.Limits.pullback.fst ≫ f) ⟶
      PullbackObj hp (ha hf) (CategoryTheory.Limits.pullback.fst) from
      objects_glue' J hp S I hI hI' a ha α hα hα' Y Y' f f' hf hf' b hb)
    (show PullbackObj hp hb ((@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf')) ≫ f) ⟶
      PullbackObj hp hb (CategoryTheory.Limits.pullback.fst ≫ f') from
        (PullbackPullbackIso hp hb f f' ).hom)
    (show PullbackObj hp (ha hf) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf')) ⟶
      PullbackObj hp (ha hf') (CategoryTheory.Limits.pullback.fst) from
      ((α hf hf').hom ≫ (show PullbackObj hp (ha hf') (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f f' (hI' hf hf'))
          ⟶ PullbackObj hp (ha hf') (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f' f (hI' hf' hf))
            from (@PullbackPullbackIso'  _ _ _ _ _ hp _ _ _ _ (ha hf') f' f (hI' hf' hf)).symm.hom)))
    (show PullbackObj hp hb (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f' f (hI' hf' hf) ≫ f') ⟶
      PullbackObj hp (ha hf')
      (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f' f (hI' hf' hf)) from
        objects_glue' J hp S I hI hI' a ha α hα hα' Y' Y f' f hf' hf b hb)

/- class Stack {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p) : Prop where
  (GlueMorphism : ∀ (S : 𝒮) (I : J.sieves S) (a b : 𝒳) (ha : ObjLift p S a)
  (hb : ObjLift p S b)
  {pb : I → 𝒳}
  {pbm : ∀ (s : I), (pb s → b)}
  {hpb : ∀ s : I, ObjLift p s (pb s) }
  {hpbm : ∀ i : I, HomLift p s (pbm s) 1

  }, true)   -/


--def IsFiberedInGroupoid2CommSq

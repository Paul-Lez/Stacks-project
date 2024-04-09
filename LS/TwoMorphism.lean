import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.NatIso
import LS.FiberFunctor
import LS.HasFibers


open CategoryTheory Functor Category Fibered

variable {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃} [Category 𝒳] [Category 𝒮]
  [Category 𝒴]

class IsFiberedInGroupoids (p : 𝒳 ⥤ 𝒮) extends IsFibered p where
  (IsPullback {a b : 𝒳} (φ : b ⟶ a) : IsPullback p (p.map φ) φ)

instance (S : 𝒮) : IsFiberedInGroupoids (Over.forget S) where
  has_pullbacks := fun h f => by
    let f' := f ≫ (eqToHom h.symm) ≫ (eqToHom (Functor.id_obj _)) ≫ (_ : Over S).hom ≫ (eqToHom (Functor.const_obj_obj _ _ _))
    use Over.mk f'
    let f'' := (eqToHom (Over.mk_left f')) ≫ f ≫ (eqToHom h.symm)
    let φ := Over.homMk f''
    use φ
    let pb : IsPullback (Over.forget S) f φ := {
      ObjLiftDomain := by simp
      ObjLiftCodomain := by simp only [←h, Over.forget_obj]
      HomLift := by
        constructor
        simp only [Over.forget_obj, eqToHom_refl, const_obj_obj, Over.mk_left, id_comp, Over.forget_map,
          Over.homMk_left]
        aesop
      UniversalProperty := by
        intro T a' g k hk ψ hψ
        sorry
    }
    exact pb
  IsPullback := by
    intro a b φ
    let pb : IsPullback (Over.forget S) ((Over.forget S).map φ) φ := {
      ObjLiftDomain := by simp
      ObjLiftCodomain := by simp
      HomLift := sorry
      UniversalProperty := sorry
    }
    exact pb

structure Fibered.TwoMorphism {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (f g : Fibered.Morphism p q) extends
  CategoryTheory.NatTrans f.toFunctor g.toFunctor where
  (aboveId : ∀ {a : 𝒳} {S : 𝒮} (_ : p.obj a = S), IsHomLift q  (𝟙 S) (toNatTrans.app a))

@[ext]
lemma Fibered.TwoMorphism.ext {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g : Fibered.Morphism p q} (α β : Fibered.TwoMorphism f g)
  (h : α.toNatTrans = β.toNatTrans) : α = β := by
  cases α
  cases β
  simp at h
  subst h
  rfl

def Fibered.TwoMorphism.id {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (f : Fibered.Morphism p q) : Fibered.TwoMorphism f f := {
  toNatTrans := CategoryTheory.NatTrans.id f.toFunctor
  aboveId := by
    intro a S ha
    constructor
    · constructor
      simp only [NatTrans.id_app', map_id, id_comp, comp_id]
    all_goals rwa [←CategoryTheory.Functor.comp_obj, f.w] }

@[simp]
lemma Fibered.TwoMorphism.id_toNatTrans {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (f : Fibered.Morphism p q) : (Fibered.TwoMorphism.id f).toNatTrans = CategoryTheory.NatTrans.id f.toFunctor := rfl

def Fibered.TwoMorphism.comp {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g h : Fibered.Morphism p q} (α : Fibered.TwoMorphism f g) (β : Fibered.TwoMorphism g h) :
  Fibered.TwoMorphism f h := {
    toNatTrans := CategoryTheory.NatTrans.vcomp α.toNatTrans β.toNatTrans
    aboveId := by
      intro a S ha
      rw [CategoryTheory.NatTrans.vcomp_app, show 𝟙 S = 𝟙 S ≫ 𝟙 S by simp only [comp_id]]
      apply IsHomLift_comp (α.aboveId ha) (β.aboveId ha)
  }

@[simp]
lemma Fibered.TwoMorphism.comp_app {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g h : Fibered.Morphism p q} (α : Fibered.TwoMorphism f g) (β : Fibered.TwoMorphism g h) (x : 𝒳) : (comp α β).app x = (α.app x) ≫ β.app x:= rfl

@[simp]
lemma CategoryTheory.NatTrans.id_vcomp {C D : Type _} [Category C] [Category D] {F G : C ⥤ D} (f : NatTrans F G) :
  NatTrans.vcomp (NatTrans.id F) f = f := by
  ext x
  simp only [vcomp_eq_comp, comp_app, id_app', id_comp]

@[simp]
lemma CategoryTheory.NatTrans.vcomp_id {C D : Type _} [Category C] [Category D] {F G : C ⥤ D} (f : NatTrans F G) :
  NatTrans.vcomp f (NatTrans.id G) = f := by
  ext x
  simp only [vcomp_eq_comp, comp_app, id_app', comp_id]

@[simp]
lemma Fibered.TwoMorphism.comp_toNatTrans {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g h : Fibered.Morphism p q} (α : Fibered.TwoMorphism f g) (β : Fibered.TwoMorphism g h) : (comp α β).toNatTrans = NatTrans.vcomp α.toNatTrans β.toNatTrans := rfl

@[simp]
lemma Fibered.TwoMorphism.id_comp {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g : Fibered.Morphism p q} (α : Fibered.TwoMorphism f g) :
  Fibered.TwoMorphism.comp (Fibered.TwoMorphism.id f) α = α := by
  apply Fibered.TwoMorphism.ext
  rw [Fibered.TwoMorphism.comp_toNatTrans, Fibered.TwoMorphism.id_toNatTrans, CategoryTheory.NatTrans.id_vcomp]

@[simp]
lemma Fibered.TwoMorphism.comp_id {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g : Fibered.Morphism p q} (α : Fibered.TwoMorphism f g) :
  Fibered.TwoMorphism.comp α (Fibered.TwoMorphism.id g) = α := by
  apply Fibered.TwoMorphism.ext
  rw [Fibered.TwoMorphism.comp_toNatTrans, Fibered.TwoMorphism.id_toNatTrans, CategoryTheory.NatTrans.vcomp_id]

lemma Fibered.TwoMorphism.comp_assoc {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g h i : Fibered.Morphism p q} (α : Fibered.TwoMorphism f g) (β : Fibered.TwoMorphism g h) (γ : Fibered.TwoMorphism h i) :
  Fibered.TwoMorphism.comp (Fibered.TwoMorphism.comp α β) γ = Fibered.TwoMorphism.comp α (Fibered.TwoMorphism.comp β γ):= by
  apply Fibered.TwoMorphism.ext
  rw [Fibered.TwoMorphism.comp_toNatTrans, Fibered.TwoMorphism.comp_toNatTrans, Fibered.TwoMorphism.comp_toNatTrans, Fibered.TwoMorphism.comp_toNatTrans, NatTrans.vcomp_eq_comp, NatTrans.vcomp_eq_comp, NatTrans.vcomp_eq_comp, NatTrans.vcomp_eq_comp, assoc]

structure Fibered.TwoIsomorphism {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (f g : Fibered.Morphism p q) extends
  f.toFunctor ≅ g.toFunctor where
  (aboveId : ∀ {a : 𝒳} {S : 𝒮} (_ : p.obj a = S), IsHomLift q (𝟙 S) (toIso.hom.app a))

@[ext]
lemma Fibered.TwoIsomorphism.ext {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g : Fibered.Morphism p q} (α β : Fibered.TwoIsomorphism f g)
  (h : α.toIso = β.toIso) : α = β := by
  cases α
  cases β
  simp at h
  subst h
  rfl

def Fibered.TwoIsomorphism.id {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (f : Fibered.Morphism p q) : Fibered.TwoIsomorphism f f := {
  toIso := CategoryTheory.Iso.refl f.toFunctor
  aboveId := by
    intro a S ha
    constructor
    · constructor
      simp only [Iso.refl_hom, NatTrans.id_app, map_id, id_comp, comp_id]
    all_goals rwa [←CategoryTheory.Functor.comp_obj, f.w] }

@[simp]
lemma Fibered.TwoIsomorphism.id_toNatIso {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} (f : Fibered.Morphism p q) : (Fibered.TwoIsomorphism.id f).toIso = CategoryTheory.Iso.refl f.toFunctor := rfl

def Fibered.TwoIsomorphism.comp {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g h : Fibered.Morphism p q} (α : Fibered.TwoIsomorphism f g) (β : Fibered.TwoIsomorphism g h) :
  Fibered.TwoIsomorphism f h := {
    toIso := α.toIso.trans β.toIso
    aboveId := by
      intro a S ha
      rw [Iso.trans_hom, NatTrans.comp_app, show 𝟙 S = 𝟙 S ≫ 𝟙 S by simp only [comp_id]]
      apply IsHomLift_comp (α.aboveId ha) (β.aboveId ha)
  }

@[simp]
lemma Fibered.TwoIsomorphism.comp_app {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g h : Fibered.Morphism p q} (α : Fibered.TwoIsomorphism f g) (β : Fibered.TwoIsomorphism g h) (x : 𝒳) : (comp α β).hom.app x = (α.hom.app x) ≫ β.hom.app x := rfl

@[simp]
lemma Fibered.TwoIsomorphism.comp_toIso {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g h : Fibered.Morphism p q} (α : Fibered.TwoIsomorphism f g) (β : Fibered.TwoIsomorphism g h) : (comp α β).toIso = α.toIso.trans β.toIso := rfl

@[simp]
lemma Fibered.TwoIsomorphism.id_comp {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g : Fibered.Morphism p q} (α : Fibered.TwoIsomorphism f g) :
  Fibered.TwoIsomorphism.comp (Fibered.TwoIsomorphism.id f) α = α := by
  apply Fibered.TwoIsomorphism.ext
  rw [Fibered.TwoIsomorphism.comp_toIso, Fibered.TwoIsomorphism.id_toNatIso, Iso.refl_trans]

@[simp]
lemma Fibered.TwoIsomorphism.comp_id {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g : Fibered.Morphism p q} (α : Fibered.TwoIsomorphism f g) :
  Fibered.TwoIsomorphism.comp α (Fibered.TwoIsomorphism.id g) = α := by
  apply Fibered.TwoIsomorphism.ext
  rw [Fibered.TwoIsomorphism.comp_toIso, Fibered.TwoIsomorphism.id_toNatIso, Iso.trans_refl]

lemma Fibered.TwoIsomorphism.comp_assoc {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {f g h i : Fibered.Morphism p q} (α : Fibered.TwoIsomorphism f g) (β : Fibered.TwoIsomorphism g h) (γ : Fibered.TwoIsomorphism h i) :
  Fibered.TwoIsomorphism.comp (Fibered.TwoIsomorphism.comp α β) γ = Fibered.TwoIsomorphism.comp α (Fibered.TwoIsomorphism.comp β γ):= by
  apply Fibered.TwoIsomorphism.ext
  rw [Fibered.TwoIsomorphism.comp_toIso, Fibered.TwoIsomorphism.comp_toIso, Fibered.TwoIsomorphism.comp_toIso, Fibered.TwoIsomorphism.comp_toIso, Iso.trans_assoc]

instance (p : 𝒳 ⥤ 𝒮) (q : 𝒴 ⥤ 𝒮) [IsFiberedInGroupoids p] [IsFiberedInGroupoids q] : Category (Fibered.Morphism p q) where
  Hom f g := Fibered.TwoIsomorphism f g
  id f := Fibered.TwoIsomorphism.id f
  comp := Fibered.TwoIsomorphism.comp
  id_comp := Fibered.TwoIsomorphism.id_comp
  comp_id := Fibered.TwoIsomorphism.comp_id
  assoc := Fibered.TwoIsomorphism.comp_assoc

@[simp]
lemma Fibered.Morphism_Cat_id_apply (p : 𝒳 ⥤ 𝒮) (q : 𝒴 ⥤ 𝒮) [IsFiberedInGroupoids p] [IsFiberedInGroupoids q] (f : Fibered.Morphism p q) (x : 𝒳) :
  (𝟙 f : Fibered.TwoIsomorphism f f).hom.app x = 𝟙 (f.obj x) := rfl

@[simp]
lemma Fibered.Morphism_Cat_comp_apply (p : 𝒳 ⥤ 𝒮) (q : 𝒴 ⥤ 𝒮) [IsFiberedInGroupoids p] [IsFiberedInGroupoids q] (f g h : Fibered.Morphism p q) (α : f ⟶ g) (β : g ⟶ h) (x : 𝒳) :
  (α ≫ β : Fibered.TwoIsomorphism f h).hom.app x = (α.hom.app x) ≫ β.hom.app x := rfl


def TwoYoneda.toFun (p : 𝒳 ⥤ 𝒮) (S : 𝒮) [IsFiberedInGroupoids p] : Fibered.Morphism (Over.forget S) p ⥤ Fiber p S where
  obj := fun f => by
    apply Fiber.mk_obj (show p.obj (f.toFunctor.obj (Over.mk (𝟙 S))) = S from _)
    rw [←Functor.comp_obj, f.w, Over.forget_obj, Over.mk_left]
  map := fun f => by
    apply Fiber.mk_map _ _ (f.toIso.hom.app (Over.mk (𝟙 S))) _
    apply f.aboveId
    simp only [Over.forget_obj, Over.mk_left]
  map_id := by
    intro f
    simp only [comp_obj, Eq.ndrec, id_eq, Over.forget_obj, Over.mk_left, eq_mpr_eq_cast, cast_eq]
    apply Fiber.mk_map_id
  map_comp := by
    intro X Y Z f g
    simp only [comp_obj, Eq.ndrec, id_eq, Over.forget_obj, Over.mk_left, eq_mpr_eq_cast, cast_eq]
    rw [←Fiber.mk_map_com]
    rfl

-- Any object a in the fiber above S (i.e. a morphism a ⟶ S in 𝒮) gives rise to a fibered morphism from the forgetful functor
-- (Fiber p S ⥤ 𝒮) to p
@[simps]
noncomputable def TwoIsomorphism.Fibered_Morphism_of_fiber_obj {p : 𝒳 ⥤ 𝒮} {S : 𝒮} (hp : IsFiberedInGroupoids p) (a : Fiber p S) : Fibered.Morphism (Over.forget S) p where
  obj := fun b => PullbackObj hp.toIsFibered a.2 b.hom
  map := fun f => by
    apply IsPullbackInducedMap (p:= p) (f := (_ : Over S).hom) (g := f.left) (f' := f.left ≫ (_ : Over S).hom) (φ := PullbackMap hp.toIsFibered a.2 (_ : Over S).hom) (φ' := PullbackMap hp.toIsFibered a.2 (_ : Over S).hom) (PullbackMapIsPullback _ _ _) rfl
    rw [Over.w]
    apply (PullbackMapIsPullback _ _ _).toIsHomLift
  map_id X := by
    simp only [id_obj, const_obj_obj, id_eq, eq_mpr_eq_cast, Over.id_left, id_comp, IsPullbackInducedMap_self_eq_id]
  map_comp := by
    simp only [id_obj, const_obj_obj, id_eq, eq_mpr_eq_cast, Over.comp_left, assoc, Over.w,
      IsPullbackInducedMap_comp, implies_true]
  w := by
    apply Functor.ext ?_ ?_
    · intro X
      simp only [id_obj, const_obj_obj, Over.w, comp_obj, Over.forget_obj, PullbackObjLiftDomain]
    · intro X Y f
      simp only [id_obj, const_obj_obj, id_eq, Over.id_left, Over.comp_left, comp_obj,
        Functor.comp_map, Over.w, Over.forget_obj, Over.forget_map]
      rw [←Category.assoc, ←comp_eqToHom_iff]
      apply (IsPullbackInducedMap_IsHomLift _ _ _).HomLift.w

/- lemma TwoIsomorphism.Fibered_Morphism_of_fiber_obj_apply_obj {p : 𝒳 ⥤ 𝒮} {S : 𝒮} (hp : IsFiberedInGroupoids p) (a : Fiber p S) {b : Over S} : (TwoIsomorphism.Fibered_Morphism_of_fiber_obj hp a).obj a =  -/

-- Any morphism f : a ⟶ b in the fiber above S (i.e. a morphism a ⟶ b above S) gives rise to a 2-isomorphism between the fibered
-- morphisms defined above
@[simps]
noncomputable def TwoIsomorphism.TwoIsomorphism_of_fiber_morphism {p : 𝒳 ⥤ 𝒮} {S : 𝒮}
  (hp : IsFiberedInGroupoids p) {a b : Fiber p S} (f : a ⟶ b) : Fibered.TwoIsomorphism (TwoIsomorphism.Fibered_Morphism_of_fiber_obj hp a) (TwoIsomorphism.Fibered_Morphism_of_fiber_obj hp b) where
    hom := {
      app := fun x => IsPullbackNaturalityHom (p := p) (PullbackMapIsPullback hp.toIsFibered a.2 _) (PullbackMapIsPullback hp.toIsFibered b.2 _) (ψ := f.1) (HasFibersHomLift  _)
      naturality := by
        intro X Y f
        simp only [id_obj]
        apply CommSq.w
        simp only [Fibered_Morphism_of_fiber_obj_obj, id_obj, Fibered_Morphism_of_fiber_obj_map,
          const_obj_obj, Over.w]
        sorry
    }
    inv := {
      app := fun x => sorry
        /- IsPullbackNaturalityHom (p := p) (PullbackMapIsPullback hp.toIsFibered b.2 _) (PullbackMapIsPullback hp.toIsFibered a.2 _) f.1 (HasFibersHomLift  _)  -/
      naturality := sorry
    }
    hom_inv_id := sorry
    inv_hom_id := sorry
    aboveId := sorry

-- the pseudo-inverse two yoneda functor
noncomputable def TwoYoneda.invFun (p : 𝒳 ⥤ 𝒮) (S : 𝒮) [IsFiberedInGroupoids p] : Fiber p S ⥤ Fibered.Morphism (Over.forget S) p where
  obj := fun a => TwoIsomorphism.Fibered_Morphism_of_fiber_obj (p := p) (by infer_instance) a
  map := fun f => TwoIsomorphism.TwoIsomorphism_of_fiber_morphism (p := p) (by infer_instance) f
  map_id := by
    intro X
    simp only
    apply Fibered.TwoIsomorphism.ext
    ext x
    simp only [TwoIsomorphism.Fibered_Morphism_of_fiber_obj_obj, id_obj,
      TwoIsomorphism.TwoIsomorphism_of_fiber_morphism_hom_app, FiberCategory_id_coe]
    rw [Fibered.Morphism_Cat_id_apply]
    rw [IsPullbackNaturalityHom_id]
  map_comp := by
    intro X Y Z f g
    apply Fibered.TwoIsomorphism.ext
    ext x
    simp only [IsPullbackNaturalityHom_comp]
    simp only [TwoIsomorphism.Fibered_Morphism_of_fiber_obj_obj, id_obj,
      TwoIsomorphism.TwoIsomorphism_of_fiber_morphism_hom_app, FiberCategory_comp_coe]
    simp only [id_obj, TwoIsomorphism.Fibered_Morphism_of_fiber_obj_obj, Morphism_Cat_comp_apply,
      TwoIsomorphism.TwoIsomorphism_of_fiber_morphism_hom_app]
    rw [IsPullbackNaturalityHom_comp]

noncomputable def TwoYoneda.Equivalence (p : 𝒳 ⥤ 𝒮) (S : 𝒮) [IsFiberedInGroupoids p] :
  Fibered.Morphism (Over.forget S) p  ≌ Fiber p S  where
    functor := TwoYoneda.toFun p S
    inverse := TwoYoneda.invFun p S
    unitIso := sorry
    counitIso := sorry
    functor_unitIso_comp := sorry

import LS.HasFibers
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.DiscreteCategory

/-!

# Fibered category associated to a presheaf

This file defines the fibered category associated to a presheaf.

## Implementation


## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by Angelo Vistoli
-/

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category Fibered Opposite Discrete

variable {𝒮 : Type u₁} [Category 𝒮](F : 𝒮ᵒᵖ ⥤ Type u₃)

def ℱ := (S : 𝒮) × Discrete (F.obj (op S))

@[simps]
instance : Category (ℱ F) where
  Hom X Y := (f : X.1 ⟶ Y.1) × (X.2 ⟶ (Discrete.mk ((F.map f.op) Y.2.1)))
  -- TODO: figure out PLift up "::" meaning
  id X := ⟨𝟙 X.1, eqToHom (by simp only [op_id, map_id]; rfl)⟩
  comp {X Y Z} f g :=
    have h₁ :  (F.map f.1.op) Y.2.1 = (F.map f.1.op) ((F.map g.1.op) Z.2.1) :=
      congrArg ((F.map f.1.op) ·) (Discrete.eq_of_hom g.2)
    have h : (F.map f.1.op) Y.2.1 =
        (F.map (f.1 ≫ g.1).op) Z.2.1 := Eq.trans h₁
      (by simp only [op_comp, FunctorToTypes.map_comp_apply])
    ⟨f.1 ≫ g.1, f.2 ≫ Discrete.eqToHom h⟩
  id_comp := by
    intro X Y f
    -- TODO: make this procedure into a helper lemma?
    simp only; ext
    { dsimp; exact id_comp _ }
    apply Subsingleton.helim
    simp only [id_comp]
  comp_id := by
    intro X Y f
    simp only; ext
    { dsimp; exact comp_id _ }
    apply Subsingleton.helim
    simp only [comp_id]
  assoc := by
    intro W X Y Z f g h
    simp only; ext
    { dsimp; exact assoc _ _ _ }
    apply Subsingleton.helim
    simp only [assoc]

@[simps]
def ℱ.π (F : 𝒮ᵒᵖ ⥤ Type u₃) : ℱ F ⥤ 𝒮 where
  obj := λ X => X.1
  map := @λ X Y f => f.1

def ℱ.mk_obj {S : 𝒮} (a : F.obj (op S)) : ℱ F := ⟨S, Discrete.mk a⟩

def ℱ.mk_map₁ {R S : 𝒮} (f : R ⟶ S) {X Y : ℱ F} (hX : X.1 = S)
    (hY : Y.1 = R) : Y.1 ⟶ X.1 := eqToHom hY ≫ f ≫ eqToHom hX.symm

def ℱ.mk_map {R S : 𝒮} {f : R ⟶ S} {X Y : ℱ F} {hX : X.1 = S}
    {hY : Y.1 = R} (hXY : Y.2 = Discrete.mk ((F.map (ℱ.mk_map₁ F f hX hY).op) X.2.1)) : Y ⟶ X :=
  ⟨ℱ.mk_map₁ F f hX hY, eqToHom hXY⟩

-- lemma ℱ.IsHomLift_self {X Y : ℱ F} (f : X ⟶ Y) : IsHomLift (ℱ.π F) f f where
--   ObjLiftDomain := rfl
--   ObjLiftCodomain := rfl
--   HomLift := ⟨by simp only [eqToHom_refl, comp_id, id_comp]; rfl⟩

lemma ℱ.mk_map_IsHomLift {R S : 𝒮} {f : R ⟶ S} {X Y : ℱ F} {hX : X.1 = S}
    {hY : Y.1 = R} (hXY : Y.2 = Discrete.mk ((F.map (ℱ.mk_map₁ F f hX hY).op) X.2.1) )
    : IsHomLift (ℱ.π F) f (ℱ.mk_map F hXY) where
  ObjLiftDomain := hY
  ObjLiftCodomain := hX
  HomLift := ⟨by simp [ℱ.mk_map, ℱ.mk_map₁]⟩

lemma ℱ.mk_map_IsPullback {R S : 𝒮} {f : R ⟶ S} {X Y : ℱ F} {hX : X.1 = S}
    {hY : Y.1 = R} (hXY : Y.2 = Discrete.mk ((F.map (ℱ.mk_map₁ F f hX hY).op) X.2.1))
    : IsPullback (ℱ.π F) f (ℱ.mk_map F hXY) :=
  { ℱ.mk_map_IsHomLift F hXY with
    UniversalProperty := by
      intro T Z g h w φ' hφ'
      have := hφ'.1
      -- TODO: mk_map₁ / IsHomLift interaction
      have hZY : Z.2 = Discrete.mk ((F.map (ℱ.mk_map₁ F g hY hφ'.1).op) Y.2.1) := by
        have := (eq_of_hom φ'.2)
        -- homlift => φ'.1 = h (up to conj) ----> MAKE HOMLIFT CONGR LEMMA
        ext
        rw [this]
        simp only
        sorry

      use ℱ.mk_map F hZY
      refine ⟨⟨ℱ.mk_map_IsHomLift F hZY, ?_⟩, ?_⟩

      have := hφ'.3.1
      simp [w, comp_eqToHom_iff] at this
      simp [ℱ.mk_map, ℱ.mk_map₁, this]
      apply Sigma.ext -- WHY DIDNT EXT SEE THIS?
      { simp [this] }
      { apply Subsingleton.helim; simp [this] }

      intro ψ hψ
      have := hψ.1.3.1
      simp [comp_eqToHom_iff] at this
      simp [ℱ.mk_map, ℱ.mk_map₁, this]
      apply Sigma.ext -- WHY DIDNT EXT SEE THIS?
      { simp [this] }
      { apply Subsingleton.helim; simp [this] }
  }




instance : IsFibered (ℱ.π F) where
  has_pullbacks := by
    intros X R S hS f
    subst hS
    let Y : ℱ F := ⟨R, Discrete.mk ((F.map (op f)) X.2.1)⟩
    have hY : Y.2 = Discrete.mk ((F.map (ℱ.mk_map₁ F f rfl (show Y.1 = R from rfl)).op) X.2.1) := by
      simp [ℱ.mk_map₁]; rfl
    use Y, ℱ.mk_map F hY
    exact ℱ.mk_map_IsPullback F hY


/-
@[simps]
instance : Category (ℱ F) where
  Hom X Y := (f : X.1 ⟶ Y.1) × (X.2 ⟶ ((F.map f.op).obj Y.2))
  -- TODO: figure out PLift up "::" meaning
  id X := ⟨𝟙 X.1, eqToHom (by simp only [op_id, map_id]; rfl)⟩
  comp {X Y Z} f g :=
    have h :  (F.map f.fst.op).obj ((F.map g.fst.op).obj Z.2) =
        (F.map (f.fst ≫ g.fst).op).obj Z.2 := by rw [op_comp, map_comp, Cat.comp_obj]
    ⟨f.1 ≫ g.1, f.2 ≫ (F.map f.1.op).map g.2 ≫ eqToHom h⟩
  id_comp := by
    intro X Y f
    simp only; ext
    { dsimp; exact id_comp _ }
    dsimp
    rw [←conj_eqToHom_iff_heq _ _ rfl (by simp only [comp_id]),
      congr_hom (map_id F (op X.1))]
    simp
  comp_id := by
    intro X Y f
    simp only; ext
    { dsimp; exact comp_id _ }
    dsimp
    rw [←conj_eqToHom_iff_heq _ _ rfl (by simp only [id_comp])]
    sorry
  assoc := by
    intro W X Y Z f g h
    simp only; ext
    { dsimp; exact assoc _ _ _ }
    dsimp
    rw [←conj_eqToHom_iff_heq _ _ rfl (by simp)]
    rw [congr_hom (map_comp F _ _)]
    simp
    congr
    rw [←comp_eqToHom_iff (by simp only [map_comp, Cat.comp_obj])]
    simp only [eqToHom_trans, eqToHom_map]




-/



--by subst hX; subst hY; exact f

-- lemma ℱ.IsHomLift_self {X Y : ℱ F} (f : X ⟶ Y) : IsHomLift (ℱ.π F) f f where
--   ObjLiftDomain := rfl
--   ObjLiftCodomain := rfl
--   HomLift := ⟨by simp only [eqToHom_refl, comp_id, id_comp]; rfl⟩

-- lemma ℱ.mk_map_IsPullback {R S : 𝒮} (f : R ⟶ S) {X Y : ℱ F} (hX : X.1 = R)
--     (hY : Y.1 = S) : IsPullback (ℱ.π F) f (ℱ.mk_map F f hX hY) :=
--   { ℱ.mk_map_IsHomLift F f hX hY with
--     UniversalProperty := by
--       intro T Z g h w φ' hφ'
--       use ℱ.mk_map F g (hφ'.1) hX
--       refine ⟨⟨ℱ.mk_map_IsHomLift F g _ hX, ?_⟩, ?_⟩

--       have := hφ'.3.1
--       simp [w, comp_eqToHom_iff] at this
--       simp [ℱ.mk_map, this]

--       intro ψ hψ
--       have := hψ.1.3.1
--       simp [comp_eqToHom_iff] at this
--       simp [ℱ.mk_map, this]
--   }


-- /- TODO: Define HasFibers instance to check it works OK -/
-- noncomputable instance : HasFibers (ℱ.π F) where
--   Fib S := Discrete (F.obj (op S))
--   ι := fun S => {
--     obj := fun a => ⟨S, a.1⟩
--     map := @fun a b φ => 𝟙 S
--     map_comp := @fun a b c φ ψ => by simp only [instCategoryℱ_comp, comp_id] }
--   comp_const := by
--     intro S
--     simp
--     apply Functor.ext_of_iso {
--       hom := { app := by intro a; exact 𝟙 S }
--       inv := { app := by intro a; exact 𝟙 S } }
--     all_goals simp

--   equiv := by
--     intro S
--     refine @Equivalence.ofFullyFaithfullyEssSurj _ _ _ _ _ ?_ ?_ ?_
--     { apply fullOfExists
--       intro X Y f
--       -- here we need X = Y! The existence of f should give this..
--       -- f : ⟨S, X⟩ ⟶ ⟨S, Y⟩ in the fiber ---> corr. to 𝟙 S
--       -- HAVE AN ERROR IN DEFINITION OF ℱ!!!
--       sorry
--     }

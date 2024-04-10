import LS.refactor.Bicategory
import LS.refactor.HasFibers
import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
In this file we construct the bicategory of fibered categories

-/


/-
Plan:
- "HasFibers" bicategory
- "FiberedCategory" bicategory
 -- This should use HasFibers, but should infer standard structure if there is none!

Need:
- Put stuff from FiberFunctor in here!

-/


universe u₁ v₁ u₂ v₂

open CategoryTheory Functor Category Based

variable {𝒮 : Type u₁} [Category 𝒮]

namespace Fibered

-- Cant do bundled unless I replace BasedCategory with a typeclass
--def FiberCategory' (𝒮 : Type u₁) [Category 𝒮] := Bundled (@HasFibers 𝒮 inferInstance)

-- use bundled instead?
structure FiberCat (𝒮 : Type u₁) [Category 𝒮] extends BasedCategory 𝒮 where
  [hasFibers : HasFibers toBasedCategory]

/-- A notion of functor between HasFibers. It is given by a functor F : 𝒳 ⥤ 𝒴 such that F ⋙ q = p,
  and a collection of functors fiber_functor S between the fibers of p and q over S in 𝒮 such that
  .... -/

-- TODO: either this, or demand that HasFibers is functorial....
-- If its a class we could use default_instance...
structure FiberMorphism (𝒳 𝒴 : BasedCategory 𝒮) [hp : HasFibers 𝒳] [hq : HasFibers 𝒴] extends Morphism 𝒳 𝒴 where
  (onFib (S : 𝒮) : hp.Fib S ⥤ hq.Fib S)
  (fib_w : ∀ (S : 𝒮), (onFib S) ⋙ (hq.ι S) = (hp.ι S) ⋙ toFunctor) -- Maybe try aesop_cat by default here.

@[simps!]
def FiberMorphism.comp {𝒳 𝒴 𝒵 : BasedCategory 𝒮} [h𝒳 : HasFibers 𝒳] [h𝒴 : HasFibers 𝒴]
    [h𝒵 : HasFibers 𝒵] (F : FiberMorphism 𝒳 𝒴) (G : FiberMorphism 𝒴 𝒵) : FiberMorphism 𝒳 𝒵 :=
  { Morphism.comp F.toMorphism G.toMorphism with
    onFib := fun S => F.onFib S ⋙ G.onFib S
    fib_w := by
      intro S
      rw [Functor.assoc, G.fib_w, ←Functor.assoc, F.fib_w, Functor.assoc]
      rfl
  }

@[simps!]
def FiberMorphism.id (𝒳 : BasedCategory 𝒮) [hp : HasFibers 𝒳] : FiberMorphism 𝒳 𝒳 :=
  { Morphism.id 𝒳 with
    onFib := fun S => 𝟭 (hp.Fib S)
    fib_w := fun S => by simp only [Functor.id_comp, Functor.comp_id]; rfl
  }

@[simp]
lemma FiberMorphism.assoc {𝒳 𝒴 𝒵 𝒯 : BasedCategory 𝒮} [HasFibers 𝒳] [HasFibers 𝒴]
    [HasFibers 𝒵] [HasFibers 𝒯] (F : FiberMorphism 𝒳 𝒴) (G : FiberMorphism 𝒴 𝒵)
    (H : FiberMorphism 𝒵 𝒯) : FiberMorphism.comp (FiberMorphism.comp F G) H =
      FiberMorphism.comp F (FiberMorphism.comp G H) := rfl

@[simp]
lemma FiberMorphism.comp_id {𝒳 𝒴 : BasedCategory 𝒮} [HasFibers 𝒳] [HasFibers 𝒴]
    (F : FiberMorphism 𝒳 𝒴) : FiberMorphism.comp (FiberMorphism.id 𝒳) F = F := rfl

@[simp]
lemma FiberMorphism.id_comp {𝒳 𝒴 : BasedCategory 𝒮} [HasFibers 𝒳] [HasFibers 𝒴]
    (F : FiberMorphism 𝒳 𝒴) : FiberMorphism.comp F (FiberMorphism.id 𝒴) = F := rfl

-- Might be better to move this somewhere else
@[simp]
lemma Morphism.fiber_proj {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳]
    (F : 𝒳 ⟶ 𝒴) {S : 𝒮} (a : hp.Fib S) : 𝒴.p.obj (F.obj ((hp.ι S).obj a)) = S := by
  rw [Morphism.obj_proj F ((hp.ι S).obj a), HasFibersObjLift]

def Morphism.toFiberMorphism {𝒳 𝒴 : BasedCategory 𝒮} (F : 𝒳 ⟶ 𝒴) :
    FiberMorphism 𝒳 𝒴 :=
{ F with
  onFib := fun S => {
    obj := fun a => ⟨F.obj a.1, by rw [F.obj_proj, a.2]⟩
    map := @fun a b φ => ⟨F.map φ.val, Morphism.pres_IsHomLift F φ.2⟩
    map_id := by
      intro a
      -- TODO THIS SHOULD ALL BE SIMP SOMEHOW..
      simp [FiberCategory_id_coe 𝒳 S a]
      rw [←Subtype.val_inj, FiberCategory_id_coe 𝒴 S _]
    map_comp := by
      intro x y z φ ψ
      -- THIS SHOULD ALSO ALL BE SIMP SOMEHOW...
      simp [FiberCategory_comp_coe 𝒳 S φ ψ]
      rw [←Subtype.val_inj, FiberCategory_comp_coe 𝒴 S _ _]
  }
  fib_w := by aesop_cat
}
/- TWO MORPHISMS FOR HASFIBERS CLASS -/
structure FiberTwoMorphism {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [hq : HasFibers 𝒴]
    (F G : FiberMorphism 𝒳 𝒴) extends TwoMorphism F.toMorphism G.toMorphism where
  /- A family of natural transformations between the functors for each fiber  -/
  (onFib (S : 𝒮) : (F.onFib S) ⟶ (G.onFib S))
  -- TODO: use whisker notation here
  /- The family of natural transformations satisfy the following diagram for any a : hp.Fib S
  ```
  (hp.ι S ⋙ F)(a) ---------- α.app (a) ----------> (hq.ι S ⋙ G)(a)
    |                                                      |
  eqToHom                                                 eqToHom
    |                                                      |
    V                                                      V
  (F.onFib ⋙ hq.ι S)(a) --- α.onFib.app (a) ---> (G.onFib ⋙ hq.ι S)(a)

  ```
  In other words, α.app (a) = α.onFib.app (a) -/
  (fib_w (S : 𝒮) : whiskerLeft (hp.ι S) toNatTrans =
    eqToHom (F.fib_w S).symm ≫ whiskerRight (onFib S) (hq.ι S) ≫ eqToHom (G.fib_w S))

def FiberTwoMorphism.comp {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [hq : HasFibers 𝒴]
    {F G H : FiberMorphism 𝒳 𝒴} (α : FiberTwoMorphism F G) (β : FiberTwoMorphism G H) :
    FiberTwoMorphism F H :=
  { TwoMorphism.comp α.toTwoMorphism β.toTwoMorphism with
    onFib := fun S => α.onFib S ≫ β.onFib S
    fib_w := by
      intro S
      simp
      sorry
      --rw [whiskerLeft_comp, whiskerRight_comp, ←category.assoc, α.fib_w, β.fib_w, category.assoc]

  }

def FiberTwoMorphism.id {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [hq : HasFibers 𝒴]
    (F : FiberMorphism 𝒳 𝒴) : FiberTwoMorphism F F :=
  { TwoMorphism.id F.toMorphism with
    onFib := fun S => 𝟙 _
    fib_w := fun S => by simp; rfl }

-- need FiberTwoMorphism.comp_app

@[ext]
lemma FiberTwoMorphism.ext {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [hq : HasFibers 𝒴]
    {F G : FiberMorphism 𝒳 𝒴} (α β : FiberTwoMorphism F G) (h : α.toTwoMorphism = β.toTwoMorphism) :
    α = β :=
  by
    rcases α with ⟨α, α_fib, αw⟩
    rcases β with ⟨β, β_fib, βw⟩
    simp only [mk.injEq]
    refine ⟨h, ?_⟩
    ext S a
    sorry -- NEED API FOR THIS




-- instance IsFiberTwoMorphism.default {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [hq : HasFibers 𝒴]
--     {F G : 𝒳 ⟶ 𝒴} [hF : IsFiberMorphism F] [hG : IsFiberMorphism G] :

/- TODO:
1. define id, comp & show assoc, id_comp, comp_id of IsFiberTwoMorphism
-- id should be obtained from default instance


2. define IsFiberBiCategory (should I even?)
3. define default instance for IsFiberTwoMorphism

Can I do this using bundled? If so, is there bundled API for bicategories?
-/



-- instance



end Fibered

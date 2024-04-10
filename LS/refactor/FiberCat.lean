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
class IsFiberMorphism {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [hq : HasFibers 𝒴] (F : 𝒳 ⟶ 𝒴) where
  (onFib (S : 𝒮) : hp.Fib S ⥤ hq.Fib S)
  (comp : ∀ (S : 𝒮), (onFib S) ⋙ (hq.ι S) = (hp.ι S) ⋙ F.toFunctor) -- Maybe try aesop_cat by default here.

-- MIGHT BE BETTER TO MOVE THIS SOMEWHERE...!
@[simp]
lemma Morphism.fiber_proj {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳]
    (F : 𝒳 ⟶ 𝒴) {S : 𝒮} (a : hp.Fib S) : 𝒴.p.obj (F.obj ((hp.ι S).obj a)) = S := by
  rw [Morphism.obj_proj F ((hp.ι S).obj a), HasFibersObjLift]

@[default_instance]
instance Morphism.IsFiberMorphism {𝒳 𝒴 : BasedCategory 𝒮} (F : 𝒳 ⟶ 𝒴) :
    IsFiberMorphism F where
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
  comp := by aesop_cat

/- TWO MORPHISMS FOR HASFIBERS CLASS -/
class IsFiberTwoMorphism {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [hq : HasFibers 𝒴]
    {F G : 𝒳 ⟶ 𝒴} [hF : IsFiberMorphism F] [hG : IsFiberMorphism G] (α : TwoMorphism F G) where
  /- A family of natural transformations between the functors for each fiber  -/
  (onFib (S : 𝒮) : (hF.onFib S) ⟶ (hG.onFib S))
  -- TODO: use whisker notation here
  -- TODO: also comment a diagram of what this actually means
  (comp : whiskerLeft (hp.ι S) α.toNatTrans =
    eqToHom (hF.comp S).symm ≫ whiskerRight (onFib S) (hq.ι S) ≫ eqToHom (hG.comp S))

-- instance IsFiberTwoMorphism.default {𝒳 𝒴 : BasedCategory 𝒮} [hp : HasFibers 𝒳] [hq : HasFibers 𝒴]
--     {F G : 𝒳 ⟶ 𝒴} [hF : IsFiberMorphism F] [hG : IsFiberMorphism G] :

--def IsFiberTwoMorphism.comp


-- TODO: think about a good ext lemma...


/- TODO:
1. define id, comp & show assoc, id_comp, comp_id of IsFiberTwoMorphism
-- id should be obtained from default instance

2. define IsFiberBiCategory (should I even?)
3. define default instance for IsFiberTwoMorphism

Can I do this using bundled? If so, is there bundled API for bicategories?
-/



-- instance



end Fibered

import LS.HasFibers
import Mathlib.CategoryTheory.Sites.Grothendieck

/-!

# Fibered categories

This file defines the fibered category associated to a sheaf.

## Implementation


## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by Angelo Vistoli
-/

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category Fibered Opposite

variable {𝒮 : Type u₁} {A : Type u₂} [Category 𝒮] [Category A] (F : 𝒮ᵒᵖ ⥤ Type u₃)

def ℱ := (S : 𝒮) × (F.obj (op S))

instance : Category (ℱ F) where
  Hom X Y := X.1 ⟶ Y.1
  id X := 𝟙 X.1
  comp f g := f ≫ g

def ℱ.π (F : 𝒮ᵒᵖ ⥤ Type u₃) : ℱ F ⥤ 𝒮 :=
  { obj := λ X => X.1,
    map := @λ X Y f => f }

lemma ℱ.mk_hom {R S : 𝒮} (f : R ⟶ S) {X Y : ℱ F} (hX : X.1 = R)
    (hY : Y.1 = S) : X ⟶ Y := by subst hX; subst hY; exact f

lemma ℱ.IsHomLift_self {X Y : ℱ F} (f : X ⟶ Y) : IsHomLift (ℱ.π F) f f where
  ObjLiftDomain := rfl
  ObjLiftCodomain := rfl
  HomLift := ⟨by simp only [eqToHom_refl, comp_id, id_comp]; rfl⟩

instance : IsFibered (ℱ.π F) where
  has_pullbacks := by
    intros X R S hS f
    subst hS
    let Y : ℱ F := ⟨R, (F.map (op f)) X.2⟩
    use Y, (f : Y ⟶ X)
    exact {
      ObjLiftDomain := rfl
      ObjLiftCodomain := rfl
      HomLift := ⟨by simp only [eqToHom_refl, comp_id, id_comp]; rfl⟩
      UniversalProperty := by
        intro T Z g h w φ' hφ'
        have := hφ'.1
        subst this
        use g
        refine ⟨⟨?_, ?_⟩, ?_⟩
        -- TODO: extract this somehow
        exact {
          ObjLiftDomain := rfl
          ObjLiftCodomain := rfl
          HomLift := ⟨by simp only [eqToHom_refl, comp_id, id_comp]; rfl⟩
        }
        have := hφ'.3.1
        simp at this
        rw [←this] at w
        exact w.symm

        intro ψ hψ
        have := hψ.1.3.1
        simp at this
        rw [←this]
        rfl
    }

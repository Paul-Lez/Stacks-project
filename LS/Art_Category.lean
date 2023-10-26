import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Artinian
import Mathlib.CategoryTheory.CommSq
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.GroupTheory.GroupAction.Defs

set_option autoImplicit true

universe u v w w'

open LocalRing RingHom Ideal Submodule RingHom

section Pullback

end Pullback

open CategoryTheory

section Class 

namespace LocalAlgebraWithFixedResidue

variable (R : Type w) [CommRing R] (k : Type w') [Field k] [Algebra R k]

noncomputable instance {A : Type u} [CommRing A] [Algebra R A] [LocalRing A] : 
  Algebra R (LocalRing.ResidueField A) := 
 (RingHom.comp (LocalRing.residue A) (algebraMap R A)).toAlgebra

instance {A : Type u} [CommRing A] [Algebra R A] [LocalRing A] : 
  IsScalarTower R A (ResidueField A) := IsScalarTower.of_algebraMap_eq (congrFun rfl) 

class LocalAlgebraWithFixedResidue (A : Type u) [CommRing A] [Algebra R A] [LocalRing A] where 
  (res : ResidueField A ≃+* k)
  (comp : algebraMap R k = comp (res : ResidueField A →+* k)
    (algebraMap R (ResidueField A)))

--variable {R : Type w} [CommRing R] {k : Type w'} [Field k] [Algebra R k]

def proj (A : Type u) [CommRing A] [Algebra R A] [LocalRing A] [LocalAlgebraWithFixedResidue R k A] :
  A →+* k := (LocalAlgebraWithFixedResidue.res R).toRingHom.comp (residue A)

end LocalAlgebraWithFixedResidue 

end Class 

namespace LocalArtinAlgebraWithFixedResidueHoms

open LocalAlgebraWithFixedResidue 

variable {R : Type w} [CommRing R] {k : Type w'} [Field k] [Algebra R k]

structure LocalAlgebraWithFixedResidueHom
  (A B : Type u) [CommRing A] [CommRing B] [LocalRing A] [LocalRing B] [Algebra R A] [Algebra R B] [LocalRing A] [LocalRing B]
  [LocalAlgebraWithFixedResidue R k A] [LocalAlgebraWithFixedResidue R k B] extends (A →ₐ[R] B)
  where 
  [isLocal : IsLocalRingHom toRingHom]
  (comp : (LocalAlgebraWithFixedResidue.proj R k A) = (LocalAlgebraWithFixedResidue.proj R k B).comp toRingHom)

/- /- test -/
add_decl_doc LocalAlgebraWithFixedResidueHom.toAlgHom -/

notation:25 A " →[" π "] "  B => LocalAlgebraWithFixedResidueHom π A B

section 

open Polynomial 

variable (k)

def DualNumbers := k[X] ⧸ (Ideal.span ({X} : Set (k[X])))

attribute [local instance] Polynomial.commRing 

instance : LocalAlgebraWithFixedResidue R k k :=
{ res := sorry 
  comp := sorry 

}

--instance : _root_.CommRing (DualNumbers k) := @Ideal.Quotient.commRing (k[X]) _ (Ideal.span ({X} : Set (k[X])))



end 

variable (A B : Type u) [CommRing A] [CommRing B] [LocalRing A] [LocalRing B] [Algebra R A] [Algebra R B] [LocalRing A] [LocalRing B]
  [LocalAlgebraWithFixedResidue R k A] [LocalAlgebraWithFixedResidue R k B] (f : A →[π] B)

def Simps.apply (f : A →[π] B) : A → B := f.toAlgHom

lemma Coe_inj (f g : A →[π] B) (h : f.toAlgHom = g.toAlgHom) : f = g := by
  cases f 
  cases g
  congr 
  
instance : AlgHomClass (A →[π] B) R A B where
  coe f := f.toAlgHom
  coe_injective' f g h := by 
    apply Coe_inj π A B f g 
    simp at h
    convert h
  map_mul := by simp
  map_one := by simp
  map_add := by simp
  map_zero := by simp
  commutes := by simp

instance : @IsLocalRingHom A B _ _ f.toAlgHom := LocalAlgebraWithFixedResidueHom.isLocal f

def id : A →[π] A := 
{ AlgHom.id R A with 
  isLocal := isLocalRingHom_id A 
  comp := by simp }

--instance : CoeTC (A →[π] B) (A → B) := by apply_instance

lemma apply_coe (f : A →[π] B) (a : A) : f a = f.toFun a := rfl

def comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [LocalRing A] [LocalRing B] [LocalRing C] [Algebra R A] [Algebra R B]    [Algebra R C] [LocalRing A] [LocalRing B] [LocalRing C] [LocalAlgebraWithFixedResidue R k π A] [LocalAlgebraWithFixedResidue R k π B]
  [LocalAlgebraWithFixedResidue R k π C] (f : A →[π] B ) (g : B →[π] C) : A →[π] C := 
  { AlgHom.comp g.toAlgHom f.toAlgHom with 
    isLocal := @isLocalRingHom_comp _ _ _ _ _ _ _ _ (LocalAlgebraWithFixedResidueHom.isLocal g) 
        (LocalAlgebraWithFixedResidueHom.isLocal f)
    comp := by 
      simp [LocalAlgebraWithFixedResidueHom.comp f, LocalAlgebraWithFixedResidueHom.comp g]
      exact rfl }

end LocalArtinAlgebraWithFixedResidueHoms


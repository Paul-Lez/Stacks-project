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

universe u v w w'

open LocalRing RingHom Ideal Submodule RingHom

open CategoryTheory

section Class 

namespace LocalAlgebraWithFixedResidue

variable (R : Type w) [CommRing R] (k : Type w') [Field k] (π : R →+* k)

noncomputable instance {A : Type u} [CommRing A] [Algebra R A] [LocalRing A] : 
  Algebra R (LocalRing.ResidueField A) := 
 (RingHom.comp (LocalRing.residue A) (algebraMap R A)).toAlgebra

instance {A : Type u} [CommRing A] [Algebra R A] [LocalRing A] : 
  IsScalarTower R A (ResidueField A) := IsScalarTower.of_algebraMap_eq (congrFun rfl) 

class LocalAlgebraWithFixedResidue (A : Type u) [CommRing A] [Algebra R A] [LocalRing A] where 
  (res : ResidueField A ≃+* k)
  (comp : π = comp (res : ResidueField A →+* k)
    (algebraMap R (ResidueField A)))

variable {R : Type w} [CommRing R] {k : Type w'} [Field k] (π : R →+* k)

def proj (A : Type u) [CommRing A] [Algebra R A] [LocalRing A] [LocalAlgebraWithFixedResidue R k π A] :
  A →+* k := (LocalAlgebraWithFixedResidue.res π).toRingHom.comp (residue A)

end LocalAlgebraWithFixedResidue 

end Class 

section LocalArtinAlgebraWithFixedResidueHoms

open LocalAlgebraWithFixedResidue 

variable {R : Type w} [CommRing R] {k : Type w'} [Field k] (π : R →+* k)

structure LocalAlgebraWithFixedResidueHom
  (A B : Type u) [CommRing A] [CommRing B] [LocalRing A] [LocalRing B] [Algebra R A] [Algebra R B] [LocalRing A] [LocalRing B]
  [LocalAlgebraWithFixedResidue R k π A] [LocalAlgebraWithFixedResidue R k π B] extends (A →ₐ[R] B)
  where 
  [isLocal : IsLocalRingHom toRingHom]
  (comp : (LocalAlgebraWithFixedResidue.proj π A) = (LocalAlgebraWithFixedResidue.proj π B).comp toRingHom)

notation:25 A " →[" π "] "  B => LocalAlgebraWithFixedResidueHom π A B

variable (A B : Type u) [CommRing A] [CommRing B] [LocalRing A] [LocalRing B] [Algebra R A] [Algebra R B] [LocalRing A] [LocalRing B]
  [LocalAlgebraWithFixedResidue R k π A] [LocalAlgebraWithFixedResidue R k π B] (f : A →[π] B)

instance : @IsLocalRingHom A B _ _ f.toAlgHom := LocalAlgebraWithFixedResidueHom.isLocal f

variable (R : Type w) [CommRing R] (k : Type w') [Field k] (π : R →+* k)

def comp (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [LocalRing A] [LocalRing B] [LocalRing C] [Algebra R A] [Algebra R B]    [Algebra R C] [LocalRing A] [LocalRing B] [LocalRing C]
  [LocalAlgebraWithFixedResidue R k π A] [LocalAlgebraWithFixedResidue R k π B]
  [LocalAlgebraWithFixedResidue R k π C]  (f : A →[π] B ) (g : B →[π] C): 
    A →[π] C := 
  { AlgHom.comp g.toAlgHom f.toAlgHom with 
    isLocal := @isLocalRingHom_comp _ _ _ _ _ _ _ _ (LocalAlgebraWithFixedResidueHom.isLocal g) 
        (LocalAlgebraWithFixedResidueHom.isLocal f)
    comp := by 
      simp [LocalAlgebraWithFixedResidueHom.comp f, LocalAlgebraWithFixedResidueHom.comp g]
      exact rfl }

end LocalArtinAlgebraWithFixedResidueHoms


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

namespace LocalArtinAlgebraWithFixedResidue

variable (R : Type w) [CommRing R] (k : Type w') [Field k] (π : R →+* k)

noncomputable instance {A : Type u} [CommRing A] [Algebra R A] [LocalRing A] : 
  Algebra R (LocalRing.ResidueField A) := 
 (RingHom.comp (LocalRing.residue A) (algebraMap R A)).toAlgebra

instance {A : Type u} [CommRing A] [Algebra R A] [LocalRing A] : 
  IsScalarTower R A (ResidueField A) := IsScalarTower.of_algebraMap_eq (congrFun rfl) 

class LocalArtinAlgebraWithFixedResidue (A : Type u) [CommRing A] [Algebra R A] [IsArtinian A A] [LocalRing A] where 
  (res : ResidueField A ≃+* k)
  (comp : π = comp (res : ResidueField A →+* k)
    (algebraMap R (ResidueField A)))

variable {R : Type w} [CommRing R] {k : Type w'} [Field k] (π : R →+* k)

def proj (A : Type u) [CommRing A] [Algebra R A] [IsArtinian A A] [LocalRing A] 
  [LocalArtinAlgebraWithFixedResidue R k π A] :
  A →+* k := (LocalArtinAlgebraWithFixedResidue.res π).toRingHom.comp (residue A)

end LocalArtinAlgebraWithFixedResidue 

end Class 

section LocalArtinAlgebraWithFixedResidueHoms

open LocalArtinAlgebraWithFixedResidue 

section 

variable {R : Type w} [CommRing R] {k : Type w'} [Field k] (π : R →+* k)

structure LocalArtinAlgebraWithFixedResidueHoms 
  (A B : Type u) [CommRing A] [CommRing B] [LocalRing A] [LocalRing B] [Algebra R A] [Algebra R B] 
  [IsArtinian A A] [LocalRing A]  [IsArtinian B B] [LocalRing B]
  [LocalArtinAlgebraWithFixedResidue R k π A] [LocalArtinAlgebraWithFixedResidue R k π B] extends (A →ₐ[R] B)
  where 
  (isLocal : IsLocalRingHom toRingHom)
  (comp : (LocalArtinAlgebraWithFixedResidue.proj π A) = (LocalArtinAlgebraWithFixedResidue.proj π B).comp toRingHom)

end 

notation:25 A " →[" π "] "  B => LocalArtinAlgebraWithFixedResidueHoms π A B

variable (R : Type w) [CommRing R] (k : Type w') [Field k] (π : R →+* k)

def comp (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [LocalRing A] [LocalRing B] [LocalRing C] [Algebra R A] 
  [Algebra R B] [Algebra R C]
  [IsArtinian A A] [LocalRing A] [IsArtinian B B] [LocalRing B] [IsArtinian C C] [LocalRing C]
  [LocalArtinAlgebraWithFixedResidue R k π A] [LocalArtinAlgebraWithFixedResidue R k π B]
  [LocalArtinAlgebraWithFixedResidue R k π C]  (f : A →[π] B ) (g : B →[π] C): 
    A →[π] C := 
  { AlgHom.comp g.toAlgHom f.toAlgHom with 
    isLocal := by 
      haveI inst1: IsLocalRingHom g.toAlgHom := g.isLocal
      haveI inst2 : IsLocalRingHom f.toAlgHom := f.isLocal
      apply @isLocalRingHom_comp _ _ _ _ _ _ _ _ inst1 inst2
    comp := sorry }

end LocalArtinAlgebraWithFixedResidueHoms


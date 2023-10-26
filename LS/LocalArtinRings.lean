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

universe u v w w'

open  LocalRing RingHom Ideal Submodule RingHom

section

open CategoryTheory

variable (R : Type w) [CommRing R] (k : Type w') [Field k] (π : R → k)

structure LocalArtinAlgebraWithFixedResidueCat where
  carrier : Type v
  [isCommRing : CommRing carrier]
  [isAlgebra : Algebra R carrier]
  [isArtin : IsArtinian carrier carrier]
  [isLocal : LocalRing carrier]
  (res : carrier ⧸ (maximalIdeal carrier) ≃+* k)
  (h :  π = comp (res : carrier ⧸ (maximalIdeal carrier) →+* k)
    (algebraMap R (carrier ⧸ (maximalIdeal carrier))))

-- set_option hygiene false in 
local notation " 𝔸 R k π " => LocalArtinAlgebraWithFixedResidueCat R k π

attribute [instance] LocalArtinAlgebraWithFixedResidueCat.isCommRing
  LocalArtinAlgebraWithFixedResidueCat.isAlgebra LocalArtinAlgebraWithFixedResidueCat.isLocal

instance : CoeSort (𝔸 R k π) (Type v) := ⟨LocalArtinAlgebraWithFixedResidueCat.carrier⟩

attribute [coe] LocalArtinAlgebraWithFixedResidueCat.carrier

-- variable (A : Art R k π)

--instance : Semiring A := A.isCommRing.toSemiring

def LocalArtinAlgebraWithFixedResidue.proj (A : 𝔸) : A →+* k := comp A.res (Ideal.Quotient.mk (maximalIdeal A))

/- def LocalArtinAlgebraWithFixedResidueHoms (A B : LocalArtinAlgebraWithFixedResidueCat R k π) : Type :=
  {f : A →ₐ[R] B // IsLocalRingHom (f : A →+* B) ∧
    (comp (LocalArtinAlgebraWithFixedResidue.proj R k π B) f) =
      LocalArtinAlgebraWithFixedResidue.proj R k π A} -/



variable (A B C : 𝔸)

structure LocalArtinAlgebraWithFixedResidueHoms where
  func : A →ₐ[R] B
  (isLocal : true)
  (h : true)

infixr:25 " →ₗ+* " => LocalArtinAlgebraWithFixedResidueHoms

instance : Coe (A →ₗ+* B) (A →ₐ[R] B) := ⟨LocalArtinAlgebraWithFixedResidueHoms.func⟩

attribute [coe] LocalArtinAlgebraWithFixedResidueHoms.func

namespace LocalArtinAlgebraWithFixedResidueHoms

def comp {A B C : LocalArtinAlgebraWithFixedResidueCat R k π}
  (f : A →ₗ+* B) (g : B →ₗ+* C) : A →ₗ+* C :=
⟨AlgHom.comp (g : B →ₐ[R] C) f, sorry, sorry⟩

def id {A : Art R k π} : A →ₗ+* A := ⟨by { haveI := A.isAlgebra ; convert @AlgHom.id R A.carrier _ _ this }, 
 IsLocalRingHom.Id A, sorry⟩

end LocalArtinAlgebraWithFixedResidueHoms

initialize_simps_projections LocalArtinAlgebraWithFixedResidueCat (-isCommRing, -isAlgebra)

instance: CategoryTheory.Category (LocalArtinAlgebraWithFixedResidueCat R k π) where
  Hom A B := A →ₗ+* B
  id A := ⟨AlgHom.id R A, sorry, sorry⟩
  comp f g := f.comp g

def small_extension (f : A →+* B) : Prop :=
  (ker f) * (maximalIdeal A) = ⊥ ∧ (ker f : Submodule A A).IsPrincipal ∧
    (Function.Surjective f)



/- #check Submodule.mkQ

lemma temp : Module.IsTorsionBySet A
  ((maximalIdeal A ) ⧸ (comap (Submodule.subtype (maximalIdeal A)) ((maximalIdeal A)^2))) (maximalIdeal A) :=
by
  intros x a
  obtain ⟨b, hb⟩ := a
  --obtain ⟨z, hz⟩ := x
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective (comap (Submodule.subtype (maximalIdeal A)) ((maximalIdeal A)^2)) x
  have : ∃ (z : maximalIdeal A),
    x = Submodule.mkQ (comap (Submodule.subtype (maximalIdeal A)) ((maximalIdeal A)^2)) z := sorry
 -/


section

namespace LocalRing

instance : Module (LocalRing.ResidueField A)
  ((maximalIdeal A) ⧸ (comap (Submodule.subtype (maximalIdeal A)) ((maximalIdeal A)^2))) :=
Module.IsTorsionBySet.module
  (show Module.IsTorsionBySet A _ (maximalIdeal A) by sorry )

/- instance : Module R
  ((maximalIdeal A) ⧸ (comap (Submodule.subtype (maximalIdeal A)) ((maximalIdeal A)^2))) :=
  infer_instance -/

def LocalRingHom.IdealMap {A : Type u} {B : Type v} [CommRing A] [CommRing B] [LocalRing A]
  [LocalRing B] {f : A →+* B} (hf : IsLocalRingHom (f : A →+* B)) :
    maximalIdeal A →+ maximalIdeal B :=
{ toFun := fun (a : maximalIdeal A) ↦ ⟨f a, sorry⟩
  map_zero' := sorry
  map_add' := sorry
}

def RelCotangentSpace {A : Type u} [CommRing A] [LocalRing A] {B : Type v} [CommRing B] 
  [LocalRing B] {f : A →+* B} := 
    (maximalIdeal B) ⧸ ((Submodule.comap (Submodule.subtype (maximalIdeal B)) 
    (((maximalIdeal A).map f) ⊔ (maximalIdeal B)^2)))

def TangentSpace (A : Type u) [CommRing A] [LocalRing A] :=
  ((maximalIdeal A) ⧸ (comap (Submodule.subtype (maximalIdeal A)) ((maximalIdeal A)^2)))

instance {A : Type u} [CommRing A] [LocalRing A] :
  AddCommGroup (LocalRing.TangentSpace A) := QuotientAddGroup.Quotient.addCommGroup
    (comap (Submodule.subtype (maximalIdeal A)) ((maximalIdeal A)^2)).toAddSubgroup

instance {A : Type u} [CommRing A] [LocalRing A] :
  Module A (LocalRing.TangentSpace A) := Submodule.Quotient.module
    (comap (Submodule.subtype (maximalIdeal A)) ((maximalIdeal A)^2))

instance {A : Type u} [CommRing A] [LocalRing A] [Algebra R A] :
  Module R (LocalRing.TangentSpace A) := Submodule.Quotient.module'
    (comap (Submodule.subtype (maximalIdeal A)) ((maximalIdeal A)^2))

instance : Module (LocalRing.ResidueField A) (LocalRing.TangentSpace A):=
Module.IsTorsionBySet.module (show Module.IsTorsionBySet A _ (maximalIdeal A) by sorry)

end LocalRing

end
/- instance {A : Type u} [CommRing A] [LocalRing A] [Algebra R A] :
  isScalarTower  (LocalRing.TangentSpace A) := sorry  -/

/- def test {A : Type u} [CommRing A] [LocalRing A] : Module A
  ((maximalIdeal A) ⧸ (comap (Submodule.subtype (maximalIdeal A)) ((maximalIdeal A)^2))) -/

def LocalRingHom.DifferentialGroupHom {A : Type u} {B : Type v} [CommRing A] [CommRing B] [LocalRing A]
  [LocalRing B] {f : A →+* B} (hf : IsLocalRingHom f) :
    (LocalRing.TangentSpace A) →+ (LocalRing.TangentSpace B) :=
QuotientAddGroup.map
  (comap (Submodule.subtype (maximalIdeal A)) ((maximalIdeal A)^2)).toAddSubgroup
  (comap (Submodule.subtype (maximalIdeal B)) ((maximalIdeal B)^2)).toAddSubgroup
  (LocalRingHom.IdealMap hf)
  (by sorry )

lemma  LocalRingHom.DifferentialGroupHomLinear {A : Type u} {B : Type v} [CommRing A]
  [CommRing B] [LocalRing A] [LocalRing B] [Algebra R A] [Algebra R B]
  {f : A →ₐ[R] B} (hf : IsLocalRingHom (f : A →+* B)) (r : R)
  (a : (LocalRing.TangentSpace A)) :
   LocalRingHom.DifferentialGroupHom hf (r • a) =
     r • (LocalRingHom.DifferentialGroupHom hf a) := by
obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ a
rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul
  (comap (Submodule.subtype (maximalIdeal A)) ((maximalIdeal A)^2)) r x, LocalRingHom.DifferentialGroupHom]
sorry -- this is going to be painful

/- lemma  LocalRingHom.DifferentialGroupHomIsLinearMap {A : Type u} {B : Type v} [CommRing A]
  [CommRing B] [LocalRing A] [LocalRing B] [Algebra R A] [Algebra R B]
  {f : A →ₐ[R] B} (hf : IsLocalRingHom (f : A →+* B)) :
  IsLinearMap R (LocalRingHom.DifferentialGroupHom hf) := by
refine ⟨fun x y ↦ by simp, fun c x ↦ LocalRingHom.DifferentialGroupHomLinear hf c x⟩ -/

def LocalRingHom.DifferentialLinearMap {A : Type u} {B : Type v} [CommRing A]
  [CommRing B] [LocalRing A] [LocalRing B] [Algebra R A] [Algebra R B]
  {f : A →ₐ[R] B} (hf : IsLocalRingHom (f : A →+* B)) :
  LocalRing.TangentSpace A →ₗ[R] LocalRing.TangentSpace B :=
LinearMap.mk (LocalRingHom.DifferentialGroupHom hf)
(fun c x ↦ LocalRingHom.DifferentialGroupHomLinear hf c x)

section localArtin

variable {R : Type w} [CommRing R] {A : Type u} {B : Type v} [CommRing A]
  [CommRing B] [LocalRing A] [LocalRing B] [Algebra R A] [Algebra R B]  [LocalRing R]

instance : Module (ResidueField R) (TangentSpace A) :=
  Module.IsTorsionBySet.module (show Module.IsTorsionBySet R _ (maximalIdeal R) by sorry)

lemma LocalRingHom.DifferentialGroupHomLinear' {A : Type u} {B : Type v} [CommRing A]
  [CommRing B] [LocalRing A] [LocalRing B] [Algebra R A] [Algebra R B]
  {f : A →ₐ[R] B} (hf : IsLocalRingHom (f : A →+* B)) (r : ResidueField R)
  (a : (LocalRing.TangentSpace A)) : LocalRingHom.DifferentialGroupHom hf (r • a) =
     r • (LocalRingHom.DifferentialGroupHom hf a) := sorry

def LocalRingHom.DifferentialLinearMap' {A : Type u} {B : Type v} [CommRing A]
  [CommRing B] [LocalRing A] [LocalRing B] [Algebra R A] [Algebra R B]
  {f : A →ₐ[R] B} (hf : IsLocalRingHom (f : A →+* B)) :
  LocalRing.TangentSpace A →ₗ[ResidueField R] LocalRing.TangentSpace B :=
LinearMap.mk (LocalRingHom.DifferentialGroupHom hf)
(fun c x ↦ LocalRingHom.DifferentialGroupHomLinear' hf c x)

lemma LocalRingHom.DifferentialLinearMap'_mkQ {A : Type u} {B : Type v} [CommRing A]
  [CommRing B] [LocalRing A] [LocalRing B] [Algebra R A] [Algebra R B]
  {f : A →ₐ[R] B} (hf : IsLocalRingHom (f : A →+* B)) {x : A} (hx : x ∈ maximalIdeal A) :
LocalRingHom.DifferentialLinearMap' hf (Submodule.mkQ _ ⟨x, hx⟩) =
  Submodule.mkQ _ ⟨f x, show f x ∈ maximalIdeal B from sorry⟩ := rfl

end localArtin

variable [LocalRing R]

lemma main₁ {f : LocalArtinAlgebraWithFixedResidueHoms A B}
  (hf : Function.Surjective f.func) :
  Function.Surjective (LocalRingHom.DifferentialLinearMap'
    (show (IsLocalRingHom (f.func : A →+* B)) from (f.isLocal))) := by
intro z
obtain ⟨y, hy⟩ := Submodule.mkQ_surjective _ z
obtain ⟨y', hy'⟩ := y
obtain ⟨x, hx⟩ := hf y'
have : x ∈ LocalRing.maximalIdeal A
{ have := (List.TFAE.out (local_hom_TFAE (f.func : A →+* B)) 0 4).mp f.isLocal
  rw [← this, Ideal.mem_comap]
  rw [← hx] at hy'
  convert hy' }
use Submodule.mkQ _ ⟨x, this⟩
simp [LocalRingHom.DifferentialLinearMap'_mkQ, hy', hy, hx]
sorry 
done



lemma main₂ {f : LocalArtinAlgebraWithFixedResidueHoms A B}
  (hf : Function.Surjective (LocalRingHom.DifferentialLinearMap'
    (show (IsLocalRingHom (f.func : A →+* B)) from (f.isLocal)))) :
    Function.Surjective f.func := by
letI : IsLocalRingHom (f.func : A →+* B):= sorry
suffices :  Function.Surjective (LocalRing.ResidueField.map (f.func : A →+* B))
{ sorry } --Nakayama
sorry



end 
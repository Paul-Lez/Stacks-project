import LS.FiberedCategories
import Mathlib.CategoryTheory.Sites.Grothendieck


open CategoryTheory Functor Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category 𝒳] [Category 𝒮]

class IsFiberedInGroupoids (p : 𝒳 ⥤ 𝒮) extends IsFibered p where
  (IsPullback {a b : 𝒳} (φ : b ⟶ a) :  IsPullback' p (p.map φ) φ)

section Stack

noncomputable abbrev pb1 [Limits.HasPullbacks 𝒮] {S : 𝒮}
  {Y Y' : 𝒮} (f : Y ⟶ S) (f' : Y' ⟶ S)  :=
  (@Limits.pullback.fst _ _ _ _ _ f f' _)

noncomputable abbrev pb2 [Limits.HasPullbacks 𝒮] {S : 𝒮}
  {Y Y' : 𝒮} (f : Y ⟶ S) (f' : Y' ⟶ S) :=
  (@Limits.pullback.snd _ _ _ _ _ f f' _)

noncomputable abbrev dpb1 [Limits.HasPullbacks 𝒮] {S : 𝒮}
  {Y Y' Y'' : 𝒮} (f : Y ⟶ S) (f' : Y' ⟶ S) (f'' : Y'' ⟶ S)
 := (@Limits.pullback.fst _ _ _ _ _ (pb1 f f' ≫ f) f'' _)

noncomputable abbrev dpb2 [Limits.HasPullbacks 𝒮] {S : 𝒮}
  {Y Y' Y'' : 𝒮} (f : Y ⟶ S) (f' : Y' ⟶ S) (f'' : Y'' ⟶ S)
 := (@Limits.pullback.snd _ _ _ _ _ (pb1 f f' ≫ f) f'' _)

noncomputable abbrev dpb3 [Limits.HasPullbacks 𝒮] {S : 𝒮}
  {Y Y' Y'' : 𝒮} (f : Y ⟶ S) (f' : Y' ⟶ S) (f'' : Y'' ⟶ S) :=
(@Limits.pullback.snd _ _ _ _ _ (pb1 f f' ≫ f) f'' _)

variable (J : GrothendieckTopology 𝒮) (S Y : 𝒮) (I : Sieve S) (hI : I ∈ J.sieves S) (f : Y ⟶ S) (hf : I f)

/--  Say `S_i ⟶ S` is a cover in `𝒮`, `a b` elements of `𝒳` lying over `S`.
  The **morphism gluing condition**
  states that if we have a family of morphisms `φ_i : a|S_i ⟶ b` such that `φ_i|S_ij = φ_j|S_ij` then there exists a unique
  morphism `φ : a ⟶ b` such that the following triangle commutes

  a|S_i ⟶ a
    φ_i ↘  ↓ φ
           b

-/
def morphisms_glue [Limits.HasPullbacks 𝒮] {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p) : Prop :=
  ∀ (S : 𝒮) (I : Sieve S), I ∈ J.sieves S →
  ∀ (a b : 𝒳) (ha : p.obj a = S) (hb : p.obj b = S)
  (φ : ∀ (Y : 𝒮) (f : Y ⟶ S), I f → (PullbackObj' hp.1 ha f ⟶ b))
  (Y Y' : 𝒮) (f : Y ⟶ S) (f' : Y' ⟶ S) (hf : I f) (hf' : I f'),
  (PullbackMap' hp.1 (PullbackObjLiftDomain hp.1 ha f) (pb1 f f') ≫ (φ Y f hf)) = (pullback_iso_pullback' hp.1 ha f f').hom ≫
    (PullbackMap' hp.1 (PullbackObjLiftDomain hp.1 ha f') (pb2 f f') ≫ (φ Y' f' hf')) →
  ∃! Φ : a ⟶ b, HomLift' (𝟙 S) Φ ha hb ∧ ∀ (Y : 𝒮) (f : Y ⟶ S) (hf : I f), φ Y f hf = PullbackMap' hp.1 ha f ≫ Φ

/-- The canonical isomorphism `((a_j)|S_ij)|S_ijk ≅ ((a_j)|S_jk))|S_jki` where `S_ij = S_i ×_S S_j` and `S_ijk = S_ij ×_S S_k`, etc-/
noncomputable def dpbi {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {S : 𝒮} {I : Sieve S} (_ : I ∈ J.sieves S) [Limits.HasPullbacks 𝒮]
  {a : ∀ {Y : 𝒮} {f : Y ⟶ S} (_ : I f), 𝒳}
  {ha : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), p.obj (a hf) = Y} {Y Y' Y'': 𝒮}
  {f : Y ⟶ S} {f' : Y' ⟶ S} {f'' : Y'' ⟶ S} (_ : I f) (hf' : I f') (_ : I f'') :
  PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf') (pb2 f f')) (dpb1 f f' f'') ≅
    PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf') (pb1 f' f'')) (dpb1 f' f'' f) := by
  have lem₁ : IsPullback' p (dpb1 f f' f'' ≫ pb2 f f') (PullbackMap' hp.1 (PullbackObjLiftDomain hp.1 (ha hf') (pb2 f f')) (dpb1 f f' f'')
    ≫ PullbackMap' hp.1 (ha hf') (pb2 f f'))
  · apply IsPullback'_comp
    apply PullbackMap'IsPullback
    apply PullbackMap'IsPullback
  have lem₂ : IsPullback' p (dpb1 f' f'' f ≫ pb1 f' f'') (PullbackMap' hp.1 (PullbackObjLiftDomain hp.1 (ha hf') (pb1 f' f'')) (dpb1 f' f'' f) ≫ (PullbackMap' hp.1 (ha hf') (pb1 f' f'')))
  · apply IsPullback'_comp
    apply PullbackMap'IsPullback
    apply PullbackMap'IsPullback
  apply IsPullback'InducedMapIsoofIso _ lem₂ lem₁
  · calc  Limits.pullback (pb1 f f' ≫ f) f'' ≅ Limits.pullback (pb2 f f' ≫ f') f'' := Limits.pullback.congrHom
            (Limits.pullback.condition) rfl
      _ ≅ Limits.pullback f (pb1 f' f'' ≫ f') := Limits.pullbackAssoc _ _ _ _
      _ ≅  Limits.pullback (pb1 f' f'' ≫ f') f := Limits.pullbackSymmetry _ _
  · aesop

/-- Given `φ : a ⟶ b` in `𝒳` lying above `𝟙 R` and morphisms `R ⟶ S ⟵ T`, `res_int` defines the
    restriction `φ|(R ×_S T)` to the "intersection" `a|(R ×_S T)` -/
noncomputable def res_int [Limits.HasPullbacks 𝒮] {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a b : 𝒳}
  {ha : p.obj a = R} {hb : p.obj b = R} {φ : a ⟶ b} (f : R ⟶ S) (g : T ⟶ S)
  (hφ : HomLift' (𝟙 R) φ ha hb) :
  PullbackObj' hp.1 ha (pb1 f g) ⟶ PullbackObj' hp.1 hb (pb1 f g) :=
IsPullback'NaturalityHom (PullbackMap'IsPullback hp.1 ha (pb1 f g)) (PullbackMap'IsPullback hp.1 hb (pb1 f g)) φ hφ

/-- Say `S_i ⟶ S` is a cover in `𝒮` and `a_i` lies over `S_i`
  The **cocyle condition** for a family of isomorphisms `α_ij : a_i|S_ij ⟶ a_j|S_ij ` above the identity states that
  `α_jk|S_ijk ∘ α_ij|S_ijk = α_ik|S_ijk` -/
def CocyleCondition {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {S : 𝒮} {I : Sieve S} (hI : I ∈ J.sieves S) [Limits.HasPullbacks 𝒮]
  {a : ∀ {Y : 𝒮} {f : Y ⟶ S}, I f → 𝒳}
  (ha : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), p.obj (a hf) = Y)
  (α : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    PullbackObj' hp.1 (ha hf) (pb1 f f') ≅ PullbackObj' hp.1 (ha hf') (pb2 f f'))
  (hα' : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    HomLift' (𝟙 (@Limits.pullback _ _ _ _ _ f f' _)) (α hf hf').hom
    (PullbackObjLiftDomain _ _ _) (PullbackObjLiftDomain _ _ _)) : Prop :=
   ∀ {Y Y' Y'': 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} {f'' : Y'' ⟶ S} (hf : I f) (hf' : I f') (hf'' : I f''),
    ((show PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf) (pb1 f f')) (dpb1 f f' f'') ⟶
      PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf') (pb2 f f')) (dpb1 f f' f'') from
      res_int hp _ _ (hα' hf hf')) ≫
    (show PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf') (pb2 f f')) (dpb1 f f' f'') ≅
      PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf') (pb1 f' f'')) (dpb1 f' f'' f) from dpbi J hp hI hf hf' hf'').hom) ≫
    ((show PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf') (pb1 f' f'')) (dpb1 f' f'' f) ⟶
      PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf'') (pb2 f' f'')) (dpb1 f' f'' f) from
      res_int hp _ _ (hα' hf' hf'')) ≫
    (show PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf'') (pb2 f' f'')) (dpb1 f' f'' f) ≅
      PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf'') (pb1 f'' f)) (dpb1 f'' f f') from dpbi J hp hI hf' hf'' hf).hom) ≫
    ((show PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf'') (pb1 f'' f)) (dpb1 f'' f f') ⟶
      PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf) (pb2 f'' f)) (dpb1 f'' f f') from
      res_int hp _ _ (hα' hf'' hf)) ≫
    (show PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf) (pb2 f'' f)) (dpb1 f'' f f') ≅
      PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 (ha hf) (pb1 f f')) (dpb1 f f' f'') from dpbi J hp hI hf'' hf hf').hom)
    = 𝟙 _

/-TODO: the following should be defined in terms of a `descent datum` data type (containing
  all the information about the `a_i` and the `α_i`), which should have a predicate saying
  when it is effective.-/

/-- Say `S_i ⟶ S` is a cover in `𝒮` and `a_i` lies over `S_i`.
  The **object gluing condition** states that if we have a
  family of isomorphisms `α_ij : a_i|S_ij ⟶ a_j|S_ij ` above the identity that verify the cocyle condition then there
  exists an object `a` lying over `S` together with maps `φ_i : a|S_i ⟶ a_i` such that `φ_j|S_ij ∘ α_ij = φ_i|S_ij` -/
def objects_glue {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  [Limits.HasPullbacks 𝒮] : Prop :=
  ∀ (S : 𝒮) (I : Sieve S) (hI : I ∈ J.sieves S)
  (a : ∀ {Y : 𝒮} {f : Y ⟶ S}, I f → 𝒳)
  (ha : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), p.obj (a hf) = Y)
  (α : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    PullbackObj' hp.1 (ha hf) (@Limits.pullback.fst _ _ _ _ _ f f' _)
    ≅ PullbackObj' hp.1 (ha hf') (@Limits.pullback.snd _ _ _ _ _ f f' _))
  (hα : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    HomLift' (𝟙 (@Limits.pullback _ _ _ _ _ f f' _)) (α hf hf').hom
    (PullbackObjLiftDomain _ _ _) (PullbackObjLiftDomain _ _ _)),
  CocyleCondition J hp hI ha α hα →
  ∃ (b : 𝒳) (hb : p.obj b = S)
      (φ : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), PullbackObj' hp.1 hb f ≅ a hf)
      (hφ : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f),
      HomLift' (𝟙 Y) (φ hf).hom (PullbackObjLiftDomain hp.1 hb f)   (ha hf)),
     ∀ (Y Y' : 𝒮) (f : Y ⟶ S) (f' : Y' ⟶ S) (hf : I f) (hf' : I f'),
    CommSq
    (show PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 hb f) (pb1 f f') ⟶
      PullbackObj' hp.1 (ha hf) (Limits.pullback.fst) from
        IsPullback'NaturalityHom (PullbackMap'IsPullback hp.1 (PullbackObjLiftDomain hp.1 hb f)
    (pb1 f f'))  (PullbackMap'IsPullback hp.1 (ha hf) Limits.pullback.fst)
       (show PullbackObj' hp.1 hb f ⟶ a hf from (φ hf).hom) (hφ hf))
    (show PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 hb f) (pb1 f f') ⟶ PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 hb f')
      (pb1 f' f) from
        (pullback_comp_iso_pullback_pullback' hp.1 hb f (pb1 f f')).symm.hom ≫ (PullbackPullbackIso'' hp.1 hb f f').hom ≫ (pullback_comp_iso_pullback_pullback' hp.1 _ _ _).hom)
    (show PullbackObj' hp.1 (ha hf) (Limits.pullback.fst) ⟶ PullbackObj' hp.1 (ha hf') (pb1 f' f)from
      ((α hf hf').hom ≫ (show PullbackObj' hp.1 (ha hf') (pb2 f f') ⟶ PullbackObj' hp.1 (ha hf') (pb1 f' f) from
        (PullbackPullbackIso''' hp.1 (ha hf') f' f ).symm.hom)))
      (show PullbackObj' hp.1 (PullbackObjLiftDomain hp.1 hb f') (pb1 f' f) ⟶ PullbackObj' hp.1 (ha hf') (pb1 f' f)
    from IsPullback'NaturalityHom (PullbackMap'IsPullback hp.1 (PullbackObjLiftDomain hp.1 hb f')
    (pb1 f' f))  (PullbackMap'IsPullback hp.1 (ha hf') Limits.pullback.fst)
    (show PullbackObj' hp.1 hb f' ⟶ a hf' from (φ hf').hom) (hφ hf'))

/-- A **Stack** `p : 𝒳 ⥤ 𝒮` is a functor fibered in groupoids that satisfies the object gluing and morphism gluing
  properties -/
class Stack {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  [Limits.HasPullbacks 𝒮] : Prop where
  (GlueMorphism : morphisms_glue J hp)
  (ObjectsGlue : objects_glue J hp)

end Stack
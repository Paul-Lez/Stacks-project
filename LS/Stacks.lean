import LS.FiberedInGroupoids

open CategoryTheory ObjLift IsFiberedInGroupoidHom

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category 𝒳] [Category 𝒮]

section Stack

noncomputable abbrev pb1 [Limits.HasPullbacks 𝒮] {S : 𝒮}
  {Y Y' : 𝒮} (f : Y ⟶ S) (f' : Y' ⟶ S)  :=
  (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' _)

noncomputable abbrev pb2 [Limits.HasPullbacks 𝒮] {S : 𝒮}
  {Y Y' : 𝒮} (f : Y ⟶ S) (f' : Y' ⟶ S) :=
  (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f f' _)

noncomputable abbrev dpb1 [Limits.HasPullbacks 𝒮] {S : 𝒮}
  {Y Y' Y'' : 𝒮} (f : Y ⟶ S) (f' : Y' ⟶ S) (f'' : Y'' ⟶ S)
 := (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ (pb1 f f' ≫ f) f'' _)

noncomputable abbrev dpb2 [Limits.HasPullbacks 𝒮] {S : 𝒮}
  {Y Y' Y'' : 𝒮} (f : Y ⟶ S) (f' : Y' ⟶ S) (f'' : Y'' ⟶ S)
 := (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ (pb1 f f' ≫ f) f'' _)

noncomputable abbrev dpb3 [Limits.HasPullbacks 𝒮] {S : 𝒮}
  {Y Y' Y'' : 𝒮} (f : Y ⟶ S) (f' : Y' ⟶ S) (f'' : Y'' ⟶ S)  := (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ (pb1 f f' ≫ f) f'' _)

variable (J : GrothendieckTopology 𝒮) (S Y : 𝒮) (I : Sieve S) (hI : I ∈ J.sieves S) (f : Y ⟶ S) (hf : I f)

/--  Say `S_i ⟶ S` is a cover in `𝒮`, `a b` elements of `𝒳` lying over `S`. The **morphism gluing condition**
  states that if we have a family of morphisms `φ_i : a|S_i ⟶ b` such that `φ_i|S_ij = φ_j|S_ij` then there exists a unique
  morphism `φ : a ⟶ b` such that the following triangle commutes

  a|S_i ⟶ a
    φ_i ↘  ↓ φ
           b

-/
def morphisms_glue  {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p) : Prop :=
  ∀ (S : 𝒮) (I : Sieve S) (hI : I ∈ J.sieves S)
  (hI' : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    CategoryTheory.Limits.HasPullback f f')
  (a b : 𝒳) (ha : ObjLift p S a) (hb : ObjLift p S b)
  (φ : ∀ (Y : 𝒮) (f : Y ⟶ S) (hf : I f), PullbackObj hp ha f ⟶ b)
  (Y Y' : 𝒮) (f : Y ⟶ S) (f' : Y' ⟶ S) (hf : I f) (hf' : I f')
  (hφ : (PullbackMap hp (PullbackObjLift hp ha f) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf')) ≫ (φ Y f hf))
  = (show PullbackObj hp (PullbackObjLift hp ha f) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf')) ≅
      PullbackObj hp (PullbackObjLift hp ha f') (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f f' (hI' hf hf')) by
      haveI := hI' hf hf'
      exact pullback_iso_pullback hp ha f f').hom ≫
    (PullbackMap hp (PullbackObjLift hp ha f') (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f f' (hI' hf hf')) ≫ (φ Y' f' hf'))),
  ∃! Φ : a ⟶ b, HomLift p (𝟙 S) Φ ha hb ∧ ∀ (Y : 𝒮) (f : Y ⟶ S) (hf : I f), φ Y f hf = PullbackMap hp ha f ≫ Φ

noncomputable def modified_iso_family {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {S : 𝒮} {I : Sieve S} (hI : I ∈ J.sieves S) [Limits.HasPullbacks 𝒮]
  (hI' : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    CategoryTheory.Limits.HasPullback f f')
  {a : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), 𝒳}
  (ha : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), ObjLift p Y (a hf))
  (α : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    PullbackObj hp (ha hf) (pb1 f f') ≅ PullbackObj hp (ha hf') (pb2 f f'))
  {Y Y' Y'' : 𝒮} (f : Y ⟶ S) (f' : Y' ⟶ S) (f'' : Y'' ⟶ S) (hf : I f) (hf' : I f') (hf''' : I f'') :=
  ((show PullbackObj hp (PullbackObjLift hp (ha hf) (pb1 f f')) (dpb1 f f' f'') ≅
      PullbackObj hp (PullbackObjLift hp (ha hf') (pb2 f f')) (dpb1 f f' f'') from sorry).hom ≫
    (show PullbackObj hp (PullbackObjLift hp (ha hf') (pb2 f f')) (dpb1 f f' f'') ≅
      PullbackObj hp (PullbackObjLift hp (ha hf') (pb1 f' f'')) (dpb1 f' f'' f) from sorry).hom)

noncomputable abbrev dpbi {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {S : 𝒮} {I : Sieve S} (hI : I ∈ J.sieves S) [Limits.HasPullbacks 𝒮]
  {a : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), 𝒳}
  {ha : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), ObjLift p Y (a hf)} : ∀ {Y Y' Y'': 𝒮}
  {f : Y ⟶ S} {f' : Y' ⟶ S} {f'' : Y'' ⟶ S} (hf : I f) (hf' : I f') (hf'' : I f''),
  PullbackObj hp (PullbackObjLift hp (ha hf') (pb2 f f')) (dpb1 f f' f'') ≅
      PullbackObj hp (PullbackObjLift hp (ha hf') (pb1 f' f'')) (dpb1 f' f'' f) := sorry

-- IsPullbackNaturalityIso

/-- Given `φ : a ⟶ b` in `𝒳` lying above `𝟙 R` and morphisms `R ⟶ S ⟵ T`, `res_int` defines the
    restriction `φ|(R ×_S T)` to the "intersection" `a|(R ×_S T)` -/
noncomputable def res_int [Limits.HasPullbacks 𝒮] {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a b : 𝒳}
  {ha : ObjLift p R a} {hb : ObjLift p R b} {φ : a ⟶ b} (f : R ⟶ S) (g : T ⟶ S)
  (hf : HomLift p (𝟙 R) φ ha hb) :
  PullbackObj hp ha (pb1 f g) ⟶ PullbackObj hp hb (pb1 f g) := by
  sorry --apply IsPullbackNaturalityHom


--TODO: *** State the cocyle condition ***
/-- Say `S_i ⟶ S` is a cover in `𝒮` and `a_i` lies over `S_i`
  The **cocyle condition** for a family of isomorphisms `α_ij : a_i|S_ij ⟶ a_j|S_ij ` above the identity states that
  `α_jk|S_ijk ∘ α_ij|S_ijk = α_ik|S_ijk` -/
def CocyleCondition {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {S : 𝒮} {I : Sieve S} (hI : I ∈ J.sieves S) [Limits.HasPullbacks 𝒮]
  {a : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), 𝒳}
  (ha : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), ObjLift p Y (a hf))
  (α : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    PullbackObj hp (ha hf) (pb1 f f') ≅ PullbackObj hp (ha hf') (pb2 f f'))
  (hα' : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    HomLift p (𝟙 (@CategoryTheory.Limits.pullback _ _ _ _ _ f f' _)) (α hf hf').hom
    (PullbackObjLift _ _ _) (PullbackObjLift _ _ _)) : Prop :=
   ∀ {Y Y' Y'': 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} {f'' : Y'' ⟶ S} (hf : I f) (hf' : I f') (hf'' : I f''),
    ((show PullbackObj hp (PullbackObjLift hp (ha hf) (pb1 f f')) (dpb1 f f' f'') ⟶
      PullbackObj hp (PullbackObjLift hp (ha hf') (pb2 f f')) (dpb1 f f' f'') from
      res_int hp _ _ (hα' hf hf')) ≫
    (show PullbackObj hp (PullbackObjLift hp (ha hf') (pb2 f f')) (dpb1 f f' f'') ≅
      PullbackObj hp (PullbackObjLift hp (ha hf') (pb1 f' f'')) (dpb1 f' f'' f) from dpbi J hp hI hf hf' hf'').hom) ≫
    ((show PullbackObj hp (PullbackObjLift hp (ha hf') (pb1 f' f'')) (dpb1 f' f'' f) ⟶
      PullbackObj hp (PullbackObjLift hp (ha hf'') (pb2 f' f'')) (dpb1 f' f'' f) from
      res_int hp _ _ (hα' hf' hf'')) ≫
    (show PullbackObj hp (PullbackObjLift hp (ha hf'') (pb2 f' f'')) (dpb1 f' f'' f) ≅
      PullbackObj hp (PullbackObjLift hp (ha hf'') (pb1 f'' f)) (dpb1 f'' f f') from dpbi J hp hI hf' hf'' hf).hom) ≫
    ((show PullbackObj hp (PullbackObjLift hp (ha hf'') (pb1 f'' f)) (dpb1 f'' f f') ⟶
      PullbackObj hp (PullbackObjLift hp (ha hf) (pb2 f'' f)) (dpb1 f'' f f') from
      res_int hp _ _ (hα' hf'' hf)) ≫
    (show PullbackObj hp (PullbackObjLift hp (ha hf) (pb2 f'' f)) (dpb1 f'' f f') ≅
      PullbackObj hp (PullbackObjLift hp (ha hf) (pb1 f f')) (dpb1 f f' f'') from dpbi J hp hI hf'' hf hf').hom)
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
  (hI' : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'), CategoryTheory.Limits.HasPullback f f')
  (a : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), 𝒳)
  (ha : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), ObjLift p Y (a hf))
  (α : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    PullbackObj hp (ha hf) (@CategoryTheory.Limits.pullback.fst _ _ _ _ _ f f' (hI' hf hf'))
    ≅ PullbackObj hp (ha hf') (@CategoryTheory.Limits.pullback.snd _ _ _ _ _ f f' (hI' hf hf')))
  (hα : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    HomLift p (𝟙 (@CategoryTheory.Limits.pullback _ _ _ _ _ f f' (hI' hf hf'))) (α hf hf').hom
    (PullbackObjLift _ _ _) (PullbackObjLift _ _ _))
  (hα' : CocyleCondition J hp hI ha α hα),
  ∃ (b : 𝒳) (hb : ObjLift p S b)
      (φ : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), PullbackObj hp hb f ≅ a hf)
      (hφ : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), HomLift p (𝟙 Y) (φ hf).hom (PullbackObjLift hp hb f) (ha hf)),
     ∀ (Y Y' : 𝒮) (f : Y ⟶ S) (f' : Y' ⟶ S) (hf : I f) (hf' : I f'),
    CommSq
    (show PullbackObj hp (PullbackObjLift hp hb f) (pb1 f f') ⟶
      PullbackObj hp (ha hf) (CategoryTheory.Limits.pullback.fst) from
        IsPullbackNaturality hp (PullbackIsPullback hp (PullbackObjLift hp hb f)
    (pb1 f f'))  (PullbackIsPullback hp (ha hf) CategoryTheory.Limits.pullback.fst) (φ hf).hom (hφ hf))

    (show PullbackObj hp (PullbackObjLift hp hb f) (pb1 f f') ⟶ PullbackObj hp (PullbackObjLift hp hb f') (pb1 f' f) from
        (pullback_comp_iso_pullback_pullback hp hb f (pb1 f f')).symm.hom ≫ (PullbackPullbackIso hp hb f f').hom ≫ (pullback_comp_iso_pullback_pullback hp _ _ _).hom)

    (show PullbackObj hp (ha hf) (pb1 f f') ⟶ PullbackObj hp (ha hf') (CategoryTheory.Limits.pullback.fst) from ((α hf hf').hom ≫ (show PullbackObj hp (ha hf') (pb2 f f') ⟶ PullbackObj hp (ha hf') (pb1 f' f) from (PullbackPullbackIso' hp (ha hf') f' f ).symm.hom)))

    (show PullbackObj hp (PullbackObjLift hp hb f') (pb1 f' f) ⟶ PullbackObj hp (ha hf') (pb1 f' f)
      from IsPullbackNaturality hp (PullbackIsPullback hp (PullbackObjLift hp hb f')
    (pb1 f' f))  (PullbackIsPullback hp (ha hf') CategoryTheory.Limits.pullback.fst) (φ hf').hom (hφ hf'))

/-- A **Stack** `p : 𝒳 ⥤ 𝒮` is a functor fibered in groupoids that satisfies the object gluing and morphism gluing
  properties -/
class Stack {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  [Limits.HasPullbacks 𝒮] : Prop where
  (GlueMorphism : morphisms_glue J hp)
  (ObjectsGlue : objects_glue J hp)

end Stack

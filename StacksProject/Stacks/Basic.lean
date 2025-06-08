/-
Copyright (c) 2024 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib

set_option autoImplicit false

/-!


# Stacks

This files defines descent data and stacks

## TODO
  - Redefine descent data using clivages
  - Construct products of stacks, etc

-/

open CategoryTheory Functor Category Limits--Fibered

universe u₁ u₂ u₃

variable {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃} [Category 𝒳] [Category 𝒮]
  [Category 𝒴]

class IsFiberedInGroupoids (p : 𝒳 ⥤ 𝒮) extends IsFibered p where
  IsPullback {a b : 𝒳} (φ : b ⟶ a) :  IsCartesian p (p.map φ) φ


section Stack

variable [HasFiniteWidePullbacks 𝒮]

/-- Map `A ×ₛ B ⟶ S` via first coordinate-/
noncomputable abbrev pb1 [Limits.HasPullbacks 𝒮] {S : 𝒮}
  {Y Y' : 𝒮} (f : Y ⟶ S) (f' : Y' ⟶ S)  :=
  (@Limits.pullback.fst _ _ _ _ _ f f' _)

/-- Map `A ×ₛ B ⟶ S`  via second coordinate. -/
noncomputable abbrev pb2 [Limits.HasPullbacks 𝒮] {S : 𝒮}
  {Y Y' : 𝒮} (f : Y ⟶ S) (f' : Y' ⟶ S) :=
  (@Limits.pullback.snd _ _ _ _ _ f f' _)

/-- Map `A ×ₛ B ⟶ S`  via second coordinate. -/
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

-- Descent data

abbrev π {X Y Z : 𝒮} {f : X ⟶ Z} {g : Y ⟶ Z}
    (t : PullbackCone f g) : t.pt ⟶ Z :=
  t.π.app WalkingCospan.one

abbrev π {X Y Z : 𝒮} {f : X ⟶ Z} {g : Y ⟶ Z} [Limits.HasPullbacks 𝒮] :
    pullback f g ⟶ Z :=
  (CategoryTheory.Limits.Cone (CategoryTheory.Limits.cospan f g)).π.app WalkingCospan.one

#check IsHomLift
/--  Say `S_i ⟶ S` is a cover in `𝒮`, `a b` elements of `𝒳` lying over `S`.
  The **morphism gluing condition**
  states that if we have a family of morphisms `φ_i : a|S_i ⟶ b` such that `φ_i|S_ij = φ_j|S_ij` then there exists a unique
  morphism `φ : a ⟶ b` such that the following triangle commutes

  a|S_i ⟶ a
    φ_i ↘  ↓ φ
           b

-/
class MorphismsGlue {p : 𝒳 ⥤ 𝒮}  : Prop where
  pair_glues {S : 𝒮} {I : Sieve S} (hI : I ∈ J.sieves S) {a b : 𝒳} (ha : p.obj a = S) (hb : p.obj b = S)
    -- Family of morphisms from pullbacks of a to b, indexed by the cover
    (φ : ∀ ⦃Y : 𝒮⦄ {f : Y ⟶ S} (hf : I f) {c : 𝒳} {π : c ⟶ a}, IsCartesian p f π → (c ⟶ b))
    -- Compatibility condition: the family agrees on double intersections
    (compat : ∀ ⦃Y₁ Y₂ : 𝒮⦄ {f₁ : Y₁ ⟶ S} {f₂ : Y₂ ⟶ S} (hf₁ : I f₁) (hf₂ : I f₂)
      -- For any pullback cone Y₁ ×_S Y₂
      (cone₁₂ : PullbackCone f₁ f₂) (lim₁₂ : IsLimit cone₁₂)
      -- And cartesian lifts to the double intersection
      (c₁ : 𝒳) (π₁ : c₁ ⟶ a) (cart₁ : IsCartesian p f₁ π₁)
      (c₂ : 𝒳) (π₂ : c₂ ⟶ a) (cart₂ : IsCartesian p f₂ π₂)
      (c₁₂ : 𝒳) (π₁₂ : c₁₂ ⟶ a) (cart₁₂ : IsCartesian p (cone₁₂.fst ≫ f₁) π₁₂)
      -- And morphisms relating the restrictions
      (α₁ : c₁₂ ⟶ c₁) (hα₁ : IsCartesian p cone₁₂.fst α₁ ∧ α₁ ≫ π₁ = π₁₂)
      (α₂ : c₁₂ ⟶ c₂) (hα₂ : IsCartesian p cone₁₂.snd α₂ ∧ α₂ ≫ π₂ = π₁₂),
      -- The morphisms agree when restricted to the intersection
      α₁ ≫ φ hf₁ cart₁ = α₂ ≫ φ hf₂ cart₂) :
    -- Conclusion: there exists a unique global morphism
    ∃! (Φ : a ⟶ b), ∀ ⦃Y : 𝒮⦄ (f : Y ⟶ S) (hf : I f) (c : 𝒳) (π : c ⟶ a) (cart : IsCartesian p f π),
      φ hf cart = π ≫ Φ

/-- The canonical isomorphism `((a_j)|S_ij)|S_ijk ≅ ((a_j)|S_jk))|S_jki` where `S_ij = S_i ×_S S_j` and `S_ijk = S_ij ×_S S_k`, etc-/
noncomputable def dpbi {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {S : 𝒮} {I : Sieve S} (_ : I ∈ J.sieves S) [Limits.HasPullbacks 𝒮]
  {a : ∀ {Y : 𝒮} {f : Y ⟶ S} (_ : I f), 𝒳}
  {ha : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), p.obj (a hf) = Y} {Y Y' Y'': 𝒮}
  {f : Y ⟶ S} {f' : Y' ⟶ S} {f'' : Y'' ⟶ S} (_ : I f) (hf' : I f') (_ : I f'') :
  PullbackObj hp.1 (PullbackObjLiftDomain hp.1 (ha hf') (pb2 f f')) (dpb1 f f' f'') ≅
    PullbackObj hp.1 (PullbackObjLiftDomain hp.1 (ha hf') (pb1 f' f'')) (dpb1 f' f'' f) := by
  have lem₁ : IsPullback p (dpb1 f f' f'' ≫ pb2 f f') (PullbackMap hp.1 (PullbackObjLiftDomain hp.1 (ha hf') (pb2 f f')) (dpb1 f f' f'')
    ≫ PullbackMap hp.1 (ha hf') (pb2 f f')) := by
    apply IsPullback_comp
    apply PullbackMapIsPullback
    apply PullbackMapIsPullback
  have lem₂ : IsPullback p (dpb1 f' f'' f ≫ pb1 f' f'') (PullbackMap hp.1 (PullbackObjLiftDomain hp.1 (ha hf') (pb1 f' f'')) (dpb1 f' f'' f) ≫ (PullbackMap hp.1 (ha hf') (pb1 f' f''))) := by
    apply IsPullback_comp
    apply PullbackMapIsPullback
    apply PullbackMapIsPullback
  apply IsPullbackInducedMapIsoofIso _ lem₂ lem₁
  · calc  Limits.pullback (pb1 f f' ≫ f) f'' ≅ Limits.pullback (pb2 f f' ≫ f') f'' := Limits.pullback.congrHom
            (Limits.pullback.condition) rfl
      _ ≅ Limits.pullback f (pb1 f' f'' ≫ f') := Limits.pullbackAssoc _ _ _ _
      _ ≅  Limits.pullback (pb1 f' f'' ≫ f') f := Limits.pullbackSymmetry _ _
  · aesop

/-- Given `φ : a ⟶ b` in `𝒳` lying above `𝟙 R` and morphisms `R ⟶ S ⟵ T`, `res_int` defines the
    restriction `φ|(R ×_S T)` to the "intersection" `a|(R ×_S T)` -/
noncomputable def res_int [Limits.HasPullbacks 𝒮] {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  {R S T : 𝒮} {a b : 𝒳} {φ : a ⟶ b} (f : R ⟶ S) (g : T ⟶ S) (hφ : IsHomLift p (𝟙 R) φ) :
  PullbackObj hp.1 hφ.1 (pb1 f g) ⟶ PullbackObj hp.1 hφ.2 (pb1 f g) :=
IsPullbackNaturalityHom (PullbackMapIsPullback hp.1 hφ.1 (pb1 f g)) (PullbackMapIsPullback hp.1 hφ.2 (pb1 f g)) hφ

-- NOTE (From Calle): Might not need assunmptions ha anymore now that we are working with the IsHomLift class?
-- (Not sure though, havnt really thought about it, just did the minimum so that code compiles w new definitions)
/-- Say `S_i ⟶ S` is a cover in `𝒮` and `a_i` lies over `S_i`
  The **cocycle condition** for a family of isomorphisms `α_ij : a_i|S_ij ⟶ a_j|S_ij ` above the identity states that
  `α_jk|S_ijk ∘ α_ij|S_ijk = α_ik|S_ijk` for any triple intersection S_ijk -/
def CocycleCondition {p : 𝒳 ⥤ 𝒮} [IsFiberedInGroupoids p] [HasFiniteWidePullbacks 𝒮]
  {S : 𝒮} {I : Sieve S} (hI : I ∈ J.sieves S)
  {a : ∀ ⦃Y : 𝒮⦄ (f : Y ⟶ S), I f → 𝒳}
  (ha : ∀ ⦃Y : 𝒮⦄ (f : Y ⟶ S) (hf : I f), p.obj (a f hf) = Y)
  (α : ∀ ⦃Y₁ Y₂ : 𝒮⦄ (f₁ : Y₁ ⟶ S) (f₂ : Y₂ ⟶ S) (hf₁ : I f₁) (hf₂ : I f₂)
    (cone₁₂ : PullbackCone f₁ f₂) (lim₁₂ : IsLimit cone₁₂)
    {c₁ : 𝒳} (π₁ : c₁ ⟶ a f₁ hf₁) (cart₁ : IsCartesian p cone₁₂.fst π₁)
    {c₂ : 𝒳} (π₂ : c₂ ⟶ a f₂ hf₂) (cart₂ : IsCartesian p cone₁₂.snd π₂), c₁ ≅ c₂) : Prop :=
  ∀ ⦃Y₁ Y₂ Y₃ : 𝒮⦄ {f₁ : Y₁ ⟶ S} {f₂ : Y₂ ⟶ S} {f₃ : Y₃ ⟶ S}
    (hf₁ : I f₁) (hf₂ : I f₂) (hf₃ : I f₃),
  -- For any triple of pullback cones forming the triple intersection
  ∀ (cone₁₂ : PullbackCone f₁ f₂) (lim₁₂ : IsLimit cone₁₂)
    (cone₁₃ : PullbackCone f₁ f₃) (lim₁₃ : IsLimit cone₁₃)
    (cone₂₃ : PullbackCone f₂ f₃) (lim₂₃ : IsLimit cone₂₃),
  -- With cartesian lifts to each double intersection
  ∀ {c₁₂ : 𝒳} (π₁₂₁ : c₁₂ ⟶ a f₁ hf₁) (cart₁₂₁ : IsCartesian p (cone₁₂.fst ≫ f₁) π₁₂₁)
    (π₁₂₂ : c₁₂ ⟶ a f₂ hf₂) (cart₁₂₂ : IsCartesian p (cone₁₂.snd ≫ f₂) π₁₂₂),
  ∀ {c₁₃ : 𝒳} (π₁₃₁ : c₁₃ ⟶ a f₁ hf₁) (cart₁₃₁ : IsCartesian p (cone₁₃.fst ≫ f₁) π₁₃₁)
    (π₁₃₃ : c₁₃ ⟶ a f₃ hf₃) (cart₁₃₃ : IsCartesian p (cone₁₃.snd ≫ f₃) π₁₃₃),
  ∀ {c₂₃ : 𝒳} (π₂₃₂ : c₂₃ ⟶ a f₂ hf₂) (cart₂₃₂ : IsCartesian p (cone₂₃.fst ≫ f₂) π₂₃₂)
    (π₂₃₃ : c₂₃ ⟶ a f₃ hf₃) (cart₂₃₃ : IsCartesian p (cone₂₃.snd ≫ f₃) π₂₃₃),
  -- And cartesian lift to the triple intersection (using wide pullback)
  ∀ {c₁₂₃ : 𝒳} (π₁₂₃ : c₁₂₃ ⟶ a f₁ hf₁)
    (cart₁₂₃ : IsCartesian p (limit.π (WidePullbackShape.wideCospan S (![Y₁, Y₂, Y₃]) (![f₁, f₂, f₃])) ⟨0⟩ ≫ f₁) π₁₂₃),
  -- And restriction morphisms from triple to double intersections
  ∀ (ρ₁₂ : c₁₂₃ ⟶ c₁₂) (hρ₁₂ : IsCartesian p (limit.π (WidePullbackShape.wideCospan S (![Y₁, Y₂, Y₃]) (![f₁, f₂, f₃])) ⟨0⟩) ρ₁₂ ∧
    ρ₁₂ ≫ π₁₂₁ = π₁₂₃)
    (ρ₁₃ : c₁₂₃ ⟶ c₁₃) (hρ₁₃ : IsCartesian p (limit.π (WidePullbackShape.wideCospan S (![Y₁, Y₂, Y₃]) (![f₁, f₂, f₃])) ⟨0⟩) ρ₁₃ ∧
    ρ₁₃ ≫ π₁₃₁ = π₁₂₃)
    (ρ₂₃ : c₁₂₃ ⟶ c₂₃) (hρ₂₃ : IsCartesian p (limit.π (WidePullbackShape.wideCospan S (![Y₁, Y₂, Y₃]) (![f₁, f₂, f₃])) ⟨1⟩) ρ₂₃),
  -- The cocycle condition: α₂₃ ∘ α₁₂ = α₁₃ on the triple intersection
  ρ₁₂ ≫ (α f₁ f₂ hf₁ hf₂ cone₁₂ lim₁₂ π₁₂₁ cart₁₂₁ π₁₂₂ cart₁₂₂).hom ≫
  ρ₂₃ ≫ (α f₂ f₃ hf₂ hf₃ cone₂₃ lim₂₃ π₂₃₂ cart₂₃₂ π₂₃₃ cart₂₃₃).hom =
  ρ₁₃ ≫ (α f₁ f₃ hf₁ hf₃ cone₁₃ lim₁₃ π₁₃₁ cart₁₃₁ π₁₃₃ cart₁₃₃).hom

/-- A `PreDescentData` consists of:
- A base object `S` in the base category `𝒮`
- A cover `I` of `S` (a sieve in the Grothendieck topology `J`)
- A family of objects `a` in `𝒳` indexed by arrows in the cover, each lying over the domain of the arrow
- A family of isomorphisms `α` between restrictions of these objects to pairwise pullbacks

This is "pre-descent data" because it doesn't yet satisfy the cocycle condition required for true descent data. -/
structure PreDescentData {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p) [Limits.HasPullbacks 𝒮] where
  (S : 𝒮)
  (I : Sieve S)
  (hI : I ∈ J.sieves S)
  (a : ∀ {Y : 𝒮} {f : Y ⟶ S}, I f → 𝒳)
  (ha : ∀ {Y : 𝒮} {f : Y ⟶ S} (hf : I f), p.obj (a hf) = Y)
  (α : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    PullbackObj hp.1 (ha hf) (@Limits.pullback.fst _ _ _ _ _ f f' _)
    ≅ PullbackObj hp.1 (ha hf') (@Limits.pullback.snd _ _ _ _ _ f f' _))
  (hα : ∀ {Y Y' : 𝒮} {f : Y ⟶ S} {f' : Y' ⟶ S} (hf : I f) (hf' : I f'),
    IsHomLift p (𝟙 (@Limits.pullback _ _ _ _ _ f f' _)) (α hf hf').hom)



/-- A `DescentData` is `PreDescentData` that additionally satisfies the cocycle condition.

The cocycle condition ensures that on triple intersections `S_ijk`, the composition of transition isomorphisms
`α_jk ∘ α_ij = α_ik` holds. This is the fundamental compatibility requirement that allows the descent data
to potentially glue together into a single object over the base `S`.

Descent data is "effective" if it actually arises from restricting some object over `S` to the cover. -/
structure DescentData {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p) [Limits.HasPullbacks 𝒮] extends PreDescentData J hp where
  (hCocycle : CocycleCondition J hp hI ha α hα)

def DescentData.effective {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p) [Limits.HasPullbacks 𝒮]
  (D : DescentData J hp) : Prop := ∃ (b : 𝒳) (hb : p.obj b = D.S)
      (φ : ∀ {Y : 𝒮} {f : Y ⟶ D.S} (hf : D.I f), PullbackObj hp.1 hb f ≅ D.a hf)
      (hφ : ∀ {Y : 𝒮} {f : Y ⟶ D.S} (hf : D.I f),
      IsHomLift p (𝟙 Y) (φ hf).hom),
     ∀ (Y Y' : 𝒮) (f : Y ⟶ D.S) (f' : Y' ⟶ D.S) (hf : D.I f) (hf' : D.I f'),
    CommSq
    (show PullbackObj hp.1 (PullbackObjLiftDomain hp.1 hb f) (pb1 f f') ⟶
      PullbackObj hp.1 (D.ha hf) (Limits.pullback.fst) from
        IsPullbackNaturalityHom (PullbackMapIsPullback hp.1 (PullbackObjLiftDomain hp.1 hb f)
    (pb1 f f'))  (PullbackMapIsPullback hp.1 (D.ha hf) Limits.pullback.fst) (hφ hf))
    (show PullbackObj hp.1 (PullbackObjLiftDomain hp.1 hb f) (pb1 f f') ⟶ PullbackObj hp.1 (PullbackObjLiftDomain hp.1 hb f')
      (pb1 f' f) from
        (PullbackCompIsoPullbackPullback hp.1 hb f (pb1 f f')).symm.hom ≫ (PullbackPullbackIso'' hp.1 hb f f').hom ≫ (PullbackCompIsoPullbackPullback hp.1 _ _ _).hom)
    (show PullbackObj hp.1 (D.ha hf) (Limits.pullback.fst) ⟶ PullbackObj hp.1 (D.ha hf') (pb1 f' f)from
      ((D.α hf hf').hom ≫ (show PullbackObj hp.1 (D.ha hf') (pb2 f f') ⟶ PullbackObj hp.1 (D.ha hf') (pb1 f' f) from
        (PullbackPullbackIso''' hp.1 (D.ha hf') f' f ).symm.hom)))
      (show PullbackObj hp.1 (PullbackObjLiftDomain hp.1 hb f') (pb1 f' f) ⟶ PullbackObj hp.1 (D.ha hf') (pb1 f' f)
    from IsPullbackNaturalityHom (PullbackMapIsPullback hp.1 (PullbackObjLiftDomain hp.1 hb f')
    (pb1 f' f))  (PullbackMapIsPullback hp.1 (D.ha hf') Limits.pullback.fst) (hφ hf'))

/-TODO: the following should be defined in terms of a `descent datum` data type (containing
  all the information about the `a_i` and the `α_i`), which should have a predicate saying
  when it is effective.-/

/-- Say `S_i ⟶ S` is a cover in `𝒮` and `a_i` lies over `S_i`.
  The **object gluing condition** states that if we have a
  family of isomorphisms `α_ij : a_i|S_ij ⟶ a_j|S_ij ` above the identity that verify the cocyle condition then there
  exists an object `a` lying over `S` together with maps `φ_i : a|S_i ⟶ a_i` such that `φ_j|S_ij ∘ α_ij = φ_i|S_ij`.
  In other words, every descent datum is effective -/
def objects_glue {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  [Limits.HasPullbacks 𝒮] : Prop := ∀ (D : DescentData J hp), D.effective

/-- A **Stack** `p : 𝒳 ⥤ 𝒮` is a functor fibered in groupoids that satisfies the object gluing and morphism gluing
  properties -/
class Stack {p : 𝒳 ⥤ 𝒮} (hp : IsFiberedInGroupoids p)
  [Limits.HasPullbacks 𝒮] : Prop where
  (GlueMorphism : MorphismsGlue J p)
  (ObjectsGlue : objects_glue J hp)

end Stack

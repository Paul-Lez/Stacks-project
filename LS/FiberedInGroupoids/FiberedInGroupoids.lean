import LS.FiberedCategories.Basic

open CategoryTheory Functor Category

-- ================================================================================================
-- This is work in progress not needed for Stacks (IsFiberedInGroupoids also exists in Stacks.lean)
-- ================================================================================================


variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category 𝒳] [Category 𝒮]

open Fibered

class IsFiberedInGroupoids (p : 𝒳 ⥤ 𝒮) extends IsFibered p where
  (IsPullback {a b : 𝒳} {R S : 𝒮} (φ : b ⟶ a) (f : R ⟶ S) : IsHomLift p f φ → IsPullback p f φ)

/--
Lemma for creating fibered in groupoids in a simpler way (avoid showing that morphisms
are pullbacks "twice") -/
lemma IsFiberedInGroupoids' (p : 𝒳 ⥤ 𝒮) (h₁ : ∀ {a b : 𝒳} {R S : 𝒮} (φ : b ⟶ a) (f : R ⟶ S),
  IsHomLift p f φ → IsPullback p f φ)
  (h₂ : ∀ {a : 𝒳} {R S : 𝒮} (_ : p.obj a = S) (f : R ⟶ S),
    ∃ (b : 𝒳) (φ : b ⟶ a), IsHomLift p f φ) : IsFiberedInGroupoids p where
    has_pullbacks :=
      by
        intro a R S ha f
        rcases (h₂ ha f) with ⟨b, φ, hφ⟩
        existsi b, φ
        exact h₁ φ f hφ
    IsPullback := h₁

/-- The identity functor (𝟭 𝒮) : 𝒫 ⥤ 𝒫 is fibered in groupoids. -/
noncomputable instance IsFiberedInGroupoids.id : IsFiberedInGroupoids (𝟭 𝒮) :=
  IsFiberedInGroupoids' (𝟭 𝒮)
  (by
    intro a b R S φ f hφ
    constructor
    intro R' a' g f' hf' φ' hφ'
    have h₁ := hφ'.1
    simp only [id_obj, Functor.id_map] at h₁
    subst h₁
    have h₂ := hφ.1
    simp only [id_obj, Functor.id_map] at h₂
    subst h₂
    existsi g
    simp only
    nth_rw 1 [show g = (𝟭 𝒮).map g by rfl]
    refine ⟨⟨IsHomLift_self (𝟭 𝒮) g, ?_⟩, ?_⟩
    · have h₁ := hφ.3.1
      have h₂ := hφ.2
      have h₃ := hφ'.3.1
      rename_i inst_1
      aesop_subst [hf', h₂]
      simp_all only [id_obj, Functor.id_map, eqToHom_refl, comp_id, id_comp]
    intro ψ ⟨⟨_, _, ⟨hψ⟩⟩, _⟩
    simp only [id_obj, Functor.id_map, eqToHom_refl, comp_id, id_comp] at hψ
    exact hψ)
  (by
    intro a R S ha f
    existsi R, f ≫ eqToHom ha.symm
    refine ⟨id_obj _, ha, ⟨?_⟩⟩
    simp only [id_obj, Functor.id_map, assoc, eqToHom_trans, eqToHom_refl, comp_id, id_comp])



/-
-- TODO BREAK UP INTO SMALLER PIECES
lemma IsFiberedInGroupoids_iff (p : C ⥤ S) : IsFiberedInGroupoids p ↔
  (IsFibered p ∧ (∀ (s : S) {x y : (Fiber p s)} (φ : x ⟶ y), IsIso φ)) :=
  by
    constructor
    · rintro ⟨hfiber, hlift⟩
      refine ⟨⟨?_⟩, ?_⟩
      · intro x s f
        rcases hlift f with ⟨z, ψ, hz, hcomm⟩
        existsi z
        existsi ψ
        existsi hz
        refine ⟨hcomm, hfiber ψ⟩
      intro s x y ψ
      haveI hiso : IsIso (p.map ψ.val) :=
        by
          have hψ := ψ.prop
          rw [comp_eqToHom_iff, eqToHom_trans] at hψ
          rw [hψ]
          sorry -- TODO SHOULD BE FINE ALREADY? This instance exists in EqToHom...
      haveI hψiso : IsIso (ψ.val) := isiso_of_cartesian p ψ.val
      sorry -- Need iso is in fiber... separate lemma (after better definition of fibers)
    rintro ⟨hfiber, hiso⟩
    constructor
    · intro x y φ
      rcases fiber_factorization p φ with ⟨z, ψ, τ, hτ, hcomp⟩
      rw [←hcomp]
      haveI hiso := hiso (p.obj y) ψ
      haveI : IsCartesian p ψ.val :=
        by
          haveI : IsIso ψ.val := sorry -- TODO INSTANCE SHOULD ALREADY EXIST
          exact iso_iscartesian p ψ.val
      apply IsCartesian.comp
    intro x Y f
    rcases hfiber with ⟨hfiber⟩
    rcases hfiber f with ⟨y, φ, hy, hcomm, hcart⟩
    existsi y
    existsi φ
    existsi hy
    exact hcomm
-/

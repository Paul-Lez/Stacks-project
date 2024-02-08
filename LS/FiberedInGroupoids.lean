import LS.FiberedCategories'

open CategoryTheory Functor Category

-- ================================================================================================
-- This is work in progress not needed for Stacks (IsFiberedInGroupoids also exists in Stacks.lean)
-- ================================================================================================


variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category 𝒳] [Category 𝒮]

open Fibered

/--
Lemma for showing things are fibered in groupoids in a simpler way (avoid showing that morphisms
are pullbacks "twice")
-/

class IsFiberedInGroupoids (p : 𝒳 ⥤ 𝒮) extends IsFibered p where
  (IsPullback {a b : 𝒳} {R S : 𝒮} (φ : b ⟶ a) (f : R ⟶ S) : IsHomLift p f φ → IsPullback p f φ)

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

noncomputable instance IsFiberedInGroupoids.id : IsFiberedInGroupoids (Functor.id 𝒮) :=
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
    refine ⟨⟨IsHomLift_self (𝟭 𝒮), ?_⟩, ?_⟩
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

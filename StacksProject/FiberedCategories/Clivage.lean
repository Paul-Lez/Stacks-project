/-
Copyright (c) 2024 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import StacksProject.FiberedCategories.HasFibers

/-!
# Clivages on fibered categories

A clivage is ... [insert discussion]

-/


universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category Fibered

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category 𝒳] [Category 𝒮]


/--Todo Paul: work out the coherence conditions on the composition natural transformations-/
class HasClivage (p : 𝒳 ⥤ 𝒮) extends HasFibers p where
  (pullback {a b : 𝒮} : (a ⟶ b) → (Fib b ⥤ Fib a))
  (pullback_id (a : 𝒮) : pullback (𝟙 a) = 𝟭 (Fib a))
  (pullback_comp {a b c : 𝒮} (f : a ⟶ b) (g : b ⟶ c) : pullback g ⋙ pullback f ≅ pullback (f ≫ g))
  --(pullback_comp_id {a b : 𝒮} (f : a ⟶ b) : pullback_comp f (𝟙 _) =  )


--def Fib.HasClivage (p : 𝒳 ⥤ 𝒮)

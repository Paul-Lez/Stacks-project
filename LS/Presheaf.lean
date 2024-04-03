import LS.HasFibers
import Mathlib.CategoryTheory.Sites.Grothendieck

/-!

# Fibered categories

This file defines the fibered category associated to a sheaf.

## Implementation


## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by Angelo Vistoli
-/

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category Fibered

variable {𝒮 : Type u₁} {A : Type u₂} [Category 𝒮] [Category A]

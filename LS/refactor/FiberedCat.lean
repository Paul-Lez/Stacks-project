import LS.refactor.Bicategory
import LS.refactor.HasFibers

/-!
In this file we construct the bicategory of fibered categories

-/


/-
Plan:
- "HasFibers" bicategory
- "FiberedCategory" bicategory
 -- This should use HasFibers, but should infer standard structure if there is none!

Need:
- Put stuff from FiberFunctor in here!

-/


universe u₁ v₁ u₂ v₂

open CategoryTheory Functor Category Based

variable {𝒮 : Type u₁} [Category 𝒮]

namespace Fibered


end Fibered

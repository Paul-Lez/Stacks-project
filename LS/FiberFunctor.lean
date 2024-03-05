

-- class IsFiberedNatTrans (p : 𝒳 ⥤ 𝒮) (q : 𝒴 ⥤ 𝒮) [hp : IsFibered p] [hq : IsFibered q] {F : 𝒳 ⥤ 𝒴}
--   {G : 𝒳 ⥤ 𝒴} [IsFiberedFunctor p q F] [IsFiberedFunctor p q G] (α : F ⟶ G) : Prop where
--   (pointwiseInFiber : ∀ (a : 𝒳), q.map (α.app a) = eqToHom (IsFiberedFunctorPresFiberObj p q F G a))

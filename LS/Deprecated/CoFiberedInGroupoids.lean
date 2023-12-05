import LS.FiberedInGroupoids

open CategoryTheory Functor Opposite

variable {S : Type u₁} {C : Type u₂} {D : Type u₃} [Category S] [Category C] [Category D]

-- TODO FIX DEFINITION
class IsCoCartesian (p : C ⥤ S) {x y : C} (φ : y ⟶ x) : Prop where
  (isCoCartesian {z : C} {ψ : z ⟶ x} {f : p.obj z ⟶ p.obj y} (hy : f ≫ (p.map φ) = p.map ψ) :
    ∃! (χ : z ⟶ y), (χ ≫ φ = ψ) ∧ f = p.map χ)

class IsCofiberedInGroupoids (p : C ⥤ S) : Prop where
  (LiftHom {x : C} {Y : S} (f : p.obj x ⟶ Y) :
    ∃ (y : C) (φ : x ⟶ y) (hy : Y = p.obj y),
      CommSq f (𝟙 (p.obj x)) (eqToHom hy) (p.map φ))
  (IsCoCartesian {x y z : C} {φ : x ⟶ y} {ψ : x ⟶ z} {f : p.obj y ⟶ p.obj z} :
    (p.map φ) ≫ f = p.map ψ → ∃! (χ : y ⟶ z), CommSq (p.map χ) (𝟙 (p.obj y)) (𝟙 (p.obj z)) f)



lemma IsCofiberedInGroupoidsOpp (p : C ⥤ S) (hp : IsCofiberedInGroupoids p) :
  IsFiberedInGroupoids p.op :=
by
  rcases hp with ⟨hlift, hcart⟩
  refine ⟨fun f => ?_, fun φ => ⟨?_⟩⟩
  · rcases hlift f.unop with ⟨x, φ', unop_obj_lift, unop_hom_lift⟩
    existsi op x, op φ'
    rw [←op_inj_iff, ←op_obj, op_unop] at unop_obj_lift
    existsi unop_obj_lift.symm
    simpa only [op_obj, unop_op, op_unop, eqToHom_op, op_id, Quiver.Hom.op_unop] using CommSq.op unop_hom_lift
  intros z ψ f h_comp
  rcases hcart (Quiver.Hom.op_inj h_comp) with ⟨χ, χ_comm, χ_unique⟩
  refine ⟨χ.op, ⟨⟨sorry, ?_⟩, ?_⟩⟩
  · have hf := (CommSq.op χ_comm).1
    simp only [op_obj, Quiver.Hom.op_unop, op_id, Category.comp_id, Category.id_comp] at hf
    simp only [op_obj, hf, op_map, Quiver.Hom.unop_op]
  rintro g ⟨g_comm, geq⟩
  apply Quiver.Hom.unop_inj ((χ_unique (g.unop)) ?_)
  rw [op_map, ←(Quiver.Hom.op_unop f)] at geq
  rw [Quiver.Hom.op_inj geq]
  constructor
  simp only [Category.comp_id, Category.id_comp]
  --refine ⟨χ.op, ⟨?_, fun g g_comm => Quiver.Hom.unop_inj ((χ_unique (g.unop)) (CommSq.unop g_comm))⟩⟩

lemma IsFiberedInGroupoidsOpp (p : C ⥤ S) (hp : IsFiberedInGroupoids p):
  IsCofiberedInGroupoids p.op :=
by
  rcases hp with ⟨hlift, hcart⟩
  refine ⟨fun f => ?_, ?_⟩
  · rcases hlift f.unop with ⟨x, φ, unop_obj_lift, unop_hom_lift⟩
    existsi op x, op φ
    rw [←op_inj_iff, ←op_obj, op_unop] at unop_obj_lift
    existsi unop_obj_lift.symm
    simpa only [op_obj, unop_op, op_unop, eqToHom_op, op_id, Quiver.Hom.op_unop] using CommSq.op unop_hom_lift
  intros x y z φ ψ f h_comp
  rcases (hcart φ.unop).isCartesian  (Quiver.Hom.op_inj h_comp) with ⟨χ, χ_comm, χ_unique⟩
  refine ⟨χ.op, ⟨sorry, sorry⟩⟩

lemma IsFiberedInGroupoids_iff_Op (p : C ⥤ S) : IsFiberedInGroupoids p ↔ IsCofiberedInGroupoids p.op :=
by
  refine ⟨fun hp => IsFiberedInGroupoidsOpp p hp, fun hp =>  sorry --apply IsCofiberedInGroupoidsOpp p hp}
  ⟩

lemma IsCoiberedInGroupoids.id : IsCofiberedInGroupoids (Functor.id Sᵒᵖ) :=
by simpa [show Functor.id Sᵒᵖ = (Functor.id S).op from rfl, ←IsFiberedInGroupoids_iff_Op]
  using IsFiberedInGroupoids.id

import HodgeLean.Foundations.Program.SchoenTowerProjectorAlgebra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped BigOperators
namespace HodgeLean.Foundations.Program

def s2v_coverOpenDeck {X E : TopCat} (f : X ⟶ E) (d : X ⟶ X)
    (hd : d ≫ f = f) (U : Opens E) : C({x : X // f x ∈ U}, {x : X // f x ∈ U}) :=
  ⟨fun x => ⟨d x.val, by
    have hx : f (d x.val) = f x.val := congrArg (fun g : X ⟶ E => g x.val) hd
    rw [hx]; exact x.property⟩, by fun_prop⟩

theorem s2v_coverPresheafDeck_pow_section {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (U : Opens E) (t : ℕ)
    (s : LocallyConstant {x : X // f x ∈ U} ℂ) :
    ((End.of (s2c_coverPresheafDeck f d hd)) ^ t).asHom.app (op U) s =
      ((LocallyConstant.comapₗ ℂ (s2v_coverOpenDeck f d hd U) :
        Module.End ℂ (LocallyConstant {x : X // f x ∈ U} ℂ)) ^ t) s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    rw [pow_succ, End.mul_asHom, NatTrans.comp_app, ConcreteCategory.comp_apply,
      ih, pow_succ, Module.End.mul_apply]
    rfl

theorem s2v_coverOpenDeck_iterate {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (U : Opens E) (t : ℕ)
    (x : {x : X // f x ∈ U}) :
    ((s2v_coverOpenDeck f d hd U)^[t] x).val = d^[t] x.val := by
  have hs : Function.Semiconj (fun z : {x : X // f x ∈ U} => z.val)
      (s2v_coverOpenDeck f d hd U) (fun z : X => d z) := fun _ => rfl
  exact hs.iterate_right t x

end HodgeLean.Foundations.Program

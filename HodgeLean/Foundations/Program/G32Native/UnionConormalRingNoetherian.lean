import HodgeLean.Foundations.Program.G32Native.UnionConormalRingSurjective
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Noetherian.Basic

/-! # Noetherianity of the affine intersection conormal module -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The last affine module is noetherian as a quotient of the extended first ideal. -/
lemma unionConormalRingLast_isNoetherian
    {R B C D : Type} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [IsNoetherianRing R]
    (q : R →+* B) (r : R →+* C) (s : C →+* D) (k : B →+* D)
    (hc : s.comp r = k.comp q)
    (hK : (RingHom.ker q).map r = RingHom.ker s)
    (hq : Function.Surjective q) (hr : Function.Surjective r) (hs : Function.Surjective s) :
    IsNoetherian B ((ModuleCat.restrictScalars k).obj
      ((ModuleCat.extendScalars s).obj (ModuleCat.of C (RingHom.ker s)))) := by
  letI : Algebra R B := q.toAlgebra
  letI : IsNoetherianRing B := isNoetherianRing_of_surjective R B q hq
  haveI : Module.Finite B ((ModuleCat.extendScalars q).obj
      (ModuleCat.of R (RingHom.ker q))) := by
    change Module.Finite B (B ⊗[R] RingHom.ker q)
    infer_instance
  exact isNoetherian_of_surjective (unionConormalRingLast q r s k hc hK).hom
    (LinearMap.range_eq_top.mpr (unionConormalRingLast_surjective q r s k hc hK hr hs))

end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.SchoenTransferQ3CartesianStalkKernel
import HodgeLean.Foundations.Program.SchoenTransferQ3FibreIdealSquare
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreePointLength

/-! Point-fibre length under an actual cartesian immersion. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Compatible scheme-theoretic slicing leaves the local point-fibre length
unchanged, including the unreduced structure. -/
theorem s4_q3_cartesian_point_fibre_length
    {W Z C : Scheme} (t : W ⟶ Z) (i : C ⟶ Z) [IsClosedImmersion i]
    (d : (pullback t i : Scheme)) :
    SingularCycles.pointFibreLength (pullback.snd t i) d =
      SingularCycles.pointFibreLength t (pullback.fst t i d) := by
  let e := Z.presheaf.stalkCongr (Inseparable.of_eq
    (congrArg (fun k : pullback t i ⟶ Z => k d) (pullback.condition (f := t) (g := i))))
  let f := t.stalkMap (pullback.fst t i d)
  let a := e.hom ≫ i.stalkMap (pullback.snd t i d)
  let b := (pullback.fst t i).stalkMap d
  let g := (pullback.snd t i).stalkMap d
  have ha : Function.Surjective a.hom :=
    (i.stalkMap_surjective _).comp (ConcreteCategory.bijective_of_isIso e.hom).2
  have hb : Function.Surjective b.hom := (pullback.fst t i).stalkMap_surjective d
  have hsquare : b.hom.comp f.hom = g.hom.comp a.hom := by
    exact congrArg CommRingCat.Hom.hom (s4_q3_closed_pullback_stalk_square t i d)
  have hker : RingHom.ker b.hom ≤
      (IsLocalRing.maximalIdeal (Z.presheaf.stalk (t (pullback.fst t i d)))).map f.hom := by
    rw [s4_q3_closed_pullback_stalk_kernel t i d]
    exact Ideal.map_mono (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top a.hom))
  exact (s4_q3_fibre_length_surjective_square f.hom a.hom b.hom g.hom
    ha hb hsquare hker).symm

end HodgeLean.Foundations.Program

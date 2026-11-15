import HodgeLean.Foundations.Program.SchoenTowerFibreDefs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

def s2v_pointFibreEquiv {E K : Over (Spec ↧ℂ)} (p : E ⟶ K) (k : ComplexPoint K) :
    ComplexPoint (pullback p k) ≃ {x : ComplexPoint E // Point.map p x = k} where
  toFun z := ⟨Point.map (pullback.fst p k) z, by
    change (z ≫ pullback.fst p k) ≫ p = k
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hz : z ≫ pullback.snd p k = 𝟙 _ := Subsingleton.elim _ _
    rw [hz, Category.id_comp]⟩
  invFun x := pullback.lift x.val (𝟙 _) (by simpa only [Point.map, Category.id_comp] using x.property)
  left_inv z := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · rw [pullback.lift_snd]
      exact Subsingleton.elim _ _
  right_inv x := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _

theorem s2v_pointFibreEquiv_continuous {E K : Over (Spec ↧ℂ)}
    (p : E ⟶ K) (k : ComplexPoint K) : Continuous (s2v_pointFibreEquiv p k) :=
  (Point.continuousMap (pullback.fst p k)).continuous.subtype_mk _

def s2v_pointFibreHomeomorph {E K : Over (Spec ↧ℂ)}
    (p : E ⟶ K) (k : ComplexPoint K)
    [CompactSpace (ComplexPoint (pullback p k))] [T2Space (ComplexPoint E)] :
    ComplexPoint (pullback p k) ≃ₜ {x : ComplexPoint E // Point.map p x = k} :=
  (s2v_pointFibreEquiv p k).toHomeomorphOfContinuousClosed
    (s2v_pointFibreEquiv_continuous p k) (s2v_pointFibreEquiv_continuous p k).isClosedMap

theorem s2v_pointFibreHomeomorph_projection {E K : Over (Spec ↧ℂ)}
    (p : E ⟶ K) (k : ComplexPoint K)
    [CompactSpace (ComplexPoint (pullback p k))] [T2Space (ComplexPoint E)]
    (z : ComplexPoint (pullback p k)) :
    (s2v_pointFibreHomeomorph p k z).val = Point.map (pullback.fst p k) z := rfl

end HodgeLean.Foundations.Program

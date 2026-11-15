import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

def componentParametrizationHomeomorph
    (m α : ℕ) (hm : 0 < m) (F : Over (Spec ↧ℂ))
    [T2Space (ComplexPoint F)]
    (j : ZMod (Nat.gcd m α) → (projectiveLine ⟶ F))
    (hj : ∀ l, IsClosedImmersion (j l).left)
    (hexhaust : ∀ z : ComplexPoint F, ∃! l, z ∈ Set.range (Point.map (j l))) :
    componentModel m α ≃ₜ ComplexPoint F := by
  letI : NeZero (Nat.gcd m α) := ⟨Nat.ne_of_gt (Nat.gcd_pos_of_pos_left α hm)⟩
  let f : componentModel m α → ComplexPoint F :=
    fun z => Point.map (j z.1) (lineCoordinate.symm z.2)
  have hcont : Continuous f := by
    apply continuous_prod_of_discrete_left.mpr
    intro l
    exact (Point.continuous_map (j l)).comp lineCoordinate.symm.continuous
  have hinj : Function.Injective f := by
    rintro ⟨l, z⟩ ⟨k, w⟩ he
    have hlk : l = k := (hexhaust (f (l, z))).unique
      ⟨lineCoordinate.symm z, rfl⟩ ⟨lineCoordinate.symm w, he.symm⟩
    subst k
    haveI : IsClosedImmersion (j l).left := hj l
    have hp := (ComplexPoint.isClosedEmbedding_map_of_closedImmersion (j l)).injective he
    have hz : z = w := lineCoordinate.symm.injective hp
    exact Prod.ext rfl hz
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨l, ⟨w, hw⟩, _⟩ := hexhaust z
    refine ⟨(l, lineCoordinate w), ?_⟩
    change Point.map (j l) (lineCoordinate.symm (lineCoordinate w)) = z
    rw [lineCoordinate.symm_apply_apply]
    exact hw
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  exact (show Continuous e from hcont).homeoOfEquivCompactToT2

theorem componentParametrizationHomeomorph_apply
    (m α : ℕ) (hm : 0 < m) (F : Over (Spec ↧ℂ)) [T2Space (ComplexPoint F)]
    (j : ZMod (Nat.gcd m α) → (projectiveLine ⟶ F))
    (hj : ∀ l, IsClosedImmersion (j l).left)
    (hexhaust : ∀ z : ComplexPoint F, ∃! l, z ∈ Set.range (Point.map (j l)))
    (l : ZMod (Nat.gcd m α)) (z : OnePoint ℂ) :
    componentParametrizationHomeomorph m α hm F j hj hexhaust (l, z) =
      Point.map (j l) (lineCoordinate.symm z) := rfl

end AlgebraicGeometry.RamifiedNormalization.StageFour

import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ComponentTopology

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Transport the action and projection through the component parametrizations. -/
theorem componentParametrization_transport
    (m α : ℕ) (hm : 0 < m) (F E : Over (Spec ↧ℂ))
    [T2Space (ComplexPoint F)]
    (j : ZMod (Nat.gcd m α) → (projectiveLine ⟶ F))
    (hj : ∀ l, IsClosedImmersion (j l).left)
    (hexhaust : ∀ z : ComplexPoint F, ∃! l, z ∈ Set.range (Point.map (j l)))
    (D : F ⟶ F) (P : F ⟶ E) (v : ComplexPoint E ≃ₜ OnePoint ℂ)
    (c : ℂ) (hc : c ≠ 0)
    (hD : ∀ l z, Point.map D (Point.map (j l) (lineCoordinate.symm z)) =
      Point.map (j (l + 1)) (lineCoordinate.symm
        ((Homeomorph.onePointCongr (Homeomorph.mulLeft₀ c hc)) z)))
    (hP : ∀ l z, v (Point.map P (Point.map (j l) (lineCoordinate.symm z))) =
      projection m α c (l, z)) :
    let u := (componentParametrizationHomeomorph m α hm F j hj hexhaust).symm
    (∀ z, u (Point.map D z) = deck m α c hc (u z)) ∧
    (∀ z, v (Point.map P z) = projection m α c (u z)) := by
  let e := componentParametrizationHomeomorph m α hm F j hj hexhaust
  change (∀ z, e.symm (Point.map D z) = deck m α c hc (e.symm z)) ∧
    (∀ z, v (Point.map P z) = projection m α c (e.symm z))
  constructor
  · intro z
    obtain ⟨⟨l, w⟩, rfl⟩ := e.surjective z
    rw [e.symm_apply_apply]
    apply e.injective
    rw [e.apply_symm_apply]
    exact hD l w
  · intro z
    obtain ⟨⟨l, w⟩, rfl⟩ := e.surjective z
    rw [e.symm_apply_apply]
    exact hP l w

end AlgebraicGeometry.RamifiedNormalization.StageFour

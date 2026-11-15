import HodgeLean.Foundations.Program.G32Native.TowerOrbitClasses

/-! # Normalized classes of the actual pushed orbit cycle -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- Normalized representatives on disjoint image components produce a normalized
class of the actual proper pushforward, including its residue degrees.
Source: Fulton, Intersection Theory, 1.4 and 19.1–19.2. -/
theorem tower_orbit_pushed_class
    {Q W W₀ : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] [IsSeparated W₀.hom]
    (ι : Q ⟶ W) (δ : W ⟶ W) (φ : W ⟶ W₀) [QuasiCompact φ.left]
    (k m : ℕ)
    (himm : ∀ t : Fin m,
      IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom ≫ φ).left)
    (hdisj : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of δ ^ s.val).asHom ≫ φ).left)
      (Set.range (ι ≫ (End.of δ ^ t.val).asHom ≫ φ).left))
    (c : ∀ t : Fin m, s2e_supportedClass W₀
      (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom ≫ φ) ℚ) k)
    (hc : ∀ t : Fin m, a3b4_IsCycleClass W₀.hom
      (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom ≫ φ) ℚ) k (c t))
    (a : Fin m → ℚ) :
    ∃ c₀, a3b4_IsCycleClass W₀.hom
      (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι δ m a)) k c₀ ∧
      s2e_classToAbsolute W₀
        (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι δ m a)) k c₀ =
        ∑ t : Fin m,
          (a t * (a1p_degree φ.left
            ((ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)) : ℚ)) •
          s2e_classToAbsolute W₀
            (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom ≫ φ) ℚ) k (c t) := by
  classical
  rw [tower_orbit_pushforward_formula]
  apply SupportedCycleClasses.normalized_sum W₀.hom k
    (fun t : Fin m => s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom ≫ φ) ℚ)
  · intro t
    let := himm t
    rw [s2e_componentCycle_analytic_support]
    exact (ι ≫ (End.of δ ^ t.val).asHom ≫ φ).left.isClosedEmbedding.isClosed_range.preimage
      (ComplexPoint.continuous_underlying_to_zariski W₀)
  · intro s t hst
    let := himm s
    let := himm t
    rw [s2e_componentCycle_analytic_support, s2e_componentCycle_analytic_support]
    exact Set.disjoint_left.mpr fun _ hx hy => Set.disjoint_left.mp (hdisj s t hst) hx hy
  · exact hc

end HodgeLean.Foundations.Program.G32Native

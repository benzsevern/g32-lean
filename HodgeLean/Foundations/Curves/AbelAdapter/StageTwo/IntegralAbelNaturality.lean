import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.AbelianIntegralRank
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.LiftCocycleNaturality
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.ThetaExponential
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.PeriodCovectorLattice

/-! # Integral periods of the actual algebraic Abel map

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations HodgeLean.Foundations.Program HodgeLean.Foundations.IntegralHomology
open scoped TensorProduct Manifold ContDiff CategoryTheory.MonObj
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

/-- The actual singular pushforward retains the original integral Abel periods.
Source: Forster, §21; Hatcher, §3.1; liftCocycle_pairing_natural.
HC no distance; AV milestone no distance. -/
theorem integralAbel_period_natural
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [ChartedSpace E (ComplexPoint X)] [IsManifold 𝓘(ℂ, E) ω (ComplexPoint X)]
    [ConnectedSpace (ComplexPoint X)] (h : Module.finrank ℂ E = 1)
    (p : ComplexPoint X) (j : X ⟶ model h)
    (hj : ∀ x, Point.map j x = modelAbel h p x)
    [IsCommMonObj (model (C := ComplexPoint X) h)]
    (a : IntegralHomology.Lattice (TopCat.of (ComplexPoint X))) :
    abelianIntegralPeriod (model h) (mapLattice (pointMap j) a) =
      modelPeriod h (curvePeriodEquiv h p a) := by
  letI := b3_periodLattice_finite (C := ComplexPoint X) h
  letI := b3_periodLattice_free (E := E) (C := ComplexPoint X)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint X) h)
  let A := model (C := ComplexPoint X) h
  let D := thetaCoverLinear (C := ComplexPoint X) h
  let f := analyticAbel h p
  have hf : Continuous f := analyticAbel_continuous h p
  let g : ComplexPoint X → Additive (ComplexPoint A) := Additive.ofMul ∘ Point.map j
  have hg : Continuous g := continuous_ofMul.comp (pointMap j).hom.continuous
  have hcomm : ∀ x v, b3Rest2_covHom v = f x →
      complexExponentialHom A _ (D v) = g x := by
    intro x v hv
    apply Additive.toMul.injective
    change (complexExponential A _ (D v)).toMul = Point.map j x
    rw [hj x]
    exact (thetaCoverLinear_exp h v).symm.trans (congrArg (theta h) hv)
  apply Subtype.ext
  funext i
  let ℓ : (Fin (TopologicalSpace.dim A.left) → ℂ) →+ ℂ := Pi.evalAddMonoidHom _ i
  let L : b3Rest2_VJ E (ComplexPoint X) →L[ℂ] ℂ := (ContinuousLinearMap.proj i).comp D
  obtain ⟨θ, hθ⟩ := (periodFormEquiv h).surjective L
  have hθ' : periodLinear θ = L := (periodFormEquiv_apply h θ).symm.trans hθ
  have hℓ : ℓ.comp D.toAddMonoidHom =
      (AddMonoidHom.id ℂ).comp (b3Rest2_ellV θ) := by
    apply AddMonoidHom.ext
    intro v
    exact (congrArg (fun T : b3Rest2_VJ E (ComplexPoint X) →L[ℂ] ℂ ↦ T v) hθ').symm
  have ht := liftCocycle_transport b3Rest2_covHom b3Rest2_covHom_spec
    (complexExponentialHom A _) (abelianExpCover_spec A) D.toAddMonoidHom D.continuous
    f hf g hg hcomm ℓ
  have hn := liftCocycle_pairing_natural (complexExponentialHom A _)
    (abelianExpCover_spec A) (pointMap j) Additive.ofMul continuous_ofMul ℓ a
  calc
    (abelianIntegralPeriod A (mapLattice (pointMap j) a)).val i =
        StageThree.cocyclePairing _ (b3Rest2_liftCocycle (complexExponentialHom A _)
          (abelianExpCover_spec A) Additive.ofMul continuous_ofMul ℓ)
          (mapLattice (pointMap j) a) := rfl
    _ = StageThree.cocyclePairing _
        (b3Rest2_liftCocycle (complexExponentialHom A _) (abelianExpCover_spec A) g hg ℓ) a := hn.symm
    _ = StageThree.cocyclePairing _
        (b3Rest2_integCocycle f hf (AddMonoidHom.id ℂ) θ) a := by
      rw [ht, hℓ]
      rfl
    _ = (curvePeriodEquiv h p a).val θ := (curvePeriodEquiv_pairing h p a θ).symm
    _ = periodLinear θ (b5_lattice _ _ (curvePeriodEquiv h p a)) := (periodLinear_lattice θ _).symm
    _ = D (b5_lattice _ _ (curvePeriodEquiv h p a)) i :=
      congrArg (fun T : b3Rest2_VJ E (ComplexPoint X) →L[ℂ] ℂ ↦
        T (b5_lattice _ _ (curvePeriodEquiv h p a))) hθ'
    _ = (modelPeriod h (curvePeriodEquiv h p a)).val i := rfl

#print axioms integralAbel_period_natural
end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

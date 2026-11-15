import HodgeLean.Adapters.NormalConeB4aGysinSmoothSourceCover
import HodgeLean.Adapters.NormalConeB4aGysinCriticalValues

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Analytic

/-- Outside a null set of parameter values, every point of an equal-dimensional
smooth source has an intrinsic coordinate chart with invertible parameter derivative. -/
theorem a3b4a_gysin_smooth_source_regular_parameter_charts
    (X Y : Over (Spec (CommRingCat.of ℂ))) (n c : ℕ)
    [SmoothOfRelativeDimension n X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ) :
    ∃ B : Set (Fin n → ℂ), MeasureTheory.volume B = 0 ∧
      ∀ x : ComplexPoint X, Point.map f x ∈ Φ.source →
        (Φ (Point.map f x)).1 ∉ B →
        ∃ j : ComplexPoint X, x ∈ (chartAt (Fin n → ℂ) j).source ∧
          IsUnit (fderiv ℂ
            (fun a => (Φ (Point.map f ((chartAt (Fin n → ℂ) j).symm a))).1)
            ((chartAt (Fin n → ℂ) j) x)) := by
  classical
  letI : SecondCountableTopology (ComplexPoint X) := f4_secondCountable X
  let V := Point.map f ⁻¹' Φ.source
  have hV : IsOpen V := Φ.open_source.preimage (Point.continuous_map f)
  obtain ⟨J, hJ, _, hcover⟩ := a3b4a_gysin_countable_restricted_chart_cover
    (H := Fin n → ℂ) V hV
  let η : ComplexPoint X → (Fin n → ℂ) → (Fin n → ℂ) :=
    fun j a => (Φ (Point.map f ((chartAt (Fin n → ℂ) j).symm a))).1
  let Ω : ComplexPoint X → Set (Fin n → ℂ) := fun j =>
    (chartAt (Fin n → ℂ) j).target ∩ (chartAt (Fin n → ℂ) j).symm ⁻¹' V
  let B : Set (Fin n → ℂ) := ⋃ j ∈ J,
    η j '' {a | a ∈ Ω j ∧ ¬ IsUnit (fderiv ℂ (η j) a)}
  have hnull : MeasureTheory.volume B = 0 := by
    apply (MeasureTheory.measure_biUnion_null_iff hJ).mpr
    intro j _
    apply a3b4a_gysin_complex_critical_values_null (Ω j)
      ((chartAt (Fin n → ℂ) j).isOpen_inter_preimage_symm hV) (η j)
    apply AnalyticOnNhd.differentiableOn
    intro a ha
    exact ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) (Fin c → ℂ)).analyticAt _).comp
      (a3b4a_gysin_smooth_source_coordinate_parametrization X Y n n c f Φ hΦ j a ha)
  refine ⟨B, hnull, ?_⟩
  intro x hx hnot
  have hxcover : x ∈ ⋃ j ∈ J, ((chartAt (Fin n → ℂ) j).restrOpen V hV).source :=
    hcover ▸ hx
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hxcover
  refine ⟨j, hxj.1, ?_⟩
  by_contra hbad
  apply hnot
  apply Set.mem_iUnion₂.mpr
  refine ⟨j, hj, (chartAt (Fin n → ℂ) j) x, ⟨?_, hbad⟩, ?_⟩
  · refine ⟨(chartAt (Fin n → ℂ) j).map_source hxj.1, ?_⟩
    change (chartAt (Fin n → ℂ) j).symm ((chartAt (Fin n → ℂ) j) x) ∈ V
    rwa [(chartAt (Fin n → ℂ) j).left_inv hxj.1]
  · change (Φ (Point.map f ((chartAt (Fin n → ℂ) j).symm
      ((chartAt (Fin n → ℂ) j) x)))).1 = _
    rw [(chartAt (Fin n → ℂ) j).left_inv hxj.1]

end HodgeLean.Adapters

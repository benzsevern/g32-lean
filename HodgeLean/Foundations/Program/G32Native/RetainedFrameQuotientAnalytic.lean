import HodgeLean.Foundations.Program.G32Native.RetainedNormalFrameQuotient
import HodgeLean.Foundations.Program.G32Native.OriginalEquationIdentityCoefficients
import HodgeLean.Foundations.Program.G32Native.AnalyticQuotientFromEquations
import HodgeLean.Foundations.Program.G32Native.OriginalEquationRowsAnalytic

/-! # Analytic quotient coefficients in a fixed original ambient chart -/

noncomputable section
set_option maxHeartbeats 50000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- The quotient in the given frame and ambient chart, extended by zero
outside their common domain. -/
def retainedFrameQuotientOperator
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A) (U : Y.left.Opens)
    (hU : U ≤ j.left ⁻¹ᵁ A)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (z : ComplexPoint X) (x : ComplexPoint Y) :
    (Fin d → ℂ) →L[ℂ] (Fin k → ℂ) := by
  classical
  exact if h : x ∈ Point.overOpen U ∧ Point.map j x ∈ (chartAt (Fin d → ℂ) z).source
    then framedCovectorQuotient (i1_conormalFrameBasis j.left k U E x h.1)
      (retainedAffineConormalDifferential X Y j d A hA x (hU h.1) z h.2)
    else 0

theorem retainedFrameQuotientOperator_eq
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A) (U : Y.left.Opens)
    (hU : U ≤ j.left ⁻¹ᵁ A)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (z : ComplexPoint X) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen U) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    retainedFrameQuotientOperator X Y j d k A hA U hU E z x =
      framedCovectorQuotient (i1_conormalFrameBasis j.left k U E x hx)
        (retainedAffineConormalDifferential X Y j d A hA x (hU hx) z hz) := by
  classical
  unfold retainedFrameQuotientOperator
  rw [dite_eq_left (show x ∈ Point.overOpen U ∧
    Point.map j x ∈ (chartAt (Fin d → ℂ) z).source from ⟨hx, hz⟩)]

/-- Analytic original equation rows and their coefficient matrix determine
analytic coefficients of the intrinsic quotient in the specified frame. -/
theorem analyticAt_retained_frame_quotient
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A)
    (U : Y.left.Opens) (hU : U ≤ j.left ⁻¹ᵁ A)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (u : Fin k → RingHom.ker (j.left.app A).hom)
    (r : Fin k → Fin k → Γ(Y.left, U))
    (hr : ∀ (x : ComplexPoint Y) (hx : x ∈ Point.overOpen U) (i a : Fin k),
      i1_conormalFrameCoordinates j.left k U E x hx
        (originalRegularConormalValue j.left A hA (u i) x (hU hx)) a =
        Point.evaluate U (r i a) x)
    (σ : B → ComplexPoint Y) (b : B) (z : ComplexPoint X)
    (hdom : ∀ᶠ c in 𝓝 b, σ c ∈ Point.overOpen U ∧
      Point.map j (σ c) ∈ (chartAt (Fin d → ℂ) z).source)
    (hC : AnalyticAt ℂ (fun c => regularEquationCoefficientOperator Y k U r (σ c)) b)
    (hF : AnalyticAt ℂ (fun c => ContinuousLinearMap.pi (fun i : Fin k =>
      fderiv ℂ (fun a : Fin d → ℂ =>
        Point.evaluate A (u i).val ((chartAt (Fin d → ℂ) z).symm a))
        ((chartAt (Fin d → ℂ) z) (Point.map j (σ c))))) b)
    (hid : regularEquationCoefficientOperator Y k U r (σ b) =
      ContinuousLinearMap.id ℂ (Fin k → ℂ)) :
    AnalyticAt ℂ (fun c => retainedFrameQuotientOperator X Y j d k A hA U hU E z (σ c)) b := by
  apply analyticAt_quotient_of_equation_coefficients
    (fun c => regularEquationCoefficientOperator Y k U r (σ c))
    (fun c => ContinuousLinearMap.pi (fun i : Fin k =>
      fderiv ℂ (fun a : Fin d → ℂ =>
        Point.evaluate A (u i).val ((chartAt (Fin d → ℂ) z).symm a))
        ((chartAt (Fin d → ℂ) z) (Point.map j (σ c)))))
    _ b hC hF (ContinuousLinearEquiv.refl ℂ (Fin k → ℂ)) hid
  filter_upwards [hdom] with c hc
  apply ContinuousLinearMap.ext
  intro v
  funext i
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply]
  rw [retainedFrameQuotientOperator_eq X Y j d k A hA U hU E z (σ c) hc.1 hc.2]
  rw [← retainedNormalFrameQuotientAt_eq X Y j d k A hA U hU E (σ c) hc.1 z hc.2]
  exact retainedNormalFrameQuotientAt_equation X Y j d k A hA U hU E u r (σ c) hc.1
    (hr (σ c) hc.1) z hc.2 v i

/-- Analytic parametrizations of the original base give analytic quotient
operators whenever the selected original equation coefficients are the
identity at the reference point. -/
theorem retained_frame_quotient_analytic_in_coordinates
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (m d k : ℕ) [SmoothOfRelativeDimension m Y.hom]
    [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A)
    (U : Y.left.Opens) (hU : U ≤ j.left ⁻¹ᵁ A)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (u : Fin k → RingHom.ker (j.left.app A).hom)
    (r : Fin k → Fin k → Γ(Y.left, U))
    (hr : ∀ (x : ComplexPoint Y) (hx : x ∈ Point.overOpen U) (i a : Fin k),
      i1_conormalFrameCoordinates j.left k U E x hx
        (originalRegularConormalValue j.left A hA (u i) x (hU hx)) a =
        Point.evaluate U (r i a) x)
    (σ : B → ComplexPoint Y) (b : B) (z : ComplexPoint X)
    (hσ : ContMDiffAt 𝓘(ℂ, B) 𝓘(ℂ, Fin m → ℂ) ω σ b)
    (hbU : σ b ∈ Point.overOpen U)
    (hbz : Point.map j (σ b) ∈ (chartAt (Fin d → ℂ) z).source)
    (hid : regularEquationCoefficientOperator Y k U r (σ b) =
      ContinuousLinearMap.id ℂ (Fin k → ℂ)) :
    AnalyticAt ℂ (fun c => retainedFrameQuotientOperator X Y j d k A hA U hU E z (σ c)) b := by
  have hJ : ContMDiff 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (Point.map j) :=
    (HodgeLean.Foundations.Analytic.f4_isHom_iff_contMDiff
      (d := m) (e := d) (Point.map j)).mp
      (HodgeLean.Foundations.Analytic.f4_map_isHom j)
  have hJσ := hJ.contMDiffAt.comp b hσ
  have hcoord : AnalyticAt ℂ
      (fun c => (chartAt (Fin d → ℂ) z) (Point.map j (σ c))) b :=
    (((contMDiffOn_chart (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) (x := z)).contMDiffAt
      ((chartAt (Fin d → ℂ) z).open_source.mem_nhds hbz)).comp b hJσ).contDiffAt.analyticAt
  have hC := (((regularEquationCoefficientOperator_contMDiffOn Y k m U r).contMDiffAt
    ((Point.isOpen_overOpen U).mem_nhds hbU)).comp b hσ).contDiffAt.analyticAt
  have hF := original_equation_rows_analyticAt X d k A (fun i => (u i).val) z
    (fun c => (chartAt (Fin d → ℂ) z) (Point.map j (σ c))) b hcoord
    ((chartAt (Fin d → ℂ) z).map_source hbz)
    (by rw [(chartAt (Fin d → ℂ) z).left_inv hbz]; exact hU hbU)
  have hdom : ∀ᶠ c in 𝓝 b, σ c ∈ Point.overOpen U ∧
      Point.map j (σ c) ∈ (chartAt (Fin d → ℂ) z).source :=
    (hσ.continuousAt.eventually ((Point.isOpen_overOpen U).mem_nhds hbU)).and
      (hJσ.continuousAt.eventually ((chartAt (Fin d → ℂ) z).open_source.mem_nhds hbz))
  exact analyticAt_retained_frame_quotient X Y j d k A hA U hU E u r hr σ b z hdom hC hF hid

/-- Original equations can be selected internally; the analytic quotient
requires only the specified algebraic frame and analytic base parameter. -/
theorem retained_frame_quotient_analytic
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (m d k : ℕ) [SmoothOfRelativeDimension m Y.hom]
    [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A)
    (U : Y.left.Opens) (hU : U ≤ j.left ⁻¹ᵁ A)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j.left) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (σ : B → ComplexPoint Y) (b : B) (z : ComplexPoint X)
    (hσ : ContMDiffAt 𝓘(ℂ, B) 𝓘(ℂ, Fin m → ℂ) ω σ b)
    (hbU : σ b ∈ Point.overOpen U)
    (hbz : Point.map j (σ b) ∈ (chartAt (Fin d → ℂ) z).source) :
    AnalyticAt ℂ (fun c => retainedFrameQuotientOperator X Y j d k A hA U hU E z (σ c)) b := by
  obtain ⟨u, r, hr, hid⟩ := exists_original_equation_identity_coefficients
    X Y j k m A hA U hU E (σ b) hbU
  exact retained_frame_quotient_analytic_in_coordinates X Y j m d k A hA U hU E
    u r hr σ b z hσ hbU hbz hid

#print axioms retained_frame_quotient_analytic

#print axioms retained_frame_quotient_analytic_in_coordinates

#print axioms analyticAt_retained_frame_quotient
end HodgeLean.Foundations.TubularEuler

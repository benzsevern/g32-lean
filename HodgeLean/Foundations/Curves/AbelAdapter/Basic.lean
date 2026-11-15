import HodgeLean.Foundations.Curves.AbelAdapter.Proofs

/-! # Normalized algebraic Abel adapter: review interfaces

Five units retain the actual period quotient and literal complex-point equation.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
open scoped TensorProduct Manifold ContDiff CategoryTheory.MonObj
namespace HodgeLean.Foundations.Curves.AbelAdapter
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- curveChart: retained construction interface.
Source: Serre, GAGA, §2; `connectedSpace_complexPoint`; Mathlib `Module.finrank_pi`. -/
theorem curveChart (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 1) :
    Module.finrank ℂ (Fin (TopologicalSpace.dim X.left) → ℂ) = 1 ∧
    Nonempty (ChartedSpace (Fin (TopologicalSpace.dim X.left) → ℂ) (ComplexPoint X)) ∧
    ConnectedSpace (ComplexPoint X) := 
  curveChart_aux X hdim

/-- projectiveGroup: retained construction interface.
Source: Birkenhake–Lange, Theorem 4.5.1 and Ch. 11; `b5_groupObj`. -/
theorem projectiveGroup (hE : Module.finrank ℂ E = 1) :
    Smooth (model (C := C) hE).hom ∧ IsProjective (model (C := C) hE).hom ∧
    IsIntegral (model (C := C) hE).left ∧
    ∃ G : GrpObj (model (C := C) hE), letI := G; IsCommMonObj (model (C := C) hE) := 
  projectiveGroup_aux hE

/-- thetaNormalization: retained construction interface.
Source: Birkenhake–Lange, §§1.1–1.2, Theorem 4.5.1; `b5_period_filtration`. -/
theorem thetaNormalization (hE : Module.finrank ℂ E = 1) :
    letI := b3_periodLattice_finite (C := C) hE
    letI := b3_periodLattice_free (E := E) (C := C)
    let Λ := b3_periodLattice E C
    let F := b3_periodF E C
    let hF := b3_isWeightOne (C := C) hE
    let Q := polarization (C := C) hE
    let hQ := b3_intersectionForm_isRiemannForm hE Q
      (b3_exists_intersectionForm (C := C) hE).choose_spec
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    b5_theta Λ F hF Q hQ 0 = 1 ∧
    (∀ t u, b5_theta Λ F hF Q hQ (t + u) =
      b5_theta Λ F hF Q hQ t * b5_theta Λ F hF Q hQ u) ∧
    (∀ v : (ℂ ⊗[ℤ] Λ) ⧸ F, theta hE (QuotientAddGroup.mk v) =
      b5_thetaCover Λ F hF Q hQ (b2_coord _ v)) ∧
    (∀ l : Λ, b5_periodDerivative Λ F hF Q hQ (b5_lattice Λ F l) ∈
      HodgeLean.Adapters.abelianPeriodLattice (b5_model Λ F hF Q)) ∧
    F.map (b2_cplxMap (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom) =
      b2_abelianF (b5_model Λ F hF Q) := 
  thetaNormalization_aux hE

/-- holomorphicAbel: retained construction interface.
Source: Forster, §21; `b3_abelJacobi_holomorphic`; `b5_theta_holomorphicFunctions`. -/
theorem holomorphicAbel (hE : Module.finrank ℂ E = 1) (p : C) :
    letI := b3_periodLattice_finite (C := C) hE
    letI := b3_periodLattice_free (E := E) (C := C)
    let Λ := b3_periodLattice E C
    let F := b3_periodF E C
    let hF := b3_isWeightOne (C := C) hE
    let Q := polarization (C := C) hE
    let hQ := b3_intersectionForm_isRiemannForm hE Q
      (b3_exists_intersectionForm (C := C) hE).choose_spec
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    letI : IsIntegral (model (C := C) hE).left := by
      dsimp [model]; exact b5_integral _ _ hF Q hQ
    letI : Smooth (model (C := C) hE).hom := by
      dsimp [model]; exact b5_smooth _ _ hF Q hQ
    letI : IsProjective (model (C := C) hE).hom := by
      dsimp [model]; exact b5_projective _ _ hF Q hQ
    ContMDiff 𝓘(ℂ, E)
      𝓘(ℂ, Fin (TopologicalSpace.dim (model (C := C) hE).left) → ℂ) ω
      (modelAbel hE p) := 
  holomorphicAbel_aux hE p

/-- algebraicAbel: retained construction interface.
Source: Serre, GAGA (1956), §3 Proposition 13; `gagam_algebraize`; Forster, §21. -/
theorem algebraicAbel (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 1) (p : ComplexPoint X) :
    letI := HodgeLean.Foundations.connectedSpace_complexPoint X
    let hE : Module.finrank ℂ (Fin (TopologicalSpace.dim X.left) → ℂ) = 1 := by
      simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
        smul_eq_mul, mul_one] using hdim
    ∃ j : X ⟶ model hE,
      (∀ x : ComplexPoint X, Point.map j x = modelAbel hE p x) ∧
      Point.map j p = theta hE (0 : b3_Jacobian _ (ComplexPoint X)) := 
  algebraicAbel_aux X hdim p

end HodgeLean.Foundations.Curves.AbelAdapter

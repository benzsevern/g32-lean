import HodgeLean.Foundations.Curves.AbelAdapter.Defs

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
theorem curveChart_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 1) :
    Module.finrank ℂ (Fin (TopologicalSpace.dim X.left) → ℂ) = 1 ∧
    Nonempty (ChartedSpace (Fin (TopologicalSpace.dim X.left) → ℂ) (ComplexPoint X)) ∧
    ConnectedSpace (ComplexPoint X) := by
  refine ⟨?_, ⟨inferInstance⟩, HodgeLean.Foundations.connectedSpace_complexPoint X⟩
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
    smul_eq_mul, mul_one] using hdim

/-- projectiveGroup: retained construction interface.
Source: Birkenhake–Lange, Theorem 4.5.1 and Ch. 11; `b5_groupObj`. -/
theorem projectiveGroup_aux (hE : Module.finrank ℂ E = 1) :
    Smooth (model (C := C) hE).hom ∧ IsProjective (model (C := C) hE).hom ∧
    IsIntegral (model (C := C) hE).left ∧
    ∃ G : GrpObj (model (C := C) hE), letI := G; IsCommMonObj (model (C := C) hE) := by
  letI := b3_periodLattice_finite (C := C) hE
  letI := b3_periodLattice_free (E := E) (C := C)
  let Λ := b3_periodLattice E C
  let F := b3_periodF E C
  let hF := b3_isWeightOne (C := C) hE
  let Q := polarization (C := C) hE
  have hQ := b3_intersectionForm_isRiemannForm hE Q
    (b3_exists_intersectionForm (C := C) hE).choose_spec
  exact ⟨b5_smooth Λ F hF Q hQ, b5_projective Λ F hF Q hQ,
    b5_integral Λ F hF Q hQ, b5_groupObj Λ F hF Q hQ,
    b5_commutative Λ F hF Q hQ⟩

/-- thetaNormalization: retained construction interface.
Source: Birkenhake–Lange, §§1.1–1.2, Theorem 4.5.1; `b5_period_filtration`. -/
theorem thetaNormalization_aux (hE : Module.finrank ℂ E = 1) :
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
      b2_abelianF (b5_model Λ F hF Q) := by
  letI := b3_periodLattice_finite (C := C) hE
  letI := b3_periodLattice_free (E := E) (C := C)
  dsimp only
  refine ⟨(b5_group _ _ _ _ _).1, (b5_group _ _ _ _ _).2.1, ?_,
    b5_periodDerivative_lattice _ _ _ _ _, b5_period_filtration _ _ _ _ _⟩
  intro v
  exact b5_theta_descent _ _ _ _ _ v

/-- holomorphicAbel: retained construction interface.
Source: Forster, §21; `b3_abelJacobi_holomorphic`; `b5_theta_holomorphicFunctions`. -/
theorem holomorphicAbel_aux (hE : Module.finrank ℂ E = 1) (p : C) :
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
      (modelAbel hE p) := by
  letI := b3_periodLattice_finite (C := C) hE
  letI := b3_periodLattice_free (E := E) (C := C)
  let Λ := b3_periodLattice E C
  let F := b3_periodF E C
  let hF := b3_isWeightOne (C := C) hE
  let Q := polarization (C := C) hE
  have hQ := b3_intersectionForm_isRiemannForm hE Q
    (b3_exists_intersectionForm (C := C) hE).choose_spec
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI : Smooth (b5_model Λ F hF Q).hom := b5_smooth Λ F hF Q hQ
  letI : IsProjective (b5_model Λ F hF Q).hom := b5_projective Λ F hF Q hQ
  letI := b2_latticeMap_discrete F hF
  have ht := (b5_theta_holomorphicFunctions Λ F hF Q hQ).1
  have ha := b3_abelJacobi_holomorphic (E := E) (C := C) hE p _
    (b3_exists_abelJacobi (C := C) hE p).choose_spec
  exact ht.comp ha

private theorem algebraize_test_map (Z W : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W.left] [Smooth W.hom] [IsProjective W.hom]
    (f : ComplexPoint Z → ComplexPoint W)
    (hf : ContMDiff
      (modelWithCornersSelf ℂ (Fin (TopologicalSpace.dim Z.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (TopologicalSpace.dim W.left) → ℂ)) ω f) :
    ∃ j : Z ⟶ W, Point.map j = f :=
  HodgeLean.Adapters.gagam_algebraize Z W f hf

set_option maxHeartbeats 400000 in
/-- algebraicAbel: retained construction interface.
Source: Serre, GAGA (1956), §3 Proposition 13; `gagam_algebraize`; Forster, §21. -/
theorem algebraicAbel_aux (X : Over (Spec ↧ℂ))
    [hZI : IsIntegral X.left] [hZS : Smooth X.hom] [hZP : IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 1) (p : ComplexPoint X) :
    letI := HodgeLean.Foundations.connectedSpace_complexPoint X
    let hE : Module.finrank ℂ (Fin (TopologicalSpace.dim X.left) → ℂ) = 1 := by
      simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
        smul_eq_mul, mul_one] using hdim
    ∃ j : X ⟶ model hE,
      (∀ x : ComplexPoint X, Point.map j x = modelAbel hE p x) ∧
      Point.map j p = theta hE (0 : b3_Jacobian _ (ComplexPoint X)) := by
  letI := HodgeLean.Foundations.connectedSpace_complexPoint X
  let E₂ := Fin (TopologicalSpace.dim X.left) → ℂ
  have h₂ : Module.finrank ℂ E₂ = 1 := by
    simpa only [E₂, Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      smul_eq_mul, mul_one] using hdim
  let Λ₂ := b3_periodLattice E₂ (ComplexPoint X)
  let F₂ := b3_periodF E₂ (ComplexPoint X)
  letI := b3_periodLattice_finite (E := E₂) (C := ComplexPoint X) h₂
  letI := b3_periodLattice_free (E := E₂) (C := ComplexPoint X)
  let hF₂ := b3_isWeightOne (E := E₂) (C := ComplexPoint X) h₂
  let Q₂ := polarization (E := E₂) (C := ComplexPoint X) h₂
  have hQ₂ := b3_intersectionForm_isRiemannForm (E := E₂) (C := ComplexPoint X) h₂ Q₂
    (b3_exists_intersectionForm (E := E₂) (C := ComplexPoint X) h₂).choose_spec
  let Y := model (E := E₂) (C := ComplexPoint X) h₂
  letI : IsIntegral Y.left := b5_integral Λ₂ F₂ hF₂ Q₂ hQ₂
  letI : Smooth Y.hom := b5_smooth Λ₂ F₂ hF₂ Q₂ hQ₂
  letI : IsProjective Y.hom := b5_projective Λ₂ F₂ hF₂ Q₂ hQ₂
  letI : IsIntegral (b5_model Λ₂ F₂ hF₂ Q₂).left := b5_integral Λ₂ F₂ hF₂ Q₂ hQ₂
  letI : Smooth (b5_model Λ₂ F₂ hF₂ Q₂).hom := b5_smooth Λ₂ F₂ hF₂ Q₂ hQ₂
  letI : IsProjective (b5_model Λ₂ F₂ hF₂ Q₂).hom := b5_projective Λ₂ F₂ hF₂ Q₂ hQ₂
  letI := b2_latticeMap_discrete F₂ hF₂
  have ht := (b5_theta_holomorphicFunctions Λ₂ F₂ hF₂ Q₂ hQ₂).1
  have ha := b3_abelJacobi_holomorphic (E := E₂) (C := ComplexPoint X) h₂ p _
    (b3_exists_abelJacobi (E := E₂) (C := ComplexPoint X) h₂ p).choose_spec
  have hh := ht.comp ha
  let f : ComplexPoint X → ComplexPoint (b5_model Λ₂ F₂ hF₂ Q₂) :=
    b5_theta Λ₂ F₂ hF₂ Q₂ hQ₂ ∘ analyticAbel (E := E₂) (C := ComplexPoint X) h₂ p
  have hh' : ContMDiff
      (modelWithCornersSelf ℂ (Fin (TopologicalSpace.dim X.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (TopologicalSpace.dim (b5_model Λ₂ F₂ hF₂ Q₂).left) → ℂ)) ω f := hh
  have hex : ∃ j : X ⟶ b5_model Λ₂ F₂ hF₂ Q₂, Point.map j = f :=
    @algebraize_test_map X (b5_model Λ₂ F₂ hF₂ Q₂)
    hZI hZS hZP
    (b5_integral Λ₂ F₂ hF₂ Q₂ hQ₂) (b5_smooth Λ₂ F₂ hF₂ Q₂ hQ₂)
    (b5_projective Λ₂ F₂ hF₂ Q₂ hQ₂) f hh'
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, fun x ↦ congrFun hj x, ?_⟩
  exact (congrFun hj p).trans (congrArg (theta (E := E₂) (C := ComplexPoint X) h₂)
    (b3_exists_abelJacobi (E := E₂) (C := ComplexPoint X) h₂ p).choose_spec.1)
end HodgeLean.Foundations.Curves.AbelAdapter

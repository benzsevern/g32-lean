import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartPointClassNormalization

/-! Exact point orientation of an actual radial chart parametrization. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- An actual point-pair parametrization with the specified positive radial
chart coordinates carries the exact ordered complex point class. -/
theorem s4_q3_radial_point_chart_class
    {M : Type} [TopologicalSpace M] [T1Space M] (c : ℕ)
    (e : OpenPartialHomeomorph M (Fin c → ℂ)) (x : M) (hx : x ∈ e.source)
    (r : ℝ) (hr : 0 < r) (P : puncturedPair ℂ c ⟶ pointComplementPair x)
    (hsource : ∀ v : Fin c → ℂ, TopPair.Hom.fst P v ∈ e.source)
    (hcoord : ∀ v : Fin c → ℂ, e (TopPair.Hom.fst P v) =
      OpenPartialHomeomorph.univBall (e x) r v) :
    relativeHomologyMap ℚ (2 * c) P (standardComplexLocalClass ℚ c) =
      localClassOfChart c e x hx := by
  have hcont := e.continuousOn.comp_continuous (TopPair.Hom.fst P).hom.continuous hsource
  let Q : puncturedPair ℂ c ⟶ neighborhoodPointComplementPair e.target (e x) :=
    TopPair.ofHom
      (TopCat.ofHom ⟨fun v => ⟨e (TopPair.Hom.fst P v), e.map_source (hsource v)⟩,
        hcont.subtype_mk _⟩)
      (TopCat.ofHom ⟨fun v => ⟨⟨e (TopPair.Hom.fst P v.1), e.map_source (hsource v.1)⟩, by
        intro h
        have heq := e.injOn (hsource v.1) hx h
        have hw := TopPair.Hom.w_apply P v
        exact (TopPair.Hom.snd P v).2 (hw.trans heq)⟩, by
          exact ((hcont.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩) (by ext; rfl)
  have hQP : Q ≫ chartTargetInverseAtSourcePairMap c e x = P := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext v
      apply Subtype.ext
      exact (e.left_inv (hsource v.1)).trans (TopPair.Hom.w_apply P v).symm
    · ext v
      exact e.left_inv (hsource v)
  rw [← hQP]
  apply chartTargetPointPairMap_localClass c e x hx Q
  have hcomp : Q ≫ neighborhoodPointComplementPairMap e.target (e x) =
      centeredComplexEmbeddingPair c (OpenPartialHomeomorph.univBall (e x) r)
        (continuous_complexUnivBall c _ _) (injective_complexUnivBall c _ _) 0 ≫
        translationPointComplementPairMap (Fin c → ℂ) (e x) := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext v
      apply Subtype.ext
      change e (TopPair.Hom.fst P v.1) =
        OpenPartialHomeomorph.univBall (e x) r (v.1 + 0) -
          OpenPartialHomeomorph.univBall (e x) r 0 + e x
      simp only [hcoord, add_zero, OpenPartialHomeomorph.univBall_apply_zero, sub_add_cancel]
    · ext v
      change Fin c → ℂ at v
      change e (TopPair.Hom.fst P v) =
        OpenPartialHomeomorph.univBall (e x) r (v + 0) -
          OpenPartialHomeomorph.univBall (e x) r 0 + e x
      simp only [hcoord, add_zero, OpenPartialHomeomorph.univBall_apply_zero, sub_add_cancel]
  rw [hcomp, relativeHomologyMap_comp, LinearMap.comp_apply,
    centeredComplexUnivBall_preserves_standardComplexLocalClass c _ r hr 0]

end HodgeLean.Foundations.Program

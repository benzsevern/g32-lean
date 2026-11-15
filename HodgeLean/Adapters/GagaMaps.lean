import HodgeLean.Adapters.GagaMapsProofs

/-!
# Algebraization of holomorphic maps (FROZEN SPEC)

This specification isolates the implication from a closed analytic graph to a morphism between
integral smooth projective complex schemes. It claims the analytic graph statement, its set-level
Chow image, the graph-specific algebraic bridge, and the resulting algebraization. It does not
claim a general analytification equivalence or a comparison of analytic structure sheaves.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped Manifold ContDiff MonoidalCategory
open HodgeLean.Foundations

namespace HodgeLean.Adapters

/-- The graph of a holomorphic map between smooth projective complex varieties is a closed
analytic subset of their fibre product.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Chapter VIII, §A
(the graph theorem for holomorphic maps). -/
theorem gagam_graph_closedAnalytic (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y)
    (hF : ContMDiff (modelWithCornersSelf ℂ (Fin (dim X.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (dim Y.left) → ℂ)) ω F) :
    IsClosedAnalytic (Fin (dim (gagam_product X Y).left) → ℂ) (gagam_graph X Y F) :=
  gagam_graph_closedAnalytic_aux X Y F hF

example (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y)
    (hF : ContMDiff (modelWithCornersSelf ℂ (Fin (dim X.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (dim Y.left) → ℂ)) ω F) :
    IsClosedAnalytic (Fin (dim (gagam_product X Y).left) → ℂ) (gagam_graph X Y F) :=
  gagam_graph_closedAnalytic X Y F hF

/-- The analytic graph has a closed carrier in the scheme-theoretic fibre product.
Source: Chow, *On compact complex analytic varieties*, Amer. J. Math. 71 (1949), together with
`chowG_setLevel`. -/
theorem gagam_graph_closed (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y)
    (hF : ContMDiff (modelWithCornersSelf ℂ (Fin (dim X.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (dim Y.left) → ℂ)) ω F) :
    ∃ C : Set (gagam_product X Y).left, IsClosed C ∧
      gagam_graph X Y F =
        (Point.underlying : ComplexPoint (gagam_product X Y) →
          (gagam_product X Y).left) ⁻¹' C :=
  gagam_graph_closed_aux X Y F hF

example (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y)
    (hF : ContMDiff (modelWithCornersSelf ℂ (Fin (dim X.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (dim Y.left) → ℂ)) ω F) :
    ∃ C : Set (gagam_product X Y).left, IsClosed C ∧
      gagam_graph X Y F = Point.underlying ⁻¹' C :=
  gagam_graph_closed X Y F hF

/-- A closed carrier whose complex points are the graph determines an algebraic morphism.
Source: Hartshorne, *Algebraic Geometry*, Chapter III, Corollary 11.4 (proper quasi-finite
morphisms and Zariski's Main Theorem); EGA III, 4.4; smooth varieties are normal. -/
theorem gagam_morphism_of_closed_graph (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y)
    (C : Set (gagam_product X Y).left) (hC : IsClosed C)
    (hgraph : gagam_graph X Y F =
      (Point.underlying : ComplexPoint (gagam_product X Y) →
        (gagam_product X Y).left) ⁻¹' C) :
    ∃ f : X ⟶ Y, Point.map f = F :=
  gagam_morphism_of_closed_graph_aux X Y F C hC hgraph

example (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y) (C : Set (gagam_product X Y).left)
    (hC : IsClosed C) (hgraph : gagam_graph X Y F = Point.underlying ⁻¹' C) :
    ∃ f : X ⟶ Y, Point.map f = F :=
  gagam_morphism_of_closed_graph X Y F C hC hgraph

/-- Every holomorphic map between integral smooth projective complex varieties is induced by an
algebraic morphism.
Source: Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6
(1956), §3, Proposition 13; Chow (1949). -/
theorem gagam_algebraize (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y)
    (hF : ContMDiff (modelWithCornersSelf ℂ (Fin (dim X.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (dim Y.left) → ℂ)) ω F) :
    ∃ f : X ⟶ Y, Point.map f = F :=
  gagam_algebraize_aux X Y F hF

example (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (F : ComplexPoint X → ComplexPoint Y)
    (hF : ContMDiff (modelWithCornersSelf ℂ (Fin (dim X.left) → ℂ))
      (modelWithCornersSelf ℂ (Fin (dim Y.left) → ℂ)) ω F) :
    ∃ f : X ⟶ Y, Point.map f = F :=
  gagam_algebraize X Y F hF

/-- The self-map algebraization binder used by the abelian-endomorphism consumers.
Source: Serre, GAGA (1956), §3, Proposition 13; specialization of `gagam_algebraize`. -/
theorem gagam_hAlg (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff (modelWithCornersSelf ℂ (Fin (dim X.left) → ℂ))
        (modelWithCornersSelf ℂ (Fin (dim X.left) → ℂ)) ω F →
        ∃ h : X ⟶ X, Point.map h = F :=
  gagam_hAlg_aux X

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ l ∈ abelianPeriodLattice X, A l ∈ abelianPeriodLattice X) :
    ∃ f : AbelianEnd X, ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)) :=
  spec_exists_abelianEnd_of_lattice X (gagam_hAlg X) A hA

end HodgeLean.Adapters

import HodgeLean.Foundations.Program.SchoenTowerCurveCoordinateAssembly

/-! # Actual etale coordinates near finite affine curve support

Finite-support differential interpolation supplies an etale affine-line map
separating every distinct point in the given support.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- A finite set on the actual smooth affine curve has a separating etale coordinate on an affine neighborhood of the entire support.
Source: Stacks Project, tag 054L; Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10. -/
theorem s2v_l1a_affine_curve_finite_etale_coordinates (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
    (hdim : TopologicalSpace.dim X.left = 1) (s : Finset (ComplexPoint X)) :
    ∃ (U : X.left.affineOpens)
      (f : Over.mk (U.1.ι ≫ X.hom) ⟶
        Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ)),
      (∀ x ∈ s, Set.range x.left ⊆ U.1) ∧ Etale f.left ∧
      ∀ (x y : ComplexPoint (Over.mk (U.1.ι ≫ X.hom))),
        Point.map (Over.homMk U.1.ι) x ∈ s →
        Point.map (Over.homMk U.1.ι) y ∈ s →
        Point.map f x = Point.map f y → x = y := by
  classical
  letI : SmoothOfRelativeDimension 1 X.hom := by
    rw [← hdim]
    infer_instance
  by_cases hs : s.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hs
    letI : Algebra ℂ Γ(X.left, ⊤) := overSpecAlgebra X ⊤
    letI : Algebra.FiniteType ℂ Γ(X.left, ⊤) := s2t_globalSections_finiteType X
    letI : Nonempty ↥s := ⟨⟨p₀, hp₀⟩⟩
    let φ (i : ↥s) := s2t_affinePointAlgHom X i.1
    have hinj : Function.Injective φ :=
      (s2t_affinePointAlgHom_injective X).comp Subtype.val_injective
    letI (i : ↥s) : (RingHom.ker (φ i).toRingHom).IsPrime := RingHom.ker_isPrime _
    have hex (i : ↥s) := s2t_curve_affine_local_differential_generator X i.1
    choose t hne ht using hex
    letI (i : ↥s) : Nontrivial
        (KaehlerDifferential ℂ (Localization.AtPrime (RingHom.ker (φ i).toRingHom))) :=
      nontrivial_of_ne _ _ (hne i)
    let c (i : ↥s) : ℂ := (Fintype.equivFin ↥s i).val
    have hc : Function.Injective c := by
      intro i j hij
      apply (Fintype.equivFin ↥s).injective
      apply Fin.ext
      exact Nat.cast_injective hij
    obtain ⟨g, r, hg, hr, hEt⟩ :=
      s2t_etale_coordinate_of_local_differential_generators φ hinj t ht c
    have hrp (p : ComplexPoint X) (hp : p ∈ s) : Point.evaluate ⊤ r p = 1 := by
      rw [← s2t_affinePointAlgHom_apply]
      exact hr ⟨p, hp⟩
    have hgp (p : ComplexPoint X) (hp : p ∈ s) : Point.evaluate ⊤ g p = c ⟨p, hp⟩ := by
      rw [← s2t_affinePointAlgHom_apply]
      exact hg ⟨p, hp⟩
    obtain ⟨f, hf, hvalue⟩ := s2t_principal_etale_coordinate X g r p₀
      (by rw [hrp p₀ hp₀]; exact one_ne_zero) hEt
    let U := X.left.basicOpen r
    have hU : IsAffineOpen U := (isAffineOpen_top X.left).basicOpen r
    refine ⟨⟨U, hU⟩, f, ?_, hf, ?_⟩
    · intro p hp
      have hmem : p ∈ Point.overOpen U :=
        (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero r p
          (show p ∈ Point.overOpen ⊤ from trivial)).mpr (by rw [hrp p hp]; exact one_ne_zero)
      simpa only [Scheme.Opens.range_ι] using point_range_subset X U p hmem
    · intro x y hx hy heq
      have heval : Point.evaluate ⊤ g (Point.map (openInclusion X U) x) =
          Point.evaluate ⊤ g (Point.map (openInclusion X U) y) :=
        (hvalue x).symm.trans ((congrArg (fun z => affineSpaceEquiv (Fin 1) z 0) heq).trans (hvalue y))
      have hcs : c ⟨Point.map (openInclusion X U) x, hx⟩ =
          c ⟨Point.map (openInclusion X U) y, hy⟩ := by
        rw [← hgp _ hx, ← hgp _ hy]
        exact heval
      exact (cancel_mono (show openScheme X U ⟶ X from openInclusion X U)).mp
        (congrArg Subtype.val (hc hcs))
  · apply s2t_curve_subsingleton_coordinates X hdim s
    intro p hp q _
    exact (hs ⟨p, hp⟩).elim

end HodgeLean.Foundations.Program

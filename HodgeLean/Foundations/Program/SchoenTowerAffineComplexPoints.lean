import HodgeLean.Foundations.Program.SchoenTowerStalkCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint

namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra s2t_complexStalkAlgebra

/-- The canonical map to the spectrum of global sections respects the complex structure map.
Source: Mathlib, `ΓSpecIso_inv_ΓSpec_adjunction_homEquiv`. -/
theorem s2t_toSpecΓ_over (X : Over (Spec ↧ℂ)) :
    X.left.toSpecΓ ≫ affineSpecStructureMap Γ(X.left, ⊤) = X.hom := by
  have hcomp : CommRingCat.ofHom (algebraMap ℂ Γ(X.left, ⊤)) =
      (Scheme.ΓSpecIso ↧ℂ).inv ≫ X.hom.appTop := by
    ext c
    change X.hom.appLE ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso ↧ℂ).inv c) =
      X.hom.appTop ((Scheme.ΓSpecIso ↧ℂ).inv c)
    simp only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl,
      op_id]
    rw [X.left.presheaf.map_id, Category.comp_id]
  apply ext_to_Spec
  exact (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
    (CommRingCat.ofHom (algebraMap ℂ Γ(X.left, ⊤)))).trans hcomp

/-- The complex algebra homomorphism on global sections associated to a complex point.
Source: Mathlib, `ComplexPoint.affineSpecEquiv`; `s2t_toSpecΓ_over`. -/
def s2t_affinePointAlgHom (X : Over (Spec ↧ℂ)) (p : ComplexPoint X) :
    Γ(X.left, ⊤) →ₐ[ℂ] ℂ :=
  affineSpecEquiv Γ(X.left, ⊤)
    (Point.map (Over.homMk X.left.toSpecΓ (s2t_toSpecΓ_over X)) p)

example (X : Over (Spec ↧ℂ)) (p : ComplexPoint X) :
    s2t_affinePointAlgHom X p = affineSpecEquiv Γ(X.left, ⊤)
      (Point.map (Over.homMk X.left.toSpecΓ (s2t_toSpecΓ_over X)) p) := rfl

/-- Global sections distinguish complex points of an affine complex scheme.
Source: Mathlib, `ComplexPoint.affineSpecEquiv`; the affine global section equivalence. -/
theorem s2t_affinePointAlgHom_injective (X : Over (Spec ↧ℂ)) [IsAffine X.left] :
    Function.Injective (s2t_affinePointAlgHom X) := by
  intro p q hpq
  have h := (affineSpecEquiv Γ(X.left, ⊤)).injective hpq
  exact (cancel_mono (show X ⟶ Over.mk (affineSpecStructureMap Γ(X.left, ⊤)) from
    Over.homMk X.left.toSpecΓ (s2t_toSpecΓ_over X))).mp h

/-- The global section homomorphism of a complex point evaluates every section at that point.
Source: Mathlib, `ComplexPoint.affineSpecEquiv_apply` and `Point.evaluate_map`. -/
theorem s2t_affinePointAlgHom_apply (X : Over (Spec ↧ℂ)) (p : ComplexPoint X)
    (a : Γ(X.left, ⊤)) : s2t_affinePointAlgHom X p a = Point.evaluate ⊤ a p := by
  rw [s2t_affinePointAlgHom, affineSpecEquiv_apply, Point.evaluate_map]
  change Point.evaluate ⊤
    (X.left.toSpecΓ.appTop ((Scheme.ΓSpecIso Γ(X.left, ⊤)).inv a)) p = _
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply]

/-- The kernel of evaluation is the affine prime corresponding to the underlying scheme point.
Source: Mathlib, `IsAffineOpen.primeIdealOf_eq_map_closedPoint`; localness of a point stalk map. -/
theorem s2t_affinePointAlgHom_ker (X : Over (Spec ↧ℂ)) [IsAffine X.left]
    (p : ComplexPoint X) :
    RingHom.ker (s2t_affinePointAlgHom X p).toRingHom =
      ((isAffineOpen_top X.left).primeIdealOf ⟨p.underlying, trivial⟩).asIdeal := by
  rw [(isAffineOpen_top X.left).primeIdealOf_eq_map_closedPoint]
  ext a
  change s2t_affinePointAlgHom X p a = 0 ↔
    X.left.presheaf.germ ⊤ p.underlying trivial a ∈
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying)
  rw [s2t_affinePointAlgHom_apply, Point.evaluate, dif_pos (show p.underlying ∈ ⊤ from trivial)]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff p.stalkHom.hom,
    isUnit_iff_ne_zero, not_ne_iff]

/-- The actual stalk at a complex point is the localization of global sections at its
field-valued evaluation kernel.
Source: Mathlib, `IsAffineOpen.isLocalization_stalk`; `s2t_affinePointAlgHom_ker`. -/
theorem s2t_affinePoint_stalk_isLocalization (X : Over (Spec ↧ℂ)) [IsAffine X.left]
    (p : ComplexPoint X) :
    letI : (RingHom.ker (s2t_affinePointAlgHom X p).toRingHom).IsPrime :=
      RingHom.ker_isPrime _
    letI := X.left.presheaf.algebra_section_stalk ⟨p.underlying, show p.underlying ∈ ⊤ from trivial⟩
    IsLocalization.AtPrime (X.left.presheaf.stalk p.underlying)
      (RingHom.ker (s2t_affinePointAlgHom X p).toRingHom) := by
  letI : (RingHom.ker (s2t_affinePointAlgHom X p).toRingHom).IsPrime :=
    RingHom.ker_isPrime _
  letI := X.left.presheaf.algebra_section_stalk ⟨p.underlying, show p.underlying ∈ ⊤ from trivial⟩
  simpa only [s2t_affinePointAlgHom_ker] using
    (isAffineOpen_top X.left).isLocalization_stalk ⟨p.underlying, trivial⟩

end HodgeLean.Foundations.Program

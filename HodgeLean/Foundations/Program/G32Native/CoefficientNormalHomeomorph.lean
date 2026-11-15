import HodgeLean.Foundations.Program.G32Native.CoefficientKernelHomeomorph
import HodgeLean.Foundations.Program.G32Native.CoefficientNormalPairMap

/-! # Continuous coefficient identifications as total-space homeomorphisms -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular Bundle
open HodgeLean.Foundations.BundleThom
open HodgeLean.Foundations.Program.G32Native.EulerModel
namespace HodgeLean.Foundations.Program.G32Native

/-- The supplied forward and inverse fields give a homeomorphism on the original normal total space. -/
def coefficientNormalEvaluationHomeomorph (G : CanonicalAbelGeometry)
    (D : CoefficientNormalIdentification G) :
    @Homeomorph (TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left))
      (TotalSpace (Fin G.k → ℂ)
        (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
      (i1_normalTotalTopology G.ι.left G.k) (coefficientTotalTopology G) := by
  letI := i1_normalTotalTopology G.ι.left G.k
  letI := coefficientTotalTopology G
  exact {
    toFun z := ⟨z.proj, D.fibre z.proj z.2⟩
    invFun z := ⟨z.proj, (D.fibre z.proj).symm z.2⟩
    left_inv z := by
      apply TotalSpace.ext
      · rfl
      · exact heq_of_eq ((D.fibre z.proj).symm_apply_apply z.2)
    right_inv z := by
      apply TotalSpace.ext
      · rfl
      · exact heq_of_eq ((D.fibre z.proj).apply_symm_apply z.2)
    continuous_toFun := D.continuous_forward
    continuous_invFun := D.continuous_inverse }

/-- The specified coefficient total map has its actual continuous inverse. -/
def coefficientNormalTotalHomeomorph (G : CanonicalAbelGeometry)
    (D : CoefficientNormalIdentification G) :
    @Homeomorph (TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left))
      (ProjectiveNormalTotalSpace G.k) (i1_normalTotalTopology G.ι.left G.k) inferInstance := by
  letI := i1_normalTotalTopology G.ι.left G.k
  letI := coefficientTotalTopology G
  exact (coefficientNormalEvaluationHomeomorph G D).trans (coefficientKernelTotalHomeomorph G)

/-- The homeomorphism uses exactly the total map fixed in the transport statement. -/
theorem coefficientNormalTotalHomeomorph_apply (G : CanonicalAbelGeometry)
    (D : CoefficientNormalIdentification G)
    (z : TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left)) :
    coefficientNormalTotalHomeomorph G D z = coefficientNormalTotalMap G D z := rfl

/-- The inverse retains the inverse of the specified map on the base. -/
theorem coefficientNormalTotalHomeomorph_symm_proj (G : CanonicalAbelGeometry)
    (D : CoefficientNormalIdentification G) (v : ProjectiveNormalTotalSpace G.k) :
    letI := i1_normalTotalTopology G.ι.left G.k
    ((coefficientNormalTotalHomeomorph G D).symm v).proj =
      (coefficientBaseHomeomorph G).symm v.val.1 := rfl

/-- The same continuous coefficient map is an isomorphism of zero-complement pairs. -/
def coefficientNormalPairIso (G : CanonicalAbelGeometry)
    (D : CoefficientNormalIdentification G) :
    letI := i1_normalTotalTopology G.ι.left G.k
    TopPair.ofSubset (X := i1_totalSpace G.k (i1_normalFibre G.ι.left))
        (i1_zeroSupport G.k (i1_normalFibre G.ι.left))ᶜ ≅
      TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace G.k)) {w | w.1.2 = 0}ᶜ := by
  letI := i1_normalTotalTopology G.ι.left G.k
  exact TopPair.isoOfSubset (coefficientNormalTotalHomeomorph G D)
    (fun z => not_congr (coefficientNormalTotalMap_zero_iff G D z))

/-- The pair isomorphism retains the map specified by all original coefficient equations. -/
theorem coefficientNormalPairIso_hom (G : CanonicalAbelGeometry)
    (D : CoefficientNormalIdentification G) :
    (coefficientNormalPairIso G D).hom = coefficientNormalPairMap G D := rfl

end HodgeLean.Foundations.Program.G32Native

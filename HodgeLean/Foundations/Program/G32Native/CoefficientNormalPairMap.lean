import HodgeLean.Foundations.Program.G32Native.CoefficientNormalIdentification
import HodgeLean.Foundations.Program.G32Native.CoefficientKernelTransport
import HodgeLean.Foundations.BundleThom.ImmersionDefs
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalSectionHomotopy

/-! # The specified coefficient map on zero-complement pairs -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular Bundle
open HodgeLean.Foundations.BundleThom
open HodgeLean.Foundations.Program.G32Native.EulerModel
namespace HodgeLean.Foundations.Program.G32Native

/-- The total coefficient map for the supplied fibre identification. -/
def coefficientNormalTotalMap (G : CanonicalAbelGeometry)
    (D : CoefficientNormalIdentification G) :
    @ContinuousMap (TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left))
      (ProjectiveNormalTotalSpace G.k) (i1_normalTotalTopology G.ι.left G.k) inferInstance := by
  letI := i1_normalTotalTopology G.ι.left G.k
  letI := coefficientTotalTopology G
  exact ⟨fun z => coefficientKernelTotalMap G ⟨z.proj, D.fibre z.proj z.2⟩,
    (continuous_coefficientKernelTotalMap G).comp D.continuous_forward⟩

/-- The specified total map detects exactly the zero normal vector. -/
theorem coefficientNormalTotalMap_zero_iff (G : CanonicalAbelGeometry)
    (D : CoefficientNormalIdentification G)
    (z : TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left)) :
    (coefficientNormalTotalMap G D z).val.2 = 0 ↔ z.2 = 0 := by
  change (coefficientKernelTotalMap G ⟨z.proj, D.fibre z.proj z.2⟩).val.2 = 0 ↔ _
  rw [coefficientKernelTotalMap_zero_iff, (D.fibre z.proj).map_eq_zero_iff]

/-- The original normal vector maps to its specified ordered coefficient vector. -/
def coefficientNormalPairMap (G : CanonicalAbelGeometry)
    (D : CoefficientNormalIdentification G) :
    letI := i1_normalTotalTopology G.ι.left G.k
    TopPair.ofSubset (X := i1_totalSpace G.k (i1_normalFibre G.ι.left))
        (i1_zeroSupport G.k (i1_normalFibre G.ι.left))ᶜ ⟶
      TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace G.k)) {w | w.1.2 = 0}ᶜ := by
  letI := i1_normalTotalTopology G.ι.left G.k
  exact TopPair.ofSubsetHom (TopCat.ofHom (coefficientNormalTotalMap G D))
    (fun z hz hzero => hz ((coefficientNormalTotalMap_zero_iff G D z).mp hzero))

/-- The base equation holds at every vector in the original normal total space. -/
theorem coefficientNormalPairMap_base (G : CanonicalAbelGeometry)
    (D : CoefficientNormalIdentification G)
    (z : TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left)) :
    (TopPair.Hom.fst (coefficientNormalPairMap G D) z).val.1 =
      (normalProjectiveSchemeHomeomorph G.k).symm (Point.map G.eQ.hom z.proj) := rfl

/-- The vector equation retains the ordered coordinate evaluations. -/
theorem coefficientNormalPairMap_vector (G : CanonicalAbelGeometry)
    (D : CoefficientNormalIdentification G)
    (z : TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left)) :
    (TopPair.Hom.fst (coefficientNormalPairMap G D) z).val.2 =
      ((D.fibre z.proj z.2).val (Pi.single 0 1),
        fun i => (D.fibre z.proj z.2).val (Pi.single i.succ 1)) := rfl

/-- The zero section maps to the zero section over the specified projective point. -/
theorem coefficientNormalPairMap_zeroSection (G : CanonicalAbelGeometry)
    (D : CoefficientNormalIdentification G) (x : ComplexPoint G.Q) :
    TopPair.Hom.fst (coefficientNormalPairMap G D)
      (⟨x, 0⟩ : TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left)) =
      projectiveNormalZeroSection G.k
        ((normalProjectiveSchemeHomeomorph G.k).symm (Point.map G.eQ.hom x)) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (coefficientNormalTotalMap_zero_iff G D ⟨x, 0⟩).mpr rfl

end HodgeLean.Foundations.Program.G32Native

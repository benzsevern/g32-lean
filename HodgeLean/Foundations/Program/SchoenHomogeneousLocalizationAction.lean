import HodgeLean.Foundations.Program.SchoenGradedActionHom
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A degree-preserving ring action extends to homogeneous localization at a stable submonoid. -/
def s2_homogeneousLocalizationAction {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (M : Submonoid A) (hM : ∀ g : G, ∀ a ∈ M, g • a ∈ M) :
    MulSemiringAction G (HomogeneousLocalization 𝒜 M) where
  smul g := HomogeneousLocalization.map (s2_gradedActionHom 𝒜 hgrade g) (fun a ha => hM g a ha)
  one_smul z := by
    change HomogeneousLocalization.map (s2_gradedActionHom 𝒜 hgrade (1 : G)) _ z = z
    simp only [s2_gradedActionHom_one, HomogeneousLocalization.map_id, RingHom.id_apply]
  mul_smul g h z := by
    change HomogeneousLocalization.map (s2_gradedActionHom 𝒜 hgrade (g * h)) _ z =
      HomogeneousLocalization.map (s2_gradedActionHom 𝒜 hgrade g) _
        (HomogeneousLocalization.map (s2_gradedActionHom 𝒜 hgrade h) _ z)
    rw [HomogeneousLocalization.map_map]
    simp only [← s2_gradedActionHom_mul]
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

end HodgeLean.Foundations.Program

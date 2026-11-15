import HodgeLean.Foundations.Singular.TorusBetti

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

/-- Integration over the circle factor, using the specified circle generator.
Source: `HodgeLean.Foundations.Singular.prodCircleCohomologyEquiv`, Hatcher,
*Algebraic Topology*, §3.2 and Theorem 3.15. -/
def cq_circleTrace (X : TopCat.{0}) (n : ℕ) :
    Cohomology ℚ (TopCat.of (X × UnitAddCircle)) (n + 1) →ₗ[ℚ] Cohomology ℚ X n :=
  LinearMap.snd ℚ _ _ ∘ₗ (prodCircleCohomologyEquiv X n).symm.toLinearMap

def cq_circleProductMap {X Y : TopCat.{0}} (f : X ⟶ Y) :
    TopCat.of (X × UnitAddCircle) ⟶ TopCat.of (Y × UnitAddCircle) :=
  TopCat.ofHom ⟨fun p => (f p.1, p.2),
    (f.hom.continuous.comp continuous_fst).prodMk continuous_snd⟩

theorem cq_circleProductEquiv_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a : Cohomology ℚ Y (n + 1)) (b : Cohomology ℚ Y n) :
    cohomologyMap ℚ (n + 1) (cq_circleProductMap f) (prodCircleCohomologyEquiv Y n (a, b)) =
      prodCircleCohomologyEquiv X n (cohomologyMap ℚ (n + 1) f a, cohomologyMap ℚ n f b) := by
  have hf (k : ℕ) (c : Cohomology ℚ Y k) :
      cohomologyMap ℚ k (cq_circleProductMap f)
        (cohomologyMap ℚ k (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) c) =
      cohomologyMap ℚ k (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩)
        (cohomologyMap ℚ k f c) := by
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp,
      ← LinearMap.comp_apply, ← cohomologyMap_comp]
    rfl
  have hs (c : Cohomology ℚ (TopCat.of UnitAddCircle) 1) :
      cohomologyMap ℚ 1 (cq_circleProductMap f)
        (cohomologyMap ℚ 1 (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) c) =
      cohomologyMap ℚ 1 (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) c := by
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    rfl
  rw [prodCircleCohomologyEquiv_apply, map_add, cohomologyMap_cup,
    hf, hf, hs, prodCircleCohomologyEquiv_apply]

theorem cq_circleTrace_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (c : Cohomology ℚ (TopCat.of (Y × UnitAddCircle)) (n + 1)) :
    cq_circleTrace X n (cohomologyMap ℚ (n + 1) (cq_circleProductMap f) c) =
      cohomologyMap ℚ n f (cq_circleTrace Y n c) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (prodCircleCohomologyEquiv Y n).surjective c
  rw [cq_circleProductEquiv_naturality]
  change ((prodCircleCohomologyEquiv X n).symm
    (prodCircleCohomologyEquiv X n (cohomologyMap ℚ (n + 1) f a,
      cohomologyMap ℚ n f b))).2 =
    cohomologyMap ℚ n f ((prodCircleCohomologyEquiv Y n).symm
      (prodCircleCohomologyEquiv Y n (a, b))).2
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

end HodgeLean.Foundations.Program

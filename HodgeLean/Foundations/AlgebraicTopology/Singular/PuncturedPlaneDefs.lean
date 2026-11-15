import HodgeLean.Foundations.AlgebraicTopology.Singular.PuncturedPlaneBase

/-! Local integral generators and forward degree transport.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
open scoped Manifold ContDiff

namespace AlgebraicTopology.Singular.PuncturedPlane

/-- The existing oriented chart generator, with integral coefficients.
Source: Hatcher, Algebraic Topology (2002), §3.3, local orientations. -/
abbrev localClass {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] (x : M) :=
  HodgeLean.Foundations.Program.b6m_surfaceLocalClass ℤ x

/-- Coefficient extraction against the specified integral local generator.
Source: Hatcher, Algebraic Topology (2002), §3.3, local orientations. -/
def localCoefficient {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace ℂ M] (x : M) :
    RelativeHomology ℤ (pointComplementPair x) 2 ≃ ℤ :=
  (Equiv.ofBijective _
    (HodgeLean.Foundations.Program.b6m_surfaceLocalClass_smul_bijective ℤ x)).symm

/-- Local degree uses forward transport on point-complement pairs.
Source: Hatcher, Algebraic Topology (2002), §2.2, local degree; §3.3. -/
def localDegree {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [T1Space N] [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    (e : M ≃ₜ N) (x : M) : ℤ :=
  localCoefficient (e x) (relativeHomologyMap ℤ 2
    (imagePointPairMap (TopCat.ofHom ⟨e, e.continuous⟩) e.injective x) (localClass x))

example {M : Type} [TopologicalSpace M] [T1Space M] [ChartedSpace ℂ M] (x : M) :
    localClass x ≠ 0 := by
  intro h
  have hi := (HodgeLean.Foundations.Program.b6m_surfaceLocalClass_smul_bijective ℤ x).1
  have he : (1 : ℤ) = 0 := hi (by
    rw [show HodgeLean.Foundations.Program.b6m_surfaceLocalClass ℤ x = 0 from h]
    simp only [smul_zero, zsmul_zero])
  exact one_ne_zero he

example {M : Type} [TopologicalSpace M] [T1Space M] [ChartedSpace ℂ M]
    (x : M) (n : ℤ) : localCoefficient x (n • localClass x) = n := by
  rw [← int_smul_eq_zsmul (ModuleCat.isModule _) n]
  exact (Equiv.ofBijective _
    (HodgeLean.Foundations.Program.b6m_surfaceLocalClass_smul_bijective ℤ x)).symm_apply_apply n

private theorem degree_identity {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace ℂ M] (x : M) : localDegree (Homeomorph.refl M) x = 1 := by
  have hm : imagePointPairMap
      (TopCat.ofHom ⟨Homeomorph.refl M, (Homeomorph.refl M).continuous⟩)
      (Homeomorph.refl M).injective x = 𝟙 (pointComplementPair x) := rfl
  unfold localDegree
  rw [hm]
  unfold relativeHomologyMap
  rw [(relativeHomologyFunctor ℤ 2).map_id]
  change (Equiv.ofBijective _
    (HodgeLean.Foundations.Program.b6m_surfaceLocalClass_smul_bijective ℤ x)).symm
      (localClass x) = 1
  refine (congrArg (fun a => localCoefficient x a) (one_smul ℤ (localClass x)).symm).trans ?_
  rw [← int_smul_eq_zsmul (ModuleCat.isModule _) (1 : ℤ)]
  exact (Equiv.ofBijective _
    (HodgeLean.Foundations.Program.b6m_surfaceLocalClass_smul_bijective ℤ x)).symm_apply_apply 1

example : localDegree (Homeomorph.refl ℂ) 0 = 1 := degree_identity 0

example : localDegree (Homeomorph.refl ℂ) 0 = 1 ∨
    localDegree (Homeomorph.refl ℂ) 0 = -1 := Or.inl (degree_identity 0)

example : localDegree (Homeomorph.refl ℂ) 0 = localDegree (Homeomorph.refl ℂ) 1 := by
  rw [degree_identity, degree_identity]

end AlgebraicTopology.Singular.PuncturedPlane

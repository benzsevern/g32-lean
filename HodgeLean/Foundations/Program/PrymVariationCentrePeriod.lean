import HodgeLean.Foundations.Program.PrymVariationCentreRange

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

theorem b63d_period_centre_projector_commute (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (x : b3_periodLattice ℂ C) :
    b4b_centreAct C hG (b4_groupEnd ℂ b4b_projectorCoeff x) =
      b4_groupEnd ℂ b4b_projectorCoeff (b4b_centreAct C hG x) := by
  classical
  simp only [b4b_centreAct, b4_groupEnd, AddMonoidHom.finsetSum_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  split_ifs with hz
  · apply Finset.sum_congr rfl
    intro h hh
    calc
      b4_latticeAct ℂ g ((b4b_projectorCoeff h • b4_latticeAct ℂ h) x) =
          b4b_projectorCoeff h • b4_latticeAct ℂ g (b4_latticeAct ℂ h x) := by
            change b4_latticeAct ℂ g (b4b_projectorCoeff h • b4_latticeAct ℂ h x) = _
            rw [map_zsmul]
      _ = b4b_projectorCoeff h • b4_latticeAct ℂ h (b4_latticeAct ℂ g x) := by
            rw [← AddMonoidHom.comp_apply, ← b4_latticeAct_mul hG,
              ← AddMonoidHom.comp_apply, ← b4_latticeAct_mul hG,
              b63d_scalar_commutes g h hz]
      _ = (b4b_projectorCoeff h • b4_latticeAct ℂ h) (b4_latticeAct ℂ g x) := rfl
  · simp only [map_zero, AddMonoidHom.zero_apply, Finset.sum_const_zero]

theorem b63d_period_centre_range (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) :
    ∃ Z : b63l_periodLattice C →ₗ[ℤ] b63l_periodLattice C,
      ∀ x, (Z x).val = b4b_centreAct C hG x.val := by
  let A := (b4b_centreAct C hG).toIntLinearMap
  let P := (b4_groupEnd ℂ (C := C) b4b_projectorCoeff).toIntLinearMap
  have hcomm (x : b3_periodLattice ℂ C) : A (P x) = P (A x) := by
    exact b63d_period_centre_projector_commute C hG x
  have hA (x : b3_periodLattice ℂ C) (hx : x ∈ b63l_saturation (LinearMap.range P)) :
      A x ∈ b63l_saturation (LinearMap.range P) := by
    rcases hx with ⟨n, hn, y, hy⟩
    refine ⟨n, hn, A y, ?_⟩
    rw [← hcomm, hy]
    exact A.map_smul n x
  let Za : b63l_periodLattice C →+ b63l_periodLattice C := {
    toFun := fun x ↦ ⟨A x.val, hA x.val x.property⟩
    map_zero' := Subtype.ext (map_zero A)
    map_add' := by
      intro x y
      apply Subtype.ext
      exact map_add A x.val y.val }
  let Z := Za.toIntLinearMap
  refine ⟨Z, fun x ↦ ?_⟩
  rfl

set_option maxHeartbeats 400000 in
theorem b63d_period_operator_filtration (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) :
    ∃ (Z J : b63l_periodLattice C →ₗ[ℤ] b63l_periodLattice C),
      (∀ x, (Z x).val = b4b_centreAct C hG x.val) ∧
      J = LinearMap.id + 2 • Z ∧
      (∀ x, (J x).val = b63d_periodOperator C hG x.val) ∧
      b63l_periodF C ≤ (b63l_periodF C).comap (J.baseChange ℂ) := by
  classical
  rcases b63d_period_centre_range C hG with ⟨Z, hZ⟩
  let J : b63l_periodLattice C →ₗ[ℤ] b63l_periodLattice C := LinearMap.id + Z + Z
  refine ⟨Z, J, hZ, ?_, ?_, ?_⟩
  · simp [J, two_smul, add_assoc]
  · intro x
    simp [J, hZ, b63d_periodOperator, two_smul, add_assoc]
  · intro x hx
    change (b63l_periodLattice C).subtype.baseChange ℂ (J.baseChange ℂ x) ∈ b3_periodF ℂ C
    have hcentre : (b4b_centreAct C hG).toIntLinearMap.baseChange ℂ
        ((b63l_periodLattice C).subtype.baseChange ℂ x) ∈ b3_periodF ℂ C := by
      let a : b4b_Group → ℤ := fun g ↦ if b4b_toMatrix g =
        g32h_omega • (1 : Matrix (Fin 4) (Fin 4) ℂ) then 1 else 0
      have hp := b4_groupEnd_periodF (E := ℂ) hG a hx
      simpa [a, b4b_centreAct, b4_groupEnd, b2_cplxMap] using hp
    have hcompat_int : (b63l_periodLattice C).subtype.comp Z =
        (b4b_centreAct C hG).toIntLinearMap.comp (b63l_periodLattice C).subtype := by
      apply LinearMap.ext
      intro y
      exact hZ y
    have hcompat_map : ((b63l_periodLattice C).subtype.baseChange ℂ).comp
        (Z.baseChange ℂ) = ((b4b_centreAct C hG).toIntLinearMap.baseChange ℂ).comp
          ((b63l_periodLattice C).subtype.baseChange ℂ) := by
      simpa only [LinearMap.baseChange_comp] using
        congrArg (LinearMap.baseChange ℂ) hcompat_int
    have hcompat : (b63l_periodLattice C).subtype.baseChange ℂ (Z.baseChange ℂ x) =
        (b4b_centreAct C hG).toIntLinearMap.baseChange ℂ
          ((b63l_periodLattice C).subtype.baseChange ℂ x) := by
      exact LinearMap.congr_fun hcompat_map x
    change (b63l_periodLattice C).subtype.baseChange ℂ (J.baseChange ℂ x) ∈ b3_periodF ℂ C
    dsimp only [J]
    simp only [LinearMap.baseChange_add, LinearMap.baseChange_id, LinearMap.add_apply,
      LinearMap.id_apply]
    rw [map_add, map_add, hcompat]
    exact (b3_periodF ℂ C).add_mem ((b3_periodF ℂ C).add_mem hx hcentre) hcentre

end HodgeLean.Foundations.Program

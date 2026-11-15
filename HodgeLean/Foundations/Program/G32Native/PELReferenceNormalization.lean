import HodgeLean.Foundations.Program.G32Native.PELReferenceBasisInclusion
import HodgeLean.Foundations.Program.G32Native.PELRealComponentDensity

noncomputable section
set_option maxHeartbeats 400000
open scoped Quaternion
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations

/-- The real and complex reference equations use the same scalar extension. -/
theorem pel_reference_complex_isometry_eq (R : PELSplitReference) :
    pelIsometryGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℂ)) =
    pelIsometryGroup ((R.form.map (algebraMap ℚ ℝ)).map Complex.ofReal)
      ((fun T => T.map Complex.ofReal) ''
        (Set.range fun i : Fin 4 =>
          (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℝ))) := by
  have hm (A : Matrix (Fin 12) (Fin 12) ℚ) :
      A.map (algebraMap ℚ ℂ) = (A.map (algebraMap ℚ ℝ)).map Complex.ofReal := by
    ext i j
    simp
  refine congrArg₂ (fun E S => pelIsometryGroup E S) (hm R.form) ?_
  ext T
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, (hm _).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, hm _⟩

/-- Real-component normalization for the retained reference equations,
using the general Cayley-chart density theorem. -/
theorem pel_reference_real_normalization (R : PELSplitReference)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 12) ℂ))
    (hclosed : @IsClosed _ (g1_zariski ℂ 12) (H : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ)))
    (hreal : ∀ g : pelRealIsometries R,
      g ∈ connectedComponent (1 : pelRealIsometries R) →
      ∀ x ∈ H, (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val)⁻¹ * x *
        Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val ∈ H) :
    ∀ g ∈ g1_identityComponent
      (pelIsometryGroup (R.form.map (algebraMap ℚ ℂ))
        (Set.range fun i : Fin 4 =>
          (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℂ))),
      ∀ x ∈ H, g⁻¹ * x * g ∈ H := by
  let E := R.form.map (algebraMap ℚ ℝ)
  let S := Set.range fun i : Fin 4 =>
    (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℝ)
  let K := Subgroup.normalizer (H : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ))
  have hK := pel_zariski_isClosed_normalizer H hclosed
  have hr : ∀ g : pelIsometrySubgroup E S, g ∈ connectedComponent 1 →
      Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val ∈ K := by
    intro g hg
    let q := pel_reference_basis_inclusion R g
    have hq : q ∈ connectedComponent (1 : pelRealIsometries R) := by
      have hh := (pel_reference_basis_inclusion_continuous R).mapsTo_connectedComponent 1 hg
      simpa only [map_one] using hh
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    constructor
    · exact hreal q hq x
    · intro hx
      have hi : q⁻¹ ∈ connectedComponent (1 : pelRealIsometries R) :=
        inv_mem_connectedComponent_one hq
      have hh := hreal q⁻¹ hi _ hx
      simp only [Subgroup.coe_inv, map_inv, inv_inv] at hh
      change (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val) *
        ((Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val)⁻¹ * x *
          Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val) *
        (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val)⁻¹ ∈ H at hh
      simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
        mul_inv_cancel, mul_one] using hh
  have hd := pel_complex_component_subset_of_real_component E S K hK hr
  intro g hg x hx
  rw [pel_reference_complex_isometry_eq R] at hg
  have hk : g ∈ K := hd hg
  exact ((Subgroup.mem_normalizer_iff''.mp hk) x).mp hx

end HodgeLean.Foundations.Program.GeneralTypeIII

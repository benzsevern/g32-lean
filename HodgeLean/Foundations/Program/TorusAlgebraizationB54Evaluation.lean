import HodgeLean.Foundations.Program.TorusAlgebraizationDefs
import HodgeLean.Foundations.SegreProjective

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
open CategoryTheory AlgebraicGeometry

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b54_eval_translate (l : Λ) (z : b5_V Λ F) (n : ℕ)
    (r : b5_S Λ F hF Q) (hr : r ∈ b5_grade Λ F hF Q n) :
    b5_eval Λ F hF Q (z + b5_lattice Λ F l) r =
      (b5_factor Λ F hF Q l z ^ 3) ^ n * b5_eval Λ F hF Q z r := by
  obtain ⟨s, rfl⟩ := hr
  simpa [b5_eval, DirectSum.lof_eq_of, pow_mul] using s.property.2 l z

set_option backward.isDefEq.respectTransparency false in
theorem b54_eval_proj_translate (l : Λ) (z : b5_V Λ F)
    (hz : (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q z) = ⊤)
    (hz' : (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q (z + b5_lattice Λ F l)) = ⊤) :
    Proj.fromOfGlobalSections (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z) hz =
      Proj.fromOfGlobalSections (b5_grade Λ F hF Q)
        (b5_evalGlobal Λ F hF Q (z + b5_lattice Λ F l)) hz' := by
  have hu : IsUnit (b5_factor Λ F hF Q l z ^ 3) :=
    (Ne.isUnit (mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _))).pow 3
  let u : Γ(Spec ↧ℂ, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom hu.unit
  apply HodgeLean.Foundations.spec_g3c_fromOfGlobalSections_unit_twist _ _ _ hz hz' u
  intro n r hr
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
      (b5_eval Λ F hF Q (z + b5_lattice Λ F l) r) = _
  rw [b54_eval_translate Λ F hF Q l z n r hr, map_mul, map_pow]
  simp only [u, Units.coe_map, IsUnit.unit_spec, b5_evalGlobal, RingHom.comp_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem b54_eval_proj_ne (z w : b5_V Λ F)
    (hz : (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q z) = ⊤)
    (hw : (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q w) = ⊤)
    (n : ℕ) (hn : 0 < n) (r : b5_S Λ F hF Q) (hr : r ∈ b5_grade Λ F hF Q n)
    (hrz : b5_eval Λ F hF Q z r ≠ 0) (hrw : b5_eval Λ F hF Q w r = 0) :
    Proj.fromOfGlobalSections (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z) hz ≠
      Proj.fromOfGlobalSections (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q w) hw := by
  intro h
  have he := congrArg (fun f : Spec ↧ℂ ⟶ Proj (b5_grade Λ F hF Q) ↦
    f ⁻¹ᵁ Proj.basicOpen (b5_grade Λ F hF Q) r) h
  rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hn hr,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hn hr] at he
  have hu : IsUnit (b5_evalGlobal Λ F hF Q z r) :=
    (Ne.isUnit hrz).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hzero : b5_evalGlobal Λ F hF Q w r = 0 := by
    simp only [b5_evalGlobal, RingHom.comp_apply, hrw, map_zero]
  rw [Scheme.basicOpen_of_isUnit _ hu, hzero, Scheme.basicOpen_zero] at he
  exact top_ne_bot he

theorem b54_eval_continuous (r : b5_S Λ F hF Q) :
    Continuous (fun z ↦ b5_eval Λ F hF Q z r) := by
  induction r using DirectSum.induction_on with
  | zero => simpa using (continuous_const : Continuous (fun _ : b5_V Λ F ↦ (0 : ℂ)))
  | add r s hr hs =>
    apply (hr.add hs).congr
    intro z
    exact (map_add (b5_eval Λ F hF Q z) r s).symm
  | of n s => simpa [b5_eval] using s.property.1.continuous

theorem b54_eval_scalar (z : b5_V Λ F) (c : ℂ) :
    b5_eval Λ F hF Q z (algebraMap ℂ (b5_S Λ F hF Q) c) = c := by
  letI := b5_sectionsGraded Λ F hF Q 3
  change (DirectSum.coeAlgHom (fun n ↦ b5_sections Λ F hF Q (3 * n))
    (algebraMap ℂ (b5_S Λ F hF Q) c)) z = c
  rw [AlgHom.commutes]
  rfl

theorem b54_homogeneous_eq_zero_of_eval (n : ℕ) (r : b5_S Λ F hF Q)
    (hr : r ∈ b5_grade Λ F hF Q n)
    (h : ∀ z, b5_eval Λ F hF Q z r = 0) : r = 0 := by
  obtain ⟨s, rfl⟩ := hr
  have hs : s = 0 := by
    apply Subtype.ext
    funext z
    simpa [b5_eval, DirectSum.lof_eq_of] using h z
  rw [hs, map_zero]

end HodgeLean.Foundations.Program

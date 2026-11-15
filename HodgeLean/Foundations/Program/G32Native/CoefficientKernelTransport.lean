import HodgeLean.Foundations.Program.G32Native.CoefficientCoordinateEquiv
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalProjectiveScheme

/-! # Ordered covectors in the projective evaluation kernel -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Bundle
open scoped BigOperators
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Program.G32Native.EulerModel
namespace HodgeLean.Foundations.Program.G32Native

/-- Evaluation of a covector is its ordered finite coordinate pairing. -/
theorem coefficient_evaluation_sum (k : ℕ)
    (a : Module.Dual ℂ (Fin (k + 1) → ℂ)) (v : Fin (k + 1) → ℂ) :
    a v = ∑ i, v i * a (Pi.single i 1) := by
  have hv : v = ∑ i : Fin (k + 1), v i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Pi.smul_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- Ordered covectors pair with precisely the model's homogeneous evaluation. -/
theorem coefficient_evaluation_model (k : ℕ)
    (a : Module.Dual ℂ (Fin (k + 1) → ℂ)) (v : ℂ × (Fin k → ℂ)) :
    a (normalHomogeneousCoordinates k v) =
      homogeneousNormalEvaluation k v
        (a (Pi.single 0 1), fun i : Fin k => a (Pi.single i.succ 1)) := by
  rw [coefficient_evaluation_sum, homogeneousNormalEvaluation_apply, Fin.sum_univ_succ]
  rfl

/-- A covector annihilating the ordered homogeneous line belongs to the model kernel. -/
theorem coefficient_mem_projectiveKernel (k : ℕ)
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ)))
    (a : Module.Dual ℂ (Fin (k + 1) → ℂ))
    (ha : a ∈ (s2e_projectiveLinearEquiv (normalHomogeneousCoordinates k) p).submodule.dualAnnihilator) :
    (a (Pi.single 0 1), fun i : Fin k => a (Pi.single i.succ 1)) ∈ projectiveNormalKernel k p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [projectiveNormalKernel_mk, LinearMap.mem_ker]
    rw [← coefficient_evaluation_model]
    apply (Submodule.mem_dualAnnihilator a).mp ha
    change normalHomogeneousCoordinates k v ∈
      (Projectivization.mk ℂ (normalHomogeneousCoordinates k v) _).submodule
    rw [Projectivization.submodule_mk]
    exact Submodule.mem_span_singleton_self _

/-- The line selected over the scheme point is the ordered model line. -/
theorem coefficient_line_model (G : CanonicalAbelGeometry) (x : ComplexPoint G.Q) :
    g32n_homogeneousLine G.k G.eQ x =
      s2e_projectiveLinearEquiv (normalHomogeneousCoordinates G.k)
        ((normalProjectiveSchemeHomeomorph G.k).symm (Point.map G.eQ.hom x)) := by
  apply s2e_projectivizationToComplexPoint_injective
  rw [g32n_homogeneousLine_point]
  exact ((normalProjectiveSchemeHomeomorph G.k).apply_symm_apply (Point.map G.eQ.hom x)).symm

/-- The specified covector determines an actual vector in the original model total space. -/
def coefficientKernelTotalMap (G : CanonicalAbelGeometry)
    (z : TotalSpace (Fin G.k → ℂ)
      (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator)) :
    ProjectiveNormalTotalSpace G.k :=
  ⟨((normalProjectiveSchemeHomeomorph G.k).symm (Point.map G.eQ.hom z.proj),
    z.2.1 (Pi.single 0 1), fun i => z.2.1 (Pi.single i.succ 1)),
    coefficient_mem_projectiveKernel G.k _ z.2.1 (by
      rw [← coefficient_line_model]
      exact z.2.2)⟩

/-- The coefficient total map is continuous for the evaluation topology. -/
theorem continuous_coefficientKernelTotalMap (G : CanonicalAbelGeometry) :
    @Continuous _ _ (coefficientTotalTopology G) inferInstance
      (coefficientKernelTotalMap G) := by
  letI := coefficientTotalTopology G
  have hc := (continuous_coefficientTotal_iff G (fun z => z)).mp continuous_id
  exact (((normalProjectiveSchemeHomeomorph G.k).symm.continuous.comp
    ((Point.continuous_map G.eQ.hom).comp hc.1)).prodMk
      ((hc.2 (Pi.single 0 1)).prodMk
        (continuous_pi (fun i : Fin G.k => hc.2 (Pi.single i.succ 1))))).subtype_mk _

/-- Vanishing of all ordered covector coordinates detects the zero covector. -/
theorem coefficient_coordinates_zero_iff (k : ℕ)
    (a : Module.Dual ℂ (Fin (k + 1) → ℂ)) :
    (a (Pi.single 0 1), fun i : Fin k => a (Pi.single i.succ 1)) = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply (coefficientCoordinateEquiv k).injective
    ext i
    rw [coefficientCoordinateEquiv_apply]
    have hi : a (Pi.single i 1) = 0 := by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact congrArg Prod.fst h
      · exact congrArg (fun v : ℂ × (Fin k → ℂ) => v.2 j) h
    simpa only [map_zero, Pi.zero_apply] using hi
  · rintro rfl
    rfl

/-- The total map retains exactly the original zero support. -/
theorem coefficientKernelTotalMap_zero_iff (G : CanonicalAbelGeometry)
    (z : TotalSpace (Fin G.k → ℂ)
      (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator)) :
    (coefficientKernelTotalMap G z).val.2 = 0 ↔ z.2 = 0 := by
  change (z.2.1 (Pi.single 0 1), fun i : Fin G.k => z.2.1 (Pi.single i.succ 1)) = 0 ↔ z.2 = 0
  rw [coefficient_coordinates_zero_iff]
  constructor
  · intro h
    exact Subtype.ext h
  · rintro h
    rw [h]
    rfl

end HodgeLean.Foundations.Program.G32Native

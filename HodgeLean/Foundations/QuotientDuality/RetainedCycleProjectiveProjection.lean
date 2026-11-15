import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints

/-! Literal linear projections away from their projective kernel. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical
namespace HodgeLean.Foundations.QuotientDuality

/-- The domain of the actual projective linear projection. -/
def retained_projective_projection_domain {n m : ℕ}
    (L : (Fin (n+1) → ℂ) →L[ℂ] (Fin (m+1) → ℂ)) :
    Set (Projectivization ℂ (Fin (n+1) → ℂ)) :=
  {p | L p.rep ≠ 0}

/-- The actual projective projection, defined on the complement of its kernel. -/
def retained_projective_projection {n m : ℕ}
    (L : (Fin (n+1) → ℂ) →L[ℂ] (Fin (m+1) → ℂ)) :
    retained_projective_projection_domain L → Projectivization ℂ (Fin (m+1) → ℂ) :=
  fun p => Projectivization.mk ℂ (L p.val.rep) p.property

/-- The projection domain is exactly nonvanishing on any homogeneous representative. -/
lemma retained_projective_projection_domain_mk {n m : ℕ}
    (L : (Fin (n+1) → ℂ) →L[ℂ] (Fin (m+1) → ℂ))
    (v : Fin (n+1) → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ retained_projective_projection_domain L ↔ L v ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  change (a : ℂ) • v = (Projectivization.mk ℂ v hv).rep at ha
  change L (Projectivization.mk ℂ v hv).rep ≠ 0 ↔ L v ≠ 0
  rw [← ha, map_smul]
  exact smul_ne_zero_iff_right (Units.ne_zero a)

/-- The literal projection carries a homogeneous vector to its projected homogeneous vector. -/
lemma retained_projective_projection_mk {n m : ℕ}
    (L : (Fin (n+1) → ℂ) →L[ℂ] (Fin (m+1) → ℂ))
    (v : Fin (n+1) → ℂ) (hv : v ≠ 0)
    (h : Projectivization.mk ℂ v hv ∈ retained_projective_projection_domain L) :
    retained_projective_projection L ⟨Projectivization.mk ℂ v hv, h⟩ =
      Projectivization.mk ℂ (L v) ((retained_projective_projection_domain_mk L v hv).mp h) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  change (a : ℂ) • v = (Projectivization.mk ℂ v hv).rep at ha
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(a : ℂ), ?_⟩
  rw [← map_smul, ha]

/-- The domain of the literal projective projection is open in the original quotient topology. -/
lemma retained_projective_projection_domain_open {n m : ℕ}
    (L : (Fin (n+1) → ℂ) →L[ℂ] (Fin (m+1) → ℂ)) :
    IsOpen (retained_projective_projection_domain L) := by
  let q := Projectivization.mk' ℂ (V := Fin (n+1) → ℂ)
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  apply hq.isOpen_preimage.mp
  have he : q ⁻¹' retained_projective_projection_domain L =
      {v : {v : Fin (n+1) → ℂ // v ≠ 0} | L v.val ≠ 0} := by
    ext v
    exact retained_projective_projection_domain_mk L v.val v.property
  rw [he]
  exact isOpen_ne.preimage (L.continuous.comp continuous_subtype_val)

/-- The literal projective projection is continuous on its nonkernel domain. -/
lemma retained_projective_projection_continuous {n m : ℕ}
    (L : (Fin (n+1) → ℂ) →L[ℂ] (Fin (m+1) → ℂ)) :
    Continuous (retained_projective_projection L) := by
  let q := Projectivization.mk' ℂ (V := Fin (n+1) → ℂ)
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  apply (hq.restrictPreimage_isOpen (retained_projective_projection_domain_open L)).continuous_iff.mpr
  let E := {v : {v : Fin (n+1) → ℂ // v ≠ 0} |
    q v ∈ retained_projective_projection_domain L}
  change Continuous (fun v : E => retained_projective_projection L ⟨q v.val, v.property⟩)
  let f : E → {w : Fin (m+1) → ℂ // w ≠ 0} := fun v =>
    ⟨L v.val.val, (retained_projective_projection_domain_mk L v.val.val v.val.property).mp v.property⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact L.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hm : Continuous (Projectivization.mk' ℂ (V := Fin (m+1) → ℂ)) :=
    continuous_quotient_mk'
  exact (hm.comp hf).congr (fun v =>
    (retained_projective_projection_mk L v.val.val v.val.property v.property).symm)

end HodgeLean.Foundations.QuotientDuality

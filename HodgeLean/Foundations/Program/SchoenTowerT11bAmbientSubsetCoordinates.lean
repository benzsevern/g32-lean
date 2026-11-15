import HodgeLean.Foundations.Program.SchoenTowerT11bOrderedAmbientCoordinates
import HodgeLean.Foundations.Program.SchoenTowerT11bCoordinates

/-! Subset and inverse coordinates for ambient straightening maps.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The inverse of a base-preserving ambient coordinate map preserves the same base.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, coordinate transport step. -/
theorem s2v_t11b_ambient_inverse_base {X : Type*} [TopologicalSpace X]
    (E : (X × ℝ) ≃ₜ (X × ℝ)) (hbase : ∀ z, (E z).1 = z.1) (z : X × ℝ) :
    (E.symm z).1 = z.1 := by
  have h := hbase (E.symm z)
  rw [E.apply_symm_apply] at h
  exact h.symm

/-- An inverse ambient height section returns to that same height and base under the forward map.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, coordinate transport step. -/
theorem s2v_t11b_ambient_inverse_section {X : Type*} [TopologicalSpace X]
    (E : (X × ℝ) ≃ₜ (X × ℝ)) (hbase : ∀ z, (E z).1 = z.1) (b : X) (r : ℝ) :
    E (b, (E.symm (b, r)).2) = (b, r) := by
  have hpoint : (b, (E.symm (b, r)).2) = E.symm (b, r) :=
    Prod.ext (s2v_t11b_ambient_inverse_base E hbase (b, r)).symm rfl
  rw [hpoint, E.apply_symm_apply]

/-- Ambient coordinates carrying a subset to a cylinder induce product coordinates on that subset.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, subset coordinate transport step. -/
def s2v_t11b_ambientSubsetProduct {X : Type*} [TopologicalSpace X]
    (E : (X × ℝ) ≃ₜ (X × ℝ)) (S : Set (X × ℝ)) (D : Set ℝ)
    (hS : ∀ z, z ∈ S ↔ (E z).2 ∈ D) : S ≃ₜ (D × X) where
  toFun z := (⟨(E z.val).2, (hS z.val).mp z.property⟩, (E z.val).1)
  invFun y := ⟨E.symm (y.2, y.1.val), by
    apply (hS _).mpr
    rw [E.apply_symm_apply]
    exact y.1.property⟩
  left_inv z := by
    apply Subtype.ext
    exact E.symm_apply_apply z.val
  right_inv y := by
    apply Prod.ext
    · apply Subtype.ext
      change (E (E.symm (y.2, y.1.val))).2 = y.1.val
      rw [E.apply_symm_apply]
    · change (E (E.symm (y.2, y.1.val))).1 = y.2
      rw [E.apply_symm_apply]
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_snd.comp (E.continuous.comp continuous_subtype_val)
    · exact continuous_fst.comp (E.continuous.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact E.symm.continuous.comp (continuous_snd.prodMk
      (continuous_subtype_val.comp continuous_fst))

/-- Base-independent membership at each normalized height constructs product coordinates on a subset.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, subset coordinate transport step. -/
theorem s2v_t11b_normalized_membership_product {X : Type*} [TopologicalSpace X]
    (E : (X × ℝ) ≃ₜ (X × ℝ)) (hbase : ∀ z, (E z).1 = z.1)
    (S : Set (X × ℝ)) (a : X)
    (hconstant : ∀ b r, E.symm (b, r) ∈ S ↔ E.symm (a, r) ∈ S) :
    ∃ D : Set ℝ, ∃ e : S ≃ₜ (D × X), ∀ y, (e y).2 = y.val.1 := by
  let D : Set ℝ := {r | E.symm (a, r) ∈ S}
  have hS : ∀ z, z ∈ S ↔ (E z).2 ∈ D := by
    intro z
    have hpoint : E.symm (z.1, (E z).2) = z := by
      have hz : (z.1, (E z).2) = E z := Prod.ext (hbase z).symm rfl
      rw [hz, E.symm_apply_apply]
    have h := hconstant z.1 (E z).2
    rw [hpoint] at h
    exact h
  refine ⟨D, s2v_t11b_ambientSubsetProduct E S D hS, ?_⟩
  intro y
  exact hbase y.val

/-- A specified fiber of a product subset is its actual vertical slice.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, actual-fiber coordinate step. -/
def s2v_t11b_productSubsetFiberChart {X : Type*} [TopologicalSpace X]
    (S : Set (X × ℝ)) (a : X) :
    {z : S | z.val.1 = a} ≃ₜ {r : ℝ | (a, r) ∈ S} where
  toFun z := ⟨z.val.val.2, by
    have hpoint : z.val.val = (a, z.val.val.2) := Prod.ext z.property rfl
    have hz := z.val.property
    rw [hpoint] at hz
    exact hz⟩
  invFun r := ⟨⟨(a, r.val), r.property⟩, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext z.property.symm rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_const.prodMk continuous_subtype_val

end HodgeLean.Foundations.Program

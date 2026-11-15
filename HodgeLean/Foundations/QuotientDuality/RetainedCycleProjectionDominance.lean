import HodgeLean.Foundations.QuotientDuality.RetainedCyclePresentationProjection
import HodgeLean.Adapters.IntersectionProductScaf

/-! # Dominance of the actual finite linear projection -/

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

local instance projectionTargetIntegral (n : ℕ) : IsIntegral (a3m_Pn n) :=
  IntersectionProductScaf_projective_integral n

/-- Finite Noether parameters send the actual source generic point to the target generic point. -/
lemma retained_presentation_projection_generic
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) {n : ℕ}
    {ℓ : Matrix (Fin (n+1)) (Fin (D.ambientDimension+1)) ℂ}
    (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp
      (a3r_lin ℓ).toRingHom).Finite)
    (hdim : ringKrullDim (MvPolynomial (Fin (D.ambientDimension+1)) ℂ ⧸
      retained_presentation_cone_ideal X D) = (n+1 : ℕ)) :
    retained_presentation_π X D hfin (genericPoint X.left) = genericPoint (a3m_Pn n) := by
  have hs : retained_presentation_π X D hfin (genericPoint X.left) ⤳
      genericPoint (a3m_Pn n) := by
    apply (a3m_projCharts n).specializes_of_prime_le
    rw [retained_presentation_prime_π,
      retained_presentation_comap_IX X D hfin hdim]
    exact bot_le
  exact (hs.antisymm (genericPoint_specializes _)).eq

/-- The actual finite projective projection has positive residue degree at its source generic point. -/
lemma retained_presentation_projection_degree_pos
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) {n : ℕ}
    {ℓ : Matrix (Fin (n+1)) (Fin (D.ambientDimension+1)) ℂ}
    (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp
      (a3r_lin ℓ).toRingHom).Finite) :
    0 < a1p_degree (retained_presentation_π X D hfin) (genericPoint X.left) := by
  let f : X ⟶ a3h_PnO n := Over.homMk (retained_presentation_π X D hfin)
    (retained_presentation_π_fst X D hfin)
  apply (a1p_degree_pos_iff f (genericPoint X.left)).2
  let C := a3m_projCharts n
  let _ : ∀ j, Algebra ℂ (C.T j) := fun j => ((C.θ j).comp MvPolynomial.C).toAlgebra
  have hy := a3m_SpecCharts.height_add_one (Y := a3h_PnO n) C
    (fun _ _ => rfl) (f.left (genericPoint X.left))
  have hx := retained_presentation_height_add_one X D (genericPoint X.left)
  have hd := a3r_dim_eq_of_finite (retained_presentation_cone_ideal X D) ℓ hfin
    (retained_presentation_cone_ideal X D) le_rfl
  have he : (Order.height (f.left (genericPoint X.left)) : WithBot ℕ∞) + 1 =
      (Order.height (genericPoint X.left) : WithBot ℕ∞) + 1 := by
    rw [hy]
    change ringKrullDim (MvPolynomial (Fin (n+1)) ℂ ⧸
      (a3m_projCharts n).prime (retained_presentation_π X D hfin (genericPoint X.left))) = _
    rw [retained_presentation_prime_π]
    exact hd.symm.trans hx.symm
  apply ENat.add_left_injective_of_ne_top (by simp : (1 : ℕ∞) ≠ ⊤)
  exact_mod_cast he

end HodgeLean.Foundations.QuotientDuality

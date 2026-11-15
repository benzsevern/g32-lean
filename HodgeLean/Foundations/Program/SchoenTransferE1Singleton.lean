import HodgeLean.Foundations.Program.SchoenTransferE1OneFactor
import HodgeLean.Foundations.Program.SchoenTransferE1DirectSum

/-! The ordered comparison for one factor in every degree. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct DirectSum BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A one-coordinate multidegree has the specified total degree at its coordinate.
Source: the sum over a singleton finite ordinal. -/
theorem s4_e1_singleton_degree (n : ℕ)
    (d : {d : Fin 1 → ℕ // ∑ i, d i = n}) : d.val 0 = n := by
  simpa only [Fin.sum_univ_one] using d.property

/-- The tensor for a one-coordinate multidegree is its single cohomology factor.
Source: Hatcher, Algebraic Topology, §3.2, the tensor unit. -/
def s4_e1_singletonTensorEquiv
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (n : ℕ) (d : {d : Fin 1 → ℕ // ∑ i, d i = n}) :
    s4_e1_tensor Y 1 d.val ≃ₗ[ℚ] HQ Y n :=
  (TensorProduct.rid ℚ (HQ Y (d.val 0))).trans
    (HQ.castEquiv Y (s4_e1_singleton_degree n d))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- After transport of its total degree, a one-factor ordered cup is scalar
multiplication of the coordinate pullback.
Source: Hatcher, Algebraic Topology, §3.2, the cup unit. -/
theorem s4_e1_singleton_orderedCup_tmul
    (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (d : Fin 1 → ℕ) (f : Fin 1 → (T ⟶ Y)) (x : HQ Y (d 0)) (q : ℚ) :
    HQ.castEquiv T (Fin.sum_univ_one d)
      (s4_e1_orderedCup Y T 1 d f (x ⊗ₜ[ℚ] q)) =
        q • homPullback (f 0) (d 0) x := by
  simp only [s4_e1_orderedCup, s4_e1_tensor, ModuleCat.of, id_eq,
    TensorProduct.lift.tmul,
    LinearMap.compl₁₂_apply, LinearMap.toSpanSingleton_apply]
  rw [CupProduct.castEquiv_cup]
  simp only [Fin.sum_univ_zero]
  erw [LinearMap.toSpanSingleton_apply]
  rw [map_smul]
  rw [(cupProductOf T).cup_one]

/-- The one-factor direct-sum inclusion evaluates by its ordered cup and degree transport.
Source: Hatcher, Algebraic Topology, §3.2, the external cup product. -/
theorem s4_e1_singleton_kunneth_lof
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral (g3_power Y 1).left] [Smooth (g3_power Y 1).hom]
    [IsProjective (g3_power Y 1).hom]
    (n : ℕ) (d : {d : Fin 1 → ℕ // ∑ i, d i = n})
    (v : s4_e1_tensor Y 1 d.val) :
    s4_e1_kunneth Y 1 n (DirectSum.lof ℚ _ _ d v) =
      HQ.castEquiv (g3_power Y 1) d.property
        (s4_e1_orderedCup Y (g3_power Y 1) 1 d.val (g3_proj Y 1) v) := by
  rcases d with ⟨d, hd⟩
  subst n
  simp only [s4_e1_kunneth, DirectSum.toModule_lof, HQ.castEquiv_apply_self]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified Künneth comparison for one factor is bijective in every degree.
Source: Hatcher, Algebraic Topology, §3.2, the tensor and cup units. -/
theorem s4_e1_kunneth_singleton
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral (g3_power Y 1).left] [Smooth (g3_power Y 1).hom]
    [IsProjective (g3_power Y 1).hom] (n : ℕ) :
    Function.Bijective (s4_e1_kunneth Y 1 n) := by
  classical
  let I := {d : Fin 1 → ℕ // ∑ i, d i = n}
  let i0 : I := ⟨fun _ => n, Fin.sum_univ_one _⟩
  letI : Unique I :=
    { default := i0
      uniq := fun d => by
        apply Subtype.ext
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        exact s4_e1_singleton_degree n d }
  let E := s4_e1_directSumUniqueEquiv ℚ (fun d : I => s4_e1_tensor Y 1 d.val)
  let g := (s4_e1_kunneth Y 1 n).comp (DirectSum.lof ℚ I _ i0)
  have hg : g = (homPullback (g3_proj Y 1 0) n).comp
      (TensorProduct.rid ℚ (HQ Y n)).toLinearMap := by
    apply TensorProduct.ext'
    intro x q
    change HQ Y n at x
    change ℚ at q
    change s4_e1_kunneth Y 1 n
      (DirectSum.lof ℚ I _ i0 (x ⊗ₜ[ℚ] q)) =
        homPullback (g3_proj Y 1 0) n
          ((TensorProduct.rid ℚ (HQ Y n)) (x ⊗ₜ[ℚ] q))
    erw [s4_e1_singleton_kunneth_lof]
    rw [TensorProduct.rid_tmul]
    dsimp only [i0]
    exact (s4_e1_singleton_orderedCup_tmul Y (g3_power Y 1)
      (fun _ => n) (g3_proj Y 1) x q).trans
        (map_smul (homPullback (g3_proj Y 1 0) n) q x).symm
  have hgbi : Function.Bijective g := by
    rw [hg]
    let e : g3_power Y 1 ≅ Y := ρ_ Y
    have hp : g3_proj Y 1 0 = e.hom :=
      (CartesianMonoidalCategory.rightUnitor_hom Y).symm
    rw [hp]
    exact (s4_e1_pullback_iso_bijective e n).comp (TensorProduct.rid ℚ (HQ Y n)).bijective
  have hk : s4_e1_kunneth Y 1 n = g.comp E.toLinearMap := by
    apply LinearMap.ext
    intro x
    change s4_e1_kunneth Y 1 n x =
      s4_e1_kunneth Y 1 n (DirectSum.lof ℚ I _ i0 (E x))
    have hx := E.symm_apply_apply x
    change DirectSum.lof ℚ I _ i0 (E x) = x at hx
    rw [hx]
  rw [hk]
  exact hgbi.comp E.bijective

#print axioms s4_e1_kunneth_singleton
#print axioms s4_e1_singleton_kunneth_lof
#print axioms s4_e1_singleton_orderedCup_tmul
#print axioms s4_e1_singleton_degree
#print axioms s4_e1_singletonTensorEquiv
end HodgeLean.Foundations.Program

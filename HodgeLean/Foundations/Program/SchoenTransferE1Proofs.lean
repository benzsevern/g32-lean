import HodgeLean.Foundations.Program.SchoenTransferE1PowerIteration
import HodgeLean.Foundations.Program.SchoenTransferE1Defs
import HodgeLean.Foundations.Program.SchoenTransferE1TopAction
import HodgeLean.Foundations.Program.SchoenTransferE1Characters
import HodgeLean.Foundations.Program.SchoenTransferE1KunnethBase
import HodgeLean.Foundations.Program.SchoenTransferE1KunnethVanishing
import HodgeLean.Foundations.Program.SchoenTransferE1OneFactor
import HodgeLean.Foundations.Program.SchoenTransferE1Singleton
import HodgeLean.Foundations.Program.SchoenTransferE1TensorAction
import HodgeLean.Foundations.Program.SchoenTransferE1PrimitiveComponents
import HodgeLean.Foundations.Program.SchoenTransferE1KunnethZero

/-! Implication from the explicit curve, coordinate action and primitive-kernel data
to the ordered Künneth and equal-character interfaces.
Determinant transport, rational comparison and algebraic cycles belong to later units.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct DirectSum BigOperators CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program
/-- The recursively constructed power map has its specified projections.
Source: the universal property of binary products. -/
theorem s4_e1_lift_proj {Y T : Over (Spec ↧ℂ)} (h : ℕ)
    (f : Fin h → (T ⟶ Y)) (i : Fin h) :
    s2_lift h f ≫ g3_proj Y h i = f i := by
  induction h with
  | zero => exact Fin.elim0 i
  | succ h ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact CartesianMonoidalCategory.lift_fst _ _
      · change CartesianMonoidalCategory.lift _ _ ≫
          (CartesianMonoidalCategory.snd _ _ ≫ g3_proj Y h j) = _
        rw [← Category.assoc, CartesianMonoidalCategory.lift_snd]
        exact ih _ j

/-- Pullback preserves the actual multilinear degree-one cup.
Source: Hatcher, Algebraic Topology, §3.2, naturality of cup products. -/
theorem s4_e1_cupMulti_pullback
    {T U : Over (Spec ↧ℂ)}
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    [IsIntegral U.left] [Smooth U.hom] [IsProjective U.hom]
    (u : U ⟶ T) (h : ℕ) (v : Fin h → HQ T 1) :
    homPullback u h ((cupProductOf T).cupMulti h v) =
      (cupProductOf U).cupMulti h (fun i => homPullback u 1 (v i)) := by
  have he := LinearMap.congr_fun (spec_homPullback_cupWedgeMap u h)
    (exteriorPower.ιMulti ℚ h v)
  simpa only [LinearMap.comp_apply, CupProduct.cupWedgeMap_ιMulti,
    exteriorPower.map_apply_ιMulti, Function.comp_def] using he

/-- Primitive characters are absent in degrees zero and two.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_curve_extremes_aux (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (δ : Y ⟶ Y) [IsIso δ] (m : ℕ) (hm : 3 ≤ m) :
    LinearMap.ker (Polynomial.aeval (homPullback δ 0) (Polynomial.cyclotomic m ℚ)) = ⊥ ∧
      LinearMap.ker (Polynomial.aeval (homPullback δ 2) (Polynomial.cyclotomic m ℚ)) = ⊥ := by
  constructor
  · rw [s4_e1_degree_zero_action]
    exact s4_e1_identity_primitive_kernel (HQ Y 0) m hm
  · letI : SmoothOfRelativeDimension 1 Y.hom := by
      rw [← hdim]
      infer_instance
    have ht : homPullback δ 2 = LinearMap.id :=
      s4_e1_top_rational_action Y 1 (asIso δ)
    rw [ht]
    exact s4_e1_identity_primitive_kernel (HQ Y 2) m hm

/-- The ordered projection cup maps give the full curve-power decomposition.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_power_kunneth_aux (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (n : ℕ) :
    Function.Bijective (s4_e1_kunneth Y h n) := by
  exact s4_e1_power_kunneth_iteration Y h n

/-- Deck equivariance uses the specified coordinate squares and actual cup maps.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_coordinate_naturality_aux (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (u : g3_power Y h ⟶ g3_power Y h)
    (b : Fin h → (Y ⟶ Y))
    (hu : ∀ i, u ≫ g3_proj Y h i = g3_proj Y h i ≫ b i)
    (d : Fin h → ℕ) :
    (homPullback u (∑ i, d i)).comp
      (s4_e1_orderedCup Y (g3_power Y h) h d (g3_proj Y h)) =
      s4_e1_orderedCup Y (g3_power Y h) h d
        (fun i => g3_proj Y h i ≫ b i) := by
  simpa only [hu] using
    s4_e1_orderedCup_pullback Y (g3_power Y h) (g3_power Y h) u h d (g3_proj Y h)

/-- The primitive invariant subspace lies in the actual all-degree-one image.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_primitive_degree_one_aux (S : g32p_Supplier) (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (hh : 0 < h)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v) :
    s4_invariantPrimitive S Y a e h hh ≤ LinearMap.range (s4_e1_oneCup Y h) := by
  exact s4_e1_primitive_degree_one_of_kunneth S Y h hh a e
    (s4_e1_power_kunneth_aux Y hdim h h)

/-- Annihilating all sum-zero tuples forces equality of the characters.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_equal_characters_aux (m h : ℕ) (hm : 3 ≤ m) (hh : 0 < h)
    (c : Fin h → ZMod m) :
    (∀ v : Fin h → ZMod m, (∑ i, v i) = 0 → (∑ i, c i * v i) = 0) ↔
      ∃ a : ZMod m, ∀ i, c i = a := by
  letI : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  exact s4_e1_sum_zero_character_algebra c

set_option maxRecDepth 4000 in
/-- Geometric permutations act with the odd-degree Koszul sign.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_permutation_cup_aux (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (σ : Equiv.Perm (Fin h)) (v : Fin h → HQ Y 1) :
    homPullback (s2_permute Y h σ) h
      (s4_e1_oneCup Y h (PiTensorProduct.tprod ℚ v)) =
      (((σ.sign : ℤˣ) : ℤ) : ℚ) •
        s4_e1_oneCup Y h (PiTensorProduct.tprod ℚ (fun i => v (σ i))) := by
  classical
  simp only [s4_e1_oneCup, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply]
  rw [s4_e1_cupMulti_pullback]
  have hp (i : Fin h) :
      homPullback (s2_permute Y h σ) 1 (homPullback (g3_proj Y h i) 1 (v i)) =
        homPullback (g3_proj Y h (σ.symm i)) 1 (v i) := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp,
      s2_permute, s4_e1_lift_proj]
  simp only [hp]
  let w : Fin h → HQ (g3_power Y h) 1 :=
    fun i => homPullback (g3_proj Y h i) 1 (v (σ i))
  have hw : (fun i => homPullback (g3_proj Y h (σ.symm i)) 1 (v i)) =
      w ∘ σ.symm := by
    funext i
    simp only [w, Function.comp_apply, Equiv.apply_symm_apply]
  rw [hw]
  have hs := ((cupProductOf (g3_power Y h)).cupAlternating h).map_perm w σ.symm
  change (cupProductOf (g3_power Y h)).cupMulti h (w ∘ σ.symm) =
    (Equiv.Perm.sign σ.symm) • (cupProductOf (g3_power Y h)).cupMulti h w at hs
  simpa only [Equiv.Perm.sign_symm,
    Units.smul_def, Int.cast_smul_eq_zsmul] using hs

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.PathCoverFamilyDefs
import HodgeLean.Foundations.Program.G32PropFourSixDefs

/-! # Jacobian objects for retained G32 fibres

The B5 algebraization of the period Jacobian and its rational operators.
All data use existing B3 and B5 constructions. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected

/-- The period lattice of the retained cover fibre.
Source: Birkenhake–Lange, Ch. 11; `b3_periodLattice`. -/
abbrev g32x_L {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) := b3_periodLattice ℂ (b65z_fibre c D.C t)

instance g32x_finite {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : Module.Finite ℤ (g32x_L D t) :=
  b3_periodLattice_finite (by simp)

instance g32x_free {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : Module.Free ℤ (g32x_L D t) :=
  b3_periodLattice_free

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : Module.Finite ℤ (g32x_L D t) := inferInstance

/-- The algebraized period Jacobian, using the retained intersection form.
Source: Birkenhake–Lange, Ch. 11 and §2.2; `b5_model`. -/
def g32x_J {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : Over (Spec ↧ℂ) :=
  b5_model (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t)) (b3_isWeightOne (by simp)) (D.Q t)

instance g32x_grp {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : GrpObj (g32x_J D t) :=
  b5_groupObj (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t)) (b3_isWeightOne (by simp)) (D.Q t) (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t))
instance g32x_comm {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : IsCommMonObj (g32x_J D t) :=
  b5_commutative_aux (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t)) (b3_isWeightOne (by simp)) (D.Q t) (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t))
instance g32x_integral {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : IsIntegral (g32x_J D t).left :=
  b5_integral (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t)) (b3_isWeightOne (by simp)) (D.Q t) (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t))
instance g32x_smooth {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : Smooth (g32x_J D t).hom :=
  b5_smooth (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t)) (b3_isWeightOne (by simp)) (D.Q t) (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t))
instance g32x_projective {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : IsProjective (g32x_J D t).hom :=
  b5_projective (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t)) (b3_isWeightOne (by simp)) (D.Q t) (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t))

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : IsProjective (g32x_J D t).hom := inferInstance

/-- Transport the transpose of a period-lattice endomorphism to rational cohomology.
Source: Birkenhake–Lange, §1.2; `b63g_modelOperator`. -/
def g32x_operator {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (φ : g32x_L D t →+ g32x_L D t) :
    Module.End ℚ (HQ (g32x_J D t) 1) :=
  b63g_modelOperator (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t)) (b3_isWeightOne (by simp)) (D.Q t) (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t)) φ

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (φ : g32x_L D t →+ g32x_L D t) :
    g32x_operator D t φ 0 = 0 := map_zero _

/-- The original theta class, without a Veronese rescaling.
Source: Birkenhake–Lange, §11.2; `b63g_modelClass`. -/
def g32x_theta {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : HQ (g32x_J D t) 2 :=
  b63g_modelClass (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t)) (b3_isWeightOne (by simp)) (D.Q t) (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t))

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : g32x_theta D t =
    b63g_modelClass (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t)) (b3_isWeightOne (by simp)) (D.Q t) (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t)) := rfl

/-- Rational cohomological action of the inverse deck transformation.
The inverse fixes the composition convention in `g32p_Cover.aut_mul`.
Source: Birkenhake–Lange, §11.4; `b4_latticeAct`. -/
def g32x_deck {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a : g32p_G) : Module.End ℚ (HQ (g32x_J D t) 1) :=
  g32x_operator D t (b4_latticeAct ℂ (C := b65z_fibre c D.C t) a⁻¹)

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a : g32p_G) : g32x_deck D t a 0 = 0 := map_zero _

/-- Transpose of the integral primitive projector on the period lattice.
Source: G32 v0.16, Definition 3.2; `b4b_projectorCoeff`, `b4_groupEnd`. -/
def g32x_projector {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : Module.End ℚ (HQ (g32x_J D t) 1) :=
  g32x_operator D t (b4_groupEnd ℂ (C := b65z_fibre c D.C t) b4b_projectorCoeff)

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : g32x_projector D t 0 = 0 := map_zero _

/-- Independent check: the total CW formula must exclude the trivial representation.
Source: G32 v0.16, Proposition 3.1 (the nontriviality restriction). -/
example : g32p_cwMult (FDRep.of (Representation.trivial ℂ g32p_G ℂ)) = -2 := by
  change -2 * (Module.finrank ℂ ℂ : ℤ) +
    ∑ _j : Fin 13, (Module.finrank ℂ
      (LinearMap.range ((LinearMap.id : ℂ →ₗ[ℂ] ℂ) - 1)) : ℤ) = -2
  have hz : (LinearMap.id : ℂ →ₗ[ℂ] ℂ) - 1 = 0 := by
    apply LinearMap.ext
    intro z
    change z - z = 0
    exact sub_self z
  rw [hz]
  simp


/-- Independent check: the local-family indexing reaches every fibre of P.
Source: `b65z_IsLocalPrym`; Mathlib `Equiv.apply_symm_apply`. -/
example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g)
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c)))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P) (s : P.S) :
    ∃ t : b6t_polydisc c, P.fiber s = b65z_fiber D B t := by
  obtain ⟨j, hj⟩ := hP
  exact ⟨j.symm s, by simpa only [j.apply_symm_apply] using (hj (j.symm s)).2⟩

end HodgeLean.Foundations.Program

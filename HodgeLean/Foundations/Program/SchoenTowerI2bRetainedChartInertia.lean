import HodgeLean.Foundations.Program.SchoenTowerI2bNormalizedEvaluation
import HodgeLean.Foundations.Program.SchoenTowerI2bRetainedInertia
import HodgeLean.Foundations.Program.SchoenTowerI2bChartPointProjection

/-! Inertia at an actual retained normalization-chart point.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A retained vanishing branch fixes the actual covering point through the specified normalization chart action.
Source: G32 v0.16, Lemma 4.3, retained monomial inertia and the actual normalization projection square. -/
theorem s2v_i2b_retained_chart_cover_point_inertia
    {ι : Type} [Fintype ι] [DecidableEq ι] (n m : ℕ) (hm : 0 < m)
    (U : Over (Spec ↧ℂ)) [IsAffine U.left] [IsDomain Γ(U.left, ⊤)]
    [Algebra ℂ Γ(U.left, ⊤)]
    (hscalar : algebraMap ℂ Γ(U.left, ⊤) =
      ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom)
    (K : Type) [Field K] [Algebra Γ(U.left, ⊤) K] [Algebra ℂ K]
    [IsScalarTower ℂ Γ(U.left, ⊤) K]
    (c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(U.left, ⊤)) (hc : c.toRingHom.Etale)
    (hinj : Function.Injective (algebraMap Γ(U.left, ⊤) K))
    (J : Finset ι) (κ : J ↪ Fin n) (z : ι → Γ(U.left, ⊤)) (α : ι → ℕ)
    (hz : ∀ s : J, z s = c (MvPolynomial.X (κ s)))
    (habsent : ∀ s, s ∉ J → z s = 1)
    (ε : Γ(U.left, ⊤)) (hε : IsUnit ε) (v : K)
    (hv : v ^ m = algebraMap Γ(U.left, ⊤) K ε *
      ∏ s, (algebraMap Γ(U.left, ⊤) K (z s)) ^ α s)
    (hgen : Subfield.closure (Set.range (algebraMap Γ(U.left, ⊤) K) ∪ {v}) = ⊤)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (δ : K ≃ₐ[Γ(U.left, ⊤)] K) (hδ : δ v = algebraMap ℂ K ζ * v)
    (W : Over (Spec ↧ℂ)) (Q : Scheme) (πU : Q ⟶ U.left) (πW : Q ⟶ W.left)
    (eN : Q ≅ Spec ↧(integralClosure Γ(U.left, ⊤) K))
    (hbase : πU ≫ U.left.toSpecΓ = eN.hom ≫ Spec.map
      (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) (integralClosure Γ(U.left, ⊤) K))))
    (d : W ⟶ W) (dn : Q ⟶ Q)
    (hπW : dn ≫ πW = πW ≫ d.left)
    (hact : dn ≫ eN.hom = eN.hom ≫
      Spec.map (CommRingCat.ofHom δ.mapIntegralClosure.toRingHom))
    (q : Spec ↧ℂ ⟶ Q) (pU : ComplexPoint U) (pW : ComplexPoint W)
    (hqU : q ≫ πU = pU.left) (hqW : q ≫ πW = pW.left)
    (s : J)
    (hzero : (pU.left.appTop ≫ (Scheme.ΓSpecIso ↧ℂ).hom).hom (z s) = 0) :
    (Point.map d)^[α s] pW = pW := by
  obtain ⟨P, hP, hPbase⟩ := s2v_i2b_normalized_chart_complex_evaluation U hscalar K Q πU
    eN hbase q pU hqU
  have hzeroP : P (algebraMap Γ(U.left, ⊤) (integralClosure Γ(U.left, ⊤) K) (z s)) = 0 := by
    calc
      _ = (pU.left.appTop ≫ (Scheme.ΓSpecIso ↧ℂ).hom).hom (z s) :=
        congrArg (fun f : Γ(U.left, ⊤) →+* ℂ => f (z s)) hPbase
      _ = 0 := hzero
  have hfixedP := s2v_i2b_retained_branch_inertia n m hm Γ(U.left, ⊤) K c hc hinj J κ z α
    hz habsent ε hε v hv hgen ζ hζ δ hδ P s hzeroP
  have hfixedq := s2v_i2b_chart_integral_iterate_fixed eN dn δ hact q (α s) (by
    intro b
    rw [← hP]
    exact hfixedP b)
  exact s2v_i2b_complex_point_fixed_of_chart W Q πW d dn hπW q pW hqW (α s) hfixedq

end HodgeLean.Foundations.Program

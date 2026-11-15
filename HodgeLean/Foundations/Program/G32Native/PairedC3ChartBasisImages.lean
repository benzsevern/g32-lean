import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalChartClass
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineConormalBasis

noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The original chart classes map to a specified affine conormal basis when
the transported ideal sections represent its kernel generators. -/
theorem paired_c3_chart_basis_images {Y W : Scheme.{0}}
    (p : Y ⟶ W) (R S : CommRingCat.{0}) (q : R ⟶ S)
    (a : Spec R ⟶ W) (b : Spec S ⟶ Y) (h : b ≫ p = Spec.map q ≫ a)
    (U : W.Opens) (V : Y.Opens) (hv : p ⁻¹ᵁ U = V)
    (ha : a ⁻¹ᵁ U = ⊤) (hb : b ⁻¹ᵁ V = ⊤)
    (hq : Function.Surjective q) {σ : Type}
    (B : Module.Basis σ (R ⧸ RingHom.ker q.hom) (RingHom.ker q.hom).Cotangent)
    (x : σ → RingHom.ker q.hom)
    (hx : ∀ j, B j = (RingHom.ker q.hom).toCotangent (x j))
    (s : σ → Γ(Conormal.idealModule p, U))
    (hs : ∀ j, s2e_affine_ideal_sections_equiv R S q
      (pairedC3AffineChartIdealSection p R S q a b h U ha (s j)) = x j)
    (D : (Scheme.Modules.pullback b).obj (Conormal.sheaf p) ≅ Conormal.sheaf (Spec.map q))
    (hD : D.hom = Conormal.comparisonMap p (Spec.map q) a b h) (j : σ) :
    D.hom.app ⊤ (pairedC3ConormalChartSourceClass p b U V hv hb (s j)) =
      pairedC3AffineConormalBasis R S q hq B j := by
  have hd := congrArg (fun f : (Scheme.Modules.pullback b).obj (Conormal.sheaf p) ⟶
      Conormal.sheaf (Spec.map q) =>
    f.app ⊤ (pairedC3ConormalChartSourceClass p b U V hv hb (s j))) hD
  exact hd.trans ((paired_c3_conormal_chart_class_restricted p R S q a b h U V hv ha hb (s j)).trans
    (paired_c3_affine_conormal_basis_apply R S q hq B x hx
      (fun j => pairedC3AffineChartIdealSection p R S q a b h U ha (s j)) hs j).symm)

#print axioms paired_c3_chart_basis_images
end HodgeLean.Foundations.Program.G32Native

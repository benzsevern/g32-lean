import HodgeLean.Foundations.Program.G32Native.PairedC3ChartBasisImages
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineFrameSpread

noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Specified kernel generators frame every subopen of the original chart source. -/
theorem paired_c3_chart_generator_frame {Y W : Scheme.{0}}
    (p : Y ⟶ W) (R S : CommRingCat.{0}) (q : R ⟶ S)
    (a : Spec R ⟶ W) (b : Spec S ⟶ Y) (h : b ≫ p = Spec.map q ≫ a)
    (U : W.Opens) (V : Y.Opens) (hv : p ⁻¹ᵁ U = V)
    (ha : a ⁻¹ᵁ U = ⊤) (hb : b ⁻¹ᵁ V = ⊤)
    (hq : Function.Surjective q) {σ : Type} [Fintype σ]
    (B : Module.Basis σ (R ⧸ RingHom.ker q.hom) (RingHom.ker q.hom).Cotangent)
    (x : σ → RingHom.ker q.hom)
    (hx : ∀ j, B j = (RingHom.ker q.hom).toCotangent (x j))
    (s : σ → Γ(Conormal.idealModule p, U))
    (hs : ∀ j, s2e_affine_ideal_sections_equiv R S q
      (pairedC3AffineChartIdealSection p R S q a b h U ha (s j)) = x j)
    (D : (Scheme.Modules.pullback b).obj (Conormal.sheaf p) ≅ Conormal.sheaf (Spec.map q))
    (hD : D.hom = Conormal.comparisonMap p (Spec.map q) a b h) (W' : (Spec S).Opens) :
    Function.Bijective (pairedC3FiniteFrameSynthesis
      (fun j => pairedC3ConormalChartSourceClass p b U V hv hb (s j)) W' le_top) := by
  let M := (Scheme.Modules.pullback b).obj (Conormal.sheaf p)
  let T := (ModuleCat.extendScalars q.hom).obj (ModuleCat.of R (RingHom.ker q.hom))
  haveI : IsIso M.fromTildeΓ := isIso_fromTildeΓ_iff.mpr
    ⟨T, ⟨(D ≪≫ pairedC3AffineConormalTensorIso R S q).symm⟩⟩
  exact paired_c3_affine_frame_of_basis_images S M _ D
    (pairedC3AffineConormalBasis R S q hq B)
    (fun j => pairedC3ConormalChartSourceClass p b U V hv hb (s j))
    (paired_c3_chart_basis_images p R S q a b h U V hv ha hb hq B x hx s hs D hD) W'

#print axioms paired_c3_chart_generator_frame
end HodgeLean.Foundations.Program.G32Native

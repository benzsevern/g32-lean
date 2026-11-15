import HodgeLean.Foundations.Program.SchoenTowerI2bSpecInertia
import HodgeLean.Foundations.Program.SchoenTowerI2bChartAction
import HodgeLean.Foundations.Program.SchoenTowerI2a

/-! Transport of integral evaluation inertia through an actual chart square.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
universe u
namespace HodgeLean.Foundations.Program

/-- An intertwining scheme isomorphism transports the fixing of every iterate.
Source: functoriality of composition and iteration. -/
theorem s2v_i2b_chart_point_iterate_fixed_iff
    {X Y T : Scheme} (e : X ≅ Y) (d : X ⟶ X) (g : Y ⟶ Y)
    (he : d ≫ e.hom = e.hom ≫ g) (p : T ⟶ X) (n : ℕ) :
    (fun q : T ⟶ X => q ≫ d)^[n] p = p ↔
      (fun q : T ⟶ Y => q ≫ g)^[n] (p ≫ e.hom) = p ≫ e.hom := by
  have hs : Function.Semiconj (fun q : T ⟶ X => q ≫ e.hom)
      (fun q => q ≫ d) (fun q => q ≫ g) := by
    intro q
    change (q ≫ d) ≫ e.hom = (q ≫ e.hom) ≫ g
    rw [Category.assoc, he, Category.assoc]
  have hn := hs.iterate_right n p
  constructor
  · intro hp
    rw [hp] at hn
    exact hn.symm
  · intro hp
    apply (cancel_mono e.hom).mp
    exact hn.trans hp

/-- Fixing integral evaluations fixes the point on the actual normalized chart.
Source: full faithfulness of spectrum and the chart action square. -/
theorem s2v_i2b_chart_integral_iterate_fixed
    {R K L : Type u} [CommRing R] [Field K] [CommRing L] [Algebra R K]
    {X : Scheme.{u}} (e : X ≅ Spec ↧(integralClosure R K))
    (dn : X ⟶ X) (d : K ≃ₐ[R] K)
    (he : dn ≫ e.hom = e.hom ≫
      Spec.map (CommRingCat.ofHom d.mapIntegralClosure.toRingHom))
    (p : Spec ↧L ⟶ X) (n : ℕ)
    (hp : ∀ b, (Spec.homEquivRingHom (p ≫ e.hom))
      ((d.mapIntegralClosure ^ n) b) =
      (Spec.homEquivRingHom (p ≫ e.hom)) b) :
    (fun q : Spec ↧L ⟶ X => q ≫ dn)^[n] p = p := by
  apply (s2v_i2b_chart_point_iterate_fixed_iff e dn _ he p n).mpr
  exact s2v_i2b_integral_spec_iterate_fixed (p ≫ e.hom) d n hp

/-- Monomial inertia fixes the actual chart point through its specified action square.
Source: G32 v0.16, Lemma 4.3, and the frozen normalized monomial inertia interface. -/
theorem s2v_i2b_monomial_chart_point_fixed
    (n m : ℕ) (hm : 0 < m)
    (R K : Type) [CommRing R] [IsDomain R] [Field K]
    [Algebra ℂ R] [Algebra R K] [Algebra ℂ K] [IsScalarTower ℂ R K]
    (c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R) (hc : c.toRingHom.Etale)
    (hinj : Function.Injective (algebraMap R K))
    (α : Fin n → ℕ) (ε : R) (hε : IsUnit ε) (v : K)
    (hv : v ^ m = algebraMap R K ε *
      ∏ j, (algebraMap R K (c (MvPolynomial.X j))) ^ α j)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (d : K ≃ₐ[R] K) (hd : d v = algebraMap ℂ K ζ * v)
    (p : integralClosure R K →ₐ[ℂ] ℂ) (j : Fin n)
    (hp : p (algebraMap R (integralClosure R K) (c (MvPolynomial.X j))) = 0)
    {X : Scheme} (e : X ≅ Spec ↧(integralClosure R K))
    (dn : X ⟶ X)
    (he : dn ≫ e.hom = e.hom ≫
      Spec.map (CommRingCat.ofHom d.mapIntegralClosure.toRingHom))
    (q : Spec ↧ℂ ⟶ X)
    (hq : Spec.homEquivRingHom (q ≫ e.hom) = p.toRingHom) :
    (fun q' : Spec ↧ℂ ⟶ X => q' ≫ dn)^[α j] q = q := by
  have hi := s2v_i2a_normalized_monomial_inertia n m hm R K c hc hinj α ε hε
    v hv hgen ζ hζ d hd p j hp
  have hf := hi (Subgroup.mem_zpowers (d.mapIntegralClosure ^ α j))
  apply s2v_i2b_chart_integral_iterate_fixed e dn d he q (α j)
  intro b
  rw [hq]
  exact hf b

end HodgeLean.Foundations.Program

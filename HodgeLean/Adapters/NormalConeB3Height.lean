import HodgeLean.Adapters.NormalConeB3Dim
import HodgeLean.Adapters.NormalConeB3DimAlg
import HodgeLean.Adapters.KleimanCoheightCharts

/-! # Diagonal cone coefficient: heights of points

Heights of points of schemes (the dimensions of their closures) do not drop along morphisms that
are injective on points, are bounded below by the dimension of a prime quotient in an affine chart,
and on a smooth integral scheme over a field satisfy `height + coheight = dim`.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry Order

universe u

/-- A morphism injective on points does not lower heights.
Source: Mathlib, `Order.height_le_height_apply_of_strictMono`. -/
theorem a3b3_height_le_of_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Function.Injective f.base) (x : X) : height x ≤ height (f.base x) := by
  refine height_le_height_apply_of_strictMono f.base (fun a b hab => ?_) x
  have h1 : f.base a ≤ f.base b := by
    rw [Scheme.le_iff_specializes]
    exact (Scheme.le_iff_specializes.1 hab.le).map f.base.hom.continuous
  refine ⟨h1, fun h2 => ?_⟩
  rw [Scheme.le_iff_specializes] at h1
  have := hf (Scheme.le_iff_specializes.1 h2 |>.antisymm h1).eq
  subst this
  exact lt_irrefl _ hab

/-- The dimension of a prime quotient of an affine chart bounds the height of the point.
Source: theorem `hc9k8_height_spec`. -/
theorem a3b3_ringKrullDim_le_height {X : Scheme.{u}} {R : CommRingCat.{u}} (f : Spec R ⟶ X)
    [IsOpenImmersion f] (P : Spec R) :
    ringKrullDim (R ⧸ P.asIdeal) ≤ height (f.base P) := by
  rw [← hc9k8_height_spec]
  exact_mod_cast a3b3_height_le_of_injective f f.isOpenEmbedding.injective P

section smooth
variable {k : Type u} [Field k] {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k))

/-- The dimension formula `ht P + dim Γ(V)/P = n` in an étale chart with `n` coordinates of a
smooth integral scheme over a field.
Source: theorems `a3b3_height_add_ringKrullDim_quotient` and `a3b3_ringKrullDim_of_etale`. -/
theorem a3b3_etaleChart_formula [IsIntegral Y] {V : Y.Opens} (hne : (V : Set Y).Nonempty)
    {n : ℕ} (g : MvPolynomial (Fin n) k →+* Γ(Y, V))
    (hgC : g.comp MvPolynomial.C = a3b2_fieldMap k Y p V) (hg : g.Etale)
    (P : Ideal Γ(Y, V)) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (Γ(Y, V) ⧸ P) = n := by
  have : Nonempty V := hne.to_subtype
  let : Algebra k Γ(Y, V) := (a3b2_fieldMap k Y p V).toAlgebra
  have hgft : g.FiniteType := by
    let := g.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) k) Γ(Y, V) := RingHom.etale_algebraMap.mp hg
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hft : (a3b2_fieldMap k Y p V).FiniteType := by
    rw [← hgC]
    exact hgft.comp (RingHom.finiteType_algebraMap.2 inferInstance)
  have : Algebra.FiniteType k Γ(Y, V) := RingHom.finiteType_algebraMap.1 hft
  rw [a3b3_height_add_ringKrullDim_quotient (k := k), a3b3_ringKrullDim_of_etale n g hg]

/-- On a smooth integral scheme over a field, `height y + coheight y = dim Y` at every point.
Source: Hartshorne, *Algebraic Geometry*, Exercise II.3.20; theorem
`hc9k8_height_add_coheight_of_charts`. -/
theorem a3b3_height_add_coheight [IsIntegral Y] [Smooth p] (y : Y) :
    height y + coheight y = (height (genericPoint Y)).toNat := by
  refine hc9k8_height_add_coheight_of_charts Y _ (fun y => ?_) y
  obtain ⟨V, hV, hyV, n, g, hgC, hg⟩ := a3b3_exists_etale_chart p y
  have hn := a3b3_height_genericPoint_eq p hV ⟨y, hyV⟩ g hg
  refine ⟨Γ(Y, V), hV.fromSpec, inferInstance, ?_, fun P hP => ?_⟩
  · rw [hV.range_fromSpec]
    exact hyV
  · rw [hn, ENat.toNat_natCast]
    exact a3b3_etaleChart_formula p ⟨y, hyV⟩ g hgC hg P

/-- In an étale chart of a smooth integral scheme over a field, the dimension of the quotient by
the prime of a point is the height of the point.
Source: theorems `a3b3_height_add_coheight` and `hc9k8_coheight_add_height_chart`. -/
theorem a3b3_etaleChart_dim_eq_height [IsIntegral Y] [Smooth p] {V : Y.Opens} (hV : IsAffineOpen V)
    {n : ℕ} (g : MvPolynomial (Fin n) k →+* Γ(Y, V))
    (hgC : g.comp MvPolynomial.C = a3b2_fieldMap k Y p V) (hg : g.Etale)
    (x : Spec Γ(Y, V)) :
    ringKrullDim (Γ(Y, V) ⧸ x.asIdeal) = height (hV.fromSpec.base x) := by
  have hne : (V : Set Y).Nonempty := ⟨hV.fromSpec.base x, by
    rw [← hV.range_fromSpec]; exact ⟨x, rfl⟩⟩
  have hn := a3b3_height_genericPoint_eq p hV hne g hg
  have h1 := hc9k8_coheight_add_height_chart hV.fromSpec n
    (fun P hP => a3b3_etaleChart_formula p hne g hgC hg P) x
  have h2 := a3b3_height_add_coheight p (hV.fromSpec.base x)
  rw [hn, ENat.toNat_natCast] at h2
  have hfin : coheight (hV.fromSpec.base x) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at h2
    exact ENat.top_ne_natCast n h2
  rw [← hc9k8_height_spec]
  exact_mod_cast WithTop.add_left_cancel hfin (h1.trans (h2.symm.trans (add_comm _ _)))

end smooth

end HodgeLean.Adapters

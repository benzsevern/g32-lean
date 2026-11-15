import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian7Proofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5Proofs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open Filter Set Topology
namespace HodgeLean.Adapters

private theorem bh5_reduced_associated_fin_zero (p : Fin 0 → ℂ)
    (f g : (Fin 0 → ℂ) → ℂ)
    (hz : ∀ᶠ z in nhds p, f z = 0 ↔ g z = 0) : AreAssociatedAt f g p := by
  by_cases hfp : f p = 0
  · have hgp : g p = 0 := (hz.self_of_nhds).mp hfp
    refine ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, ?_⟩
    filter_upwards with z
    rw [Subsingleton.elim z p, hfp, hgp, mul_zero]
  · have hgp : g p ≠ 0 := fun h ↦ hfp ((hz.self_of_nhds).mpr h)
    refine ⟨fun _ ↦ f p / g p, analyticAt_const, div_ne_zero hfp hgp, ?_⟩
    filter_upwards with z
    rw [Subsingleton.elim z p, div_mul_cancel₀ _ hgp]

/-- Reduced local equations with the same zero germ differ by a unit.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B,
local analytic Nullstellensatz and unique factorization. -/
theorem bh5_reduced_associated_aux (n : ℕ) (p : Fin n → ℂ)
    (f g : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hfr : Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p))
    (hgr : Squarefree (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p))
    (hz : ∀ᶠ z in 𝓝 p, f z = 0 ↔ g z = 0) : AreAssociatedAt f g p := by
  exact HodgeLean.Foundations.AnalyticDivisorAlgebraic18.spec_reduced_zero_germs_associated n p f g hf hg hfr hgr hz

/-- Shrink reduced germs to a cover with analytic unit transitions satisfying the cocycle law.
Source: Gunning--Rossi, II.B, reduced analytic germs and uniqueness up to a unit. -/
theorem bh5_unit_transition_cocycle_aux (n : ℕ) (S : Set (Fin n → ℂ))
    (hloc : ∀ p, ∃ (g : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g p),
      Squarefree (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p) ∧
      ∀ᶠ z in 𝓝 p, g z = 0 ↔ z ∈ S) :
    ∃ (U : (Fin n → ℂ) → Set (Fin n → ℂ))
      (g : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
      (u : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ),
      (∀ p, IsOpen (U p)) ∧ (∀ p, p ∈ U p) ∧
      ∃ hg : ∀ p, AnalyticOnNhd ℂ (g p) (U p),
        (∀ p q (hq : q ∈ U p),
          Squarefree (⟨Filter.Germ.ofFun (g p), g p, hg p q hq, rfl⟩ : AnalyticGermAt n q)) ∧
        (∀ p q, q ∈ U p → (g p q = 0 ↔ q ∈ S)) ∧
        (∀ p q, AnalyticOnNhd ℂ (u p q) (U p ∩ U q)) ∧
        (∀ p q z, z ∈ U p ∩ U q → u p q z ≠ 0) ∧
        (∀ p q z, z ∈ U p ∩ U q → g p z = u p q z * g q z) ∧
        (∀ p z, z ∈ U p → u p p z = 1) ∧
        (∀ p q r z, z ∈ U p ∩ U q ∩ U r → u p q z * u q r z = u p r z) := by
  exact bh7_unit_transition_cocycle_aux n S hloc

/-- Cousin II trivializes an analytic multiplicative cocycle on complex affine space.
The input is only the transition cocycle, with no global defining equation.
Source: Gunning--Rossi, Chapter VIII, Cousin II on a contractible Stein space. -/
theorem bh5_cousin_trivialization_aux (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (u : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hu : ∀ p q, AnalyticOnNhd ℂ (u p q) (U p ∩ U q))
    (hun : ∀ p q z, z ∈ U p ∩ U q → u p q z ≠ 0)
    (hdiag : ∀ p z, z ∈ U p → u p p z = 1)
    (hcocycle : ∀ p q r z, z ∈ U p ∩ U q ∩ U r → u p q z * u q r z = u p r z) :
    ∃ v : (Fin n → ℂ) → (Fin n → ℂ) → ℂ,
      (∀ p, AnalyticOnNhd ℂ (v p) (U p)) ∧
      (∀ p z, z ∈ U p → v p z ≠ 0) ∧
      (∀ p q z, z ∈ U p ∩ U q → v p z * u p q z = v q z) := by
  exact bh7_cousin_trivialization_aux n U hU hcover u hu hun hdiag hcocycle

/-- Compatible analytic local functions glue to an entire function.
Source: the sheaf property for holomorphic functions, Gunning--Rossi, Chapter II. -/
theorem bh5_entire_gluing_aux (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (g : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hg : ∀ p, AnalyticOnNhd ℂ (g p) (U p))
    (hcompat : ∀ p q z, z ∈ U p ∩ U q → g p z = g q z) :
    ∃ f : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ f univ ∧
      ∀ p z, z ∈ U p → f z = g p z := by
  refine ⟨fun z ↦ g z z, ?_, ?_⟩
  · intro p _
    apply (hg p p (hcover p)).congr
    filter_upwards [(hU p).mem_nhds (hcover p)] with z hz
    exact hcompat p z z ⟨hz, hcover z⟩
  · intro p z hz
    exact (hcompat p z z ⟨hz, hcover z⟩).symm

/-- Multiplication by an analytic unit preserves a reduced germ and its local zero set.
Source: squarefreeness is invariant under association in a commutative monoid;
Gunning--Rossi, II.B, units in the analytic local ring. -/
theorem bh5_squarefree_preservation_aux (n : ℕ) (p : Fin n → ℂ)
    (f g v : (Fin n → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p) (hv : AnalyticAt ℂ v p)
    (hvn : v p ≠ 0)
    (hgr : Squarefree (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p))
    (he : ∀ᶠ z in 𝓝 p, f z = v z * g z) :
    Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p) ∧
      (f p = 0 ↔ g p = 0) := by
  let G : AnalyticGermAt n p := ⟨Filter.Germ.ofFun g, g, hg, rfl⟩
  let V : AnalyticGermAt n p := ⟨Filter.Germ.ofFun v, v, hv, rfl⟩
  have hV : IsUnit V := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨Filter.Germ.ofFun (fun z ↦ (v z)⁻¹), fun z ↦ (v z)⁻¹, hv.inv hvn, rfl⟩, ?_⟩
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hv.continuousAt.eventually_ne hvn] with z hz
    exact mul_inv_cancel₀ hz
  have hF : (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p) = V * G := by
    apply Subtype.ext
    exact Filter.Germ.coe_eq.mpr he
  constructor
  · rw [hF]
    simpa only [mul_comm] using
      ((associated_mul_isUnit_left_iff hV).mpr (Associated.refl G)).squarefree_iff.mpr hgr
  · rw [he.self_of_nhds, mul_eq_zero]
    simp only [hvn, false_or]

/-- A locally reduced hypersurface on affine complex space has a reduced entire equation.
Source: Gunning--Rossi, Chapter VIII, Cousin II on a contractible Stein space;
local analytic unique factorization. -/
theorem bh5_reduced_principalization_aux (n : ℕ) (S : Set (Fin n → ℂ))
    (hloc : ∀ p, ∃ (g : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g p),
      Squarefree (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p) ∧
      ∀ᶠ z in 𝓝 p, g z = 0 ↔ z ∈ S) :
    ∃ (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ),
      (∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
        AnalyticGermAt n p)) ∧ (∀ p, f p = 0 ↔ p ∈ S) := by
  obtain ⟨U, g, u, hU, hc, hg, hgr, hgs, hu, hun, he, hd, ht⟩ :=
    bh5_unit_transition_cocycle_aux n S hloc
  obtain ⟨v, hv, hvn, hvt⟩ := bh5_cousin_trivialization_aux n U hU hc u hu hun hd ht
  obtain ⟨f, hf, hfg⟩ := bh5_entire_gluing_aux n U hU hc
    (fun p z ↦ v p z * g p z) (fun p ↦ (hv p).mul (hg p)) (by
      intro p q z hz
      rw [he p q z hz, ← mul_assoc, hvt p q z hz])
  have hlocal (p : Fin n → ℂ) := bh5_squarefree_preservation_aux n p f (g p) (v p)
    (hf p (mem_univ p)) (hg p p (hc p)) (hv p p (hc p)) (hvn p p (hc p))
    (hgr p p (hc p)) (by
      filter_upwards [(hU p).mem_nhds (hc p)] with z hz
      exact hfg p z hz)
  exact ⟨f, hf, fun p ↦ (hlocal p).1, fun p ↦ (hlocal p).2.trans (hgs p p (hc p))⟩

/-- Association is preserved by finite powered products.
Source: the definition of `AreAssociatedAt` and products of analytic units. -/
theorem bh5_associated_powered_product (n k : ℕ) (p : Fin n → ℂ)
    (f g : Fin k → (Fin n → ℂ) → ℂ) (m : Fin k → ℕ)
    (h : ∀ i, AreAssociatedAt (f i) (g i) p) :
    AreAssociatedAt (fun z ↦ ∏ i, f i z ^ m i) (fun z ↦ ∏ i, g i z ^ m i) p := by
  classical
  choose u hu hn he using h
  refine ⟨fun z ↦ ∏ i, u i z ^ m i,
    Finset.analyticAt_fun_prod _ (fun i _ ↦ (hu i).pow (m i)), ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (hn i)
  · filter_upwards [Filter.eventually_all.mpr he] with z hz
    simp only [hz, mul_pow, Finset.prod_mul_distrib]

/-- Recover the powered-product association from the local algebraization equations.
Source: the local-equation field of `bh4_Algebraization` and local reduced association. -/
theorem bh5_powered_product_associated
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (D : bh4_LocalDivisorData X) (R : bh4_Algebraization X D)
    (f : Fin R.n → (Fin (dim X.left) → ℂ) → ℂ)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) univ)
    (hr : ∀ i p, Squarefree (⟨Filter.Germ.ofFun (f i), f i, hf i p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hs : ∀ i p, f i p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X (R.x i)) :
    ∀ j p, p ∈ D.V j → AreAssociatedAt (D.f j) (fun z ↦ ∏ i, f i z ^ R.mult i) p := by
  intro j p hp
  obtain ⟨g, hg, hgr, hgs, u, hu, hun, hue⟩ := R.local_equations j p hp
  have ha : ∀ i, AreAssociatedAt (g i) (f i) p := by
    intro i
    apply bh5_reduced_associated_aux (dim X.left) p (g i) (f i) (hg i)
      (hf i p (mem_univ p)) (hgr i) (hr i p)
    filter_upwards [hgs i] with z hz
    exact hz.trans (hs i z).symm
  obtain ⟨v, hv, hvn, hve⟩ :=
    bh5_associated_powered_product (dim X.left) R.n p g f R.mult ha
  refine ⟨fun z ↦ u z * v z, hu.mul hv, mul_ne_zero hun hvn, ?_⟩
  filter_upwards [hue, hve] with z hz hz'
  rw [hz, hz', mul_assoc]

/-- Composition with exactly the stage-four reduced-cover-equations target.
Source: Cousin II on complex affine space and the local multiplicity field of algebraization. -/
theorem bh5_reduced_cover_equations_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (D : bh4_LocalDivisorData X) (R : bh4_Algebraization X D) :
    ∃ f : Fin R.n → (Fin (dim X.left) → ℂ) → ℂ,
      ∃ hf : ∀ i, AnalyticOnNhd ℂ (f i) univ,
        (∀ i p, Squarefree (⟨Filter.Germ.ofFun (f i), f i, hf i p (mem_univ p), rfl⟩ :
          AnalyticGermAt (dim X.left) p)) ∧
        (∀ i p, f i p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X (R.x i)) ∧
        (∀ j p, p ∈ D.V j →
          AreAssociatedAt (D.f j) (fun z ↦ ∏ i, f i z ^ R.mult i) p) := by
  classical
  have hi : ∀ i : Fin R.n, ∃ (f : (Fin (dim X.left) → ℂ) → ℂ)
      (hf : AnalyticOnNhd ℂ f univ),
      (∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
        AnalyticGermAt (dim X.left) p)) ∧
      (∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X (R.x i)) := by
    intro i
    apply bh5_reduced_principalization_aux (dim X.left)
      {p | abelianExp X p ∈ bh4_componentSupport X (R.x i)}
    intro p
    have hp : p ∈ ⋃ j, D.V j := by rw [D.valid.2.1]; exact mem_univ p
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    obtain ⟨g, hg, hr, hs, _⟩ := R.local_equations j p hj
    exact ⟨g i, hg i, hr i, hs i⟩
  choose f hf hr hs using hi
  exact ⟨f, hf, hr, hs, bh5_powered_product_associated X D R f hf hr hs⟩

end HodgeLean.Adapters

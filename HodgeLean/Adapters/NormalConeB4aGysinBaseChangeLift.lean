import HodgeLean.Adapters.NormalConeB4aGysinTensorPoint

/-! # Continuous local lifts from the source into the comparison base change -/

noncomputable section
namespace HodgeLean.Adapters
open AlgebraicGeometry ComplexAlgHom
open scoped TensorProduct

/-- Near compatible complex points, an étale parameter base change has a
continuous section over the original source, including a nonreduced source. -/
theorem a3b4a_gysin_exists_continuous_baseChange_lift
    {n : ℕ} (T S : Type) [CommRing T] [CommRing S] [Algebra ℂ T] [Algebra ℂ S]
    [Algebra (complexPolynomialRing n) T] [Algebra (complexPolynomialRing n) S]
    [IsScalarTower ℂ (complexPolynomialRing n) T] [IsScalarTower ℂ (complexPolynomialRing n) S]
    [Algebra.Etale (complexPolynomialRing n) T]
    (u : T →ₐ[ℂ] ℂ) (w : S →ₐ[ℂ] ℂ)
    (h : ∀ d : complexPolynomialRing n,
      u (algebraMap (complexPolynomialRing n) T d) = w (algebraMap (complexPolynomialRing n) S d)) :
    ∃ V : Set (S →ₐ[ℂ] ℂ), IsOpen V ∧
      ∃ hw : w ∈ V, ∃ G : V → (TensorProduct (complexPolynomialRing n) T S →ₐ[ℂ] ℂ),
        Continuous G ∧
        (∀ t : T, ∀ s : S, G ⟨w, hw⟩ (t ⊗ₜ[complexPolynomialRing n] s) = u t * w s) ∧
        (∀ z : V, ∀ s : S, G z (1 ⊗ₜ[complexPolynomialRing n] s) = z.val s) := by
  obtain ⟨U, hU, huU, F, hF, hFu, hbase, _⟩ :=
    a3b4a_gysin_exists_analytic_parameter_lift (n := n) T u
  have hcbase : Continuous (etaleBaseAlgHom (n := n) S) := by
    rw [continuous_induced_rng]
    exact continuous_pi fun d => ComplexPoint.continuous_affineAlgebraHom_apply S
      (algebraMap (complexPolynomialRing n) S d)
  let b := fun z : S →ₐ[ℂ] ℂ => mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom S z)
  have hb : Continuous b := (mvPolynomialAlgHomHomeomorph n).continuous.comp hcbase
  have hbw : b w = mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom T u) :=
    congrArg (mvPolynomialAlgHomHomeomorph n) (AlgHom.ext h).symm
  let V := b ⁻¹' U
  have hwV : w ∈ V := by
    change b w ∈ U
    rw [hbw]
    exact huU
  have hFcomp : Continuous (fun z : V => F (b z.val)) :=
    ((continuousOn_iff_continuous_restrict).mp hF).comp
      ((hb.comp continuous_subtype_val).subtype_mk (fun z => z.property))
  have hcompat : ∀ z : V, ∀ d : complexPolynomialRing n,
      F (b z.val) (algebraMap (complexPolynomialRing n) T d) =
        z.val (algebraMap (complexPolynomialRing n) S d) := by
    intro z d
    have hz := hbase (b z.val) z.property
    change etaleBaseAlgHom T (F (b z.val)) =
      (mvPolynomialAlgHomHomeomorph n).symm
        (mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom S z.val)) at hz
    rw [Homeomorph.symm_apply_apply] at hz
    exact congrArg (fun f : complexPolynomialRing n →ₐ[ℂ] ℂ => f d) hz
  obtain ⟨G, hG, hGval⟩ := a3b4a_gysin_exists_continuous_tensor_evaluation
    (fun z : V => F (b z.val)) (fun z : V => z.val) hFcomp continuous_subtype_val hcompat
  refine ⟨V, hU.preimage hb, hwV, G, hG, ?_, ?_⟩
  · intro t s
    rw [hGval]
    change F (b w) t * w s = u t * w s
    rw [hbw, hFu]
  · intro z s
    rw [hGval, map_one, one_mul]

/-- A continuous family of evaluations lifts to a principal localization
on an open neighborhood where the chosen denominator remains nonzero. -/
theorem a3b4a_gysin_exists_localized_evaluation_family
    {X : Type*} [TopologicalSpace X] (R : Type) [CommRing R] [Algebra ℂ R]
    (F : X → (R →ₐ[ℂ] ℂ)) (hF : Continuous F) (x : X) (r : R) (hr : F x r ≠ 0) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ H : U → (Localization.Away r →ₐ[ℂ] ℂ), Continuous H ∧
        ∀ z : U, ∀ a : R, H z (algebraMap R (Localization.Away r) a) = F z.val a := by
  let U := {z : X | F z r ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun
    ((ComplexPoint.continuous_affineAlgebraHom_apply R r).comp hF) continuous_const
  let H := fun z : U => (localizationAwayAlgHomHomeomorph R r).symm ⟨F z.val, z.property⟩
  have hH : Continuous H := (localizationAwayAlgHomHomeomorph R r).symm.continuous.comp
    ((hF.comp continuous_subtype_val).subtype_mk (fun z => z.property))
  exact ⟨U, hU, hr, H, hH, fun z a =>
    nonvanishingAlgHomExtension_algebraMap R r ⟨F z.val, z.property⟩ a⟩

end HodgeLean.Adapters

import Mathlib.RingTheory.Invariant.Basic
import HodgeLean.Foundations.Program.SchoenCycleProjectiveGraph
import HodgeLean.Foundations.ChowProjective
import HodgeLean.Adapters.IntersectionProductScaf
import HodgeLean.Adapters.GagaMaps

/-! # Algebraic carriers of canonical quotient incidence
Closed analytic incidence in native scheme charts has a closed algebraic carrier.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ComplexProjectiveSpace TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Canonical incidence on a smooth integral projective scheme has a closed algebraic carrier. -/
theorem s2e_canonicalProjective_incidence_algebraic
    (Z B T : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (N n : ℕ) (γ : HodgeLean.Adapters.g3_power Z N ⟶ B)
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (hd : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) = n + 1)
    (u : T ⟶ Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) (v : T ⟶ B) :
    letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
      Module.finite_of_finrank_pos (by rw [hd]; omega)
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) n hd
    ∃ C : Set T.left, IsClosed C ∧
      {x : ComplexPoint T | s2e_canonicalQuotientPoint Z B N γ hg
        (ep.symm (Point.map u x)) = Point.map v x} = Point.underlying ⁻¹' C := by
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  letI : IsIntegral (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)) :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral n
  letI : Smooth (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)) :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_smooth n
  letI : SmoothOfRelativeDimension (n + 1)
      (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)).hom :=
    AffineSpace.smoothOfRelativeDimension_of_card_eq (Spec ↧ℂ) (by simp)
  letI : SmoothOfRelativeDimension (dim (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)))
      (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))).hom :=
    SmoothOfRelativeDimension.of_isIntegral (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))
  apply chowG_setLevel T
  exact s2e_canonicalProjective_incidence_isClosedAnalytic Z B T N n
    (n + 1)
    (dim (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ))) (dim B.left) (dim T.left)
    γ hγ hg hd u v


/-- Actual canonical quotient evaluation is induced by a morphism from projective space. -/
theorem s2e_canonicalProjective_algebraize
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (N n : ℕ) (γ : HodgeLean.Adapters.g3_power Z N ⟶ B)
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (hd : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) = n + 1) :
    letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
      Module.finite_of_finrank_pos (by rw [hd]; omega)
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) n hd
    ∃ ℓ : Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)) ⟶ B,
      Point.map ℓ = fun R => s2e_canonicalQuotientPoint Z B N γ hg (ep.symm R) := by
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))
  letI : IsIntegral PP.left := HodgeLean.Adapters.IntersectionProductScaf_projective_integral n
  letI : Smooth PP.hom := HodgeLean.Adapters.IntersectionProductScaf_projective_smooth n
  letI : IsProjective PP.hom := ⟨⟨⟨n, 𝟙 _, Category.id_comp _⟩⟩⟩
  let ep := s2e_finiteDimensionalProjectivePointEquiv
    (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) n hd
  let g := fun R => s2e_canonicalQuotientPoint Z B N γ hg (ep.symm R)
  obtain ⟨C, hC, heq⟩ := s2e_canonicalProjective_incidence_algebraic Z B
    (HodgeLean.Adapters.gagam_product PP B) N n γ hγ hg hd
    (CartesianMonoidalCategory.fst PP B) (CartesianMonoidalCategory.snd PP B)
  apply HodgeLean.Adapters.gagam_morphism_of_closed_graph PP B g C hC
  rw [← heq]
  ext x
  exact eq_comm


/-- A finite scheme morphism has finite fibres on actual complex points. -/
theorem s2e_finite_complexPoint_fibre
    {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) [IsFinite f.left] (y : ComplexPoint Y) :
    Set.Finite {x : ComplexPoint X | Point.map f x = y} := by
  have hi : Function.Injective (Point.underlying : ComplexPoint X → X.left) :=
    underlying_injective_of_locallyOfFiniteType
  apply ((f.left.finite_preimage_singleton y.underlying).preimage hi.injOn).subset
  intro x hx
  change f.left x.underlying = y.underlying
  rw [← Point.underlying_map]
  exact congrArg Point.underlying hx


open scoped BigOperators in
/-- Finite quotient fibres contain only finitely many actual projective canonical divisors. -/
theorem s2e_canonicalQuotientPoint_finite_fibre
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (N : ℕ) (γ : HodgeLean.Adapters.g3_power Z N ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (b : ComplexPoint B) :
    Set.Finite {z | s2e_canonicalQuotientPoint Z B N γ hg z = b} := by
  classical
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let hE := Module.finrank_fin_fun (n := 1) ℂ
  let D := s2e_projectiveCanonicalDivisor (C := ComplexPoint Z) hE
  have hex z : ∃ f : Fin N → ComplexPoint Z, D z = ∑ i, Finsupp.single (f i) (1 : ℤ) :=
    s2e_effectiveDivisor_exists_tuple (D z)
      (s2e_projectiveCanonicalDivisor_effective_degree hE z).1
      ((s2e_projectiveCanonicalDivisor_effective_degree hE z).2.trans hg.symm)
  let F := fun z => (hex z).choose
  have hF z : D z = ∑ i, Finsupp.single (F z i) (1 : ℤ) := (hex z).choose_spec
  let L := fun z => s2_lift N (F z)
  have hL : Function.Injective L := by
    intro z w h
    apply s2e_projectiveCanonicalDivisor_injective hE
    have he : F z = F w := by
      funext i
      have hh := congrArg (Point.map (HodgeLean.Adapters.g3_proj Z N i)) h
      simpa only [L, Point.map, s2_check_lift_proj] using hh
    change D z = D w
    rw [hF z, hF w, he]
  have heval z : s2e_canonicalQuotientPoint Z B N γ hg z = Point.map γ (L z) := by
    induction z using Projectivization.ind with
    | h θ hθ =>
      exact s2e_canonicalQuotientPoint_eq Z B N γ hγ hg θ hθ _ (hF (Projectivization.mk ℂ θ hθ))
  apply ((s2e_finite_complexPoint_fibre γ b).preimage hL.injOn).subset
  intro z hz
  exact (heval z).symm.trans hz


/-- A proper morphism with finite complex-point fibres is finite over complex schemes of finite type. -/
theorem s2e_isFinite_of_proper_complexPoint_fibres
    {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left]
    (hf : ∀ y : ComplexPoint Y, Set.Finite {x : ComplexPoint X | Point.map f x = y}) :
    IsFinite f.left := by
  classical
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  letI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hfib (y : Y.left) (hy : IsClosed ({y} : Set Y.left)) :
      Set.Finite (f.left ⁻¹' {y}) := by
    obtain ⟨yp, hyp⟩ : ∃ yp : ComplexPoint Y, yp.underlying = y :=
      ⟨Over.homMk (pointOfClosedPoint Y.hom y hy) (by simp),
        pointOfClosedPoint_apply Y.hom y hy _⟩
    let S := f.left ⁻¹' {y} ∩ closedPoints X.left
    have hS : S.Finite := by
      apply ((hf yp).image Point.underlying).subset
      intro x hx
      obtain ⟨xp, hxp⟩ : ∃ xp : ComplexPoint X, xp.underlying = x :=
        ⟨Over.homMk (pointOfClosedPoint X.hom x hx.2) (by simp),
          pointOfClosedPoint_apply X.hom x hx.2 _⟩
      refine ⟨xp, ?_, hxp⟩
      apply underlying_injective_of_locallyOfFiniteType
      rw [Point.underlying_map, hxp, hyp]
      exact hx.1
    have hSc : IsClosed S := by
      rw [← Set.biUnion_of_singleton S]
      exact hS.isClosed_biUnion fun x hx => hx.2
    have hfc : IsClosed (f.left ⁻¹' {y}) := hy.preimage f.left.continuous
    have he := JacobsonSpace.closure_inter_closedPoints_eq_closure hfc.isLocallyClosed
    change closure S = closure (f.left ⁻¹' {y}) at he
    rw [hSc.closure_eq, hfc.closure_eq] at he
    exact he ▸ hS
  have hqf (x : X.left) (hx : IsClosed ({f.left x} : Set Y.left)) :
      f.left.QuasiFiniteAt x := by
    letI : Finite (f.left ⁻¹' {f.left x}) := (hfib _ hx).to_subtype
    letI : Finite (f.left.fiber (f.left x)) := (f.left.fiberHomeo (f.left x)).finite_iff.mpr inferInstance
    exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
  letI : LocallyQuasiFinite f.left := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
    intro x _
    by_contra hx
    have hc : IsClosed (f.left '' (f.left.quasiFiniteLocus : Set X.left)ᶜ) :=
      f.left.isClosedMap _ f.left.quasiFiniteLocus.isOpen.isClosed_compl
    obtain ⟨_, ⟨z, hz, rfl⟩, hcl⟩ :=
      nonempty_inter_closedPoints (Set.Nonempty.image f.left ⟨x, hx⟩) hc.isLocallyClosed
    exact hz (hqf z hcl)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left


/-- Actual canonical quotient evaluation is induced by a finite algebraic morphism. -/
theorem s2e_canonicalProjective_finite_morphism
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (N n : ℕ) (γ : HodgeLean.Adapters.g3_power Z N ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (hd : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) = n + 1) :
    letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
      Module.finite_of_finrank_pos (by rw [hd]; omega)
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) n hd
    ∃ ℓ : Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)) ⟶ B,
      IsFinite ℓ.left ∧
      Point.map ℓ = fun R => s2e_canonicalQuotientPoint Z B N γ hg (ep.symm R) := by
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))
  letI : IsIntegral PP.left := HodgeLean.Adapters.IntersectionProductScaf_projective_integral n
  letI : Smooth PP.hom := HodgeLean.Adapters.IntersectionProductScaf_projective_smooth n
  letI : IsProjective PP.hom := ⟨⟨⟨n, 𝟙 _, Category.id_comp _⟩⟩⟩
  let ep := s2e_finiteDimensionalProjectivePointEquiv
    (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) n hd
  obtain ⟨ℓ, hℓ⟩ := s2e_canonicalProjective_algebraize Z B N n γ hγ hg hd
  refine ⟨ℓ, ?_, hℓ⟩
  letI : IsProper (ℓ.left ≫ B.hom) := by rw [Over.w ℓ]; infer_instance
  letI : IsProper ℓ.left := IsProper.of_comp ℓ.left B.hom
  apply s2e_isFinite_of_proper_complexPoint_fibres ℓ
  intro b
  rw [hℓ]
  exact (s2e_canonicalQuotientPoint_finite_fibre Z B N γ hγ hg b).preimage ep.symm.injective.injOn


/-- A reduced surjective invariant factor of the retained symmetric quotient is an isomorphism. -/
theorem s2e_symmetric_quotient_reduced_factor_isIso
    (Z B T : Over (Spec ↧ℂ)) (N : ℕ)
    (γ : HodgeLean.Adapters.g3_power Z N ⟶ B)
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hquot : ∀ (U : Over (Spec ↧ℂ)) (f : HodgeLean.Adapters.g3_power Z N ⟶ U),
      (∀ σ, s2_permute Z N σ ≫ f = f) → ∃! u : B ⟶ U, γ ≫ u = f)
    (f : HodgeLean.Adapters.g3_power Z N ⟶ T) (t : T ⟶ B)
    [Surjective f.left] [IsReduced T.left] [IsSeparated t.left]
    (hf : ∀ σ, s2_permute Z N σ ≫ f = f) (hfac : f ≫ t = γ) :
    IsIso t.left := by
  obtain ⟨s, hs, _⟩ := hquot T f hf
  have hst : s ≫ t = 𝟙 B := by
    apply (hquot B γ hγ).unique
    · rw [← Category.assoc, hs, hfac]
    · exact Category.comp_id γ
  have hst' : s.left ≫ t.left = 𝟙 B.left := congrArg Over.Hom.left hst
  letI : IsClosedImmersion (s.left ≫ t.left) := by rw [hst']; infer_instance
  letI : IsClosedImmersion s.left := IsClosedImmersion.of_comp s.left t.left
  letI : Surjective s.left := ⟨by
    intro y
    obtain ⟨x, hx⟩ := f.left.surjective y
    refine ⟨γ.left x, ?_⟩
    change (γ ≫ s).left x = y
    rw [hs]
    exact hx⟩
  letI : IsIso s.left := isIso_of_isClosedImmersion_of_surjective s.left
  have ht : t.left = inv s.left := by
    apply (cancel_epi s.left).mp
    rw [hst', IsIso.hom_inv_id]
  rw [ht]
  infer_instance


open scoped Pointwise in
/-- Field-valued evaluations over an invariant subring differ by the finite group action. -/
theorem s2e_invariant_evaluations_orbit
    {k A R G : Type*} [Field k] [CommRing A] [CommRing R]
    [Algebra A R] [Algebra k R] [Group G] [Finite G] [MulSemiringAction G R]
    [SMulCommClass G A R] [SMulCommClass G k R] [Algebra.IsInvariant A R G]
    (φ ψ : R →ₐ[k] k)
    (h : ∀ a : A, φ (algebraMap A R a) = ψ (algebraMap A R a)) :
    ∃ g : G, ∀ r : R, ψ r = φ (g • r) := by
  let P := RingHom.ker φ.toRingHom
  let Q := RingHom.ker ψ.toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime φ.toRingHom
  letI : Q.IsPrime := RingHom.ker_isPrime ψ.toRingHom
  have hPQ : P.under A = Q.under A := by
    ext a
    change φ (algebraMap A R a) = 0 ↔ ψ (algebraMap A R a) = 0
    rw [h a]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A R G P Q hPQ
  refine ⟨g⁻¹, fun r => ?_⟩
  have hr : r - algebraMap k R (ψ r) ∈ Q := by
    change ψ (r - algebraMap k R (ψ r)) = 0
    simp
  rw [hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hr
  change φ (g⁻¹ • (r - algebraMap k R (ψ r))) = 0 at hr
  simp only [smul_sub, smul_algebraMap, map_sub, AlgHom.commutes] at hr
  exact (sub_eq_zero.mp hr).symm


/-- Invariant functions distinguish field-valued evaluations in different finite-group orbits. -/
theorem s2e_invariant_separates_evaluation_orbits
    {k R G : Type*} [Field k] [CommRing R] [Algebra k R]
    [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G k R]
    (φ ψ : R →ₐ[k] k) (hno : ¬ ∃ g : G, ∀ r : R, ψ r = φ (g • r)) :
    ∃ r : R, (∀ g : G, g • r = r) ∧ φ r ≠ ψ r := by
  classical
  by_contra hn
  push_neg at hn
  let A := FixedPoints.subalgebra k R G
  letI : SMulCommClass G A R := ⟨fun g a r => by
    change g • ((a : R) * r) = (a : R) * (g • r)
    rw [smul_mul', a.property g]⟩
  apply hno
  apply s2e_invariant_evaluations_orbit (A := A) φ ψ
  intro a
  exact hn a a.property


open scoped BigOperators in
/-- Separation of permutation orbits makes canonical quotient evaluation injective. -/
theorem s2e_canonicalQuotientPoint_injective_of_orbits
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (N : ℕ) (γ : HodgeLean.Adapters.g3_power Z N ⟶ B)
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (horbit : ∀ x y : ComplexPoint (HodgeLean.Adapters.g3_power Z N),
      Point.map γ x = Point.map γ y → ∃ σ, Point.map (s2_permute Z N σ) x = y)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2) :
    Function.Injective (s2e_canonicalQuotientPoint Z B N γ hg) := by
  classical
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let hE := Module.finrank_fin_fun (n := 1) ℂ
  let D := s2e_projectiveCanonicalDivisor (C := ComplexPoint Z) hE
  have hex z : ∃ f : Fin N → ComplexPoint Z, D z = ∑ i, Finsupp.single (f i) (1 : ℤ) :=
    s2e_effectiveDivisor_exists_tuple (D z)
      (s2e_projectiveCanonicalDivisor_effective_degree hE z).1
      ((s2e_projectiveCanonicalDivisor_effective_degree hE z).2.trans hg.symm)
  let F := fun z => (hex z).choose
  have hF z : D z = ∑ i, Finsupp.single (F z i) (1 : ℤ) := (hex z).choose_spec
  have heval z : s2e_canonicalQuotientPoint Z B N γ hg z = Point.map γ (s2_lift N (F z)) := by
    induction z using Projectivization.ind with
    | h θ hθ =>
      exact s2e_canonicalQuotientPoint_eq Z B N γ hγ hg θ hθ _ (hF (Projectivization.mk ℂ θ hθ))
  intro z w h
  obtain ⟨σ, hσ⟩ := horbit (s2_lift N (F z)) (s2_lift N (F w))
    ((heval z).symm.trans (h.trans (heval w)))
  have he : F w = fun i => F z (σ.symm i) := by
    funext i
    have hh := congrArg (Point.map (HodgeLean.Adapters.g3_proj Z N i)) hσ
    simpa only [Point.map, s2e_lift_permute, s2_check_lift_proj] using hh.symm
  apply s2e_projectiveCanonicalDivisor_injective hE
  change D z = D w
  rw [hF z, hF w, he]
  exact (σ.symm.sum_comp (fun i => Finsupp.single (F z i) (1 : ℤ))).symm


/-- Affine sections of a smooth integral complex scheme are integrally closed. -/
theorem s2e_smooth_affine_sections_integrallyClosed
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X.left, U) := by
  have hX := zmtiso_normal_of_smooth X.left X.hom
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP => ?_
  letI := TopCat.Presheaf.algebra_section_stalk X.left.presheaf
    ⟨hU.fromSpec ⟨P, hP.isPrime⟩, (hU.isoSpec.inv _).2⟩
  letI : IsLocalization.AtPrime (X.left.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩)) P :=
    hU.isLocalization_stalk' ⟨P, hP.isPrime⟩ (hU.isoSpec.inv _).2
  exact (hX _).2.of_equiv
    (IsLocalization.algEquiv P.primeCompl (X.left.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩))
      (Localization.AtPrime P)).toRingEquiv


/-- Rational functions integral over an affine base are regular on its finite smooth inverse image. -/
theorem s2e_finite_smooth_integral_rational_iff_regular
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Y) [IsFinite f.left] (U : Y.left.Opens) (hU : IsAffineOpen U)
    [Nonempty (f.left ⁻¹ᵁ U)] :
    letI : Algebra Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := (f.left.app U).hom.toAlgebra
    letI : Algebra Γ(Y.left, U) X.left.functionField :=
      ((algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField).comp (f.left.app U).hom).toAlgebra
    ∀ a : X.left.functionField, _root_.IsIntegral Γ(Y.left, U) a ↔
      ∃ b : Γ(X.left, f.left ⁻¹ᵁ U), algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField b = a := by
  letI : Algebra Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := (f.left.app U).hom.toAlgebra
  letI : Algebra Γ(Y.left, U) X.left.functionField :=
    ((algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField).comp (f.left.app U).hom).toAlgebra
  letI : IsScalarTower Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegrallyClosed Γ(X.left, f.left ⁻¹ᵁ U) :=
    s2e_smooth_affine_sections_integrallyClosed X _ (hU.preimage f.left)
  letI : IsFractionRing Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen X.left _ (hU.preimage f.left)
  intro a
  constructor
  · intro ha
    exact IsIntegrallyClosed.isIntegral_iff.mp ha.tower_top
  · rintro ⟨b, rfl⟩
    have hb : _root_.IsIntegral Γ(Y.left, U) b := f.left.isIntegral_app U hU b
    exact hb.map
      (IsScalarTower.toAlgHom Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField)


/-- Finite smooth inverse-image sections identify with the integral closure in the actual function field. -/
theorem s2e_finite_smooth_sections_integralClosure_equiv
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Y) [IsFinite f.left] (U : Y.left.Opens) (hU : IsAffineOpen U)
    [Nonempty (f.left ⁻¹ᵁ U)] :
    letI : Algebra Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := (f.left.app U).hom.toAlgebra
    letI : Algebra Γ(Y.left, U) X.left.functionField :=
      ((algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField).comp (f.left.app U).hom).toAlgebra
    ∃ e : Γ(X.left, f.left ⁻¹ᵁ U) ≃ₐ[Γ(Y.left, U)] integralClosure Γ(Y.left, U) X.left.functionField,
      ∀ b, (e b : X.left.functionField) = algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField b := by
  letI : Algebra Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := (f.left.app U).hom.toAlgebra
  letI : Algebra Γ(Y.left, U) X.left.functionField :=
    ((algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField).comp (f.left.app U).hom).toAlgebra
  letI : IsScalarTower Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen X.left _ (hU.preimage f.left)
  let φ : Γ(X.left, f.left ⁻¹ᵁ U) →ₐ[Γ(Y.left, U)] integralClosure Γ(Y.left, U) X.left.functionField :=
    (IsScalarTower.toAlgHom Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField).codRestrict
      (integralClosure Γ(Y.left, U) X.left.functionField) (fun b =>
        (s2e_finite_smooth_integral_rational_iff_regular X Y f U hU _).mpr ⟨b, rfl⟩)
  have hi : Function.Injective φ := by
    intro a b h
    exact IsFractionRing.injective Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField
      (congrArg Subtype.val h)
  have hs : Function.Surjective φ := by
    intro a
    obtain ⟨b, hb⟩ := (s2e_finite_smooth_integral_rational_iff_regular X Y f U hU a.val).mp a.property
    exact ⟨b, Subtype.ext hb⟩
  exact ⟨AlgEquiv.ofBijective φ ⟨hi, hs⟩, fun _ => rfl⟩


/-- Integral elements of an intermediate function field embed into the actual finite-cover sections. -/
theorem s2e_finite_smooth_intermediate_integralClosure_map
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Y) [IsFinite f.left] (U : Y.left.Opens) (hU : IsAffineOpen U)
    [Nonempty (f.left ⁻¹ᵁ U)] (K : Subfield X.left.functionField)
    (hK : ∀ a : Γ(Y.left, U),
      algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField ((f.left.app U).hom a) ∈ K) :
    letI : Algebra Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := (f.left.app U).hom.toAlgebra
    letI : Algebra Γ(Y.left, U) K :=
      (((algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField).comp
        (f.left.app U).hom).codRestrict K hK).toAlgebra
    ∃ j : integralClosure Γ(Y.left, U) K →ₐ[Γ(Y.left, U)] Γ(X.left, f.left ⁻¹ᵁ U),
      Function.Injective j ∧ j.toRingHom.Finite ∧ ∀ a,
        algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField (j a) = ((a : K) : X.left.functionField) := by
  letI : Algebra Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := (f.left.app U).hom.toAlgebra
  letI : Algebra Γ(Y.left, U) X.left.functionField :=
    ((algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField).comp (f.left.app U).hom).toAlgebra
  letI : Algebra Γ(Y.left, U) K :=
    (((algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField).comp
      (f.left.app U).hom).codRestrict K hK).toAlgebra
  letI : IsScalarTower Γ(Y.left, U) K X.left.functionField := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨e, he⟩ := s2e_finite_smooth_sections_integralClosure_equiv X Y f U hU
  let i : integralClosure Γ(Y.left, U) K →ₐ[Γ(Y.left, U)] X.left.functionField :=
    (IsScalarTower.toAlgHom Γ(Y.left, U) K X.left.functionField).comp
      (integralClosure Γ(Y.left, U) K).val
  let j₀ : integralClosure Γ(Y.left, U) K →ₐ[Γ(Y.left, U)]
      integralClosure Γ(Y.left, U) X.left.functionField :=
    i.codRestrict _ (fun a => a.property.map (IsScalarTower.toAlgHom Γ(Y.left, U) K X.left.functionField))
  let j := e.symm.toAlgHom.comp j₀
  have hj (a) : algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField (j a) =
      ((a : K) : X.left.functionField) := by
    rw [← he (j a)]
    change ((e (e.symm (j₀ a))) : X.left.functionField) = _
    rw [e.apply_symm_apply]
    rfl
  have hjfin : j.toRingHom.Finite := by
    apply RingHom.Finite.of_comp_finite (f := algebraMap Γ(Y.left, U) (integralClosure Γ(Y.left, U) K))
    have hc : j.toRingHom.comp (algebraMap Γ(Y.left, U) (integralClosure Γ(Y.left, U) K)) =
        (f.left.app U).hom := by
      ext a
      exact j.commutes a
    change (j.toRingHom.comp (algebraMap Γ(Y.left, U) (integralClosure Γ(Y.left, U) K))).Finite
    rw [hc]
    exact f.left.finite_app U hU
  refine ⟨j, ?_, hjfin, hj⟩
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact (hj a).symm.trans ((congrArg (algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField) hab).trans (hj b))

end HodgeLean.Foundations.Program

import HodgeLean.Adapters.IntersectionProductBasic

/-! # Cycle-level bookkeeping for Serre's intersection product

Finite sums of cycles on a Noetherian scheme, the irreducible components of a closed subscheme
whose support is `closure {u}`, the stalk ideals of the point itself and of the generic point, and
the length of `Tor` against `𝒪_{X,z}/0`. These feed the symmetry, additivity, codimension and
unit statements for `a3i_intersect`.

Source: Fulton, *Intersection Theory*, second edition, §1.5, §8.2 and §20.4; Serre,
*Algèbre locale, multiplicités*, Chapitre V; Weibel, *An Introduction to Homological Algebra*,
§2.4 (projective objects are acyclic for left derived functors). HC no distance; AV milestone no
distance.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section
namespace HodgeLean.Adapters
universe u

/-- Evaluation of a finite sum of cycles. -/
theorem a3c_finsum_apply {X : Scheme.{u}} {ι : Type*} (F : ι → AlgebraicCycle X ℚ)
    (hF : (Function.support F).Finite) (x : X) :
    (∑ᶠ i, F i) x = ∑ᶠ i, F i x := by
  rw [finsum_eq_sum F hF, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  rw [finsum_eq_sum_of_support_subset (s := hF.toFinset)]
  intro i hi
  simp only [Set.Finite.coe_toFinset, Function.mem_support] at hi ⊢
  intro h; exact hi (by rw [h]; rfl)

/-- A nonzero coefficient of a `∑ᶠ` of cycles comes from some summand. -/
theorem a3c_exists_of_finsum_apply_ne_zero {X : Scheme.{u}} {ι : Type*}
    (F : ι → AlgebraicCycle X ℚ) (x : X) (h : (∑ᶠ i, F i) x ≠ 0) : ∃ i, F i x ≠ 0 := by
  by_cases hF : (Function.support F).Finite
  · rw [finsum_eq_sum F hF, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply] at h
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact ⟨i, hi⟩
  · rw [finsum_of_infinite_support hF] at h
    exact (h rfl).elim

/-- Cycles on a Noetherian scheme have finite support. -/
theorem a3c_support_finite {X : Scheme.{u}} [IsNoetherian X] (c : AlgebraicCycle X ℚ) :
    (Function.support c).Finite :=
  Function.locallyFinsupp.finite_support c



/-- The bilinear extension is a finite double sum over sets containing the supports. -/
theorem a3c_intersect_eq_sum (X : Scheme.{u}) (c d : AlgebraicCycle X ℚ) (s t : Finset X)
    (hs : ∀ u ∉ s, c u = 0) (ht : ∀ v ∉ t, d v = 0) :
    a3i_intersect X c d = ∑ u ∈ s, ∑ v ∈ t,
      (a3i_intersectPrime X u v).mapRange (c u * d v * ·) (mul_zero _) := by
  have hz : ∀ u v, (c u = 0 ∨ d v = 0) →
      (a3i_intersectPrime X u v).mapRange (c u * d v * ·) (mul_zero _) = 0 := by
    intro u v h
    ext x
    rcases h with h | h <;> simp [h]
  unfold a3i_intersect
  rw [finsum_eq_sum_of_support_subset (s := s)]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [finsum_eq_sum_of_support_subset (s := t)]
    intro v hv
    by_contra hvt
    exact hv (hz u v (Or.inr (ht v hvt)))
  · intro u hu
    by_contra hus
    apply hu
    simp only
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro v
    exact hz u v (Or.inl (hs u hus))

/-- Points of a closed subscheme whose support is `closure {u}`: a point has its closure an
irreducible component exactly when it lies over `u`. -/
theorem a3c_mem_irreducibleComponents_iff {X : Scheme.{u}} (J : X.IdealSheafData) (u : X)
    (hJ : (J.support : Set X) = closure {u}) (w : J.subscheme) :
    closure ({w} : Set J.subscheme) ∈ irreducibleComponents J.subscheme ↔
      J.subschemeι w = u := by
  have hemb := J.subschemeι.isClosedEmbedding
  have hrange : Set.range J.subschemeι = closure {u} := by
    rw [Scheme.IdealSheafData.range_subschemeι, hJ]
  -- a point over `u` is dense
  have hdense : ∀ w₀ : J.subscheme, J.subschemeι w₀ = u →
      closure ({w₀} : Set J.subscheme) = Set.univ := by
    intro w₀ hw₀
    refine Set.eq_univ_of_forall fun w' => ?_
    rw [← specializes_iff_mem_closure, ← hemb.isInducing.specializes_iff, hw₀,
      specializes_iff_mem_closure, ← hrange]
    exact ⟨w', rfl⟩
  have huniv : Set.univ ∈ irreducibleComponents J.subscheme ↔ IsIrreducible (Set.univ : Set J.subscheme) := by
    refine ⟨fun h => h.1, fun h => ⟨h, fun t _ _ => Set.subset_univ t⟩⟩
  obtain ⟨w₀, hw₀⟩ : u ∈ Set.range J.subschemeι := by
    rw [hrange]; exact subset_closure rfl
  have h₀ := hdense w₀ hw₀
  constructor
  · intro hw
    have hirr : IsIrreducible (Set.univ : Set J.subscheme) := by
      rw [← h₀]; exact isIrreducible_singleton.closure
    have hcl : closure ({w} : Set J.subscheme) = Set.univ :=
      (Set.subset_univ _).antisymm (hw.2 hirr (Set.subset_univ _))
    have h1 : w ⤳ w₀ := by
      rw [specializes_iff_mem_closure, hcl]; trivial
    have h2 : w₀ ⤳ w := by
      rw [specializes_iff_mem_closure, h₀]; trivial
    rw [(h1.antisymm h2).eq, hw₀]
  · intro hw
    rw [hdense w hw]
    exact huniv.2 (by rw [← hdense w hw]; exact isIrreducible_singleton.closure)

/-- Some point of such a subscheme lies over `u`. -/
theorem a3c_exists_subschemeι_eq {X : Scheme.{u}} (J : X.IdealSheafData) (u : X)
    (hJ : (J.support : Set X) = closure {u}) : ∃ w : J.subscheme, J.subschemeι w = u := by
  have : u ∈ Set.range J.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, hJ]; exact subset_closure rfl
  exact this

/-- The support of the ideal of `closure {u}`. -/
theorem a3c_support_primeIdeal (X : Scheme.{u}) (u : X) :
    ((ccm3_primeIdeal X u).support : Set X) = closure {u} := by
  rw [ccm3_primeIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl


open Classical in
/-- On a closed subscheme with support `closure {u}`, the sum over generic points of
irreducible components has the single term at `u`. -/
theorem a3c_finsum_components_eq_single {X : Scheme.{u}} (J : X.IdealSheafData) (u : X)
    (hJ : (J.support : Set X) = closure {u}) (m : X → ℚ) :
    (∑ᶠ y : J.subscheme, if closure ({y} : Set J.subscheme) ∈ irreducibleComponents J.subscheme
      then Function.locallyFinsuppWithin.single (J.subschemeι y) (m (J.subschemeι y)) else 0) =
      Function.locallyFinsuppWithin.single u (m u) := by
  obtain ⟨w₀, hw₀⟩ := a3c_exists_subschemeι_eq J u hJ
  rw [finsum_eq_single _ w₀]
  · rw [ite_eq_left ((a3c_mem_irreducibleComponents_iff J u hJ w₀).2 hw₀), hw₀]
  · intro y hy
    rw [ite_eq_right]
    rw [a3c_mem_irreducibleComponents_iff J u hJ y, ← hw₀]
    exact fun h => hy (J.subschemeι.isClosedEmbedding.injective h)

/-- The stalk ideal of `z` itself is the maximal ideal. -/
theorem a3c_stalkIdeal_self (X : Scheme.{u}) (z : X) :
    a3i_stalkIdeal X z z = IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
  classical
  have hex : ∃ p : Spec (X.presheaf.stalk z), X.fromSpecStalk z p = z :=
    ⟨_, Scheme.fromSpecStalk_closedPoint⟩
  rw [a3i_stalkIdeal, dite_eq_left hex]
  have hp := (X.fromSpecStalk z).isEmbedding.injective
    ((Classical.choose_spec hex).trans Scheme.fromSpecStalk_closedPoint.symm)
  change (Classical.choose hex).asIdeal = _
  rw [hp]
  rfl

/-- On an integral scheme, the stalk ideal of the generic point is zero. -/
theorem a3c_stalkIdeal_genericPoint (X : Scheme.{u}) [IsIntegral X] (z : X) :
    a3i_stalkIdeal X z (genericPoint X) = ⊥ := by
  classical
  let p₀ : Spec (X.presheaf.stalk z) := ⟨⊥, Ideal.isPrime_bot⟩
  have hp₀ : X.fromSpecStalk z p₀ = genericPoint X := by
    have hη : genericPoint X ∈ Set.range (X.fromSpecStalk z) := by
      rw [Scheme.range_fromSpecStalk]; exact genericPoint_specializes z
    obtain ⟨q, hq⟩ := hη
    have h1 : X.fromSpecStalk z p₀ ⤳ genericPoint X := by
      rw [← hq]
      exact ((PrimeSpectrum.le_iff_specializes p₀ q).1 bot_le).map
        (X.fromSpecStalk z).continuous
    exact (h1.antisymm (genericPoint_specializes _)).eq
  have hex : ∃ p : Spec (X.presheaf.stalk z), X.fromSpecStalk z p = genericPoint X := ⟨p₀, hp₀⟩
  rw [a3i_stalkIdeal, dite_eq_left hex]
  have hp := (X.fromSpecStalk z).isEmbedding.injective
    ((Classical.choose_spec hex).trans hp₀.symm)
  change (Classical.choose hex).asIdeal = _
  rw [hp]


section Tor
open MonoidalCategory TensorProduct

variable {A : Type u} [CommRing A]

/-- `length Tor_0(A/𝔪, A/0) = 1` over a local ring. -/
theorem a3c_length_tor0_residue_bot [IsLocalRing A] :
    Module.length A (((Tor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A))).obj
        (ModuleCat.of A (A ⧸ (⊥ : Ideal A)))) = 1 := by
  rw [(a3c_tor0Iso _ _).toLinearEquiv.length_eq]
  let e : ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] (A ⧸ (⊥ : Ideal A))) ≃ₗ[A]
      (A ⧸ IsLocalRing.maximalIdeal A) :=
    (TensorProduct.congr (LinearEquiv.refl A _)
      (Submodule.quotEquivOfEqBot (⊥ : Ideal A) rfl)).trans (TensorProduct.rid A _)
  change Module.length A ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] (A ⧸ (⊥ : Ideal A))) = 1
  rw [e.length_eq, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
  infer_instance

/-- `Tor_{i+1}(M, A/0) = 0`. -/
theorem a3c_length_tor_succ_bot (M : ModuleCat.{u} A) (i : ℕ) :
    Module.length A (((Tor (ModuleCat.{u} A) (i + 1)).obj M).obj
        (ModuleCat.of A (A ⧸ (⊥ : Ideal A)))) = 0 := by
  have : Module.Projective A (A ⧸ (⊥ : Ideal A)) :=
    Module.Projective.of_equiv (Submodule.quotEquivOfEqBot (⊥ : Ideal A) rfl).symm
  rw [Module.length_eq_zero_iff, ← ModuleCat.isZero_iff_subsingleton]
  exact isZero_Tor_succ_of_projective _ _ _ _

end Tor

/-- On an integral scheme, Serre's multiplicity of `closure {z}` against the whole scheme along
`closure {z}` is one. -/
theorem a3c_serreMult_self_genericPoint (X : Scheme.{u}) [IsIntegral X] (z : X) :
    a3i_serreMult X z z (genericPoint X) = 1 := by
  unfold a3i_serreMult a3i_torModule
  rw [a3c_stalkIdeal_self, a3c_stalkIdeal_genericPoint, Finset.sum_range_succ']
  simp only [a3c_length_tor_succ_bot, a3c_length_tor0_residue_bot]
  simp


open Classical in
/-- Against the whole of an integral scheme, the intersection cycle of `closure {v}` is
`closure {v}` with Serre's multiplicity. -/
theorem a3c_intersectPrime_genericPoint (X : Scheme.{u}) [IsIntegral X] (v : X) :
    a3i_intersectPrime X (genericPoint X) v =
      Function.locallyFinsuppWithin.single v
        ((a3i_serreMult X v (genericPoint X) v : ℤ) : ℚ) := by
  classical
  have hJ : ((ccm3_primeIdeal X (genericPoint X) ⊔ ccm3_primeIdeal X v).support : Set X) =
      closure {v} := by
    rw [Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf,
      a3c_support_primeIdeal, a3c_support_primeIdeal, (genericPoint_spec X).def]
    exact Set.univ_inter _
  unfold a3i_intersectPrime
  convert a3c_finsum_components_eq_single _ v hJ
    (fun z => ((a3i_serreMult X z (genericPoint X) v : ℤ) : ℚ))

/-- On a locally Noetherian scheme every point has finite coheight. -/
theorem a3c_coheight_ne_top (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    Order.coheight x ≠ ⊤ := by
  have h := ringKrullDim_stalk_eq_coheight x
  have h2 := ringKrullDim_lt_top (R := X.presheaf.stalk x)
  intro htop
  rw [h, htop] at h2
  exact lt_irrefl _ h2

end HodgeLean.Adapters

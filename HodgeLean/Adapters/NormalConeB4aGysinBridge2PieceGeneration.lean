import HodgeLean.Adapters.NormalConeB4aGysinBridge2DifferentialComparison
import HodgeLean.Adapters.NormalConeB4aGysinBridge2StalkKernel
import HodgeLean.Adapters.NormalConeB4aGysinBridge2GenericLength
import HodgeLean.Adapters.NormalConeB4aGysinBridge2Defs
import HodgeLean.Adapters.NormalConeB4aGysinSmoothCriticalParameters

/-! # Reformulated bridge of A3-B4a: generic slices through a smooth piece

Let `P` be smooth of relative dimension `n` over `ℂ`, mapped to a closed subscheme `K` of `Z` by an
immersion that is an open embedding on underlying spaces. For parameter values outside a null set,
at every complex point of `P` over the value, the local ring of `K` has dimension `n` and the
shifted sections generate its maximal ideal modulo the nilradical. Source: Sard's theorem for
complex manifolds; Serre, *Géométrie algébrique et géométrie analytique*, §2. -/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry IsLocalRing Point Topology Filter

/-- Generic slices through a smooth piece of relative dimension `n`. -/
theorem a3b4g_piece_generic_slice
    {Z K : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (i : K ⟶ Z) (P : Over (Spec (CommRingCat.of ℂ))) {n c : ℕ}
    [SmoothOfRelativeDimension n P.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    [IsSeparated P.hom] (ψ : P ⟶ Over.mk (i ≫ q)) [IsImmersion ψ.left]
    (hψ : IsOpenEmbedding ψ.left.base)
    (Φ : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart q Φ) (U : Z.Opens) (g : Fin n → Γ(Z, U))
    (hΦU : Φ.source ⊆ Point.overOpen (X := Over.mk q) U)
    (hΦg : ∀ z ∈ Φ.source, ∀ j, (Φ z).1 j = Point.evaluate (X := Over.mk q) U (g j) z) :
    ∃ N : Set (Fin n → ℂ), MeasureTheory.volume N = 0 ∧
      ∀ x : ComplexPoint P,
        Point.map (Over.homMk i rfl : Over.mk (i ≫ q) ⟶ Over.mk q) (Point.map ψ x) ∈ Φ.source →
        (Φ (Point.map (Over.homMk i rfl : Over.mk (i ≫ q) ⟶ Over.mk q) (Point.map ψ x))).1 ∉ N →
        ringKrullDim (K.presheaf.stalk (Point.map ψ x).underlying) = n ∧
        ∀ hw : i.base (Point.map ψ x).underlying ∈ U,
          a3b4g_sliceIdeal q i U g
            (Φ (Point.map (Over.homMk i rfl : Over.mk (i ≫ q) ⟶ Over.mk q) (Point.map ψ x))).1
            (Point.map ψ x).underlying hw ⊔
            nilradical (K.presheaf.stalk (Point.map ψ x).underlying) =
          maximalIdeal (K.presheaf.stalk (Point.map ψ x).underlying) := by
  letI : LocallyOfFiniteType (Over.mk q).hom := ‹LocallyOfFiniteType q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  let φ : Over.mk (i ≫ q) ⟶ Over.mk q := Over.homMk i rfl
  let f : P ⟶ Over.mk q := ψ ≫ φ
  obtain ⟨N, hN, hreg⟩ := a3b4a_gysin_smooth_source_regular_parameter_charts P (Over.mk q) n c
    f Φ hΦ
  refine ⟨N, hN, fun x hx ha => ?_⟩
  obtain ⟨j, hxj, hunit⟩ := hreg x hx ha
  set a := (Φ (Point.map f x)).1 with ha_def
  set w := Point.map ψ x with hw_def
  have hwU : i.base w.underlying ∈ U := hΦU hx
  let V' : P.left.Opens := f.left ⁻¹ᵁ U
  have hxV' : x.underlying ∈ V' := hwU
  let s : Fin n → Γ(P.left, V') := fun k =>
    f.left.app U (g k - a3b4a_gysin_sectionConst q U (a k))
  have heval : ∀ y : ComplexPoint P, Point.map f y ∈ Φ.source → ∀ k,
      evaluate V' (s k) y = (Φ (Point.map f y)).1 k - a k := by
    intro y hy k
    rw [← Point.evaluate_map (X := P) f U, a3b4g_evaluate_sub, ← hΦg _ hy k,
      a3b4a_gysin_evaluate_sectionConst q U (Point.map f y) (hΦU hy) (a k)]
  have hf0 : ∀ k, evaluate V' (s k) x = 0 := fun k => by rw [heval x hx k, sub_self]
  let e := chartAt (Fin n → ℂ) j
  have hnear : ∀ᶠ b in 𝓝 (e x), Point.map f (e.symm b) ∈ Φ.source := by
    have hcont : ContinuousAt (fun b => Point.map f (e.symm b)) (e x) :=
      (Point.continuous_map f).continuousAt.comp (e.continuousAt_symm (e.map_source hxj))
    have hmem : Point.map f (e.symm (e x)) ∈ Φ.source := by rw [e.left_inv hxj]; exact hx
    exact hcont.preimage_mem_nhds (Φ.open_source.mem_nhds hmem)
  have hunit' : IsUnit (fderiv ℂ (fun b k => evaluate V' (s k) (e.symm b)) (e x)) := by
    have heq : (fun b k => evaluate V' (s k) (e.symm b)) =ᶠ[𝓝 (e x)]
        (fun b => (Φ (Point.map f (e.symm b))).1 - a) := by
      filter_upwards [hnear] with b hb
      funext k
      rw [heval _ hb k]
      rfl
    rw [heq.fderiv_eq, fderiv_sub_const]
    exact hunit
  have hspan := a3b4g_span_germ_eq_maximalIdeal_of_isUnit_fderiv P x j hxj V' hxV' s hf0 hunit'
  let φs : K.presheaf.stalk w.underlying →+* P.left.presheaf.stalk x.underlying :=
    (ψ.left.stalkMap x.underlying).hom
  haveI : IsLocalHom φs := inferInstanceAs (IsLocalHom (ψ.left.stalkMap x.underlying).hom)
  have hsurj : Function.Surjective φs := ψ.left.stalkMap_surjective x.underlying
  have hgerm : ∀ k, φs (K.presheaf.germ (i ⁻¹ᵁ U) w.underlying hwU
      (i.app U (g k - a3b4a_gysin_sectionConst q U (a k)))) =
        P.left.presheaf.germ V' x.underlying hxV' (s k) := by
    intro k
    exact Scheme.Hom.germ_stalkMap_apply ψ.left (i ⁻¹ᵁ U) x.underlying hwU _
  have hmap : Ideal.map φs (a3b4g_sliceIdeal q i U g a w.underlying hwU) =
      maximalIdeal (P.left.presheaf.stalk x.underlying) := by
    rw [a3b4g_sliceIdeal, Ideal.map_ofList, ← hspan]
    show Ideal.span {r | r ∈ _} = _
    congr 1
    ext r
    simp only [a3b4a_gysin_sliceSequence, List.map_ofFn, Set.mem_setOf_eq, List.mem_ofFn,
      Set.mem_range, Function.comp_apply, hgerm]
  have hker : RingHom.ker φs ≤ nilradical (K.presheaf.stalk w.underlying) := fun r hr =>
    a3b4g_isNilpotent_of_stalkMap_eq_zero ψ.left hψ x.underlying r hr
  have hmax : maximalIdeal (K.presheaf.stalk w.underlying) =
      a3b4g_sliceIdeal q i U g a w.underlying hwU ⊔ RingHom.ker φs := by
    rw [← IsLocalRing.maximalIdeal_comap φs, ← hmap,
      Ideal.comap_map_of_surjective _ hsurj, RingHom.ker_eq_comap_bot]
  refine ⟨?_, fun hw => ?_⟩
  · rw [← a3b4g_ringKrullDim_quotient_of_le_nilradical (RingHom.ker φs) hker,
      ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)]
    exact a3b4g_ringKrullDim_stalk_of_smooth P x.underlying (a3b4g_isClosed_underlying P x)
  · apply le_antisymm
    · refine sup_le ?_ (nilradical_le_prime _)
      rw [hmax]
      exact le_sup_left
    · rw [hmax]
      exact sup_le_sup_left hker _

end HodgeLean.Adapters

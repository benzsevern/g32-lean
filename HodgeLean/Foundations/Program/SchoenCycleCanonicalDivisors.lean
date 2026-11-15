import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints
import HodgeLean.Foundations.Program.SchoenCycleDivisorInjectivity
import HodgeLean.Foundations.Program.SchoenCycleDivisorEnumeration
import HodgeLean.Foundations.Program.SchoenCycleGenusTransport

/-! # Actual canonical divisors
Holomorphic differentials give effective integer divisors with the canonical degree.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold CategoryTheory AlgebraicGeometry Filter Topology
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Program
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual divisor of a nonzero holomorphic differential is effective. -/
theorem s2e_holomorphic_divisor_effective
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) (hθ : θ ≠ 0) :
    ∀ p, 0 ≤ b4c_divForm (hE := hE) (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) p := by
  let w : b4c_MeroForm E C hE := ⟨θ, RiemannRochAna_hol_isMeroForm hE θ⟩
  intro p
  have he := RiemannRochAna_coe_divForm_apply hE w
    (b4c_meroForm_orderSupport_finite_aux hE w) p
    (RiemannRochAna_hol_order_ne_top hE θ hθ p)
  have ho := (RiemannRochEichler_loc_analytic hE θ p).meromorphicOrderAt_nonneg
  rw [← he] at ho
  exact_mod_cast ho

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every nonzero holomorphic differential has the actual canonical divisor degree. -/
theorem s2e_holomorphic_divisor_degree
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) (hθ : θ ≠ 0) :
    b4c_deg (b4c_divForm (hE := hE) (θ : TangentBundle 𝓘(ℂ, E) C → ℂ)) =
      2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) - 2 := by
  let w : b4c_MeroForm E C hE := ⟨θ, RiemannRochAna_hol_isMeroForm hE θ⟩
  have hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := by
    intro hz
    apply hθ
    exact Subtype.ext hz
  let p : C := Classical.choice inferInstance
  exact b4c_deg_canonical_aux hE w hw
    ⟨p, RiemannRochAna_hol_order_ne_top hE θ hθ p⟩

/-- The selected genus equation gives an exact tuple of all canonical zeros, with multiplicities. -/
theorem s2e_holomorphic_divisor_exists_tuple
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (k : ℕ)
    (hg : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C))
    (θ : b3_HolForm E C) (hθ : θ ≠ 0) :
    ∃ f : Fin (2 * k) → C,
      b4c_divForm (hE := hE) (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) =
        ∑ i, Finsupp.single (f i) (1 : ℤ) := by
  apply s2e_effectiveDivisor_exists_tuple _ (s2e_holomorphic_divisor_effective hE θ hθ)
  rw [s2e_holomorphic_divisor_degree hE θ hθ]
  have hi : 2 * (k : ℤ) + 2 = 2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) := by
    exact_mod_cast hg
  push_cast
  omega

/-- The native canonical divisor on the retained scheme curve has the frozen tuple length. -/
theorem s2e_scheme_canonical_divisor_exists_tuple
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (e : C ≃ₜ ComplexPoint Z) (h k : ℕ) (hselected : h + 1 = 2 * k)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ C))
    (θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) (hθ : θ ≠ 0) :
    ∃ f : Fin (h + 1) → ComplexPoint Z,
      b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
        (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
          ∑ i, Finsupp.single (f i) (1 : ℤ) := by
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  have hg : 2 * k + 2 =
      2 * Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) := by
    rw [← s2e_scheme_holForm_finrank_homeomorph Z e]
    exact hgenus
  rw [hselected]
  exact s2e_holomorphic_divisor_exists_tuple (Module.finrank_fin_fun (n := 1) ℂ) k hg θ hθ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equal actual canonical divisors determine the holomorphic differential up to a nonzero scalar. -/
theorem s2e_equal_canonical_divisors_proportional
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (θ η : b3_HolForm E C) (hθ : θ ≠ 0) (hη : η ≠ 0)
    (hd : b4c_divForm (E := E) (C := C) (hE := hE) θ =
      b4c_divForm (E := E) (C := C) (hE := hE) η) :
    ∃ c : ℂ, c ≠ 0 ∧ θ = c • η := by
  let v : b4c_MeroForm E C hE := ⟨θ, RiemannRochAna_hol_isMeroForm hE θ⟩
  let w : b4c_MeroForm E C hE := ⟨η, RiemannRochAna_hol_isMeroForm hE η⟩
  have hv : (v : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := fun hz => hθ (Subtype.ext hz)
  have hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := fun hz => hη (Subtype.ext hz)
  let p : C := Classical.choice inferInstance
  have hgv : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE v p) 0 ≠ ⊤ :=
    ⟨p, RiemannRochAna_hol_order_ne_top hE θ hθ p⟩
  have hgw : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0 ≠ ⊤ :=
    ⟨p, RiemannRochAna_hol_order_ne_top hE η hη p⟩
  obtain ⟨c, hc, hr⟩ := s2e_equal_divisors_ratio_nonzero_constant hE v w hv hw hgv hgw hd
  refine ⟨c, hc, ?_⟩
  apply RiemannRochEichler_holForm_germ_ext hE
  intro q
  exact s2e_constant_formRatio_germ hE v w hgv hgw c hr q

/-- The actual canonical divisor of a projective holomorphic differential.
Source: Forster, Lectures on Riemann Surfaces, GTM 81, §13; Schoen (1988), p. 13. -/
def s2e_projectiveCanonicalDivisor (hE : Module.finrank ℂ E = 1) :
    Projectivization ℂ (b3_HolForm E C) → (C →₀ ℤ) :=
  Projectivization.lift (K := ℂ) (V := b3_HolForm E C)
    (fun θ => b4c_divForm (E := E) (C := C) (hE := hE) θ.val)
    (by
      intro a b t ht
      have hn : t ≠ 0 := by
        intro hz
        apply a.property
        simpa only [hz, zero_smul] using ht
      change b4c_divForm (E := E) (C := C) (hE := hE) a.val =
        b4c_divForm (E := E) (C := C) (hE := hE) b.val
      rw [ht]
      exact s2e_divForm_const_smul (C := C) hE b.val t hn)

example (hE : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) (hθ : θ ≠ 0) :
    s2e_projectiveCanonicalDivisor hE (Projectivization.mk ℂ θ hθ) =
      b4c_divForm (E := E) (C := C) (hE := hE) θ := rfl

/-- Projective canonical divisors distinguish projective holomorphic differentials. -/
theorem s2e_projectiveCanonicalDivisor_injective
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    Function.Injective (s2e_projectiveCanonicalDivisor (C := C) hE) := by
  intro z t h
  induction z using Projectivization.ind with
  | h θ hθ =>
    induction t using Projectivization.ind with
    | h η hη =>
      change b4c_divForm (E := E) (C := C) (hE := hE) θ =
        b4c_divForm (E := E) (C := C) (hE := hE) η at h
      obtain ⟨c, _, hc⟩ := s2e_equal_canonical_divisors_proportional hE θ η hθ hη h
      exact (Projectivization.mk_eq_mk_iff' ℂ θ η hθ hη).mpr ⟨c, hc.symm⟩

/-- Projective canonical divisors are effective and have the canonical degree. -/
theorem s2e_projectiveCanonicalDivisor_effective_degree
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (z : Projectivization ℂ (b3_HolForm E C)) :
    (∀ p, 0 ≤ s2e_projectiveCanonicalDivisor hE z p) ∧
      b4c_deg (s2e_projectiveCanonicalDivisor hE z) =
        2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) - 2 := by
  induction z using Projectivization.ind with
  | h θ hθ =>
    exact ⟨s2e_holomorphic_divisor_effective hE θ hθ,
      s2e_holomorphic_divisor_degree hE θ hθ⟩

/-- Evaluate the actual canonical zero divisor in the retained symmetric quotient. -/
def s2e_canonicalQuotientPoint
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : HodgeLean.Adapters.g3_power Z n ⟶ B)
    (hg : (n : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (z : Projectivization ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))) :
    ComplexPoint B := by
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let hE := Module.finrank_fin_fun (n := 1) ℂ
  let D := s2e_projectiveCanonicalDivisor (C := ComplexPoint Z) hE z
  exact s2e_symmetricQuotientEvaluation n γ
    (s2e_divisorSym D
      (s2e_projectiveCanonicalDivisor_effective_degree hE z).1
      ((s2e_projectiveCanonicalDivisor_effective_degree hE z).2.trans hg.symm))

/-- Any exact tuple of a canonical divisor evaluates to its specified quotient point. -/
theorem s2e_canonicalQuotientPoint_eq
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : HodgeLean.Adapters.g3_power Z n ⟶ B)
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hg : (n : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) (hθ : θ ≠ 0)
    (f : Fin n → ComplexPoint Z)
    (hdiv : b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
      (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
        ∑ i, Finsupp.single (f i) (1 : ℤ)) :
    s2e_canonicalQuotientPoint Z B n γ hg (Projectivization.mk ℂ θ hθ) =
      Point.map γ (s2_lift n f) := by
  unfold s2e_canonicalQuotientPoint
  apply s2e_symmetricQuotientEvaluation_eq n γ hγ
  exact s2e_divisor_tuple_enumeration _ _ _ f hdiv

/-- The native projective canonical system has exactly the specified canonical-divisor locus
on complex points of the retained quotient. -/
theorem s2e_canonicalQuotientPoint_range
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : HodgeLean.Adapters.g3_power Z n ⟶ B)
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hg : (n : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2) :
    ∀ b, b ∈ Set.range (s2e_canonicalQuotientPoint Z B n γ hg) ↔
        ∃ f : Fin n → ComplexPoint Z, Point.map γ (s2_lift n f) = b ∧
          ∃ θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z), θ ≠ 0 ∧
            b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
              (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
                ∑ i, Finsupp.single (f i) (1 : ℤ) := by
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let hE := Module.finrank_fin_fun (n := 1) ℂ
  let D := s2e_projectiveCanonicalDivisor (C := ComplexPoint Z) hE
  have heff (z) : ∀ p, 0 ≤ D z p :=
    (s2e_projectiveCanonicalDivisor_effective_degree hE z).1
  have hd (z) : b4c_deg (D z) = (n : ℤ) :=
    (s2e_projectiveCanonicalDivisor_effective_degree hE z).2.trans hg.symm
  let F (z : Projectivization ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))) :
      ComplexPoint B := s2e_symmetricQuotientEvaluation n γ (s2e_divisorSym (D z) (heff z) (hd z))
  intro b
  change b ∈ Set.range F ↔ _
  constructor
  · rintro ⟨z, hz⟩
    induction z using Projectivization.ind with
    | h θ hθ =>
      let z := Projectivization.mk ℂ θ hθ
      obtain ⟨f, hf, hdiv⟩ := (s2e_effectiveDivisor_quotient_eq_iff Z B n γ hγ
        (D z) (heff z) (hd z) b).mp hz
      exact ⟨f, hf, θ, hθ, hdiv⟩
  · rintro ⟨f, hf, θ, hθ, hdiv⟩
    let z := Projectivization.mk ℂ θ hθ
    refine ⟨z, ?_⟩
    exact (s2e_effectiveDivisor_quotient_eq_iff Z B n γ hγ
      (D z) (heff z) (hd z) b).mpr ⟨f, hf, hdiv⟩

/-- The native projective canonical system has exactly the specified canonical-divisor locus
on complex points of the retained quotient. -/
theorem s2e_scheme_canonical_quotient_point_locus
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : HodgeLean.Adapters.g3_power Z n ⟶ B)
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hg : (n : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2) :
    ∃ F : Projectivization ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) → ComplexPoint B,
      ∀ b, b ∈ Set.range F ↔
        ∃ f : Fin n → ComplexPoint Z, Point.map γ (s2_lift n f) = b ∧
          ∃ θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z), θ ≠ 0 ∧
            b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
              (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
                ∑ i, Finsupp.single (f i) (1 : ℤ) := by
  exact ⟨s2e_canonicalQuotientPoint Z B n γ hg,
    s2e_canonicalQuotientPoint_range Z B n γ hγ hg⟩

/-- Actual projective scheme parameters give the native canonical quotient point locus. -/
theorem s2e_projective_scheme_canonical_point_locus
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (k n : ℕ)
    (hk : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) = k + 1)
    (γ : HodgeLean.Adapters.g3_power Z n ⟶ B)
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hg : (n : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2) :
    ∃ F : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
        ComplexPoint B,
      ∀ b, b ∈ Set.range F ↔
        ∃ f : Fin n → ComplexPoint Z, Point.map γ (s2_lift n f) = b ∧
          ∃ θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z), θ ≠ 0 ∧
            b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
              (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
                ∑ i, Finsupp.single (f i) (1 : ℤ) := by
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
    Module.finite_of_finrank_pos (by omega)
  obtain ⟨F, hF⟩ := s2e_scheme_canonical_quotient_point_locus Z B n γ hγ hg
  let e := s2e_finiteDimensionalProjectivePointEquiv k hk
  refine ⟨F ∘ e.symm, ?_⟩
  intro b
  rw [← hF b]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨e.symm z, hz⟩
  · rintro ⟨z, hz⟩
    refine ⟨e z, ?_⟩
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hz


/-- Every finite cluster presentation of an actual canonical divisor has its retained quotient value. -/
theorem s2e_canonicalQuotientPoint_eq_clusters
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : HodgeLean.Adapters.g3_power Z n ⟶ B)
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hg : (n : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) (hθ : θ ≠ 0)
    {ι : Type} [Fintype ι] (d : ι → ℕ) (e : Fin n ≃ ((i : ι) × Fin (d i)))
    (f : (i : ι) → Fin (d i) → ComplexPoint Z)
    (hdiv : b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
      (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
        ∑ i, ∑ j, Finsupp.single (f i j) (1 : ℤ)) :
    s2e_canonicalQuotientPoint Z B n γ hg (Projectivization.mk ℂ θ hθ) =
      Point.map γ (s2_lift n (fun j => f (e j).1 (e j).2)) := by
  apply s2e_canonicalQuotientPoint_eq Z B n γ hγ hg θ hθ
  rw [hdiv]
  simpa only [Fintype.sum_sigma] using
    (e.sum_comp (fun t : (i : ι) × Fin (d i) => Finsupp.single (f t.1 t.2) (1 : ℤ))).symm

end HodgeLean.Foundations.Program

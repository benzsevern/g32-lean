import HodgeLean.Foundations.Program.SchoenCycleAdicFiltration
import HodgeLean.Foundations.Program.SchoenCycleAffineStalkAdic
import Mathlib.AlgebraicGeometry.Noetherian
import HodgeLean.Foundations.Program.SchoenCycleSingletonFiberRadical
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # The affine ideal of an actual singleton fiber -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A singleton fiber over a closed point identifies the radical of the extended
point ideal on every actual affine inverse-image chart.
Source: Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald,
Introduction to Commutative Algebra, Proposition 1.14. -/
theorem s2e_affine_singleton_fiber_radical
    {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] (x : X)
    (hclosed : IsClosed ({f x} : Set Y))
    (hfiber : f ⁻¹' {f x} = {x})
    (U : Y.Opens) (hU : IsAffineOpen U) (hx : f x ∈ U) :
    let V := f ⁻¹ᵁ U
    let hV : IsAffineOpen V := hU.preimage f
    (((hU.primeIdealOf ⟨f x, hx⟩).asIdeal).map (f.app U).hom).radical =
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let V := f ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage f
  let m := (hU.primeIdealOf ⟨f x, hx⟩).asIdeal
  let P := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  letI : m.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨f x, hx⟩ hclosed
  letI : P.IsPrime := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  have hc (z : V) : (hV.primeIdealOf z).asIdeal.comap (f.app U).hom =
      (hU.primeIdealOf ⟨f z.1, z.2⟩).asIdeal := by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl z.2)
  apply s2e_singleton_prime_fiber_radical (f.app U).hom m P (hc ⟨x, hx⟩)
  intro Q hQ hQm
  obtain ⟨z, hz⟩ := hV.isoSpec.hom.homeomorph.surjective (⟨Q, hQ⟩ : PrimeSpectrum Γ(X, V))
  have hzQ : (hV.primeIdealOf z).asIdeal = Q := congrArg PrimeSpectrum.asIdeal hz
  have hzm : (hU.primeIdealOf ⟨f z.1, z.2⟩).asIdeal = m := by
    rw [← hc z, hzQ, hQm]
  have hzx : f z.1 = f x := by
    have he : hU.primeIdealOf ⟨f z.1, z.2⟩ = hU.primeIdealOf ⟨f x, hx⟩ :=
      PrimeSpectrum.ext hzm
    exact congrArg Subtype.val (hU.isoSpec.hom.homeomorph.injective he)
  have he : z.1 = x := by
    have hzmem : z.1 ∈ f ⁻¹' {f x} := hzx
    rw [hfiber] at hzmem
    exact hzmem
  exact hzQ.symm.trans (congrArg (fun z : V => (hV.primeIdealOf z).asIdeal) (Subtype.ext he))

#print axioms s2e_affine_singleton_fiber_radical

/-- Over a singleton closed fiber, the extended affine point ideal gives the
actual stalk's maximal-ideal adic ring, compatibly with every section germ.
Source: Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald,
Introduction to Commutative Algebra, Chapters 3 and 10. -/
theorem s2e_affine_singleton_fiber_adic_equiv
    {X Y : Scheme} [IsLocallyNoetherian X] (f : X ⟶ Y) [IsFinite f] (x : X)
    (hclosed : IsClosed ({f x} : Set Y))
    (hfiber : f ⁻¹' {f x} = {x})
    (U : Y.Opens) (hU : IsAffineOpen U) (hx : f x ∈ U) :
    let V := f ⁻¹ᵁ U
    let I := ((hU.primeIdealOf ⟨f x, hx⟩).asIdeal).map (f.app U).hom
    ∃ E : AdicCompletion I Γ(X, V) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x),
      ∀ s, E (AdicCompletion.of I Γ(X, V) s) =
        AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) _
          ((X.presheaf.germ V x hx).hom s) := by
  let V := f ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage f
  let I := ((hU.primeIdealOf ⟨f x, hx⟩).asIdeal).map (f.app U).hom
  let P := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have hr : I.radical = P := s2e_affine_singleton_fiber_radical f x hclosed hfiber U hU hx
  letI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have H := s2e_adic_equiv_radical I (Ideal.fg_of_isNoetherianRing _)
  rw [hr] at H
  obtain ⟨e, he⟩ := H
  have hcx : IsClosed ({x} : Set X) := hfiber ▸ hclosed.preimage f.continuous
  obtain ⟨E, hE⟩ := s2e_affine_stalk_adic_equiv X V hV x hx hcx
  refine ⟨e.trans E, fun s => ?_⟩
  change E (e (AdicCompletion.of I Γ(X, V) s)) = _
  rw [he, hE]

#print axioms s2e_affine_singleton_fiber_adic_equiv
/-- Over a singleton closed fiber, the canonical germ map on the extended-ideal
adic ring is bijective.
Source: Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_affine_singleton_fiber_adic_map_bijective
    {X Y : Scheme} [IsLocallyNoetherian X] (f : X ⟶ Y) [IsFinite f] (x : X)
    (hclosed : IsClosed ({f x} : Set Y)) (hfiber : f ⁻¹' {f x} = {x})
    (U : Y.Opens) (hU : IsAffineOpen U) (hx : f x ∈ U) :
    let V := f ⁻¹ᵁ U
    let I := ((hU.primeIdealOf ⟨f x, hx⟩).asIdeal).map (f.app U).hom
    ∃ h : I.map (X.presheaf.germ V x hx).hom ≤
        IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      Function.Bijective (s2e_adic_ring_map I
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.germ V x hx).hom h) := by
  let V := f ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage f
  let I := ((hU.primeIdealOf ⟨f x, hx⟩).asIdeal).map (f.app U).hom
  let P := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let M := IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  let g := (X.presheaf.germ V x hx).hom
  have hr : I.radical = P := s2e_affine_singleton_fiber_radical f x hclosed hfiber U hU hx
  have hIP : I ≤ P := hr ▸ Ideal.le_radical
  have hPg : P.map g ≤ M := (s2e_affine_germ_map_point_ideal X V hV x hx).le
  have hIg : I.map g ≤ M := (Ideal.map_mono hIP).trans hPg
  refine ⟨hIg, ?_⟩
  letI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨k, hk⟩ := Ideal.exists_radical_pow_le_of_fg I (Ideal.fg_of_isNoetherianRing _)
  have hPI : P ^ (k + 1) ≤ I := by
    rw [← hr]
    exact (Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk
  have hb := s2e_adic_ring_map_bijective_of_power_le I P hIP (k + 1)
    (Nat.zero_lt_succ k) hPI
  have hcx : IsClosed ({x} : Set X) := hfiber ▸ hclosed.preimage f.continuous
  have hg := s2e_affine_germ_adic_map_bijective X V hV x hx hcx
  have hc := hg.comp hb
  have he : (fun z => s2e_adic_ring_map P M g hPg
      (s2e_adic_ring_map I P (RingHom.id _) (by simpa using hIP) z)) =
      s2e_adic_ring_map I M g hIg := by
    funext z
    exact s2e_adic_ring_map_comp I P M (RingHom.id _) _ g hPg hIg z
  change Function.Bijective (fun z => s2e_adic_ring_map P M g hPg
    (s2e_adic_ring_map I P (RingHom.id _) (by simpa using hIP) z)) at hc
  rw [he] at hc
  exact hc

#print axioms s2e_affine_singleton_fiber_adic_map_bijective
end HodgeLean.Foundations.Program

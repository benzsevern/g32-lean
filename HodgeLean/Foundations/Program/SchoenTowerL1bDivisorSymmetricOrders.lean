import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorFibreIncidenceOrder
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorFibreQuotientPrime
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorOrderCancellation
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorSpecializedPrime
import HodgeLean.Foundations.Program.SchoenTowerL1bKvalFactorial
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorPrimeLift
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorPrimePoint
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorFiniteCoheight
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCodimensionDVR
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCurvePoints
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIncidenceGermPrime
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorBranchNonzero
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductFunction

import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorGenericIncidence
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorGenericCoordinate
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorUnitOrder

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- Signed curve orders transport to the incidence equations of the actual symmetric quotient. -/
theorem s2v_l1b_divisor_symmetric_product_orders
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ σ, s2_permute Z (h + 1) σ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ σ, s2_permute Z (h + 1) σ ≫ f = f) → ∃! b : B ⟶ T, γ ≫ b = f)
    {J : Type} [Fintype J] (z : J → ComplexPoint Z) (hz : Function.Injective z)
    (n : J → ℕ) (m : ℕ) (v : Z.left.functionField) (hv : v ≠ 0)
    (hcurve : ∀ (z₀ : ComplexPoint Z) (C D : Z.left.presheaf.stalk z₀.underlying),
      C ≠ 0 → D ≠ 0 →
      v = algebraMap _ Z.left.functionField C / algebraMap _ Z.left.functionField D →
      ∀ π : Z.left.presheaf.stalk z₀.underlying, Prime π →
        Int.ModEq (m : ℤ)
          (((emultiplicity π C).toNat : ℤ) - ((emultiplicity π D).toNat : ℤ))
          (∑ j, if z j = z₀ then (n j : ℤ) else 0))
    (b : B.left.functionField)
    (hb : letI : IsDominant γ.left := n1bc_dominant_of_points_surjective γ hγsurj
      s2v_l1b_functionFieldPullback γ.left b = s2v_l1b_divisor_product_function Z (h + 1) v)
    (x : ComplexPoint B) (U : B.left.affineOpens) (hx : x.underlying ∈ U.1)
    (g : J → Γ(B.left, U))
    (hg : ∀ j, (s2c_branchIdeal Z B h γ (z j)).ideal U = Ideal.span {g j})
    (A D : B.left.presheaf.stalk x.underlying) (hA : A ≠ 0) (hD : D ≠ 0)
    (hbAD : b = algebraMap _ B.left.functionField A / algebraMap _ B.left.functionField D) :
    ∀ p : B.left.presheaf.stalk x.underlying, Prime p →
      Int.ModEq (m : ℤ)
        (((emultiplicity p A).toNat : ℤ) - ((emultiplicity p D).toNat : ℤ))
        (∑ j, (n j : ℤ) *
          ((emultiplicity p ((B.left.presheaf.germ U.1 x.underlying hx).hom (g j))).toNat : ℤ)) := by
  have hgne (j : J) : (B.left.presheaf.germ U.1 x.underlying hx).hom (g j) ≠ 0 :=
    s2v_l1b_divisor_branch_germ_ne_zero Z B hdimZ h γ hγsurj hγinv hγ (z j) x U hx (g j) (hg j)
  have hgprime (j : J) := s2v_l1b_divisor_incidence_germ_prime_or_unit Z B h γ (z j)
    x.underlying U hx (g j) (hg j) (hgne j)
  intro p hp
  letI : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  let R := B.left.presheaf.stalk x.underlying
  let P : Ideal R := Ideal.span {p}
  letI : P.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  let qSpec : Spec R := ⟨P, inferInstance⟩
  let q : B.left := (B.left.fromSpecStalk x.underlying) qSpec
  have hq : Order.coheight q = 1 := s2v_l1b_divisor_prime_stalk_point_coheight B.left x.underlying p hp
  letI : IsDominant γ.left := n1bc_dominant_of_points_surjective γ hγsurj
  obtain ⟨y, hy⟩ := s2_surjective_of_point_surjective γ hγsurj q
  have hycodim : Order.coheight y = 1 :=
    s2v_l1b_divisor_quasi_finite_coheight_one γ.left y (by rwa [hy])
  letI : IsDiscreteValuationRing ((g3_power Z (h + 1)).left.presheaf.stalk y) :=
    s2v_l1b_divisor_codimension_one_dvr (g3_power Z (h + 1)) y hycodim
  obtain ⟨φ, hφ, hφunit, hφfield⟩ := s2v_l1b_divisor_prime_stalk_lift γ.left
    x.underlying p qSpec rfl y hy
  have hφp : ¬ IsUnit (φ p) := fun hu => (hφunit p).mp hu (dvd_refl p)
  have hφp0 : φ p ≠ 0 := by simpa only [map_zero] using hφ.ne hp.ne_zero
  have hsource : algebraMap _ (g3_power Z (h + 1)).left.functionField (φ A) /
      algebraMap _ (g3_power Z (h + 1)).left.functionField (φ D) =
        s2v_l1b_divisor_product_function Z (h + 1) v := by
    rw [← hφfield, ← hφfield, ← map_div₀, ← hbAD]
    exact hb
  have hcoords (i : Fin (h + 1)) := s2v_l1b_divisor_curve_generic_or_complex Z hdimZ
    ((g3_proj Z (h + 1) i).left y)
  classical
  by_cases hall : ∀ i, (g3_proj Z (h + 1) i).left y = genericPoint Z.left
  · letI : UniqueFactorizationMonoid R := s2v_l1b_kval_stalk_factorial B x.underlying
    obtain ⟨u, hu, hueq⟩ := s2v_l1b_divisor_generic_product_unit Z (h + 1) y hall v hv
    have hzero := s2v_l1b_divisor_unit_fraction_order_zero φ hφ p hp hφunit
      A D hA hD u hu (hsource.trans hueq.symm)
    have hgen : γ.left y ⤳ x.underlying := by
      have H : q ∈ Set.range (B.left.fromSpecStalk x.underlying) := ⟨qSpec, rfl⟩
      rw [Scheme.range_fromSpecStalk] at H
      simpa only [hy, Set.mem_setOf_eq] using H
    have hyU : γ.left y ∈ U.1 := hgen.mem_open U.1.isOpen hx
    have hz (j : J) := s2v_l1b_divisor_generic_incidence_order_zero
      Z B hdimZ h γ hγsurj hγinv hγ x.underlying y hall p φ hφunit hφfield
      U hx hyU (z j) (g j) (hg j)
    simp only [hz, ENat.toNat_zero, Int.natCast_zero, mul_zero, Finset.sum_const_zero]
    rw [hzero]
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    obtain ⟨b₀, hb₀⟩ := (hcoords i).resolve_left hi
    have hyi : (g3_proj Z (h + 1) i).left y = b₀.underlying := hb₀.symm
    let f := (g3_proj Z (h + 1) i).left
    letI : IsDominant f := s2v_l1b_divisor_projection_dominant Z (h + 1) i
    letI : UniqueFactorizationMonoid R := s2v_l1b_kval_stalk_factorial B x.underlying
    letI : IsDiscreteValuationRing (Z.left.presheaf.stalk (f y)) := by
      have HD (q : Z.left) (he : b₀.underlying = q) :
          IsDiscreteValuationRing (Z.left.presheaf.stalk q) := by
        subst q
        exact s2v_l1b_divisor_curve_point_dvr Z hdimZ b₀
      exact HD (f y) hyi.symm
    have hgen : γ.left y ⤳ x.underlying := by
      have H : q ∈ Set.range (B.left.fromSpecStalk x.underlying) := ⟨qSpec, rfl⟩
      rw [Scheme.range_fromSpecStalk] at H
      simpa only [hy, Set.mem_setOf_eq] using H
    have hyU : γ.left y ∈ U.1 := hgen.mem_open U.1.isOpen hx
    have hgenq : q ⤳ x.underlying := by simpa only [hy] using hgen
    have hpp := s2v_l1b_divisor_specialized_prime B.left x.underlying p hp qSpec rfl hgenq
    have hpp' : Prime ((B.left.presheaf.stalkSpecializes hgen).hom p) := by
      have H (q' : B.left) (he : q = q') (hs : q' ⤳ x.underlying) :
          Prime ((B.left.presheaf.stalkSpecializes hs).hom p) := by
        subst q'
        exact hpp
      exact H (γ.left y) hy.symm hgen
    have hφpPrime : Prime (φ p) := by
      rw [s2v_l1b_divisor_specialization_stalk_lift γ.left x.underlying y φ hφfield hgen p]
      exact s2v_l1b_divisor_coordinate_fibre_quotient_prime Z B hdimZ h γ hγsurj hγinv hγ
        b₀ i y hycodim (by rwa [hy]) hyi _ hpp'
    obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible (Z.left.presheaf.stalk (f y))
    have hπ : Prime π := hπirr.prime
    let ψ := (f.stalkMap y).hom
    have hψ : Function.Injective ψ := s2v_l1b_divisor_dominant_stalk_injective f y
    have hψπ : Prime (ψ π) := s2v_l1b_divisor_prime_of_maximal_ideal_map ψ hψ
      (s2v_l1b_divisor_coordinate_maximal_ideal_prime Z hdimZ h b₀ i y hycodim hyi) π hπ
    have hψunit (r : Z.left.presheaf.stalk (f y)) : IsUnit (ψ r) ↔ ¬ π ∣ r := by
      rw [isUnit_map_iff]
      rw [← Ideal.mem_span_singleton, ← hπirr.maximalIdeal_eq]
      simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    obtain ⟨C, E, hE, hCE⟩ := IsFractionRing.div_surjective (Z.left.presheaf.stalk (f y)) v
    have hE0 : E ≠ 0 := nonZeroDivisors.ne_zero hE
    have hC0 : C ≠ 0 := by
      intro H
      rw [H, map_zero, zero_div] at hCE
      exact hv hCE.symm
    obtain ⟨u, hu, hueq⟩ := s2v_l1b_divisor_product_one_coordinate_unit Z (h + 1) y i
      (s2v_l1b_divisor_other_coordinates_generic Z hdimZ h b₀ i y hycodim hyi) v hv
    have heq := hsource.trans hueq
    rw [← hCE, map_div₀, s2v_l1b_divisor_generic_stalk, s2v_l1b_divisor_generic_stalk] at heq
    have hassoc := IsDiscreteValuationRing.associated_of_irreducible
      ((g3_power Z (h + 1)).left.presheaf.stalk y) hφpPrime.irreducible hψπ.irreducible
    have horder := s2v_l1b_divisor_parameter_order_cancellation φ ψ hφ hψ p hp π hπ
      hφunit hψunit hassoc A D hA hD C E hC0 hE0 u hu heq
    have HC (q : Z.left) (he : b₀.underlying = q) :
        ∀ (C E : Z.left.presheaf.stalk q), C ≠ 0 → E ≠ 0 →
          v = algebraMap _ Z.left.functionField C / algebraMap _ Z.left.functionField E →
          ∀ π : Z.left.presheaf.stalk q, Prime π →
            Int.ModEq (m : ℤ)
              (((emultiplicity π C).toNat : ℤ) - ((emultiplicity π E).toNat : ℤ))
              (∑ j, if z j = b₀ then (n j : ℤ) else 0) := by
      subst q
      exact hcurve b₀
    have hcurve' := HC (f y) hyi.symm C E hC0 hE0 hCE.symm π hπ
    have hsum : (∑ j, (n j : ℤ) *
        ((emultiplicity p ((B.left.presheaf.germ U.1 x.underlying hx).hom (g j))).toNat : ℤ)) =
          ∑ j, if z j = b₀ then (n j : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [s2v_l1b_divisor_coordinate_fibre_incidence_order Z B hdimZ h γ hγsurj hγinv hγ
        b₀ (z j) i x.underlying y hycodim hyi p hp φ hφunit hφfield U hx hyU (g j) (hg j) (hgne j)]
      split_ifs <;> simp
    rw [hsum, horder]
    exact hcurve'

end HodgeLean.Foundations.Program

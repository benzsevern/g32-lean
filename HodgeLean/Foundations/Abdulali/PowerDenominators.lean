import HodgeLean.Foundations.Program.G32Native.TypeIIIOrbitPullback

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program.TypeIIIPaper
namespace HodgeLean.Foundations.Abdulali

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- A finite family of rational endomorphisms has one common nonzero integral
multiplier, without any commutativity assumption on the endomorphism algebra.
Source: Mumford, Abelian Varieties, §19, rational endomorphisms as a localization. -/
theorem end0_family_integral_multiple {r : ℕ} (d : Fin r → AbelianEnd0 A) :
    ∃ (s : ℤ) (f : Fin r → AbelianEnd A), s ≠ 0 ∧
      ∀ i, s • d i = (1 : ℚ) ⊗ₜ[ℤ] f i := by
  classical
  choose s f hs hf using fun i => end0_integral_multiple A (d i)
  let N : ℤ := ∏ i, s i
  have hN : N ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hs i)
  have hd (i : Fin r) : s i ∣ N := Finset.dvd_prod_of_mem s (Finset.mem_univ i)
  choose k hk using hd
  refine ⟨N, fun i => k i • f i, hN, ?_⟩
  intro i
  rw [hk i, mul_comm, mul_smul, hf i, TensorProduct.tmul_smul]

variable {A} {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}

/-- Exterior pullback for a tuple of rational endomorphisms on arbitrary power
data. Its degree-one map is the sum of the actual projection pullbacks.
Source: Abdulali, Annals of Mathematics 155 (2002), Remark 4.2;
Mumford, Abelian Varieties, §19. -/
def rationalPowerPullback (power : AbelianPowerData A Y r)
    (d : Fin r → AbelianEnd0 A) (n : ℕ) : HQ A n →ₗ[ℚ] HQ Y n :=
  ((torusCohomology_cupProductOf Y).cupWedgeEquiv n).toLinearMap ∘ₗ
    exteriorPower.map n (∑ i, homPullback (power.proj i) 1 ∘ₗ
      (abelianEnd0Action A (d i)).unop) ∘ₗ
    ((torusCohomology_cupProductOf A).cupWedgeEquiv n).symm.toLinearMap

example (power : AbelianPowerData A Y r) (d : Fin r → AbelianEnd0 A) (n : ℕ) :
    rationalPowerPullback power d n =
      ((torusCohomology_cupProductOf Y).cupWedgeEquiv n).toLinearMap ∘ₗ
        exteriorPower.map n (∑ i, homPullback (power.proj i) 1 ∘ₗ
          (abelianEnd0Action A (d i)).unop) ∘ₗ
        ((torusCohomology_cupProductOf A).cupWedgeEquiv n).symm.toLinearMap := rfl

/-- Clearing a common denominator multiplies the degree-n pullback by its
n-th power, and gives the actual sum morphism on the specified power data.
Source: Mumford, Abelian Varieties, §19; exterior-power homogeneity. -/
theorem rationalPowerPullback_integral_multiple
    (power : AbelianPowerData A Y r) (d : Fin r → AbelianEnd0 A)
    (s : ℤ) (f : Fin r → AbelianEnd A)
    (hf : ∀ i, s • d i = (1 : ℚ) ⊗ₜ[ℤ] f i) (n : ℕ) :
    (s : ℚ) ^ n • rationalPowerPullback power d n =
      homPullback (power.sumMap f) n := by
  have h1 (i : Fin r) :
      (s : ℚ) • (abelianEnd0Action A (d i)).unop = abelianEndAction A (f i) := by
    have h := congrArg (fun x => (abelianEnd0Action A x).unop) (hf i)
    simpa only [← Int.cast_smul_eq_zsmul ℚ s, map_smul, MulOpposite.unop_smul,
      spec_g4_abelianEnd0Action_tmul, MulOpposite.unop_op, one_smul] using h
  have hsum : homPullback (power.sumMap f) 1 =
      (s : ℚ) • (∑ i, homPullback (power.proj i) 1 ∘ₗ
        (abelianEnd0Action A (d i)).unop) := by
    rw [spec_g4_homPullback_sumMap, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← h1 i, LinearMap.comp_smul]
  rw [spec_homPullback_eq_cupWedgeEquiv, hsum]
  simp only [rationalPowerPullback, exteriorPower_map_smul,
    LinearMap.smul_comp, LinearMap.comp_smul]

/-- Rational endomorphism tuples and integral sum morphisms span the same
pullbacks of every rational subspace, in every degree, on arbitrary power data.
Source: Abdulali, Annals of Mathematics 155 (2002), Remark 4.2;
Mumford, Abelian Varieties, §19, clearing denominators. -/
theorem rationalPowerPullback_span_eq (power : AbelianPowerData A Y r)
    (n : ℕ) (U : Submodule ℚ (HQ A n)) :
    (⨆ d : Fin r → AbelianEnd0 A, U.map (rationalPowerPullback power d n)) =
      ⨆ f : Fin r → AbelianEnd A, U.map (homPullback (power.sumMap f) n) := by
  apply le_antisymm
  · apply iSup_le
    intro d
    obtain ⟨s, f, hs, hf⟩ := end0_family_integral_multiple A d
    have hc : (s : ℚ) ^ n ≠ 0 := pow_ne_zero _ (Int.cast_ne_zero.mpr hs)
    rintro _ ⟨x, hx, rfl⟩
    apply (Submodule.smul_mem_iff _ hc).mp
    have h := LinearMap.congr_fun
      (rationalPowerPullback_integral_multiple power d s f hf n) x
    rw [LinearMap.smul_apply] at h
    rw [h]
    exact (le_iSup (fun f => U.map (homPullback (power.sumMap f) n)) f)
      ⟨x, hx, rfl⟩
  · apply iSup_le
    intro f
    have h := rationalPowerPullback_integral_multiple power
      (fun i => (1 : ℚ) ⊗ₜ[ℤ] f i) 1 f (fun _ => one_smul _ _ ) n
    simp only [Int.cast_one, one_pow, one_smul] at h
    rw [← h]
    exact le_iSup (fun d => U.map (rationalPowerPullback power d n)) _

end HodgeLean.Foundations.Abdulali

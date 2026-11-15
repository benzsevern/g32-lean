import HodgeLean.Adapters.IntersectionProductDefs
import HodgeLean.Adapters.IntersectionProductDivisorLocal
import HodgeLean.Adapters.IntersectionProductDivisorCycle
import HodgeLean.Adapters.IntersectionProductFibreTor
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import HodgeLean.Adapters.IntersectionProductLocalBaseChange
import HodgeLean.Adapters.IntersectionProductMovingRoberts
import HodgeLean.Adapters.IntersectionProductCycle
import HodgeLean.Adapters.IntersectionProductSpectralHelpers
import HodgeLean.Adapters.IntersectionProductDivisorCycle
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Data.Finset.NatAntidiagonal

/-! # Global assembly for Serre's local intersection product

This file isolates the two global assembly steps needed after the local associativity and
proper-pushforward multiplicity formulas have been established.

Source: Fulton, *Intersection Theory*, second edition, Proposition 8.1.1 and §20.4;
Serre, *Algèbre locale, multiplicités*, Chapitre V, §B–C. -/

noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped TensorProduct

namespace HodgeLean.Adapters

universe u v w x

/-- IntersectionProductLoc2 S1: the length Euler characteristic through degree `m`.
For homology supported in degrees at most `m`, this is the full Euler characteristic. -/
def a3i_complexEuler {R : Type u} [CommRing R]
    (m : ℕ) (C : ChainComplex (ModuleCat.{u} R) ℕ) : ℤ :=
  ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
    ((Module.length R (C.homology i)).toNat : ℤ)

/-- IntersectionProductLoc2 S1: additivity for a short exact sequence of complexes,
with finite homology lengths and vanishing of the upper boundary term. -/
theorem a3i_complex_euler {R : Type u} [CommRing R]
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact) (m : ℕ)
    (h₁ : ∀ i ≤ m, Module.length R (S.X₁.homology i) ≠ ⊤)
    (h₂ : ∀ i ≤ m, Module.length R (S.X₂.homology i) ≠ ⊤)
    (h₃ : ∀ i ≤ m, Module.length R (S.X₃.homology i) ≠ ⊤)
    (htop : IsZero (S.X₃.homology (m + 1))) :
    a3i_complexEuler m S.X₂ = a3i_complexEuler m S.X₁ + a3i_complexEuler m S.X₃ := by
  unfold a3i_complexEuler
  let f := fun i : ℕ => (HomologicalComplex.homologyMap S.f i).hom
  let g := fun i : ℕ => (HomologicalComplex.homologyMap S.g i).hom
  let δ := fun i : ℕ => (hS.δ (i + 1) i (by simp)).hom
  have ex₁ : ∀ i, LinearMap.range (δ i) = LinearMap.ker (f i) := fun i =>
    (hS.homology_exact₁ (i + 1) i (by simp)).moduleCat_range_eq_ker
  have ex₂ : ∀ i, LinearMap.range (f i) = LinearMap.ker (g i) := fun i =>
    (hS.homology_exact₂ i).moduleCat_range_eq_ker
  have ex₃ : ∀ i, LinearMap.range (g (i + 1)) = LinearMap.ker (δ i) := fun i =>
    (hS.homology_exact₃ (i + 1) i (by simp)).moduleCat_range_eq_ker
  let k : ℕ → ℤ := fun i => ((Module.length R (LinearMap.ker (f i))).toNat : ℤ)
  let p : ℕ → ℤ := fun i => ((Module.length R (LinearMap.range (f i))).toNat : ℤ)
  let q : ℕ → ℤ := fun i => ((Module.length R (LinearMap.range (g i))).toNat : ℤ)
  have key := a3s_alt_sum3
    (fun i => ((Module.length R (S.X₁.homology i)).toNat : ℤ))
    (fun i => ((Module.length R (S.X₂.homology i)).toNat : ℤ))
    (fun i => ((Module.length R (S.X₃.homology i)).toNat : ℤ))
    k p q m
    (fun i hi => a3s_toNat_add (a3e_length_eq_ker_add_range (f i)) (h₁ i hi))
    (fun i hi => by
      have := a3s_toNat_add (a3e_length_eq_ker_add_range (g i)) (h₂ i hi)
      rw [this, ← ex₂ i])
    (by
      have : Epi S.g := hS.epi_g
      have : Epi (S.g.f 0) := inferInstance
      have : Epi (HomologicalComplex.homologyMap S.g 0) :=
        HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by simp)
      have hsurj := (ModuleCat.epi_iff_surjective (HomologicalComplex.homologyMap S.g 0)).1 inferInstance
      change _ = ((Module.length R (LinearMap.range (g 0))).toNat : ℤ)
      rw [LinearMap.range_eq_top.mpr hsurj, Module.length_top])
    (fun i hi => by
      refine (a3s_toNat_add (a3e_length_eq_ker_add_range (δ i)) (h₃ (i + 1) hi)).trans ?_
      rw [← ex₃ i, ex₁ i])
    m le_rfl
  have hk : k m = 0 := by
    have hδ : hS.δ (m + 1) m (by simp) = 0 := htop.eq_of_src _ _
    have : LinearMap.ker (f m) = ⊥ := by
      rw [← ex₁ m]
      change LinearMap.range (hS.δ (m + 1) m (by simp)).hom = ⊥
      rw [hδ, ModuleCat.hom_zero, LinearMap.range_zero]
    have h0 : Module.length R (LinearMap.ker (f m)) = 0 := by
      rw [this]
      exact Module.length_bot
    simp only [k, h0, ENat.toNat_zero, Nat.cast_zero]
  rw [key, hk, mul_zero, sub_zero]


/-- IntersectionProductLoc2 S2: a projective resolution computes the length Euler
characteristic defining the Tor pairing. -/
theorem a3i_tor_eq_euler {R : Type u} [CommRing R] (M N : ModuleCat.{u} R)
    (Q : ProjectiveResolution N) (m : ℕ) :
    a3s_chi m M N = a3i_complexEuler m (a3c_tensC M Q.complex) := by
  unfold a3s_chi a3i_complexEuler
  exact Finset.sum_congr rfl fun i _ => by
    rw [(a3c_torIso M N Q i).toLinearEquiv.length_eq]

/-- IntersectionProductLoc2 S2: the frozen multiplicity is the Euler characteristic
of a quotient tensored with a resolution of the other quotient. -/
theorem a3i_serreMult_eq_euler (X : Scheme.{u}) (z v w : X)
    (Q : ProjectiveResolution
      (ModuleCat.of (X.presheaf.stalk z) (X.presheaf.stalk z ⧸ a3i_stalkIdeal X z w))) :
    a3i_serreMult X z v w = a3i_complexEuler (Order.coheight z).toNat
      (a3c_tensC (ModuleCat.of (X.presheaf.stalk z)
        (X.presheaf.stalk z ⧸ a3i_stalkIdeal X z v)) Q.complex) :=
  a3i_tor_eq_euler _ _ Q _

/-- IntersectionProductLoc2 P1: flat extension of both Tor arguments. -/
theorem a3i_local_flat_tor_basechange {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (M N : ModuleCat.{u} A) (i : ℕ) :
    Nonempty (((Tor (ModuleCat.{u} B) i).obj
      ((ModuleCat.extendScalars.{u, u, u} f).obj M)).obj
        ((ModuleCat.extendScalars.{u, u, u} f).obj N) ≅
      (ModuleCat.extendScalars.{u, u, u} f).obj
        (((Tor (ModuleCat.{u} A) i).obj M).obj N)) :=
  a3i_flat_tor_basechange f hf M N i

/-- IntersectionProductLoc2 S3: equicharacteristic vanishing for the local rings of
smooth complex varieties, through the diagonal and regular-sequence argument. -/
theorem a3i_local_vanishing (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (T : X.left) (M N : Type) [AddCommGroup M] [Module (X.left.presheaf.stalk T) M]
    [Module.Finite (X.left.presheaf.stalk T) M] [AddCommGroup N]
    [Module (X.left.presheaf.stalk T) N] [Module.Finite (X.left.presheaf.stalk T) N]
    (hsupp : ∀ P ∈ Module.support (X.left.presheaf.stalk T) M,
      ∀ Q ∈ Module.support (X.left.presheaf.stalk T) N,
      ∀ 𝔓 : PrimeSpectrum (X.left.presheaf.stalk T), P ≤ 𝔓 → Q ≤ 𝔓 →
        𝔓 = IsLocalRing.closedPoint (X.left.presheaf.stalk T))
    (hdimMN : ∀ P ∈ Module.support (X.left.presheaf.stalk T) M,
      ∀ Q ∈ Module.support (X.left.presheaf.stalk T) N,
      ringKrullDim (X.left.presheaf.stalk T ⧸ P.asIdeal) +
          ringKrullDim (X.left.presheaf.stalk T ⧸ Q.asIdeal) <
        ringKrullDim (X.left.presheaf.stalk T))
    (m : ℕ) (hm : ringKrullDim (X.left.presheaf.stalk T) ≤ m) :
    a3s_chi m (ModuleCat.of (X.left.presheaf.stalk T) M)
      (ModuleCat.of (X.left.presheaf.stalk T) N) = 0 :=
  a3w_vanishing_stalk X T M N hsupp hdimMN m hm

/-- IntersectionProductLoc2 S4: the coefficient of the homology cycle of a complex
at a prime, with degrees truncated at `n`. -/
def a3i_complexCycleCoeff {B : Type} [CommRing B] (n : ℕ)
    (C : ChainComplex (ModuleCat.{0} B) ℕ) (P : PrimeSpectrum B) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * ((a3e_locLen P (C.homology i)).toNat : ℤ)

/-- IntersectionProductLoc2 S4a: prime-filtration expansion of the homology pairing.
The vanishing input is supplied by S3 when the omitted primes have smaller dimension. -/
theorem a3i_homology_topCycle {B : Type} [CommRing B] [IsRegularLocalRing B]
    (m n : ℕ) (hm : ringKrullDim B < (m + 1 : ℕ)) (N : ModuleCat.{0} B)
    [Module.Finite B N] (Z : Set (PrimeSpectrum B)) (F : Finset (PrimeSpectrum B))
    (hfin : ∀ P ∈ Z, Module.annihilator B N ≤ P.asIdeal → P = IsLocalRing.closedPoint B)
    (hmin : ∀ P ∈ Z, ∀ D ∈ F, P ≤ D → P = D)
    (hlow : ∀ P ∈ Z, P ∉ F → a3s_chi m (ModuleCat.of B (B ⧸ P.asIdeal)) N = 0)
    (C : ChainComplex (ModuleCat.{0} B) ℕ)
    (hfinite : ∀ i, Module.Finite B (C.homology i))
    (hsupport : ∀ i, Module.support B (C.homology i) ⊆ Z) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * a3s_chi m (C.homology i) N) =
      ∑ P ∈ F, a3i_complexCycleCoeff n C P * a3s_chi m (ModuleCat.of B (B ⧸ P.asIdeal)) N := by
  classical
  have hdev (i : ℕ) := by
    have := hfinite i
    exact (a3w_chi_devissage_top m hm N Z F hfin hmin hlow
      (C.homology i) (hsupport i)).1
  simp only [hdev, Finset.mul_sum, a3i_complexCycleCoeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro i hi
  ring

namespace IntersectionProductRing

theorem meetProperly_symm (X : Scheme.{u}) (u v : X) (h : a3i_MeetProperly X u v) :
    a3i_MeetProperly X v u := by
  unfold a3i_MeetProperly at *
  rw [sup_comm]
  intro w hw
  rw [add_comm]
  exact h w hw

theorem cyclesMeetProperly_symm (X : Scheme.{u}) (c d : AlgebraicCycle X ℚ)
    (h : a3i_CyclesMeetProperly X c d) : a3i_CyclesMeetProperly X d c := by
  intro u v hu hv
  exact meetProperly_symm X v u (h v u hv hu)

theorem cyclesMeetProperly_sum_left (X : Scheme.{u}) {s : Finset X}
    (g : X → AlgebraicCycle X ℚ) (d : AlgebraicCycle X ℚ)
    (h : ∀ x ∈ s, a3i_CyclesMeetProperly X (g x) d) :
    a3i_CyclesMeetProperly X (∑ x ∈ s, g x) d := by
  intro u v hu hv
  obtain ⟨x, hx, hxu⟩ := a3m_exists_of_sum_apply_ne_zero s g u hu
  exact h x hx u v (fun h0 => hxu (by simp [h0])) hv

theorem cyclesMeetProperly_add_left (X : Scheme.{u}) (c c' d : AlgebraicCycle X ℚ)
    (h : a3i_CyclesMeetProperly X c d) (h' : a3i_CyclesMeetProperly X c' d) :
    a3i_CyclesMeetProperly X (c + c') d := by
  intro u v hu hv
  by_cases hcu : c u = 0
  · exact h' u v (fun h0 => hu (by simp [hcu, h0])) hv
  · exact h u v hcu hv

theorem moving_total (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (α β : AlgebraicCycle X.left ℚ) :
    ∃ α', α' - α ∈ a3i_ratAll X.left ∧ a3i_CyclesMeetProperly X.left α' β := by
  classical
  set s := (a3c_support_finite α).toFinset
  have hs : ∀ x ∉ s, α x = 0 := fun x hx => by simpa [s] using hx
  have hp : ∀ x : X.left,
      Function.locallyFinsuppWithin.single x (α x) ∈
        a3i_codimCycles X.left ℚ (Order.coheight x).toNat := by
    intro x y hy
    rw [Function.locallyFinsuppWithin.single_apply] at hy
    split_ifs at hy with hxy
    · subst y
      exact (ENat.coe_toNat (a3c_coheight_ne_top X.left x)).symm
    · exact (hy rfl).elim
  choose g hgcod hgrat hgproper using fun x =>
    a3m_moving X (Order.coheight x).toNat
      (Function.locallyFinsuppWithin.single x (α x)) β (hp x)
  refine ⟨∑ x ∈ s, g x, ?_, cyclesMeetProperly_sum_left X.left g β fun x _ => hgproper x⟩
  have hdec := a3m_eq_sum_single α s hs
  have hsingle : ∀ x : X.left,
      a3m_smul (α x) (Function.locallyFinsuppWithin.single x 1) =
        Function.locallyFinsuppWithin.single x (α x) := by
    intro x
    ext y
    simp [a3m_smul, Function.locallyFinsuppWithin.single_apply]
  rw [hdec]
  simp_rw [hsingle]
  rw [← Finset.sum_sub_distrib]
  exact AddSubgroup.sum_mem _ fun x hx => hgrat x

theorem moving_total_pair (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (α β γ : AlgebraicCycle X.left ℚ) :
    ∃ α', α' - α ∈ a3i_ratAll X.left ∧
      a3i_CyclesMeetProperly X.left α' β ∧ a3i_CyclesMeetProperly X.left α' γ := by
  classical
  let s := ((a3c_support_finite β).union (a3c_support_finite γ)).toFinset
  let d : AlgebraicCycle X.left ℚ :=
    ∑ x ∈ s, Function.locallyFinsuppWithin.single x 1
  obtain ⟨α', hr, hp⟩ := moving_total X α d
  refine ⟨α', hr, ?_, ?_⟩ <;> intro x y hx hy <;> apply hp x y hx
  · have hyS : y ∈ s := by
      simp only [s, Set.Finite.mem_toFinset, Set.mem_union, Function.mem_support]
      exact Or.inl hy
    simp only [d, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single y (fun z _ hzy => by
      simp [Function.locallyFinsuppWithin.single_apply, Ne.symm hzy]) (fun h => (h hyS).elim)]
    simp
  · have hyS : y ∈ s := by
      simp only [s, Set.Finite.mem_toFinset, Set.mem_union, Function.mem_support]
      exact Or.inr hy
    simp only [d, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single y (fun z _ hzy => by
      simp [Function.locallyFinsuppWithin.single_apply, Ne.symm hzy]) (fun h => (h hyS).elim)]
    simp

/-- Move one cycle so that it meets each of three prescribed cycles properly. -/
theorem IntersectionProductProj_moving_total_triple (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (α β γ δ : AlgebraicCycle X.left ℚ) :
    ∃ α', α' - α ∈ a3i_ratAll X.left ∧
      a3i_CyclesMeetProperly X.left α' β ∧
      a3i_CyclesMeetProperly X.left α' γ ∧
      a3i_CyclesMeetProperly X.left α' δ := by
  classical
  let s := (((a3c_support_finite β).union (a3c_support_finite γ)).union
    (a3c_support_finite δ)).toFinset
  let d : AlgebraicCycle X.left ℚ :=
    ∑ x ∈ s, Function.locallyFinsuppWithin.single x 1
  obtain ⟨α', hr, hp⟩ := moving_total X α d
  refine ⟨α', hr, ?_, ?_, ?_⟩ <;> intro x y hx hy <;> apply hp x y hx
  · have hyS : y ∈ s := by
      simp only [s, Set.Finite.mem_toFinset, Set.mem_union, Function.mem_support]
      exact Or.inl (Or.inl hy)
    simp only [d, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single y (fun z _ hzy => by
      simp [Function.locallyFinsuppWithin.single_apply, Ne.symm hzy]) (fun h => (h hyS).elim)]
    simp
  · have hyS : y ∈ s := by
      simp only [s, Set.Finite.mem_toFinset, Set.mem_union, Function.mem_support]
      exact Or.inl (Or.inr hy)
    simp only [d, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single y (fun z _ hzy => by
      simp [Function.locallyFinsuppWithin.single_apply, Ne.symm hzy]) (fun h => (h hyS).elim)]
    simp
  · have hyS : y ∈ s := by
      simp only [s, Set.Finite.mem_toFinset, Set.mem_union, Function.mem_support]
      exact Or.inr hy
    simp only [d, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single y (fun z _ hzy => by
      simp [Function.locallyFinsuppWithin.single_apply, Ne.symm hzy]) (fun h => (h hyS).elim)]
    simp

end IntersectionProductRing

/-- A quasi-isomorphism preserves every truncated length Euler characteristic.
IntersectionProductSE. -/
theorem a3i_complexEuler_eq_of_quasiIso {R : Type u} [CommRing R]
    {C D : ChainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D) [QuasiIso f] (m : ℕ) :
    a3i_complexEuler m C = a3i_complexEuler m D := by
  unfold a3i_complexEuler
  apply Finset.sum_congr rfl
  intro i _
  rw [(isoOfQuasiIsoAt f i).toLinearEquiv.length_eq]

open MonoidalCategory HomologicalComplex in
set_option backward.isDefEq.respectTransparency false in
/-- The degreewise tensor with a complex concentrated in degree zero.
IntersectionProductSE. -/
def a3i_singleTensorDegreeIso {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj ((single (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).obj M) C).X n ≅
      M ⊗ C.X n := by
  let S := (single (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).obj M
  let f : (HomologicalComplex.tensorObj S C).X n ⟶ M ⊗ C.X n :=
    mapBifunctorDesc (fun i j h => if hi : i = 0 then
      ((singleObjXIsoOfEq (ComplexShape.down ℕ) 0 M i hi).hom ▷ C.X j) ≫
        (M ◁ (C.XIsoOfEq (by simpa [hi] using h)).hom) else 0)
  let g : M ⊗ C.X n ⟶ (HomologicalComplex.tensorObj S C).X n :=
    ((singleObjXSelf (ComplexShape.down ℕ) 0 M).inv ▷ C.X n) ≫
      ιTensorObj S C 0 n n (zero_add n)
  refine ⟨f, g, ?_, ?_⟩
  · apply mapBifunctor.hom_ext
    intro i j h
    dsimp only [f]
    rw [← Category.assoc, ι_mapBifunctorDesc]
    by_cases hi : i = 0
    · subst i
      have hj : j = n := by simpa using h
      subst j
      simp [g, S, singleObjXIsoOfEq]
    · rw [dite_eq_right hi, zero_comp]
      have hz := (tensorRight (C.X j)).map_isZero
        (isZero_single_obj_X (ComplexShape.down ℕ) 0 M i hi)
      exact hz.eq_of_src _ _
  · dsimp only [g, f]
    rw [Category.assoc, ι_mapBifunctorDesc, dite_eq_left rfl]
    simp [singleObjXIsoOfEq]

open MonoidalCategory HomologicalComplex in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero tensor identification respects differentials.
IntersectionProductSE. -/
theorem a3i_singleTensorDegreeIso_inv_comm {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (C : ChainComplex (ModuleCat.{u} R) ℕ) (i j : ℕ) :
    (a3i_singleTensorDegreeIso M C i).inv ≫
        (HomologicalComplex.tensorObj
          ((single (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).obj M) C).d i j =
      (a3c_tensC M C).d i j ≫ (a3i_singleTensorDegreeIso M C j).inv := by
  let S := (single (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).obj M
  simp only [a3i_singleTensorDegreeIso, singleObjXSelf, singleObjXIsoOfEq,
    eqToIso_refl, Iso.refl_inv]
  erw [id_whiskerRight, id_whiskerRight]
  simp only [Category.id_comp]
  change ιTensorObj S C 0 i i (zero_add i) ≫ (HomologicalComplex.tensorObj S C).d i j =
    (M ◁ C.d i j) ≫ ιTensorObj S C 0 j j (zero_add j)
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp), zero_add,
      mapBifunctor.d₂_eq _ _ _ _ _ hij _ (by simp)]
    simp
    rfl
  · rw [HomologicalComplex.shape _ _ _ hij, HomologicalComplex.shape C _ _ hij]
    simp

/-- Tensoring a degree-zero complex agrees with termwise tensoring.
IntersectionProductSE. -/
def a3i_singleTensorIso {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex.tensorObj
      ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).obj M) C ≅
      a3c_tensC M C :=
  (HomologicalComplex.Hom.isoOfComponents (fun i => (a3i_singleTensorDegreeIso M C i).symm)
    (fun i j _ => a3i_singleTensorDegreeIso_inv_comm M C i j)).symm

/-- The augmentation from the tensor of a resolution with a complex to
termwise tensoring with the resolved module. IntersectionProductSE. -/
def a3i_tensorResolutionAugmentation {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex.tensorObj P.complex C ⟶ a3c_tensC M C :=
  HomologicalComplex.tensorHom P.π (𝟙 C) ≫ (a3i_singleTensorIso M C).hom

open MonoidalCategory in
/-- Tensoring a resolution augmentation with a projective module preserves its
quasi-isomorphism. IntersectionProductSE. -/
theorem a3i_tensorRight_resolution_quasiIso {R : Type u} [CommRing R]
    (M V : ModuleCat.{u} R) (P : ProjectiveResolution M) [Projective V] :
    QuasiIso (((tensorRight V).mapHomologicalComplex (ComplexShape.down ℕ)).map P.π) := by
  infer_instance

open MonoidalCategory HomologicalComplex in
/-- Projection onto one bidegree of a tensor complex. IntersectionProductSE. -/
def a3i_tensorProjection {R : Type u} [CommRing R]
    (C D : ChainComplex (ModuleCat.{u} R) ℕ) (i j n : ℕ) :
    (HomologicalComplex.tensorObj C D).X n ⟶ C.X i ⊗ D.X j :=
  mapBifunctorDesc (fun a b _ => if h : a = i ∧ b = j then
    eqToHom (by obtain ⟨rfl, rfl⟩ := h; rfl) else 0)

open MonoidalCategory HomologicalComplex in
/-- A tensor summand projects identically onto its own bidegree and to zero
onto every other bidegree. IntersectionProductSE. -/
theorem a3i_ι_tensorProjection {R : Type u} [CommRing R]
    (C D : ChainComplex (ModuleCat.{u} R) ℕ) (a b i j n : ℕ) (h : a + b = n) :
    ιTensorObj C D a b n h ≫ a3i_tensorProjection C D i j n =
      if e : a = i ∧ b = j then eqToHom (by obtain ⟨rfl, rfl⟩ := e; rfl) else 0 := by
  apply ι_mapBifunctorDesc

open MonoidalCategory HomologicalComplex in
/-- The bidegree inclusions and projections reconstruct a tensor degree.
IntersectionProductSE. -/
theorem a3i_tensor_sum_projection {R : Type u} [CommRing R]
    (C D : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).attach,
      a3i_tensorProjection C D p.val.1 p.val.2 n ≫
        ιTensorObj C D p.val.1 p.val.2 n (Finset.HasAntidiagonal.mem_antidiagonal.mp p.property)) =
      𝟙 ((HomologicalComplex.tensorObj C D).X n) := by
  classical
  apply mapBifunctor.hom_ext
  intro a b h
  rw [Preadditive.comp_sum]
  rw [Finset.sum_eq_single ⟨(a, b), Finset.HasAntidiagonal.mem_antidiagonal.mpr h⟩]
  · rw [← Category.assoc, a3i_ι_tensorProjection]
    simp
  · intro p _ hp
    rw [← Category.assoc, a3i_ι_tensorProjection, dite_eq_right, zero_comp]
    intro e
    apply hp
    apply Subtype.ext
    exact Prod.ext e.1.symm e.2.symm
  · intro hnot
    exact (hnot (Finset.mem_attach _ _)).elim

open MonoidalCategory HomologicalComplex in
/-- Horizontal differentiation followed by a bidegree projection.
IntersectionProductSE. -/
theorem a3i_tensor_D₁_projection {R : Type u} [CommRing R]
    (C D : ChainComplex (ModuleCat.{u} R) ℕ) (i j n : ℕ) (h : i + j = n) :
    mapBifunctor.D₁ C D (curriedTensor _) (ComplexShape.down ℕ) (n + 1) n ≫
      a3i_tensorProjection C D i j n =
    a3i_tensorProjection C D (i + 1) j (n + 1) ≫ (C.d (i + 1) i ▷ D.X j) := by
  apply mapBifunctor.hom_ext
  intro a b hab
  rw [← Category.assoc, mapBifunctor.ι_D₁, ← Category.assoc, a3i_ι_tensorProjection]
  cases a with
  | zero =>
    rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp)]
    simp
  | succ a =>
    have hab' : a + b = n := by change a + 1 + b = n + 1 at hab; omega
    rw [mapBifunctor.d₁_eq _ _ _ _ (by simp) b n hab']
    change ((1 : ℤˣ) • ((C.d (a + 1) a ▷ D.X b) ≫ ιTensorObj C D a b n hab')) ≫
      a3i_tensorProjection C D i j n = _
    rw [one_smul, Category.assoc, a3i_ι_tensorProjection]
    by_cases ha : a = i
    · subst a
      have hb : b = j := by omega
      subst b
      simp
    · simp [ha]

open MonoidalCategory HomologicalComplex in
/-- Vertical differentiation followed by a bidegree projection.
IntersectionProductSE. -/
theorem a3i_tensor_D₂_projection {R : Type u} [CommRing R]
    (C D : ChainComplex (ModuleCat.{u} R) ℕ) (i j n : ℕ) (h : i + j = n) :
    mapBifunctor.D₂ C D (curriedTensor _) (ComplexShape.down ℕ) (n + 1) n ≫
      a3i_tensorProjection C D i j n =
    ((-1 : ℤˣ) ^ i) • (a3i_tensorProjection C D i (j + 1) (n + 1) ≫
      (C.X i ◁ D.d (j + 1) j)) := by
  apply mapBifunctor.hom_ext
  intro a b hab
  rw [← Category.assoc, mapBifunctor.ι_D₂, Linear.comp_units_smul,
    ← Category.assoc, a3i_ι_tensorProjection]
  cases b with
  | zero =>
    rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp)]
    simp
  | succ b =>
    have hab' : a + b = n := by change a + (b + 1) = n + 1 at hab; omega
    rw [mapBifunctor.d₂_eq _ _ _ _ a (by simp) n hab']
    change (((-1 : ℤˣ) ^ a) • ((C.X a ◁ D.d (b + 1) b) ≫
      ιTensorObj C D a b n hab')) ≫ a3i_tensorProjection C D i j n = _
    rw [Linear.units_smul_comp, Category.assoc, a3i_ι_tensorProjection]
    by_cases ha : a = i
    · subst a
      have hb : b = j := by omega
      subst b
      simp
    · simp [ha]

open MonoidalCategory HomologicalComplex in
/-- The two adjacent bidegrees contributing to a tensor differential.
IntersectionProductSE. -/
theorem a3i_tensor_d_projection {R : Type u} [CommRing R]
    (C D : ChainComplex (ModuleCat.{u} R) ℕ) (i j n m : ℕ)
    (h : i + j = m) (hn : m + 1 = n) :
    (HomologicalComplex.tensorObj C D).d n m ≫ a3i_tensorProjection C D i j m =
      a3i_tensorProjection C D (i + 1) j n ≫ (C.d (i + 1) i ▷ D.X j) +
      ((-1 : ℤˣ) ^ i) • (a3i_tensorProjection C D i (j + 1) n ≫
        (C.X i ◁ D.d (j + 1) j)) := by
  subst n
  rw [mapBifunctor.d_eq, Preadditive.add_comp,
    a3i_tensor_D₁_projection C D i j m h, a3i_tensor_D₂_projection C D i j m h]

open HomologicalComplex in
/-- An element of a tensor degree vanishes when all its components vanish.
IntersectionProductSE. -/
theorem a3i_tensor_eq_zero {R : Type u} [CommRing R]
    (C D : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (x : (HomologicalComplex.tensorObj C D).X n)
    (hx : ∀ i j, i + j = n → a3i_tensorProjection C D i j n x = 0) : x = 0 := by
  have he := congrArg (fun f : (HomologicalComplex.tensorObj C D).X n ⟶
      (HomologicalComplex.tensorObj C D).X n => f.hom x)
    (a3i_tensor_sum_projection C D n)
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at he
  have hz : (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).attach,
      (ιTensorObj C D p.val.1 p.val.2 n
        (Finset.HasAntidiagonal.mem_antidiagonal.mp p.property))
        (a3i_tensorProjection C D p.val.1 p.val.2 n x)) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    rw [hx _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mp p.property)]
    exact map_zero _
  exact he.symm.trans hz

open MonoidalCategory HomologicalComplex in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor augmentation is the degree-zero horizontal projection followed
by the module augmentation. IntersectionProductSE. -/
theorem a3i_tensorResolutionAugmentation_f {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (a3i_tensorResolutionAugmentation M P C).f n =
      a3i_tensorProjection P.complex C 0 n n ≫ (P.π.f 0 ▷ C.X n) := by
  apply mapBifunctor.hom_ext
  intro a b hab
  change ιTensorObj P.complex C a b n hab ≫
      ((HomologicalComplex.tensorHom P.π (𝟙 C)).f n ≫ (a3i_singleTensorDegreeIso M C n).hom) = _
  conv_rhs => rw [← Category.assoc, a3i_ι_tensorProjection]
  rw [← Category.assoc, ι_mapBifunctorMap, Category.assoc]
  cases a with
  | zero =>
    have hb : b = n := by simpa using hab
    subst b
    simp [a3i_singleTensorDegreeIso, singleObjXIsoOfEq]
  | succ a =>
    rw [P.π_f_succ]
    simp

open MonoidalCategory HomologicalComplex in
/-- The horizontal leading component of a boundary from one tensor summand.
IntersectionProductSE. -/
theorem a3i_tensor_boundary_same {R : Type u} [CommRing R]
    (C D : ChainComplex (ModuleCat.{u} R) ℕ) (k j n : ℕ) (h : k + j = n) :
    ιTensorObj C D (k + 1) j (n + 1) (by omega) ≫
      (HomologicalComplex.tensorObj C D).d (n + 1) n ≫
        a3i_tensorProjection C D k j n = C.d (k + 1) k ▷ D.X j := by
  rw [a3i_tensor_d_projection C D k j (n + 1) n h rfl,
    Preadditive.comp_add, Linear.comp_units_smul,
    ← Category.assoc, a3i_ι_tensorProjection,
    ← Category.assoc, a3i_ι_tensorProjection]
  simp

open MonoidalCategory HomologicalComplex in
/-- A boundary from horizontal degree `k + 1` has no components below `k`.
IntersectionProductSE. -/
theorem a3i_tensor_boundary_below {R : Type u} [CommRing R]
    (C D : ChainComplex (ModuleCat.{u} R) ℕ) (k j n : ℕ) (h : k + j = n)
    (i b : ℕ) (hib : i + b = n) (hik : i < k) :
    ιTensorObj C D (k + 1) j (n + 1) (by omega) ≫
      (HomologicalComplex.tensorObj C D).d (n + 1) n ≫
        a3i_tensorProjection C D i b n = 0 := by
  rw [a3i_tensor_d_projection C D i b (n + 1) n hib rfl,
    Preadditive.comp_add, Linear.comp_units_smul,
    ← Category.assoc, a3i_ι_tensorProjection,
    ← Category.assoc, a3i_ι_tensorProjection]
  simp [show k ≠ i by omega, show k + 1 ≠ i by omega]

open MonoidalCategory HomologicalComplex in
set_option backward.isDefEq.respectTransparency false in
/-- Positive horizontal summands vanish under the tensor augmentation.
IntersectionProductSE. -/
theorem a3i_tensorResolutionAugmentation_ι_succ {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (k j n : ℕ) (h : k + 1 + j = n) :
    ιTensorObj P.complex C (k + 1) j n h ≫
      (a3i_tensorResolutionAugmentation M P C).f n = 0 := by
  rw [a3i_tensorResolutionAugmentation_f, ← Category.assoc, a3i_ι_tensorProjection]
  simp

open MonoidalCategory HomologicalComplex in
set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Cycles in the kernel of the tensor augmentation are boundaries in that
kernel. IntersectionProductSE. -/
theorem a3i_tensorResolution_kernel_lift {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (D : ChainComplex (ModuleCat.{u} R) ℕ) (hD : ∀ j, Projective (D.X j))
    (n : ℕ) (x : (HomologicalComplex.tensorObj P.complex D).X n)
    (hc : ∀ t, (HomologicalComplex.tensorObj P.complex D).d n t x = 0)
    (ha : (a3i_tensorResolutionAugmentation M P D).f n x = 0) :
    ∃ y : (HomologicalComplex.tensorObj P.complex D).X (n + 1),
      (HomologicalComplex.tensorObj P.complex D).d (n + 1) n y = x ∧
      (a3i_tensorResolutionAugmentation M P D).f (n + 1) y = 0 := by
  let T := HomologicalComplex.tensorObj P.complex D
  let A := a3i_tensorResolutionAugmentation M P D
  have aux : ∀ l k : ℕ, k + l = n + 1 → ∀ z : T.X n,
      (∀ t, T.d n t z = 0) → A.f n z = 0 →
      (∀ i j, i + j = n → i < k → a3i_tensorProjection P.complex D i j n z = 0) →
      ∃ y : T.X (n + 1), T.d (n + 1) n y = z ∧ A.f (n + 1) y = 0 := by
    intro l
    induction l with
    | zero =>
      intro k hk z _ _ hz
      have hzero : z = 0 := a3i_tensor_eq_zero P.complex D n z
        (fun i j hij => hz i j hij (by omega))
      subst z
      exact ⟨0, map_zero _, map_zero _⟩
    | succ l ih =>
      intro k hk z hzc hza hz
      let j := n - k
      have hkj : k + j = n := by dsimp [j]; omega
      letI := hD j
      obtain ⟨u, hu⟩ : ∃ u : (P.complex.X (k + 1) ⊗ D.X j : ModuleCat R),
          (P.complex.d (k + 1) k ▷ D.X j) u =
            a3i_tensorProjection P.complex D k j n z := by
        cases k with
        | zero =>
          have he := Module.Flat.rTensor_shortComplex_exact (D.X j) _ P.exact₀
          apply (ShortComplex.moduleCat_exact_iff _).mp he
          change (P.π.f 0 ▷ D.X j) (a3i_tensorProjection P.complex D 0 j n z) = 0
          have hj : j = n := by omega
          subst j
          dsimp only [A] at hza
          rw [a3i_tensorResolutionAugmentation_f] at hza
          change (P.π.f 0 ▷ D.X n) (a3i_tensorProjection P.complex D 0 n n z) = 0 at hza
          simpa only [Nat.sub_zero] using hza
        | succ k =>
          have he := Module.Flat.rTensor_shortComplex_exact (D.X j) _ (P.exact_succ k)
          apply (ShortComplex.moduleCat_exact_iff _).mp he
          change (P.complex.d (k + 1) k ▷ D.X j)
            (a3i_tensorProjection P.complex D (k + 1) j n z) = 0
          have hp := ConcreteCategory.congr_hom
            (a3i_tensor_d_projection P.complex D k j n (n - 1)
              (by omega) (by omega)) z
          have hzv := hz k (j + 1) (by omega) (by omega)
          have hzc' := hzc (n - 1)
          change a3i_tensorProjection P.complex D k j (n - 1) (T.d n (n - 1) z) =
            (P.complex.d (k + 1) k ▷ D.X j)
              (a3i_tensorProjection P.complex D (k + 1) j n z) +
            ((-1 : ℤˣ) ^ k) • ((P.complex.X k ◁ D.d (j + 1) j)
              (a3i_tensorProjection P.complex D k (j + 1) n z)) at hp
          rw [hzc', map_zero, hzv, map_zero, smul_zero, add_zero] at hp
          exact hp.symm
      let y₀ : T.X (n + 1) := ιTensorObj P.complex D (k + 1) j (n + 1) (by omega) u
      have hy₀ : A.f (n + 1) y₀ = 0 := by
        exact ConcreteCategory.congr_hom
          (a3i_tensorResolutionAugmentation_ι_succ M P D k j (n + 1) (by omega)) u
      have hdy₀ : A.f n (T.d (n + 1) n y₀) = 0 := by
        have hh := ConcreteCategory.congr_hom (A.comm (n + 1) n) y₀
        change (a3c_tensC M D).d (n + 1) n (A.f (n + 1) y₀) =
          A.f n (T.d (n + 1) n y₀) at hh
        rw [hy₀, map_zero] at hh
        exact hh.symm
      have hzc' : ∀ t, T.d n t (z - T.d (n + 1) n y₀) = 0 := by
        intro t
        rw [map_sub, hzc]
        have hh := ConcreteCategory.congr_hom (T.d_comp_d (n + 1) n t) y₀
        change T.d n t (T.d (n + 1) n y₀) = 0 at hh
        rw [hh, sub_self]
      have hza' : A.f n (z - T.d (n + 1) n y₀) = 0 := by
        rw [map_sub, hza, hdy₀, sub_self]
      have hz' : ∀ i b, i + b = n → i < k + 1 →
          a3i_tensorProjection P.complex D i b n (z - T.d (n + 1) n y₀) = 0 := by
        intro i b hib hik
        rw [map_sub]
        by_cases hi : i = k
        · subst i
          have hb : b = j := by omega
          subst b
          have hh := ConcreteCategory.congr_hom
            (a3i_tensor_boundary_same P.complex D k j n hkj) u
          change a3i_tensorProjection P.complex D k j n (T.d (n + 1) n y₀) =
            (P.complex.d (k + 1) k ▷ D.X j) u at hh
          rw [hh, hu, sub_self]
        · have hil : i < k := by omega
          rw [hz i b hib hil]
          have hh := ConcreteCategory.congr_hom
            (a3i_tensor_boundary_below P.complex D k j n hkj i b hib hil) u
          change a3i_tensorProjection P.complex D i b n (T.d (n + 1) n y₀) = 0 at hh
          rw [hh, sub_self]
      obtain ⟨y, hy, hya⟩ := ih (k + 1) (by omega)
        (z - T.d (n + 1) n y₀) hzc' hza' hz'
      refine ⟨y + y₀, ?_, ?_⟩
      · rw [map_add, hy, sub_add_cancel]
      · rw [map_add, hya, hy₀, add_zero]
  exact aux (n + 1) 0 (by omega) x hc ha (fun i _ _ hi => (Nat.not_lt_zero i hi).elim)

/-- Surjectivity on cycles and reflection of boundaries imply a
quasi-isomorphism of module short complexes. IntersectionProductSE. -/
theorem a3i_shortComplex_quasiIso_of_cycles {R : Type u} [CommRing R]
    {S T : ShortComplex (ModuleCat.{u} R)} (f : S ⟶ T)
    (hcycles : ∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ f.τ₂ x = y)
    (hboundaries : ∀ x : S.X₂, S.g x = 0 →
      (∃ y : T.X₁, T.f y = f.τ₂ x) → ∃ z : S.X₁, S.f z = x) :
    ShortComplex.QuasiIso f := by
  have liftCycle (U : ShortComplex (ModuleCat.{u} R)) (x : U.X₂) (hx : U.g x = 0) :
      ∃ c : U.cycles, U.iCycles c = x := by
    exact (ShortComplex.moduleCat_exact_iff _).mp
      (ShortComplex.exact_of_f_is_kernel
        (ShortComplex.mk U.iCycles U.g U.iCycles_g) U.cyclesIsKernel) x hx
  have liftBoundary (U : ShortComplex (ModuleCat.{u} R)) (c : U.cycles)
      (hc : U.homologyπ c = 0) : ∃ x : U.X₁, U.toCycles x = c := by
    exact (ShortComplex.moduleCat_exact_iff _).mp
      (ShortComplex.exact_of_g_is_cokernel
        (ShortComplex.mk U.toCycles U.homologyπ U.toCycles_comp_homologyπ)
        U.homologyIsCokernel) c hc
  rw [ShortComplex.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply (injective_iff_map_eq_zero (ShortComplex.homologyMap f).hom).mpr
    intro v hv
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance v
    have hzero : T.homologyπ (ShortComplex.cyclesMap f c) = 0 := by
      have hh := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality f) c
      exact hh.symm.trans hv
    obtain ⟨y, hy⟩ := liftBoundary T _ hzero
    have hcx : S.g (S.iCycles c) = 0 := ConcreteCategory.congr_hom S.iCycles_g c
    have hy' : T.f y = f.τ₂ (S.iCycles c) := by
      calc
        T.f y = T.iCycles (T.toCycles y) :=
          (ConcreteCategory.congr_hom T.toCycles_i y).symm
        _ = T.iCycles (ShortComplex.cyclesMap f c) := congrArg T.iCycles hy
        _ = f.τ₂ (S.iCycles c) :=
          ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i f) c
    obtain ⟨z, hz⟩ := hboundaries _ hcx ⟨y, hy'⟩
    have hz' : S.toCycles z = c := by
      apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
      exact (ConcreteCategory.congr_hom S.toCycles_i z).trans hz
    rw [← hz']
    exact ConcreteCategory.congr_hom S.toCycles_comp_homologyπ z
  · intro v
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).mp inferInstance v
    obtain ⟨x, hx, hfx⟩ := hcycles (T.iCycles c)
      (ConcreteCategory.congr_hom T.iCycles_g c)
    obtain ⟨c', hc'⟩ := liftCycle S x hx
    have hc : ShortComplex.cyclesMap f c' = c := by
      apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
      exact (ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i f) c').trans
        ((congrArg f.τ₂ hc').trans hfx)
    refine ⟨S.homologyπ c', ?_⟩
    exact (ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality f) c').trans
      (congrArg T.homologyπ hc)

/-- For a natural chain complex, the outgoing differential detects cycles.
IntersectionProductSE. -/
theorem a3i_chain_cycle_all {R : Type u} [CommRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (x : C.X n)
    (hx : C.d n (n - 1) x = 0) : ∀ t, C.d n t x = 0 := by
  intro t
  by_cases ht : t = n - 1
  · subst t
    exact hx
  · rw [C.shape n t (by change ¬t + 1 = n; omega)]
    rfl

/-- A surjective chain map with acyclic kernel is a quasi-isomorphism,
expressed through lifts of kernel cycles. IntersectionProductSE. -/
theorem a3i_chain_quasiIso_of_kernel_lift {R : Type u} [CommRing R]
    {C D : ChainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D)
    (hs : ∀ n, Function.Surjective (f.f n))
    (hk : ∀ n (x : C.X n), (∀ t, C.d n t x = 0) → f.f n x = 0 →
      ∃ y : C.X (n + 1), C.d (n + 1) n y = x ∧ f.f (n + 1) y = 0) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff' f (n + 1) n (n - 1) (by simp) (by cases n <;> simp)]
  apply a3i_shortComplex_quasiIso_of_cycles
  · intro y hy
    change D.d n (n - 1) y = 0 at hy
    obtain ⟨z, hz⟩ := hs n y
    change ∃ x : C.X n, C.d n (n - 1) x = 0 ∧ f.f n x = y
    cases n with
    | zero =>
      refine ⟨z, ?_, hz⟩
      rw [C.shape 0 0 (by simp)]
      rfl
    | succ n =>
      have hc : ∀ t, C.d n t (C.d (n + 1) n z) = 0 := fun t =>
        ConcreteCategory.congr_hom (C.d_comp_d (n + 1) n t) z
      have hf : f.f n (C.d (n + 1) n z) = 0 := by
        have hh := ConcreteCategory.congr_hom (f.comm (n + 1) n) z
        change D.d (n + 1) n (f.f (n + 1) z) = f.f n (C.d (n + 1) n z) at hh
        rw [hz] at hh
        exact hh.symm.trans hy
      obtain ⟨w, hw, hfw⟩ := hk n _ hc hf
      refine ⟨z - w, ?_, ?_⟩
      · change C.d (n + 1) n (z - w) = 0
        rw [map_sub, hw, sub_self]
      · rw [map_sub, hz, hfw, sub_zero]
  · intro x hx hb
    change C.X n at x
    change C.d n (n - 1) x = 0 at hx
    obtain ⟨y, hy⟩ := hb
    change D.d (n + 1) n y = f.f n x at hy
    obtain ⟨z, hz⟩ := hs (n + 1) y
    have hxc := a3i_chain_cycle_all C n x hx
    have hc : ∀ t, C.d n t (x - C.d (n + 1) n z) = 0 := by
      intro t
      rw [map_sub, hxc]
      have hh := ConcreteCategory.congr_hom (C.d_comp_d (n + 1) n t) z
      change C.d n t (C.d (n + 1) n z) = 0 at hh
      rw [hh, sub_self]
    have hf : f.f n (x - C.d (n + 1) n z) = 0 := by
      rw [map_sub]
      have hh := ConcreteCategory.congr_hom (f.comm (n + 1) n) z
      change D.d (n + 1) n (f.f (n + 1) z) = f.f n (C.d (n + 1) n z) at hh
      rw [hz, hy] at hh
      rw [← hh, sub_self]
    obtain ⟨w, hw, _⟩ := hk n _ hc hf
    refine ⟨w + z, ?_⟩
    change C.d (n + 1) n (w + z) = x
    rw [map_add, hw, sub_add_cancel]

open MonoidalCategory HomologicalComplex in
set_option backward.isDefEq.respectTransparency false in
/-- Each component of the tensor augmentation is surjective.
IntersectionProductSE. -/
theorem a3i_tensorResolutionAugmentation_surjective {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    Function.Surjective ((a3i_tensorResolutionAugmentation M P C).f n) := by
  have he : Epi (P.π.f 0 ▷ C.X n) := inferInstance
  intro y
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective (P.π.f 0 ▷ C.X n)).mp he y
  refine ⟨ιTensorObj P.complex C 0 n n (by simp) x, ?_⟩
  have hh : ιTensorObj P.complex C 0 n n (by simp) ≫
      (a3i_tensorResolutionAugmentation M P C).f n = P.π.f 0 ▷ C.X n := by
    rw [a3i_tensorResolutionAugmentation_f, ← Category.assoc, a3i_ι_tensorProjection]
    simp
  exact (ConcreteCategory.congr_hom hh x).trans hx

/-- Tensoring a resolution augmentation with a complex of projective modules
is a quasi-isomorphism. IntersectionProductSE. -/
theorem a3i_tensorResolutionAugmentation_quasiIso {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (hC : ∀ j, Projective (C.X j)) :
    QuasiIso (a3i_tensorResolutionAugmentation M P C) :=
  a3i_chain_quasiIso_of_kernel_lift (a3i_tensorResolutionAugmentation M P C)
    (a3i_tensorResolutionAugmentation_surjective M P C)
    (a3i_tensorResolution_kernel_lift M P C hC)

/-- IntersectionProductLoc2 S2b: tensoring two projective resolutions computes Tor. -/
theorem a3i_resolutions_euler {R : Type u} [CommRing R] (M N : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (m : ℕ) :
    a3i_complexEuler m (HomologicalComplex.tensorObj P.complex Q.complex) =
      a3s_chi m M N := by
  letI : QuasiIso (a3i_tensorResolutionAugmentation M P Q.complex) :=
    a3i_tensorResolutionAugmentation_quasiIso M P Q.complex (fun j => Q.projective j)
  rw [a3i_tor_eq_euler M N Q m]
  exact a3i_complexEuler_eq_of_quasiIso (a3i_tensorResolutionAugmentation M P Q.complex) m

/-- IntersectionProductSV: homology of a finite module complex over a Noetherian ring
is finite in each degree. -/
theorem a3sv_finite_homology {B : Type} [CommRing B] [IsNoetherianRing B]
    (C : ChainComplex (ModuleCat.{0} B) ℕ) (i : ℕ) [Module.Finite B (C.X i)] :
    Module.Finite B (C.homology i) := by
  have : Module.Finite B (C.cycles i) := Module.Finite.of_injective
    (C.iCycles i).hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (C.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- IntersectionProductSV: proper support makes every Tor group of the homology
pairing have finite length. -/
theorem a3sv_homology_tor_length_ne_top {B : Type} [CommRing B] [IsRegularLocalRing B]
    (C : ChainComplex (ModuleCat.{0} B) ℕ) (N : ModuleCat.{0} B) [Module.Finite B N]
    (hfinite : ∀ i, Module.Finite B (C.X i))
    (hproper : ∀ i, ∀ P ∈ Module.support B (C.homology i),
      Module.annihilator B N ≤ P.asIdeal → P = IsLocalRing.closedPoint B)
    (i j : ℕ) :
    Module.length B (((Tor (ModuleCat.{0} B) j).obj (C.homology i)).obj N) ≠ ⊤ := by
  have := hfinite i
  have := a3sv_finite_homology C i
  exact a3s_length_tor_ne_top (C.homology i) N j fun P hP hN =>
    hproper i P ((Module.mem_support_iff_of_finite).mpr hP) hN

/-- IntersectionProductSV: extending the Euler sum beyond the bound of a complex
does not change its value. -/
theorem a3sv_complexEuler_eq_of_le {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (n m : ℕ) (hnm : n ≤ m)
    (hbounded : ∀ i, n < i → IsZero (C.X i)) :
    a3i_complexEuler m C = a3i_complexEuler n C := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    unfold a3i_complexEuler at *
    rw [Finset.sum_range_succ, ih]
    have hz : IsZero (C.homology (k + 1)) :=
      (C.sc (k + 1)).isZero_homology_of_isZero_X₂ (hbounded _ (by omega))
    rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hz)]
    simp

/-- IntersectionProductSV: flat tensoring commutes with the homology of a complex. -/
def a3sv_tensorHomologyIso {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (N : ModuleCat.{u} B) [Module.Flat B N]
    (i : ℕ) : (a3c_tensC N C).homology i ≅
      MonoidalCategory.tensorObj N (C.homology i) :=
  (C.sc i).mapHomologyIso (MonoidalCategory.tensorLeft N)

/-- IntersectionProductSV: positive Tor groups vanish when the first module is flat. -/
theorem a3sv_isZero_tor_succ_flat {B : Type u} [CommRing B]
    (M N : ModuleCat.{u} B) [Module.Flat B M] (i : ℕ) :
    IsZero (((Tor (ModuleCat.{u} B) (i + 1)).obj M).obj N) := by
  let Q := ProjectiveResolution.of N
  apply IsZero.of_iso _ (a3c_torIso M N Q (i + 1))
  apply IsZero.of_iso _ (a3sv_tensorHomologyIso Q.complex M (i + 1))
  apply (MonoidalCategory.tensorLeft M).map_isZero
  exact (Q.complex_exactAt_succ i).isZero_homology

/-- IntersectionProductSV: with a flat second argument the Tor Euler sum is the
length of the ordinary tensor product. -/
theorem a3sv_chi_flat_right {B : Type u} [CommRing B]
    (M N : ModuleCat.{u} B) [Module.Flat B N] (m : ℕ) :
    a3s_chi m M N =
      ((Module.length B (MonoidalCategory.tensorObj N M : ModuleCat.{u} B)).toNat : ℤ) := by
  rw [a3s_chi_symm]
  unfold a3s_chi
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul]
    rw [(a3c_tor0Iso N M).toLinearEquiv.length_eq]
  · intro i hi hi0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    have hz := a3sv_isZero_tor_succ_flat N M j
    rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hz)]
    simp
  · intro h
    exact (h (by simp)).elim

/-- IntersectionProductSV: the tensor Euler identity for a flat second module,
without a regularity or finite-length assumption. -/
theorem a3sv_tensor_euler_homology_flat {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (N : ModuleCat.{u} B) [Module.Flat B N]
    (n m : ℕ) (hbounded : ∀ i, n < i → IsZero (C.X i)) :
    a3i_complexEuler (n + m) (a3c_tensC N C) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * a3s_chi m (C.homology i) N := by
  rw [a3sv_complexEuler_eq_of_le (a3c_tensC N C) n (n + m) (by omega)
    (fun i hi => (MonoidalCategory.tensorLeft N).map_isZero (hbounded i hi))]
  unfold a3i_complexEuler
  apply Finset.sum_congr rfl
  intro i hi
  rw [a3sv_chi_flat_right,
    (a3sv_tensorHomologyIso C N i).toLinearEquiv.length_eq]

/-- IntersectionProductSV: a term decomposes in length into homology and the
images of its two adjacent differentials. -/
theorem a3sv_length_shortComplex {B : Type u} [CommRing B]
    (S : ShortComplex (ModuleCat.{u} B)) :
    Module.length B S.X₂ = Module.length B S.homology +
      Module.length B S.f.hom.range + Module.length B S.g.hom.range := by
  have hr : Module.length B S.moduleCatToCycles.range = Module.length B S.f.hom.range := by
    rw [← S.moduleCatToCycles.quotKerEquivRange.length_eq,
      ← S.f.hom.quotKerEquivRange.length_eq]
    have hk : S.moduleCatToCycles.ker = S.f.hom.ker := by
      ext x
      change S.moduleCatToCycles x = 0 ↔ S.f.hom x = 0
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hk]
  have hker := Module.length_eq_add_of_exact S.moduleCatToCycles.range.subtype
    S.moduleCatToCycles.range.mkQ (Submodule.injective_subtype _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [a3e_length_eq_ker_add_range S.g.hom, hker, hr]
  rw [S.moduleCatHomologyIso.toLinearEquiv.length_eq]
  change _ + _ + _ = _ + _ + _
  ac_rfl

/-- IntersectionProductSV: finite length turns the homology and boundary
length decomposition into an identity of integers. -/
theorem a3sv_int_length_shortComplex {B : Type u} [CommRing B]
    (S : ShortComplex (ModuleCat.{u} B)) (hfinite : Module.length B S.X₂ ≠ ⊤) :
    ((Module.length B S.X₂).toNat : ℤ) =
      ((Module.length B S.homology).toNat : ℤ) +
      ((Module.length B S.f.hom.range).toNat : ℤ) +
      ((Module.length B S.g.hom.range).toNat : ℤ) := by
  have he := a3sv_length_shortComplex S
  have hpair : Module.length B S.homology + Module.length B S.f.hom.range ≠ ⊤ := by
    intro h
    exact hfinite (he.trans (by rw [h, top_add]))
  have hp := WithTop.add_ne_top.mp hpair
  have hn := a3s_toNat_add he hfinite
  rw [ENat.toNat_add hp.1 hp.2] at hn
  push_cast at hn
  exact hn

/-- IntersectionProductSV: the signed length sum of a finite complex with any
shape equals the signed length sum of its homology. -/
theorem a3sv_euler_finite_shape {B : Type u} [CommRing B] {ι : Type*}
    (c : ComplexShape ι) (C : HomologicalComplex (ModuleCat.{u} B) c)
    (s : Finset ι) (sign : ι → ℤ)
    (hsign : ∀ i j, c.Rel i j → sign i = -sign j)
    (hfinite : ∀ i ∈ s, Module.length B (C.X i) ≠ ⊤)
    (hbounded : ∀ i ∉ s, IsZero (C.X i)) :
    (∑ i ∈ s, sign i * ((Module.length B (C.homology i)).toNat : ℤ)) =
      ∑ i ∈ s, sign i * ((Module.length B (C.X i)).toNat : ℤ) := by
  classical
  let b (i j : ι) : ℤ := ((Module.length B (C.d i j).hom.range).toNat : ℤ)
  have bzero (i j : ι) (h : C.d i j = 0) : b i j = 0 := by
    dsimp only [b]
    rw [h, ModuleCat.hom_zero, LinearMap.range_zero, Module.length_bot]
    rfl
  have hin (i : ι) : (∑ j ∈ s, b j i) = b (c.prev i) i := by
    apply Finset.sum_eq_single (c.prev i)
    · intro j hj hji
      apply bzero
      apply C.shape
      exact fun h => hji (c.prev_eq' h).symm
    · intro hi
      exact bzero _ _ ((hbounded _ hi).eq_of_src _ _)
  have hout (i : ι) : (∑ j ∈ s, b i j) = b i (c.next i) := by
    apply Finset.sum_eq_single (c.next i)
    · intro j hj hji
      apply bzero
      apply C.shape
      exact fun h => hji (c.next_eq' h).symm
    · intro hi
      exact bzero _ _ ((hbounded _ hi).eq_of_tgt _ _)
  have hlen (i : ι) (hi : i ∈ s) :
      ((Module.length B (C.X i)).toNat : ℤ) =
        ((Module.length B (C.homology i)).toNat : ℤ) +
          (∑ j ∈ s, b j i) + ∑ j ∈ s, b i j := by
    rw [hin, hout]
    exact a3sv_int_length_shortComplex (C.sc i) (hfinite i hi)
  have hcancel : (∑ i ∈ s, ∑ j ∈ s, sign i * b j i) =
      -(∑ i ∈ s, ∑ j ∈ s, sign i * b i j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : c.Rel i j
    · rw [hsign i j h]
      ring
    · rw [bzero i j (C.shape _ _ h)]
      ring
  calc
    _ = (∑ i ∈ s, sign i * ((Module.length B (C.homology i)).toNat : ℤ)) +
        ((∑ i ∈ s, ∑ j ∈ s, sign i * b j i) +
        ∑ i ∈ s, ∑ j ∈ s, sign i * b i j) := by rw [hcancel]; ring
    _ = _ := by
      symm
      calc
        _ = ∑ i ∈ s, sign i * (((Module.length B (C.homology i)).toNat : ℤ) +
            (∑ j ∈ s, b j i) + ∑ j ∈ s, b i j) :=
          Finset.sum_congr rfl (fun i hi => congrArg (sign i * ·) (hlen i hi))
        _ = _ := by simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]; ring

/-- IntersectionProductSV: finite length and finite support of one page pass to
the next page of a spectral sequence. -/
theorem a3sv_spectralSequence_page_finite {B : Type u} [CommRing B] {ι : Type*}
    {c : ℤ → ComplexShape ι} {r₀ : ℤ}
    (E : SpectralSequence (ModuleCat.{u} B) c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (s : Finset ι)
    (hfinite : ∀ i ∈ s, Module.length B ((E.page r hr).X i) ≠ ⊤)
    (hbounded : ∀ i ∉ s, IsZero ((E.page r hr).X i)) :
    (∀ i ∈ s, Module.length B ((E.page (r + 1) (by omega)).X i) ≠ ⊤) ∧
      (∀ i ∉ s, IsZero ((E.page (r + 1) (by omega)).X i)) := by
  constructor
  · intro i hi
    rw [← (E.iso r (r + 1) i rfl hr).toLinearEquiv.length_eq]
    have hf := hfinite i hi
    change Module.length B ((E.page r hr).sc i).X₂ ≠ ⊤ at hf
    rw [a3sv_length_shortComplex ((E.page r hr).sc i)] at hf
    exact (WithTop.add_ne_top.mp (WithTop.add_ne_top.mp hf).1).1
  · intro i hi
    exact IsZero.of_iso
      (((E.page r hr).sc i).isZero_homology_of_isZero_X₂ (hbounded i hi))
      (E.iso r (r + 1) i rfl hr).symm

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: a spectral sequence with finite-length terms and
finite support on its initial page has constant signed length Euler sum. -/
theorem a3sv_spectralSequence_euler {B : Type u} [CommRing B] {ι : Type*}
    {c : ℤ → ComplexShape ι} {r₀ : ℤ}
    (E : SpectralSequence (ModuleCat.{u} B) c r₀)
    (s : Finset ι) (sign : ι → ℤ)
    (hsign : ∀ r, r₀ ≤ r → ∀ i j, (c r).Rel i j → sign i = -sign j)
    (hfinite : ∀ i ∈ s, Module.length B ((E.page r₀ le_rfl).X i) ≠ ⊤)
    (hbounded : ∀ i ∉ s, IsZero ((E.page r₀ le_rfl).X i)) (k : ℕ) :
    (∑ i ∈ s, sign i * ((Module.length B ((E.page (r₀ + k) (by omega)).X i)).toNat : ℤ)) =
      ∑ i ∈ s, sign i * ((Module.length B ((E.page r₀ le_rfl).X i)).toNat : ℤ) := by
  have hdata (j : ℕ) :
      (∀ i ∈ s, Module.length B ((E.page (r₀ + j) (by omega)).X i) ≠ ⊤) ∧
        (∀ i ∉ s, IsZero ((E.page (r₀ + j) (by omega)).X i)) := by
    induction j with
    | zero =>
      constructor
      · intro i hi
        rw [← (E.pageXIsoOfEq i r₀ (r₀ + (0 : ℕ)) (by omega) le_rfl).toLinearEquiv.length_eq]
        exact hfinite i hi
      · intro i hi
        exact IsZero.of_iso (hbounded i hi)
          (E.pageXIsoOfEq i r₀ (r₀ + (0 : ℕ)) (by omega) le_rfl).symm
    | succ j ih =>
      have hh := a3sv_spectralSequence_page_finite E (r₀ + j) (by omega) s ih.1 ih.2
      constructor
      · intro i hi
        rw [← (E.pageXIsoOfEq i (r₀ + j + 1) (r₀ + (j + 1 : ℕ))
          (by omega) (by omega)).toLinearEquiv.length_eq]
        exact hh.1 i hi
      · intro i hi
        exact IsZero.of_iso (hh.2 i hi)
          (E.pageXIsoOfEq i (r₀ + j + 1) (r₀ + (j + 1 : ℕ))
            (by omega) (by omega)).symm
  induction k with
  | zero =>
    apply Finset.sum_congr rfl
    intro i hi
    rw [(E.pageXIsoOfEq i (r₀ + (0 : ℕ)) r₀ (by omega) (by omega)).toLinearEquiv.length_eq]
  | succ k ih =>
    have he := a3sv_euler_finite_shape (c (r₀ + k))
      (E.page (r₀ + k) (by omega)) s sign (hsign _ (by omega)) (hdata k).1 (hdata k).2
    have ht :
        (∑ i ∈ s, sign i *
          ((Module.length B ((E.page (r₀ + k) (by omega)).homology i)).toNat : ℤ)) =
        ∑ i ∈ s, sign i *
          ((Module.length B ((E.page (r₀ + (k + 1 : ℕ)) (by omega)).X i)).toNat : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(E.iso (r₀ + k) (r₀ + (k + 1 : ℕ)) i (by omega) (by omega)).toLinearEquiv.length_eq]
    exact ht.symm.trans (he.trans ih)


/-- IntersectionProductSV: a homological spectral page supported in a finite
horizontal strip has zero differential once the page exceeds the strip width. -/
theorem a3sv_spectralPage_d_eq_zero {B : Type u} [CommRing B]
    (r : ℤ) (m : ℕ) (hr : (m : ℤ) < r)
    (C : HomologicalComplex (ModuleCat.{u} B)
      (ComplexShape.spectralSequenceNat (-r, r - 1)))
    (hbounded : ∀ p : ℕ × ℕ, m < p.1 → IsZero (C.X p))
    (p q : ℕ × ℕ) : C.d p q = 0 := by
  by_cases hp : m < p.1
  · exact (hbounded p hp).eq_of_src _ _
  · apply C.shape
    intro hpq
    change (p.1 : ℤ) + -r = q.1 ∧ (p.2 : ℤ) + (r - 1) = q.2 at hpq
    omega

/-- IntersectionProductSV: consecutive homological spectral pages are isomorphic
at each index after the page number exceeds the horizontal support width. -/
def a3sv_spectralSequence_stableIso {B : Type u} [CommRing B] {r₀ : ℤ}
    (E : SpectralSequence (ModuleCat.{u} B)
      (fun r => ComplexShape.spectralSequenceNat (-r, r - 1)) r₀)
    (r : ℤ) (hr₀ : r₀ ≤ r) (m : ℕ) (hr : (m : ℤ) < r)
    (hbounded : ∀ p : ℕ × ℕ, m < p.1 → IsZero ((E.page r hr₀).X p))
    (p : ℕ × ℕ) :
    (E.page r hr₀).X p ≅ (E.page (r + 1) (by omega)).X p := by
  let C := E.page r hr₀
  have hd (a b : ℕ × ℕ) : C.d a b = 0 :=
    a3sv_spectralPage_d_eq_zero r m hr C hbounded a b
  exact (ShortComplex.LeftHomologyData.ofZeros (C.sc p)
    (hd _ _) (hd _ _)).homologyIso.symm ≪≫ E.iso r (r + 1) p rfl hr₀

/-- IntersectionProductSV: the length of a finite filtered module is the sum
of the lengths of its successive quotients. -/
theorem a3sv_length_filtration {B : Type u} [CommRing B]
    {M : Type u} [AddCommGroup M] [Module B M]
    (F : ℕ → Submodule B M) (hF : Monotone F) (hzero : F 0 = ⊥)
    (n : ℕ) :
    Module.length B (F n) = ∑ i ∈ Finset.range n,
      Module.length B ((F (i + 1)) ⧸
        LinearMap.range (Submodule.inclusion (hF (Nat.le_succ i)))) := by
  induction n with
  | zero =>
    simpa only [Finset.range_zero, Finset.sum_empty] using
      (congrArg (fun P : Submodule B M => Module.length B P) hzero).trans
        Module.length_bot
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    let f := Submodule.inclusion (hF (Nat.le_succ n))
    exact Module.length_eq_add_of_exact f f.range.mkQ
      (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_map_mkQ_range f)

/-- IntersectionProductSV: a finite filtration with finite-length successive
quotients computes the integer length of the ambient module. -/
theorem a3sv_int_length_filtration {B : Type u} [CommRing B]
    {M : Type u} [AddCommGroup M] [Module B M]
    (F : ℕ → Submodule B M) (hF : Monotone F) (hzero : F 0 = ⊥)
    (n : ℕ) (htop : F n = ⊤)
    (hfinite : ∀ i < n, Module.length B ((F (i + 1)) ⧸
      LinearMap.range (Submodule.inclusion (hF (Nat.le_succ i)))) ≠ ⊤) :
    ((Module.length B M).toNat : ℤ) = ∑ i ∈ Finset.range n,
      ((Module.length B ((F (i + 1)) ⧸
        LinearMap.range (Submodule.inclusion (hF (Nat.le_succ i))))).toNat : ℤ) := by
  have he := a3sv_length_filtration F hF hzero n
  have ht : Module.length B (F n) = Module.length B M :=
    (congrArg (fun P : Submodule B M => Module.length B P) htop).trans Module.length_top
  rw [ht] at he
  rw [he, ENat.toNat_sum (fun i hi => hfinite i (Finset.mem_range.mp hi)), Nat.cast_sum]

/-- IntersectionProductSV: the filtration on homology induced by submodules of
one term of a complex, using cycle representatives and the homology projection. -/
def a3sv_homologyFiltration {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (i : ℕ)
    (F : ℕ →o Submodule B (C.X i)) : ℕ →o Submodule B (C.homology i) where
  toFun p := ((F p).comap (C.iCycles i).hom).map (C.homologyπ i).hom
  monotone' := fun _ _ hpq => Submodule.map_mono (Submodule.comap_mono (F.monotone hpq))

/-- IntersectionProductSV: a filtration starting at zero and exhausting a term
induces a filtration starting at zero and exhausting its homology. -/
theorem a3sv_homologyFiltration_endpoints {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (i : ℕ)
    (F : ℕ →o Submodule B (C.X i)) (n : ℕ)
    (hzero : F 0 = ⊥) (htop : F n = ⊤) :
    a3sv_homologyFiltration C i F 0 = ⊥ ∧
      a3sv_homologyFiltration C i F n = ⊤ := by
  constructor
  · change ((F 0).comap (C.iCycles i).hom).map (C.homologyπ i).hom = ⊥
    rw [hzero, Submodule.comap_bot,
      LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective _).mp inferInstance),
      Submodule.map_bot]
  · change ((F n).comap (C.iCycles i).hom).map (C.homologyπ i).hom = ⊤
    rw [htop, Submodule.comap_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp inferInstance)]

/-- IntersectionProductSV: the quotient of two image submodules is the quotient
of the larger source submodule by the smaller submodule and the kernel. -/
def a3sv_imageQuotientEquiv {B : Type u} [CommRing B]
    {M N : Type u} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (f : M →ₗ[B] N) (S T : Submodule B M) (hST : S ≤ T) :
    (T ⧸ (S ⊔ f.ker).comap T.subtype) ≃ₗ[B]
      ((T.map f) ⧸ LinearMap.range
        (Submodule.inclusion (Submodule.map_mono hST) : S.map f →ₗ[B] T.map f)) := by
  let g : T →ₗ[B] T.map f :=
    (f.comp T.subtype).codRestrict (T.map f) (fun x => ⟨x, x.property, rfl⟩)
  let U := LinearMap.range
    (Submodule.inclusion (Submodule.map_mono hST) : S.map f →ₗ[B] T.map f)
  let q := U.mkQ.comp g
  have hg : Function.Surjective g := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hk : q.ker = (S ⊔ f.ker).comap T.subtype := by
    ext x
    change U.mkQ (g x) = 0 ↔ (x : M) ∈ S ⊔ f.ker
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change g x ∈ LinearMap.range (Submodule.inclusion (Submodule.map_mono hST)) ↔ _
    rw [Submodule.range_inclusion]
    change f x ∈ S.map f ↔ (x : M) ∈ S ⊔ f.ker
    exact SetLike.ext_iff.mp (Submodule.comap_map_eq f S) (x : M)
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (q.quotKerEquivOfSurjective (U.mkQ_surjective.comp hg))

/-- IntersectionProductSV: boundaries are exactly the kernel of the homology
projection in a module complex. -/
theorem a3sv_homologyProjection_ker {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (i : ℕ) :
    (C.homologyπ i).hom.ker = (C.toCycles (i + 1) i).hom.range := by
  let S := ShortComplex.mk (C.toCycles (i + 1) i) (C.homologyπ i)
    (C.toCycles_comp_homologyπ (i + 1) i)
  exact (S.exact_of_g_is_cokernel
    (C.homologyIsCokernel (i + 1) i (by simp))).moduleCat_range_eq_ker.symm

/-- IntersectionProductSV: cycles of filtration degree at most `p`, modulo
cycles of lower filtration degree and boundaries. -/
def a3sv_filteredHomologyPiece {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (i : ℕ)
    (F : ℕ →o Submodule B (C.X i)) (p : ℕ) : ModuleCat.{u} B :=
  let Z := fun q => (F q).comap (C.iCycles i).hom
  ModuleCat.of B ((Z (p + 1)) ⧸
    ((Z p) ⊔ (C.toCycles (i + 1) i).hom.range).comap (Z (p + 1)).subtype)

/-- IntersectionProductSV: the cycle-and-boundary quotient identifies with
the corresponding successive quotient of the induced homology filtration. -/
def a3sv_filteredHomologyPieceIso {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (i : ℕ)
    (F : ℕ →o Submodule B (C.X i)) (p : ℕ) :
    a3sv_filteredHomologyPiece C i F p ≅
      ModuleCat.of B ((a3sv_homologyFiltration C i F (p + 1)) ⧸
        LinearMap.range (Submodule.inclusion
          ((a3sv_homologyFiltration C i F).monotone (Nat.le_succ p)))) := by
  unfold a3sv_filteredHomologyPiece
  dsimp only
  rw [← a3sv_homologyProjection_ker]
  exact (a3sv_imageQuotientEquiv (C.homologyπ i).hom
    ((F p).comap (C.iCycles i).hom) ((F (p + 1)).comap (C.iCycles i).hom)
    (Submodule.comap_mono (F.monotone (Nat.le_succ p)))).toModuleIso

/-- IntersectionProductSV: a finite exhaustive filtration computes homology
length from its quotients of filtered cycles by boundaries and lower cycles. -/
theorem a3sv_homology_length_eq_filteredPieces {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (i : ℕ)
    (F : ℕ →o Submodule B (C.X i)) (n : ℕ)
    (hzero : F 0 = ⊥) (htop : F n = ⊤) :
    Module.length B (C.homology i) =
      ∑ p ∈ Finset.range n, Module.length B (a3sv_filteredHomologyPiece C i F p) := by
  let H := a3sv_homologyFiltration C i F
  obtain ⟨hH0, hHn⟩ := a3sv_homologyFiltration_endpoints C i F n hzero htop
  have h := a3sv_length_filtration H H.monotone hH0 n
  rw [hHn, Module.length_top] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro p hp
  exact (a3sv_filteredHomologyPieceIso C i F p).toLinearEquiv.length_eq.symm

/-- IntersectionProductSV: the integer homology length is the sum of the
integer lengths of the finite filtered homology pieces. -/
theorem a3sv_int_homology_length_eq_filteredPieces {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (i : ℕ)
    (F : ℕ →o Submodule B (C.X i)) (n : ℕ)
    (hzero : F 0 = ⊥) (htop : F n = ⊤)
    (hfinite : ∀ p < n, Module.length B (a3sv_filteredHomologyPiece C i F p) ≠ ⊤) :
    ((Module.length B (C.homology i)).toNat : ℤ) =
      ∑ p ∈ Finset.range n,
        ((Module.length B (a3sv_filteredHomologyPiece C i F p)).toNat : ℤ) := by
  rw [a3sv_homology_length_eq_filteredPieces C i F n hzero htop,
    ENat.toNat_sum (fun p hp => hfinite p (Finset.mem_range.mp hp)), Nat.cast_sum]

/-- IntersectionProductSV: the column filtration of a first-quadrant total
complex, indexed so that filtration degree zero is the zero submodule. -/
def a3sv_totalColumnFiltration {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (i : ℕ) :
    ℕ →o Submodule B ((HomologicalComplex₂.total K (ComplexShape.down ℕ)).X i) where
  toFun p := ⨆ (a : ℕ) (_ : a < p) (b : ℕ) (h : a + b = i),
    LinearMap.range (HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i h).hom
  monotone' := by
    intro p q hpq
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun b => iSup_le fun h => ?_
    exact le_iSup_of_le a (le_iSup_of_le (lt_of_lt_of_le ha hpq)
      (le_iSup_of_le b (le_iSup_of_le h le_rfl)))

/-- IntersectionProductSV: the column filtration of total degree `i` starts
at zero and exhausts the total term by filtration degree `i + 1`. -/
theorem a3sv_totalColumnFiltration_endpoints {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (i : ℕ) :
    a3sv_totalColumnFiltration K i 0 = ⊥ ∧
      a3sv_totalColumnFiltration K i (i + 1) = ⊤ := by
  constructor
  · change (⨆ (a : ℕ) (_ : a < 0) (b : ℕ) (h : a + b = i),
      LinearMap.range (HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i h).hom) = ⊥
    simp only [Nat.not_lt_zero, iSup_of_empty, iSup_bot]
  · let S := a3sv_totalColumnFiltration K i (i + 1)
    have hq : ModuleCat.ofHom S.mkQ = 0 := by
      apply HomologicalComplex₂.total.hom_ext
      intro a b hab
      ext x
      change S.mkQ ((HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i hab).hom x) = 0
      apply (Submodule.Quotient.mk_eq_zero S).mpr
      have ha : a < i + 1 := by change a + b = i at hab; omega
      change _ ∈ ⨆ (a : ℕ) (_ : a < i + 1) (b : ℕ) (h : a + b = i),
        LinearMap.range (HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i h).hom
      exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha
        (Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hab ⟨x, rfl⟩)))
    apply Submodule.eq_top_iff'.mpr
    intro x
    exact (Submodule.Quotient.mk_eq_zero S).mp
      (congrArg (fun f => f.hom x) hq)

/-- IntersectionProductSV: projection from a total-complex term onto one
specified bicomplex summand. -/
def a3sv_totalColumnProjection {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q i : ℕ) (_h : p + q = i) :
    (HomologicalComplex₂.total K (ComplexShape.down ℕ)).X i ⟶ (K.X p).X q :=
  HomologicalComplex₂.totalDesc (K := K) fun a b _ =>
    if ha : a = p then if hb : b = q then
      (HomologicalComplex₂.XXIsoOfEq (ModuleCat.{u} B) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) K ha hb).hom else 0 else 0

/-- IntersectionProductSV: projecting the selected total-complex summand is
the identity. -/
theorem a3sv_ιTotal_totalColumnProjection {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q i : ℕ) (h : p + q = i) :
    HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) p q i h ≫
      a3sv_totalColumnProjection K p q i h = 𝟙 _ := by
  simp [a3sv_totalColumnProjection]

/-- IntersectionProductSV: projection onto one column kills every distinct
column summand. -/
theorem a3sv_ιTotal_totalColumnProjection_eq_zero {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (a b p q i : ℕ) (hab : a + b = i) (h : p + q = i) (ha : a ≠ p) :
    HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i hab ≫
      a3sv_totalColumnProjection K p q i h = 0 := by
  simp [a3sv_totalColumnProjection, ha]

/-- IntersectionProductSV: all columns below a selected column lie in the
kernel of its total-complex projection. -/
theorem a3sv_totalColumnFiltration_le_projection_ker {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q i : ℕ) (h : p + q = i) :
    a3sv_totalColumnFiltration K i p ≤
      LinearMap.ker (a3sv_totalColumnProjection K p q i h).hom := by
  change (⨆ (a : ℕ) (_ : a < p) (b : ℕ) (hab : a + b = i),
    LinearMap.range (HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i hab).hom) ≤ _
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun b => iSup_le fun hab => ?_
  rintro _ ⟨x, rfl⟩
  change (a3sv_totalColumnProjection K p q i h).hom
    ((HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i hab).hom x) = 0
  exact ConcreteCategory.congr_hom
    (a3sv_ιTotal_totalColumnProjection_eq_zero K a b p q i hab h (by omega)) x

/-- IntersectionProductSV: adjoining one column to the total filtration adds
exactly the range of that column's summand inclusion. -/
theorem a3sv_totalColumnFiltration_succ {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q i : ℕ) (h : p + q = i) :
    a3sv_totalColumnFiltration K i (p + 1) =
      a3sv_totalColumnFiltration K i p ⊔
        LinearMap.range (HomologicalComplex₂.ιTotal K
          (ComplexShape.down ℕ) p q i h).hom := by
  change (⨆ (a : ℕ) (_ : a < p + 1) (b : ℕ) (hab : a + b = i),
    LinearMap.range (HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i hab).hom) = _
  rw [Nat.iSup_lt_succ]
  congr 1
  apply le_antisymm
  · refine iSup_le fun b => iSup_le fun hab => ?_
    have hb : b = q := by omega
    subst b
    exact le_rfl
  · exact le_iSup_of_le q (le_iSup_of_le h le_rfl)

/-- IntersectionProductSV: projection from a successive column-filtration
term onto its newly adjoined column. -/
def a3sv_totalColumnProjectionRestrict {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q i : ℕ) (h : p + q = i) :
    ModuleCat.of B (a3sv_totalColumnFiltration K i (p + 1)) ⟶ (K.X p).X q :=
  ModuleCat.ofHom ((a3sv_totalColumnProjection K p q i h).hom.comp
    (a3sv_totalColumnFiltration K i (p + 1)).subtype)

/-- IntersectionProductSV: the projection from a successive filtration term
onto its new column is surjective. -/
theorem a3sv_totalColumnProjectionRestrict_surjective {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q i : ℕ) (h : p + q = i) :
    Function.Surjective (a3sv_totalColumnProjectionRestrict K p q i h) := by
  intro x
  let y := (HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) p q i h).hom x
  have hy : y ∈ a3sv_totalColumnFiltration K i (p + 1) := by
    change y ∈ ⨆ (a : ℕ) (_ : a < p + 1) (b : ℕ) (hab : a + b = i),
      LinearMap.range (HomologicalComplex₂.ιTotal K
        (ComplexShape.down ℕ) a b i hab).hom
    exact Submodule.mem_iSup_of_mem p (Submodule.mem_iSup_of_mem (by omega)
      (Submodule.mem_iSup_of_mem q (Submodule.mem_iSup_of_mem h ⟨x, rfl⟩)))
  refine ⟨⟨y, hy⟩, ?_⟩
  exact ConcreteCategory.congr_hom
    (a3sv_ιTotal_totalColumnProjection K p q i h) x

/-- IntersectionProductSV: the kernel of the projection from a successive
filtration term is exactly the preceding filtration term. -/
theorem a3sv_totalColumnProjectionRestrict_ker {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q i : ℕ) (h : p + q = i) :
    LinearMap.ker (a3sv_totalColumnProjectionRestrict K p q i h).hom =
      (a3sv_totalColumnFiltration K i p).comap
        (a3sv_totalColumnFiltration K i (p + 1)).subtype := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have hxmem : x.val ∈ a3sv_totalColumnFiltration K i p ⊔
        LinearMap.range (HomologicalComplex₂.ιTotal K
          (ComplexShape.down ℕ) p q i h).hom := by
      rw [← a3sv_totalColumnFiltration_succ K p q i h]
      exact x.property
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxmem
    obtain ⟨w, rfl⟩ := hz
    have hpy : (a3sv_totalColumnProjection K p q i h).hom y = 0 :=
      a3sv_totalColumnFiltration_le_projection_ker K p q i h hy
    have hpw : (a3sv_totalColumnProjection K p q i h).hom
        ((HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) p q i h).hom w) = w :=
      ConcreteCategory.congr_hom
        (a3sv_ιTotal_totalColumnProjection K p q i h) w
    have hw : w = 0 := by
      have he := congrArg (a3sv_totalColumnProjection K p q i h).hom hyz
      change _ = _ at he
      rw [map_add, hpy, hpw, zero_add] at he
      exact he.trans hx
    rw [hw, map_zero, add_zero] at hyz
    change x.val ∈ a3sv_totalColumnFiltration K i p
    rw [← hyz]
    exact hy
  · intro hx
    rw [LinearMap.mem_ker]
    exact a3sv_totalColumnFiltration_le_projection_ker K p q i h hx

/-- IntersectionProductSV: the quotient of two consecutive column-filtration
terms is the newly adjoined bicomplex summand. -/
def a3sv_totalColumnFiltrationQuotientEquiv {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q i : ℕ) (h : p + q = i) :
    (a3sv_totalColumnFiltration K i (p + 1) ⧸
      (a3sv_totalColumnFiltration K i p).comap
        (a3sv_totalColumnFiltration K i (p + 1)).subtype) ≃ₗ[B]
      (K.X p).X q := by
  let f := (a3sv_totalColumnProjectionRestrict K p q i h).hom
  exact (Submodule.quotEquivOfEq _ _
      (a3sv_totalColumnProjectionRestrict_ker K p q i h).symm).trans
    (f.quotKerEquivOfSurjective
      (a3sv_totalColumnProjectionRestrict_surjective K p q i h))

/-- IntersectionProductSV: the successive-filtration quotient equivalence is
induced by the column projection. -/
theorem a3sv_totalColumnFiltrationQuotientEquiv_mk {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q i : ℕ) (h : p + q = i)
    (x : a3sv_totalColumnFiltration K i (p + 1)) :
    a3sv_totalColumnFiltrationQuotientEquiv K p q i h
        (Submodule.Quotient.mk x) =
      a3sv_totalColumnProjectionRestrict K p q i h x := by
  simp [a3sv_totalColumnFiltrationQuotientEquiv]

/-- IntersectionProductSV: every summand in a column below the filtration bound
maps into the corresponding filtered total term. -/
theorem a3sv_totalColumnFiltration_ιTotalOrZero_mem {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (i p a b : ℕ) (ha : a < p) (x : (K.X a).X b) :
    (HomologicalComplex₂.ιTotalOrZero K (ComplexShape.down ℕ) a b i).hom x ∈
      a3sv_totalColumnFiltration K i p := by
  classical
  by_cases hab : a + b = i
  · rw [HomologicalComplex₂.ιTotalOrZero_eq K (ComplexShape.down ℕ) a b i hab]
    change _ ∈ ⨆ (a : ℕ) (_ : a < p) (b : ℕ) (h : a + b = i),
      LinearMap.range (HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i h).hom
    exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha
      (Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hab ⟨x, rfl⟩)))
  · rw [HomologicalComplex₂.ιTotalOrZero_eq_zero K (ComplexShape.down ℕ) a b i hab]
    exact (a3sv_totalColumnFiltration K i p).zero_mem

/-- IntersectionProductSV: the total differential preserves the column
filtration of a first-quadrant bicomplex. -/
theorem a3sv_totalColumnFiltration_d {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (i j p : ℕ) :
    a3sv_totalColumnFiltration K i p ≤
      (a3sv_totalColumnFiltration K j p).comap
        ((HomologicalComplex₂.total K (ComplexShape.down ℕ)).d i j).hom := by
  change (⨆ (a : ℕ) (_ : a < p) (b : ℕ) (h : a + b = i),
    LinearMap.range (HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i h).hom) ≤ _
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun b => iSup_le fun hab => ?_
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  change (((HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i hab) ≫
    (HomologicalComplex₂.total K (ComplexShape.down ℕ)).d i j).hom x) ∈ a3sv_totalColumnFiltration K j p
  have he : HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i hab ≫
      (HomologicalComplex₂.total K (ComplexShape.down ℕ)).d i j =
      HomologicalComplex₂.d₁ K (ComplexShape.down ℕ) a b j +
      HomologicalComplex₂.d₂ K (ComplexShape.down ℕ) a b j := by
    change _ ≫ (_ + _) = _
    rw [Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
  rw [he]
  apply Submodule.add_mem
  · have ha' : (ComplexShape.down ℕ).next a < p := by
      cases a with
      | zero => simpa only [ChainComplex.next_nat_zero] using ha
      | succ a => simp only [ChainComplex.next_nat_succ]; omega
    change (ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (a, b) : ℤ) •
      (HomologicalComplex₂.ιTotalOrZero K (ComplexShape.down ℕ)
        ((ComplexShape.down ℕ).next a) b j).hom
          (((K.d a ((ComplexShape.down ℕ).next a)).f b).hom x) ∈ a3sv_totalColumnFiltration K j p
    exact (a3sv_totalColumnFiltration K j p).toAddSubgroup.zsmul_mem
      (a3sv_totalColumnFiltration_ιTotalOrZero_mem K j p _ b ha' _) _
  · change (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (a, b) : ℤ) •
      (HomologicalComplex₂.ιTotalOrZero K (ComplexShape.down ℕ)
        a ((ComplexShape.down ℕ).next b) j).hom
          (((K.X a).d b ((ComplexShape.down ℕ).next b)).hom x) ∈ a3sv_totalColumnFiltration K j p
    exact (a3sv_totalColumnFiltration K j p).toAddSubgroup.zsmul_mem
      (a3sv_totalColumnFiltration_ιTotalOrZero_mem K j p a _ ha _) _

/-- IntersectionProductSV: submodules preserved by the differential form a
module subcomplex. -/
def a3sv_submoduleComplex {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (F : ∀ i, Submodule B (C.X i))
    (hd : ∀ i j, F i ≤ (F j).comap (C.d i j).hom) :
    ChainComplex (ModuleCat.{u} B) ℕ where
  X i := ModuleCat.of B (F i)
  d i j := ModuleCat.ofHom (((C.d i j).hom.comp (F i).subtype).codRestrict
    (F j) (fun x => hd i j x.property))
  shape i j h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (C.d i j).hom x = 0
    rw [C.shape i j h]
    rfl
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => f.hom x.val) (C.d_comp_d i j k)

/-- IntersectionProductSV: the columns below a fixed filtration bound form
a subcomplex of the total complex. -/
def a3sv_totalColumnComplex {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p : ℕ) :
    ChainComplex (ModuleCat.{u} B) ℕ where
  X i := ModuleCat.of B (a3sv_totalColumnFiltration K i p)
  d i j := ModuleCat.ofHom
    ((((HomologicalComplex₂.total K (ComplexShape.down ℕ)).d i j).hom.comp
      (a3sv_totalColumnFiltration K i p).subtype).codRestrict
      (a3sv_totalColumnFiltration K j p)
      (fun x => a3sv_totalColumnFiltration_d K i j p x.property))
  shape i j h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((HomologicalComplex₂.total K (ComplexShape.down ℕ)).d i j).hom x = 0
    rw [(HomologicalComplex₂.total K (ComplexShape.down ℕ)).shape i j h]
    rfl
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => f.hom x.val)
      ((HomologicalComplex₂.total K (ComplexShape.down ℕ)).d_comp_d i j k)

/-- IntersectionProductSV: inclusion of a column subcomplex into the total
complex. -/
def a3sv_totalColumnInclusion {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p : ℕ) :
    a3sv_totalColumnComplex K p ⟶ HomologicalComplex₂.total K (ComplexShape.down ℕ) where
  f i := ModuleCat.ofHom (a3sv_totalColumnFiltration K i p).subtype
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- IntersectionProductSV: cycles from a column subcomplex are precisely
total cycles whose representatives lie in that column filtration level. -/
theorem a3sv_totalColumn_cyclesMap_range {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p i : ℕ) :
    (HomologicalComplex.cyclesMap (a3sv_totalColumnInclusion K p) i).hom.range =
      (a3sv_totalColumnFiltration K i p).comap
        ((HomologicalComplex₂.total K (ComplexShape.down ℕ)).iCycles i).hom := by
  let T := HomologicalComplex₂.total K (ComplexShape.down ℕ)
  let D := a3sv_totalColumnComplex K p
  let ι := a3sv_totalColumnInclusion K p
  let F := a3sv_totalColumnFiltration K i p
  let Z := F.comap (T.iCycles i).hom
  have hnat (x : D.cycles i) :
      (T.iCycles i).hom ((HomologicalComplex.cyclesMap ι i).hom x) =
        ((D.iCycles i).hom x).val :=
    congrArg (fun f => f.hom x) (HomologicalComplex.cyclesMap_i ι i)
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change (T.iCycles i).hom ((HomologicalComplex.cyclesMap ι i).hom x) ∈ F
    rw [hnat]
    exact ((D.iCycles i).hom x).property
  · intro y hy
    let g : ModuleCat.of B Z ⟶ D.X i := ModuleCat.ofHom
      (((T.iCycles i).hom.comp Z.subtype).codRestrict F (fun x => x.property))
    have hg : g ≫ D.d i ((ComplexShape.down ℕ).next i) = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact congrArg (fun f => f.hom x.val)
        (T.iCycles_d i ((ComplexShape.down ℕ).next i))
    let l := D.liftCycles g ((ComplexShape.down ℕ).next i) rfl hg
    refine ⟨l.hom ⟨y, hy⟩, ?_⟩
    apply (ModuleCat.mono_iff_injective (T.iCycles i)).mp inferInstance
    rw [hnat]
    exact congrArg Subtype.val (congrArg (fun f => f.hom ⟨y, hy⟩)
      (D.liftCycles_i g ((ComplexShape.down ℕ).next i) rfl hg))

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the filtration induced on total homology equals
the image of the homology of each column subcomplex. -/
theorem a3sv_totalColumn_homologyMap_range {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p i : ℕ) :
    (HomologicalComplex.homologyMap (a3sv_totalColumnInclusion K p) i).hom.range =
      a3sv_homologyFiltration (HomologicalComplex₂.total K (ComplexShape.down ℕ))
        i (a3sv_totalColumnFiltration K i) p := by
  change _ = ((a3sv_totalColumnFiltration K i p).comap
    ((HomologicalComplex₂.total K (ComplexShape.down ℕ)).iCycles i).hom).map
      ((HomologicalComplex₂.total K (ComplexShape.down ℕ)).homologyπ i).hom
  have hr : ((a3sv_totalColumnComplex K p).homologyπ i).hom.range = ⊤ :=
    LinearMap.range_eq_top.mpr
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have h := congrArg (fun f => f.hom.range)
    (HomologicalComplex.homologyπ_naturality (a3sv_totalColumnInclusion K p) i)
  simpa only [ModuleCat.hom_comp, LinearMap.range_comp, hr, Submodule.map_top,
    a3sv_totalColumn_cyclesMap_range] using h

/-- IntersectionProductSV: the Euler characteristic of total homology is the
sum of the signed lengths of its finite column filtration pieces. -/
theorem a3sv_totalEuler_eq_filteredPieces {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (n : ℕ)
    (hfinite : ∀ i ≤ n, ∀ p < i + 1, Module.length B
      (a3sv_filteredHomologyPiece (HomologicalComplex₂.total K (ComplexShape.down ℕ))
        i (a3sv_totalColumnFiltration K i) p) ≠ ⊤) :
    a3i_complexEuler n (HomologicalComplex₂.total K (ComplexShape.down ℕ)) =
      ∑ i ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (i + 1),
        (-1 : ℤ) ^ i * ((Module.length B
          (a3sv_filteredHomologyPiece (HomologicalComplex₂.total K (ComplexShape.down ℕ))
            i (a3sv_totalColumnFiltration K i) p)).toNat : ℤ) := by
  unfold a3i_complexEuler
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨hzero, htop⟩ := a3sv_totalColumnFiltration_endpoints K i
  rw [a3sv_int_homology_length_eq_filteredPieces
    (HomologicalComplex₂.total K (ComplexShape.down ℕ)) i
    (a3sv_totalColumnFiltration K i) (i + 1) hzero htop
    (hfinite i (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi)), Finset.mul_sum]

/-- IntersectionProductSV: restricting a linear map to nested submodules
commutes with their inclusions. -/
theorem a3sv_submodule_restriction_naturality {B : Type u} [CommRing B]
    {M N : Type u} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (f : M →ₗ[B] N) (S T : Submodule B M) (U V : Submodule B N)
    (hST : S ≤ T) (hUV : U ≤ V) (hS : S ≤ U.comap f) (hT : T ≤ V.comap f) :
    (Submodule.inclusion hUV).comp
        ((f.comp S.subtype).codRestrict U (fun x => hS x.property)) =
      ((f.comp T.subtype).codRestrict V (fun x => hT x.property)).comp
        (Submodule.inclusion hST) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- IntersectionProductSV: nested differential-preserved submodules induce
a morphism of their subcomplexes. -/
def a3sv_submoduleComplexMap {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (F G : ∀ i, Submodule B (C.X i))
    (hF : ∀ i j, F i ≤ (F j).comap (C.d i j).hom)
    (hG : ∀ i j, G i ≤ (G j).comap (C.d i j).hom) (hFG : ∀ i, F i ≤ G i) :
    a3sv_submoduleComplex C F hF ⟶ a3sv_submoduleComplex C G hG where
  f i := ModuleCat.ofHom (Submodule.inclusion (hFG i))
  comm' i j _hij := ModuleCat.hom_ext
    (a3sv_submodule_restriction_naturality (C.d i j).hom
      (F i) (G i) (F j) (G j) (hFG i) (hFG j) (hF i j) (hG i j))

/-- IntersectionProductSV: increasing the column bound induces a morphism
between the filtered subcomplexes. -/
def a3sv_totalColumnMap {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    {p q : ℕ} (hpq : p ≤ q) :
    a3sv_totalColumnComplex K p ⟶ a3sv_totalColumnComplex K q :=
  a3sv_submoduleComplexMap (HomologicalComplex₂.total K (ComplexShape.down ℕ))
    (fun i => a3sv_totalColumnFiltration K i p)
    (fun i => a3sv_totalColumnFiltration K i q)
    (fun i j => a3sv_totalColumnFiltration_d K i j p)
    (fun i j => a3sv_totalColumnFiltration_d K i j q)
    (fun i => (a3sv_totalColumnFiltration K i).monotone hpq)

/-- IntersectionProductSV: a monotone differential-preserved filtration is
a functor from its filtration indices to module complexes. -/
def a3sv_submoduleComplexFunctor {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (F : ℕ → ∀ i, Submodule B (C.X i))
    (hF : ∀ p q, p ≤ q → ∀ i, F p i ≤ F q i)
    (hd : ∀ p i j, F p i ≤ (F p j).comap (C.d i j).hom) :
    ℕ ⥤ ChainComplex (ModuleCat.{u} B) ℕ where
  obj p := a3sv_submoduleComplex C (F p) (hd p)
  map f := a3sv_submoduleComplexMap C _ _ _ _ (hF _ _ (leOfHom f))
  map_id p := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    rfl
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    rfl

/-- IntersectionProductSV: the column filtration as a functor to complexes. -/
def a3sv_totalColumnFunctor {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) :
    ℕ ⥤ ChainComplex (ModuleCat.{u} B) ℕ :=
  a3sv_submoduleComplexFunctor (HomologicalComplex₂.total K (ComplexShape.down ℕ))
    (fun p i => a3sv_totalColumnFiltration K i p)
    (fun _ _ hpq i => (a3sv_totalColumnFiltration K i).monotone hpq)
    (fun p i j => a3sv_totalColumnFiltration_d K i j p)

/-- IntersectionProductSV: all column-filtration transitions are monomorphisms. -/
instance a3sv_totalColumnFunctor_map_mono {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    {p q : ℕ} (f : p ⟶ q) : Mono ((a3sv_totalColumnFunctor K).map f) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  apply (ModuleCat.mono_iff_injective _).mpr
  exact Submodule.inclusion_injective ((a3sv_totalColumnFiltration K i).monotone (leOfHom f))

/-- IntersectionProductSV: the column filtration extended by zero to
integer filtration indices and reindexed as a cochain complex. -/
def a3sv_totalColumnExtendedFunctor {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) :
    ℤ ⥤ CochainComplex (ModuleCat.{u} B) ℤ :=
  (show Monotone Int.toNat from fun _ _ h => Int.toNat_le_toNat h).functor ⋙
    a3sv_totalColumnFunctor K ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)

/-- IntersectionProductSV: every transition of the extended column filtration
is a monomorphism of complexes. -/
instance a3sv_totalColumnExtendedFunctor_map_mono {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    {p q : ℤ} (f : p ⟶ q) : Mono ((a3sv_totalColumnExtendedFunctor K).map f) := by
  let hpq : p.toNat ≤ q.toNat := Int.toNat_le_toNat (leOfHom f)
  let φ := (a3sv_totalColumnFunctor K).map (homOfLE hpq)
  have hm (i : ℕ) : Mono (φ.f i) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective
      (Submodule.inclusion ((a3sv_totalColumnFiltration K i).monotone hpq))
    exact Submodule.inclusion_injective _
  apply HomologicalComplex.mono_of_mono_f
  intro j
  change Mono ((HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat).f j)
  by_cases hj : ∃ i, ComplexShape.embeddingDownNat.f i = j
  · obtain ⟨i, hi⟩ := hj
    rw [HomologicalComplex.extendMap_f _ _ hi]
    letI := hm i
    infer_instance
  · have hz := ((a3sv_totalColumnFunctor K).obj p.toNat).isZero_extend_X
      ComplexShape.embeddingDownNat j (fun i hi => hj ⟨i, hi⟩)
    letI := ModuleCat.isZero_iff_subsingleton.mp hz
    exact (ModuleCat.mono_iff_injective _).mpr (Function.injective_of_subsingleton _)

/-- IntersectionProductSV: inclusion of a bicomplex summand into a column
filtration term whose bound is above that column. -/
def a3sv_totalColumnSummandInclusion {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (b p q i : ℕ) (hp : p < b) (hi : p + q = i) :
    (K.X p).X q ⟶ ((a3sv_totalColumnFunctor K).obj b).X i :=
  ModuleCat.ofHom ((HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) p q i hi).hom.codRestrict
    (a3sv_totalColumnFiltration K i b) (fun x => by
      change _ ∈ ⨆ (a : ℕ) (_ : a < b) (c : ℕ) (h : a + c = i),
        LinearMap.range (HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a c i h).hom
      exact Submodule.mem_iSup_of_mem p (Submodule.mem_iSup_of_mem hp
        (Submodule.mem_iSup_of_mem q (Submodule.mem_iSup_of_mem hi ⟨x, rfl⟩)))))

/-- IntersectionProductSV: a summand lift followed by column projection is the identity. -/
theorem a3sv_totalColumnSummandInclusion_projection {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    a3sv_totalColumnSummandInclusion K (p + 1) p q (p + q) (by omega) rfl ≫
      a3sv_totalColumnProjectionRestrict K p q (p + q) rfl = 𝟙 _ := by
  change HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) p q (p + q) rfl ≫
    a3sv_totalColumnProjection K p q (p + q) rfl = _
  exact a3sv_ιTotal_totalColumnProjection K p q (p + q) rfl

/-- IntersectionProductSV: the spectral object obtained from the mapping
cones of the column filtration, with zero filtration below index zero. -/
def a3sv_totalColumnSpectralObject {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) :
    Abelian.SpectralObject (ModuleCat.{u} B) ℤ :=
  ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} B)).precomp
    ((show Monotone Int.toNat from fun _ _ h => Int.toNat_le_toNat h).functor ⋙
      a3sv_totalColumnFunctor K ⋙
      ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B))).mapHomologicalFunctor
        (HomotopyCategory.homologyFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ) 0)

/-- IntersectionProductSV: the total-column spectral object is the
mapping-cone spectral object precomposed with the packaged extended filtration. -/
theorem a3sv_totalColumnSpectralObject_eq {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) :
    a3sv_totalColumnSpectralObject K =
      ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} B)).precomp
        (a3sv_totalColumnExtendedFunctor K)).mapHomologicalFunctor
          (HomotopyCategory.homologyFunctor
            (ModuleCat.{u} B) (ComplexShape.up ℤ) 0) := rfl

/-- IntersectionProductSV: homological page indices for an increasing
integer-indexed filtration, starting with its first page. -/
def a3sv_homologicalFiltrationData :
    Abelian.SpectralObject.SpectralSequenceDataCore ℤ
      (fun r => ComplexShape.up' ((-r, r - 1) : ℤ × ℤ)) 1 where
  deg pq := -pq.1 - pq.2
  i₀ r pq _ := pq.1 - r + 1
  i₁ pq := pq.1
  i₂ pq := pq.1 + 1
  i₃ r pq _ := pq.1 + r
  le₀₁ r pq hr := by omega
  le₁₂ pq := by omega
  le₂₃ r pq hr := by omega
  hc := by
    rintro r ⟨p, q⟩ _ rfl hr
    dsimp
    omega
  hc₀₂ := by
    rintro r ⟨p, q⟩ _ rfl hr
    dsimp
    omega
  hc₁₃ := by
    rintro r ⟨p, q⟩ _ rfl hr
    dsimp
    omega
  antitone_i₀ r r' pq hr hrr' := by omega
  monotone_i₃ r r' pq hr hrr' := by omega
  i₀_prev := by
    rintro r r' ⟨p, q⟩ _ rfl hrr' hr
    dsimp
    omega
  i₃_next := by
    rintro r r' ⟨p, q⟩ _ rfl hrr' hr
    dsimp
    omega

/-- IntersectionProductSV: the integer-indexed homological page data produce
a spectral sequence for every spectral object, since every index has both
an incoming and an outgoing differential position. -/
theorem a3sv_homologicalFiltration_hasSpectralSequence {B : Type*} [CommRing B]
    (S : Abelian.SpectralObject (ModuleCat B) ℤ) :
    S.HasSpectralSequence a3sv_homologicalFiltrationData := by
  constructor
  · intro r r' pq hpq n hn hrr' hr
    exact (hpq (pq + ((-r, r - 1) : ℤ × ℤ)) rfl).elim
  · intro r r' pq hpq n hn hrr' hr
    exact (hpq (pq - ((-r, r - 1) : ℤ × ℤ)) (sub_add_cancel _ _)).elim

/-- IntersectionProductSV: the first page of the increasing filtration data
is computed by the spectral object's homology of consecutive levels. -/
theorem a3sv_homologicalFiltration_firstPage :
    a3sv_homologicalFiltrationData.HasFirstPageComputation where
  hi₀₁ pq := by
    change pq.1 - 1 + 1 = pq.1
    omega
  hi₂₃ pq := rfl

/-- IntersectionProductSV: the homological spectral sequence constructed
from the actual column filtration of a first-quadrant total complex. -/
def a3sv_totalColumnSpectralSequence {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) :
    SpectralSequence (ModuleCat.{u} B)
      (fun r => ComplexShape.up' ((-r, r - 1) : ℤ × ℤ)) 1 := by
  letI := a3sv_homologicalFiltration_hasSpectralSequence (a3sv_totalColumnSpectralObject K)
  exact (a3sv_totalColumnSpectralObject K).spectralSequence a3sv_homologicalFiltrationData

/-- IntersectionProductSV: relations contributed by a binary sum have the sum of the two ranges. -/
theorem a3sv_range_biprod_desc {B : Type u} [CommRing B]
    {M N P : ModuleCat.{u} B} (f : M ⟶ P) (g : N ⟶ P) :
    (biprod.desc f g).hom.range = f.hom.range ⊔ g.hom.range := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [biprod.desc_eq]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  · apply sup_le
    · rintro y ⟨x, rfl⟩
      refine ⟨(biprod.inl : M ⟶ M ⊞ N).hom x, ?_⟩
      exact congrArg (fun k : M ⟶ P => k.hom x) (biprod.inl_desc f g)
    · rintro y ⟨x, rfl⟩
      refine ⟨(biprod.inr : N ⟶ M ⊞ N).hom x, ?_⟩
      exact congrArg (fun k : N ⟶ P => k.hom x) (biprod.inr_desc f g)

open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: the quotient presentation of a module-valued spectral term. -/
def a3sv_spectralObjectEQuotientIso {B : Type u} [CommRing B]
    {ι : Type*} [Category ι] (S : Abelian.SpectralObject (ModuleCat.{u} B) ι)
    {i j k l : ι} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l) (n : ℤ) :
    S.E f g h (n - 1) n (n + 1) ≅
      ModuleCat.of B (((S.H n).obj (mk₁ (f ≫ g))) ⧸
        (S.cokernelSequenceE f g h (f ≫ g) rfl (n - 1) n (n + 1)).f.hom.range) := by
  let T := S.cokernelSequenceE f g h (f ≫ g) rfl (n - 1) n (n + 1)
  have he := S.cokernelSequenceE_exact f g h (f ≫ g) rfl (n - 1) n (n + 1)
  exact (IsColimit.coconePointUniqueUpToIso he.gIsCokernel (cokernelIsCokernel T.f)) ≪≫
    ModuleCat.cokernelIsoRangeQuotient T.f

open CategoryTheory.ComposableArrows in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: a spectral term is a quotient by lower-level classes and the kernel of the map to the upper level. -/
def a3sv_spectralObjectERelationsIso {B : Type u} [CommRing B]
    {ι : Type*} [Category ι] (S : Abelian.SpectralObject (ModuleCat.{u} B) ι)
    {i j k l : ι} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l) (n : ℤ) :
    S.E f g h (n - 1) n (n + 1) ≅
      ModuleCat.of B (((S.H n).obj (mk₁ (f ≫ g))) ⧸
        (((S.H n).map (twoδ₂Toδ₁ f g (f ≫ g) rfl)).hom.range ⊔
          ((S.H n).map (twoδ₂Toδ₁ (f ≫ g) h ((f ≫ g) ≫ h) rfl)).hom.ker)) := by
  refine a3sv_spectralObjectEQuotientIso S f g h n ≪≫
    (Submodule.quotEquivOfEq _ _ ?_).toModuleIso
  dsimp only [Abelian.SpectralObject.cokernelSequenceE]
  rw [a3sv_range_biprod_desc]
  congr 1
  exact (S.exact₁ (f ≫ g) h ((f ≫ g) ≫ h) rfl (n - 1) n).moduleCat_range_eq_ker

/-- IntersectionProductSV: quotienting by a source submodule and a kernel computes a quotient inside the image. -/
def a3sv_rangeQuotientEquiv {B : Type u} [CommRing B]
    {M N : Type u} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (f : M →ₗ[B] N) (S : Submodule B M) :
    (M ⧸ (S ⊔ f.ker)) ≃ₗ[B]
      (f.range ⧸ (S.map f).comap f.range.subtype) := by
  let U := (S.map f).comap f.range.subtype
  let q := U.mkQ.comp f.rangeRestrict
  have hk : q.ker = S ⊔ f.ker := by
    ext x
    change U.mkQ (f.rangeRestrict x) = 0 ↔ x ∈ S ⊔ f.ker
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change f x ∈ S.map f ↔ x ∈ S ⊔ f.ker
    exact SetLike.ext_iff.mp (Submodule.comap_map_eq f S) x
  have hf : Function.Surjective f.rangeRestrict := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (q.quotKerEquivOfSurjective (U.mkQ_surjective.comp hf))

open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: a spectral term is the quotient of the upper image by the image from the lower filtration level. -/
def a3sv_spectralObjectEImageIso {B : Type u} [CommRing B]
    {ι : Type*} [Category ι] (S : Abelian.SpectralObject (ModuleCat.{u} B) ι)
    {i j k l : ι} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l) (n : ℤ) :
    let a := ((S.H n).map (twoδ₂Toδ₁ f g (f ≫ g) rfl)).hom
    let b := ((S.H n).map (twoδ₂Toδ₁ (f ≫ g) h ((f ≫ g) ≫ h) rfl)).hom
    S.E f g h (n - 1) n (n + 1) ≅
      ModuleCat.of B (b.range ⧸ (a.range.map b).comap b.range.subtype) :=
  a3sv_spectralObjectERelationsIso S f g h n ≪≫
    (a3sv_rangeQuotientEquiv _ _).toModuleIso

open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: the interval cohomology of the spectral object of a filtered complex is mapping-cone cohomology. -/
def a3sv_mappingConeSpectralHomologyIso {B : Type u} [CommRing B]
    {ι : Type*} [Category ι] (F : ι ⥤ CochainComplex (ModuleCat.{u} B) ℤ)
    {i j : ι} (f : i ⟶ j) (n : ℤ) :
    ((((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} B)).precomp F).mapHomologicalFunctor
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ) 0)).H n).obj (mk₁ f) ≅
      (CochainComplex.mappingCone (F.map f)).homology n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (ComplexShape.up ℤ) n).app _

open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: the direct mapping-cone spectral object is identified
with complex homology without a precomposition comparison. -/
def a3sv_mappingConeDirectHomologyIso {B : Type u} [CommRing B]
    {X Y : CochainComplex (ModuleCat.{u} B) ℤ} (f : X ⟶ Y) (n : ℤ) :
    ((((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} B)).mapHomologicalFunctor
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} B)
        (ComplexShape.up ℤ) 0)).H n).obj (mk₁ f)) ≅
      (CochainComplex.mappingCone f).homology n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B)
    (ComplexShape.up ℤ) n).app (CochainComplex.mappingCone f)

/-- IntersectionProductSV: the connecting morphism of the mapping-cone spectral
object is the homology connecting morphism of the canonical cone triangle. -/
theorem a3sv_mappingConeSpectral_delta_eq {B : Type u} [CommRing B]
    {C D E : CochainComplex (ModuleCat.{u} B) ℤ} (f : C ⟶ D) (g : D ⟶ E)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    let S := (HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} B)).mapHomologicalFunctor
        (HomotopyCategory.homologyFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ) 0)
    S.δ f g n₀ n₁ h =
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} B)
        (ComplexShape.up ℤ) 0).homologySequenceδ
        ((HomotopyCategory.quotient (ModuleCat.{u} B) (ComplexShape.up ℤ)).mapTriangle.obj
          (CochainComplex.mappingConeCompTriangle f g)) n₀ n₁ h := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the mapping-cone connecting morphism factors through
the shifted homology map of the canonical complex-level cone triangle. -/
theorem a3sv_mappingConeSpectral_delta_factorization {B : Type u} [CommRing B]
    {C D E : CochainComplex (ModuleCat.{u} B) ℤ} (f : C ⟶ D) (g : D ⟶ E)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    let X := HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} B)
    let H := HomotopyCategory.homologyFunctor
      (ModuleCat.{u} B) (ComplexShape.up ℤ) 0
    (X.mapHomologicalFunctor H).δ f g n₀ n₁ h =
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B)
        (ComplexShape.up ℤ) n₀).hom.app (CochainComplex.mappingCone g) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
        (ComplexShape.up ℤ) 0).shiftMap
          (CochainComplex.mappingConeCompTriangle f g).mor₃ n₀ n₁ (by omega) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B)
        (ComplexShape.up ℤ) n₁).inv.app (CochainComplex.mappingCone f) := by
  dsimp only
  exact CochainComplex.homologySequenceδ_quotient_mapTriangle_obj
    (CochainComplex.mappingConeCompTriangle f g) n₀ n₁ h

/-- IntersectionProductSV: the canonical comparison between the image of a
one-arrow diagram and the diagram of the mapped arrow is identity on objects. -/
theorem a3sv_mapComposableArrowsObjMk₁Iso_components
    {C : Type v} {D : Type u} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} (f : X ⟶ Y) :
    (F.mapComposableArrowsObjMk₁Iso f).hom.app 0 = 𝟙 (F.obj X) ∧
      (F.mapComposableArrowsObjMk₁Iso f).hom.app 1 = 𝟙 (F.obj Y) ∧
      (F.mapComposableArrowsObjMk₁Iso f).inv.app 0 = 𝟙 (F.obj X) ∧
    (F.mapComposableArrowsObjMk₁Iso f).inv.app 1 = 𝟙 (F.obj Y) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the cone comparison attached to the canonical
mapped-arrow is the identity chain map. -/
theorem a3sv_mappingConeMappedArrow_eq_id {B : Type} [CommRing B]
    (F : ℤ ⥤ CochainComplex (ModuleCat.{0} B) ℤ)
    {i j : ℤ} (f : i ⟶ j) :
    (HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
      (F.mapComposableArrowsObjMk₁Iso f).hom = 𝟙 _ := by
  dsimp [HomotopyCategory.composableArrowsFunctor]
  apply HomologicalComplex.Hom.ext
  funext n
  apply CochainComplex.mappingCone.ext_from (F.map f) (n + 1) n rfl
  · simp [CochainComplex.mappingCone.map]
  · simp [CochainComplex.mappingCone.map]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the inverse canonical mapped-arrow comparison also
induces the identity chain map on cones. -/
theorem a3sv_mappingConeMappedArrow_inv_eq_id {B : Type} [CommRing B]
    (F : ℤ ⥤ CochainComplex (ModuleCat.{0} B) ℤ)
    {i j : ℤ} (f : i ⟶ j) :
    (HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
      (F.mapComposableArrowsObjMk₁Iso f).inv = 𝟙 _ := by
  dsimp [HomotopyCategory.composableArrowsFunctor]
  apply HomologicalComplex.Hom.ext
  funext n
  apply CochainComplex.mappingCone.ext_from (F.map f) (n + 1) n rfl
  · simp [CochainComplex.mappingCone.map]
  · simp [CochainComplex.mappingCone.map]

/-- IntersectionProductSV: mapping a composable pair is compatible with its
two restrictions to one-arrow diagrams. -/
theorem a3sv_mapComposableArrows_restrictions
    {C : Type v} {D : Type u} [Category C] [Category D] (F : C ⥤ D)
    {i j k : C} (f : i ⟶ j) (g : j ⟶ k) :
    (F.mapComposableArrows 1).map
        (ComposableArrows.twoδ₂Toδ₁ f g (f ≫ g) rfl) ≫
        (ComposableArrows.isoMk₁ (Iso.refl (F.obj i)) (Iso.refl (F.obj k))).hom =
      (ComposableArrows.isoMk₁ (Iso.refl (F.obj i)) (Iso.refl (F.obj j))).hom ≫
        ComposableArrows.twoδ₂Toδ₁
          (F.map f) (F.map g) (F.map f ≫ F.map g) rfl ∧
    (F.mapComposableArrows 1).map
        (ComposableArrows.twoδ₁Toδ₀ f g (f ≫ g) rfl) ≫
        (ComposableArrows.isoMk₁ (Iso.refl (F.obj j)) (Iso.refl (F.obj k))).hom =
      (ComposableArrows.isoMk₁ (Iso.refl (F.obj i)) (Iso.refl (F.obj k))).hom ≫
        ComposableArrows.twoδ₁Toδ₀
          (F.map f) (F.map g) (F.map f ≫ F.map g) rfl := by
  constructor <;> apply ComposableArrows.hom_ext₁ <;> simp

/-- IntersectionProductSV: the endpoint restrictions of the mapped two-arrow
comparison agree with the canonical one-arrow comparisons. -/
theorem a3sv_mapComposableArrowsObjMk₂Iso_restrictions
    {C : Type v} {D : Type u} [Category C] [Category D] (F : C ⥤ D)
    {i j k : C} (f : i ⟶ j) (g : j ⟶ k) :
    (F.mapComposableArrowsObjMk₁Iso g).inv ≫
        (ComposableArrows.isoMk₁
          (Iso.refl (F.obj j)) (Iso.refl (F.obj k)) (by simp)).hom =
      (ComposableArrows.functorArrows D 1 2 2 (by omega) (by omega)).map
        (F.mapComposableArrowsObjMk₂Iso f g).hom ∧
    (F.mapComposableArrowsObjMk₁Iso f).inv ≫
        (ComposableArrows.isoMk₁
          (Iso.refl (F.obj i)) (Iso.refl (F.obj j)) (by simp)).hom =
      (ComposableArrows.functorArrows D 0 1 2 (by omega) (by omega)).map
        (F.mapComposableArrowsObjMk₂Iso f g).hom := by
  constructor <;> apply ComposableArrows.hom_ext₁ <;>
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ <;> simp

open CategoryTheory.Pretriangulated CategoryTheory.ComposableArrows in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: precomposition changes the spectral triangle only
by the canonical mapped-arrow comparisons. -/
noncomputable def a3sv_spectralObjectPrecompTriangleIso
    {C : Type u} {ι : Type v} {ι' : Type w}
    [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    [Category ι] [Category ι']
    (X : CategoryTheory.Triangulated.SpectralObject C ι) (F : ι' ⥤ ι)
    {i j k : ι'} (f : i ⟶ j) (g : j ⟶ k) :
    (X.precomp F).triangle f g ≅ X.triangle (F.map f) (F.map g) := by
  refine Triangle.isoMk _ _
    (X.ω₁.mapIso (isoMk₁ (Iso.refl _) (Iso.refl _)))
    (X.ω₁.mapIso (isoMk₁ (Iso.refl _) (Iso.refl _)))
    (X.ω₁.mapIso (isoMk₁ (Iso.refl _) (Iso.refl _))) ?_ ?_ ?_
  · dsimp
    change X.ω₁.map ((F.mapComposableArrows 1).map _) ≫ _ = _
    simp only [← Functor.map_comp]
    apply congrArg X.ω₁.map
    apply ComposableArrows.hom_ext₁ <;> simp
  · dsimp
    change X.ω₁.map ((F.mapComposableArrows 1).map _) ≫ _ = _
    simp only [← Functor.map_comp]
    apply congrArg X.ω₁.map
    apply ComposableArrows.hom_ext₁ <;> simp
  · have hn := X.δ'.naturality (F.mapComposableArrowsObjMk₂Iso f g).hom
    dsimp [CategoryTheory.Triangulated.SpectralObject.precomp,
      CategoryTheory.Triangulated.SpectralObject.δ] at hn ⊢
    rw [← cancel_epi (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).inv)]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc,
      Iso.inv_hom_id, Category.id_comp] at hn ⊢
    have hr := a3sv_mapComposableArrowsObjMk₂Iso_restrictions F f g
    rw [hr.1, hr.2]
    simpa [ComposableArrows.functorArrows] using hn.symm

open CategoryTheory.Pretriangulated in
/-- IntersectionProductSV: the connecting morphisms before and after
precomposition correspond under the canonical spectral-triangle isomorphism. -/
theorem a3sv_spectralObjectPrecomp_delta_naturality
    {C : Type u} {A : Type x} {ι : Type v} {ι' : Type w}
    [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    [Category A] [Abelian A] [Category ι] [Category ι']
    (X : CategoryTheory.Triangulated.SpectralObject C ι) (F : ι' ⥤ ι)
    (H : C ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]
    {i j k : ι'} (f : i ⟶ j) (g : j ⟶ k)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    let e := a3sv_spectralObjectPrecompTriangleIso X F f g
    (H.shift n₀).map e.hom.hom₃ ≫
        (X.mapHomologicalFunctor H).δ (F.map f) (F.map g) n₀ n₁ h =
      ((X.precomp F).mapHomologicalFunctor H).δ f g n₀ n₁ h ≫
        (H.shift n₁).map e.hom.hom₁ := by
  dsimp only
  exact H.homologySequenceδ_naturality
    (a3sv_spectralObjectPrecompTriangleIso X F f g).hom n₀ n₁ h

open CategoryTheory.Pretriangulated in
/-- IntersectionProductSV: the connecting morphism after precomposition is
conjugate to the original connecting morphism by the spectral-triangle comparison. -/
theorem a3sv_spectralObjectPrecomp_delta_conjugation
    {C : Type u} {A : Type x} {ι : Type v} {ι' : Type w}
    [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    [Category A] [Abelian A] [Category ι] [Category ι']
    (X : CategoryTheory.Triangulated.SpectralObject C ι) (F : ι' ⥤ ι)
    (H : C ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]
    {i j k : ι'} (f : i ⟶ j) (g : j ⟶ k)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    let e := a3sv_spectralObjectPrecompTriangleIso X F f g
    ((X.precomp F).mapHomologicalFunctor H).δ f g n₀ n₁ h =
      (H.shift n₀).map e.hom.hom₃ ≫
        (X.mapHomologicalFunctor H).δ (F.map f) (F.map g) n₀ n₁ h ≫
          (H.shift n₁).map e.inv.hom₁ := by
  dsimp only
  have hn := a3sv_spectralObjectPrecomp_delta_naturality X F H f g n₀ n₁ h
  rw [← cancel_mono ((H.shift n₁).map
    (a3sv_spectralObjectPrecompTriangleIso X F f g).hom.hom₁)]
  simpa [Category.assoc, ← Functor.map_comp] using hn.symm

open CategoryTheory.Pretriangulated CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: the endpoint components of the precomposition
triangle comparison are the canonical one-arrow comparisons. -/
theorem a3sv_spectralObjectPrecompTriangleIso_endpoint_components
    {C : Type u} {ι : Type v} {ι' : Type w}
    [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    [Category ι] [Category ι']
    (X : CategoryTheory.Triangulated.SpectralObject C ι) (F : ι' ⥤ ι)
    {i j k : ι'} (f : i ⟶ j) (g : j ⟶ k) :
    (a3sv_spectralObjectPrecompTriangleIso X F f g).hom.hom₁ =
        X.ω₁.map (F.mapComposableArrowsObjMk₁Iso f).hom ∧
      (a3sv_spectralObjectPrecompTriangleIso X F f g).hom.hom₃ =
        X.ω₁.map (F.mapComposableArrowsObjMk₁Iso g).hom := by
  constructor <;> apply congrArg X.ω₁.map <;>
    apply ComposableArrows.hom_ext₁ <;> rfl

open CategoryTheory.Pretriangulated CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: the inverse endpoint components of the
precomposition triangle comparison are the inverse one-arrow comparisons. -/
theorem a3sv_spectralObjectPrecompTriangleIso_inverse_endpoint_components
    {C : Type u} {ι : Type v} {ι' : Type w}
    [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    [Category ι] [Category ι']
    (X : CategoryTheory.Triangulated.SpectralObject C ι) (F : ι' ⥤ ι)
    {i j k : ι'} (f : i ⟶ j) (g : j ⟶ k) :
    (a3sv_spectralObjectPrecompTriangleIso X F f g).inv.hom₁ =
        X.ω₁.map (F.mapComposableArrowsObjMk₁Iso f).inv ∧
      (a3sv_spectralObjectPrecompTriangleIso X F f g).inv.hom₃ =
        X.ω₁.map (F.mapComposableArrowsObjMk₁Iso g).inv := by
  constructor <;> apply congrArg X.ω₁.map <;>
    apply ComposableArrows.hom_ext₁ <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: inverse homology-factor transport across the
canonical mapped-arrow cone comparison. -/
theorem a3sv_mappingConeMappedArrow_homology_inverse_naturality
    {B : Type} [CommRing B]
    (F : ℤ ⥤ CochainComplex (ModuleCat.{0} B) ℤ)
    {i j : ℤ} (f : i ⟶ j) (n : ℤ) :
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
      (ComplexShape.up ℤ) n).app
        ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).obj
          ((F.mapComposableArrows 1).obj (ComposableArrows.mk₁ f)))).inv ≫
      ((HomotopyCategory.homologyFunctor (ModuleCat.{0} B)
        (ComplexShape.up ℤ) 0).shift n).map
          ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)).ω₁.map
            (F.mapComposableArrowsObjMk₁Iso f).hom) =
    HomologicalComplex.homologyMap
        ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
          (F.mapComposableArrowsObjMk₁Iso f).hom) n ≫
      ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
        (ComplexShape.up ℤ) n).app (CochainComplex.mappingCone (F.map f))).inv := by
  rw [← cancel_mono ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
    (ComplexShape.up ℤ) n).hom.app (CochainComplex.mappingCone (F.map f)))]
  rw [Category.assoc, a3sv_mappingConeMappedArrow_homology_naturality F f n]
  simp
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: homology transports the inverse mapped-arrow
comparison to the inverse cone comparison. -/
theorem a3sv_mappingConeMappedArrow_inv_homology_naturality
    {B : Type} [CommRing B]
    (F : ℤ ⥤ CochainComplex (ModuleCat.{0} B) ℤ)
    {i j : ℤ} (f : i ⟶ j) (n : ℤ) :
    ((HomotopyCategory.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shift n).map
        ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)).ω₁.map
          (F.mapComposableArrowsObjMk₁Iso f).inv) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
        (ComplexShape.up ℤ) n).hom.app
          ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).obj
            ((F.mapComposableArrows 1).obj (ComposableArrows.mk₁ f))) =
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
      (ComplexShape.up ℤ) n).hom.app (CochainComplex.mappingCone (F.map f)) ≫
      HomologicalComplex.homologyMap
        ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
          (F.mapComposableArrowsObjMk₁Iso f).inv) n := by
  exact (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
    (ComplexShape.up ℤ) n).hom.naturality
      ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
        (F.mapComposableArrowsObjMk₁Iso f).inv)

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: after the direct cone factor is inverted, inverse
mapped-arrow transport is exactly the induced cone homology map. -/
theorem a3sv_mappingConeMappedArrow_inv_homology_typed
    {B : Type} [CommRing B]
    (F : ℤ ⥤ CochainComplex (ModuleCat.{0} B) ℤ)
    {i j : ℤ} (f : i ⟶ j) (n : ℤ) :
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
      (ComplexShape.up ℤ) n).inv.app (CochainComplex.mappingCone (F.map f)) ≫
    ((HomotopyCategory.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shift n).map
        ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)).ω₁.map
          (F.mapComposableArrowsObjMk₁Iso f).inv) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
        (ComplexShape.up ℤ) n).hom.app
          ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).obj
            ((F.mapComposableArrows 1).obj (ComposableArrows.mk₁ f))) =
    HomologicalComplex.homologyMap
      ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
        (F.mapComposableArrowsObjMk₁Iso f).inv) n := by
  have he := congrArg (fun x =>
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
      (ComplexShape.up ℤ) n).inv.app (CochainComplex.mappingCone (F.map f)) ≫ x)
    (a3sv_mappingConeMappedArrow_inv_homology_naturality F f n)
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using he

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: inverse mapped-arrow transport remains explicit
after the composable-cone connecting map. -/
theorem a3sv_mappingConeMappedArrow_inv_homology_shiftMap
    {B : Type} [CommRing B]
    (F : ℤ ⥤ CochainComplex (ModuleCat.{0} B) ℤ)
    {i j k : ℤ} (f : i ⟶ j) (g : j ⟶ k)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
          n₀ n₁ (by omega) ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
      (ComplexShape.up ℤ) n₁).inv.app (CochainComplex.mappingCone (F.map f)) ≫
    ((HomotopyCategory.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shift n₁).map
        ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)).ω₁.map
          (F.mapComposableArrowsObjMk₁Iso f).inv) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
        (ComplexShape.up ℤ) n₁).hom.app
          ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).obj
            ((F.mapComposableArrows 1).obj (ComposableArrows.mk₁ f))) =
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
          n₀ n₁ (by omega) ≫
    HomologicalComplex.homologyMap
      ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
        (F.mapComposableArrowsObjMk₁Iso f).inv) n₁ := by
  have he := congrArg (fun x =>
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
          n₀ n₁ (by omega) ≫ x)
    (a3sv_mappingConeMappedArrow_inv_homology_typed F f n₁)
  simpa only [Category.assoc] using he

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: inverse endpoint transport is compatible with both
mapped-arrow cone comparisons around a composable-cone connecting map. -/
theorem a3sv_mappingConeMappedArrow_inv_homologyMap
    {B : Type} [CommRing B]
    (F : ℤ ⥤ CochainComplex (ModuleCat.{0} B) ℤ)
    {i j k : ℤ} (f : i ⟶ j) (g : j ⟶ k)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    HomologicalComplex.homologyMap
      ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
        (F.mapComposableArrowsObjMk₁Iso g).hom) n₀ ≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
          n₀ n₁ (by omega) ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
      (ComplexShape.up ℤ) n₁).inv.app (CochainComplex.mappingCone (F.map f)) ≫
    ((HomotopyCategory.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shift n₁).map
        ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)).ω₁.map
          (F.mapComposableArrowsObjMk₁Iso f).inv) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
        (ComplexShape.up ℤ) n₁).hom.app
          ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).obj
            ((F.mapComposableArrows 1).obj (ComposableArrows.mk₁ f))) =
    HomologicalComplex.homologyMap
      ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
        (F.mapComposableArrowsObjMk₁Iso g).hom) n₀ ≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
          n₀ n₁ (by omega) ≫
    HomologicalComplex.homologyMap
      ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
        (F.mapComposableArrowsObjMk₁Iso f).inv) n₁ := by
  have he := congrArg (fun x =>
    HomologicalComplex.homologyMap
      ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
        (F.mapComposableArrowsObjMk₁Iso g).hom) n₀ ≫ x)
    (a3sv_mappingConeMappedArrow_inv_homology_shiftMap F f g n₀ n₁ h)
  simpa only [Category.assoc] using he

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the full source homology factor preserves inverse
endpoint transport across a composable-cone connecting map. -/
theorem a3sv_mappingConeMappedArrow_inv_homologyFactor
    {B : Type} [CommRing B]
    (F : ℤ ⥤ CochainComplex (ModuleCat.{0} B) ℤ)
    {i j k : ℤ} (f : i ⟶ j) (g : j ⟶ k)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
      (ComplexShape.up ℤ) n₀).hom.app
        ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).obj
          ((F.mapComposableArrows 1).obj (ComposableArrows.mk₁ g))) ≫
    HomologicalComplex.homologyMap
      ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
        (F.mapComposableArrowsObjMk₁Iso g).hom) n₀ ≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
          n₀ n₁ (by omega) ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
      (ComplexShape.up ℤ) n₁).inv.app (CochainComplex.mappingCone (F.map f)) ≫
    ((HomotopyCategory.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shift n₁).map
        ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)).ω₁.map
          (F.mapComposableArrowsObjMk₁Iso f).inv) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
        (ComplexShape.up ℤ) n₁).hom.app
          ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).obj
            ((F.mapComposableArrows 1).obj (ComposableArrows.mk₁ f))) =
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
      (ComplexShape.up ℤ) n₀).hom.app
        ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).obj
          ((F.mapComposableArrows 1).obj (ComposableArrows.mk₁ g))) ≫
    HomologicalComplex.homologyMap
      ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
        (F.mapComposableArrowsObjMk₁Iso g).hom) n₀ ≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
          n₀ n₁ (by omega) ≫
    HomologicalComplex.homologyMap
      ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
        (F.mapComposableArrowsObjMk₁Iso f).inv) n₁ := by
  have he := congrArg (fun x =>
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
      (ComplexShape.up ℤ) n₀).hom.app
        ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).obj
          ((F.mapComposableArrows 1).obj (ComposableArrows.mk₁ g))) ≫ x)
    (a3sv_mappingConeMappedArrow_inv_homologyMap F f g n₀ n₁ h)
  simpa only [Category.assoc] using he

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the complex-homology composite underlying the
connecting morphism of a precomposed mapping-cone spectral object. -/
def a3sv_mappingConePrecompHomologyMap {B : Type} [CommRing B]
    (F : ℤ ⥤ CochainComplex (ModuleCat.{0} B) ℤ)
    {i j k : ℤ} (f : i ⟶ j) (g : j ⟶ k)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    let X := HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)
    let H := HomotopyCategory.homologyFunctor
      (ModuleCat.{0} B) (ComplexShape.up ℤ) 0
    ((((X.precomp F).mapHomologicalFunctor H).H n₀).obj (ComposableArrows.mk₁ g) ⟶
      (((X.precomp F).mapHomologicalFunctor H).H n₁).obj (ComposableArrows.mk₁ f)) :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
    (ComplexShape.up ℤ) n₀).hom.app
      ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).obj
        ((F.mapComposableArrows 1).obj (ComposableArrows.mk₁ g))) ≫
  HomologicalComplex.homologyMap
    ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{0} B)).map
      (F.mapComposableArrowsObjMk₁Iso g).hom) n₀ ≫
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
    (ComplexShape.up ℤ) 0).shiftMap
      (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
        n₀ n₁ (by omega) ≫
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
    (ComplexShape.up ℤ) n₁).inv.app (CochainComplex.mappingCone (F.map f)) ≫
  ((HomotopyCategory.homologyFunctor (ModuleCat.{0} B)
    (ComplexShape.up ℤ) 0).shift n₁).map
    ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)).ω₁.map
      (F.mapComposableArrowsObjMk₁Iso f).inv)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the connecting morphism of a precomposed
mapping-cone spectral object is its packaged complex-homology map. -/
theorem a3sv_mappingConePrecomp_delta_factorization {B : Type} [CommRing B]
    (F : ℤ ⥤ CochainComplex (ModuleCat.{0} B) ℤ)
    {i j k : ℤ} (f : i ⟶ j) (g : j ⟶ k)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    let X := HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)
    let H := HomotopyCategory.homologyFunctor
      (ModuleCat.{0} B) (ComplexShape.up ℤ) 0
    ((X.precomp F).mapHomologicalFunctor H).δ f g n₀ n₁ h =
      a3sv_mappingConePrecompHomologyMap F f g n₀ n₁ h := by
  dsimp only [a3sv_mappingConePrecompHomologyMap]
  rw [a3sv_spectralObjectPrecomp_delta_conjugation
    (HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)) F
    (HomotopyCategory.homologyFunctor (ModuleCat.{0} B) (ComplexShape.up ℤ) 0)
    f g n₀ n₁ h]
  have hc := a3sv_spectralObjectPrecompTriangleIso_endpoint_components
    (HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)) F f g
  have hi := a3sv_spectralObjectPrecompTriangleIso_inverse_endpoint_components
    (HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)) F f g
  rw [hc.2, hi.1]
  rw [a3sv_mappingConeSpectral_delta_factorization
    (F.map f) (F.map g) n₀ n₁ h]
  have hn := a3sv_mappingConeMappedArrow_homology_naturality F g n₀
  have hn' := congrArg (fun q => q ≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
          n₀ n₁ (by omega) ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} B)
      (ComplexShape.up ℤ) n₁).inv.app (CochainComplex.mappingCone (F.map f)) ≫
    ((HomotopyCategory.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.up ℤ) 0).shift n₁).map
        ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)).ω₁.map
          (F.mapComposableArrowsObjMk₁Iso f).inv)) hn
  simpa only [Category.assoc] using hn'

/-- IntersectionProductSV: the total-column spectral connecting morphism is
the packaged cone-homology map for the extended column filtration. -/
theorem a3sv_totalColumn_delta_factorization {B : Type} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{0} B) ℕ) ℕ)
    {i j k : ℤ} (f : i ⟶ j) (g : j ⟶ k)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (a3sv_totalColumnSpectralObject K).δ f g n₀ n₁ h =
      a3sv_mappingConePrecompHomologyMap
        (a3sv_totalColumnExtendedFunctor K) f g n₀ n₁ h := by
  change (((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)).precomp
    (a3sv_totalColumnExtendedFunctor K)).mapHomologicalFunctor
      (HomotopyCategory.homologyFunctor (ModuleCat.{0} B)
        (ComplexShape.up ℤ) 0)).δ f g n₀ n₁ h = _
  exact a3sv_mappingConePrecomp_delta_factorization
    (a3sv_totalColumnExtendedFunctor K) f g n₀ n₁ h

/-- IntersectionProductSV: the cone of an injective map computes the homology
of its cokernel complex. -/
def a3sv_mappingConeCokernelHomologyIso {B : Type u} [CommRing B]
    {C D : CochainComplex (ModuleCat.{u} B) ℤ} (f : C ⟶ D) [Mono f] (n : ℤ) :
    (CochainComplex.mappingCone f).homology n ≅ (cokernel f).homology n := by
  let S := ShortComplex.cokernelSequence f
  letI : Mono S.f := (show Mono f from inferInstance)
  have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact f }
  letI := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  let g := HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.descShortComplex S) n
  have hg : IsIso g := (quasiIsoAt_iff_isIso_homologyMap
    (CochainComplex.mappingCone.descShortComplex S) n).mp inferInstance
  exact @asIso _ _ _ _ g hg

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the mapping-cone-to-cokernel homology comparison
is natural for commutative squares of monomorphisms. -/
theorem a3sv_mappingConeCokernelHomologyIso_naturality
    {B : Type u} [CommRing B]
    {C₁ D₁ C₂ D₂ : CochainComplex (ModuleCat.{u} B) ℤ}
    (f₁ : C₁ ⟶ D₁) (f₂ : C₂ ⟶ D₂) [Mono f₁] [Mono f₂]
    (a : C₁ ⟶ C₂) (b : D₁ ⟶ D₂) (h : f₁ ≫ b = a ≫ f₂) (n : ℤ) :
    HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.map f₁ f₂ a b h) n ≫
      (a3sv_mappingConeCokernelHomologyIso f₂ n).hom =
    (a3sv_mappingConeCokernelHomologyIso f₁ n).hom ≫
      HomologicalComplex.homologyMap (cokernel.map f₁ f₂ a b h) n := by
  let S₁ := ShortComplex.cokernelSequence f₁
  let S₂ := ShortComplex.cokernelSequence f₂
  let c := cokernel.map f₁ f₂ a b h
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk a b c h.symm (by
    dsimp [S₁, S₂, c]
    simp)
  have hn := CochainComplex.mappingCone.descShortComplex_naturality φ
  have hh := congrArg (fun k => HomologicalComplex.homologyMap k n) hn
  dsimp only [a3sv_mappingConeCokernelHomologyIso, φ, S₁, S₂, c,
    asIso_hom] at hh ⊢
  simpa [ShortComplex.cokernelSequence, ShortComplex.homMk,
    HomologicalComplex.homologyMap_comp, Category.assoc] using hh

/-- IntersectionProductSV: the cokernels of two composable monomorphisms form
the canonical three-term quotient sequence. -/
def a3sv_cokernelCompShortComplex
    {C : Type u} [Category C] [Abelian C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : ShortComplex C :=
  ShortComplex.mk
    (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (cokernel.map (f ≫ g) g f (𝟙 _) (by simp)) (by aesop)

/-- IntersectionProductSV: the canonical quotient sequence of two composable
monomorphisms is short exact. -/
theorem a3sv_cokernelCompShortComplex_shortExact
    {C : Type u} [Category C] [Abelian C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] :
    (a3sv_cokernelCompShortComplex f g).ShortExact := by
  have hmono : Mono (a3sv_cokernelCompShortComplex f g).f := by
    dsimp [a3sv_cokernelCompShortComplex]
    apply Abelian.mono_cokernel_map_of_isPullback
    refine IsPullback.of_vert_isIso_mono (fst := f) (snd := 𝟙 _)
      (f := g) (g := f ≫ g) ?_
    exact ⟨by simp⟩
  have hepi : Epi (a3sv_cokernelCompShortComplex f g).g := by
    dsimp [a3sv_cokernelCompShortComplex, cokernel.map]
    apply cokernel.desc_epi
  exact
    { exact := (kernelCokernelCompSequence_exact f g).exact 3 (by omega)
      mono_f := hmono
      epi_g := hepi }

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: a functor preserving cokernels carries the quotient
sequence of composable maps to the quotient sequence of their images. -/
def a3sv_cokernelCompShortComplexMapIso
    {A D : Type*} [Category A] [Abelian A] [Category D] [Abelian D]
    (F : A ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesColimitsOfShape WalkingParallelPair F]
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (a3sv_cokernelCompShortComplex f g).map F ≅
      a3sv_cokernelCompShortComplex (F.map f) (F.map g) := by
  let e1 := PreservesCokernel.iso F f
  let e3 := PreservesCokernel.iso F g
  let e2 := PreservesCokernel.iso F (f ≫ g) ≪≫
    cokernel.mapIso (F.map (f ≫ g)) (F.map f ≫ F.map g) (Iso.refl _) (Iso.refl _)
      (by simp)
  have h1 : F.map (cokernel.π f) ≫ e1.hom = cokernel.π (F.map f) :=
    PreservesCokernel.π_iso_hom F f
  have h3 : F.map (cokernel.π g) ≫ e3.hom = cokernel.π (F.map g) :=
    PreservesCokernel.π_iso_hom F g
  have h2 : F.map (cokernel.π (f ≫ g)) ≫ e2.hom =
      cokernel.π (F.map f ≫ F.map g) := by
    dsimp only [e2, Iso.trans_hom, cokernel.mapIso_hom]
    rw [← Category.assoc, PreservesCokernel.π_iso_hom]
    simp
  have hepi {U V : A} (a : U ⟶ V) : Epi (F.map (cokernel.π a)) := by
    have h : Epi (F.map (cokernel.π a) ≫ (PreservesCokernel.iso F a).hom) := by
      rw [PreservesCokernel.π_iso_hom]
      infer_instance
    exact (epi_comp_iff_of_isIso (F.map (cokernel.π a))
      (PreservesCokernel.iso F a).hom).mp h
  letI := hepi f
  letI := hepi (f ≫ g)
  refine ShortComplex.isoMk e1 e2 e3 ?_ ?_
  · apply (cancel_epi (F.map (cokernel.π f))).mp
    change F.map (cokernel.π f) ≫ e1.hom ≫
        (a3sv_cokernelCompShortComplex (F.map f) (F.map g)).f =
      F.map (cokernel.π f) ≫ F.map (a3sv_cokernelCompShortComplex f g).f ≫ e2.hom
    rw [reassoc_of% h1]
    have hs : cokernel.π f ≫ (a3sv_cokernelCompShortComplex f g).f =
        g ≫ cokernel.π (f ≫ g) := by simp [a3sv_cokernelCompShortComplex]
    rw [← Category.assoc (F.map (cokernel.π f)), ← F.map_comp (cokernel.π f) (a3sv_cokernelCompShortComplex f g).f,
      hs, F.map_comp g (cokernel.π (f ≫ g)),
      Category.assoc, h2]
    simp [a3sv_cokernelCompShortComplex]
  · apply (cancel_epi (F.map (cokernel.π (f ≫ g)))).mp
    change F.map (cokernel.π (f ≫ g)) ≫ e2.hom ≫
        (a3sv_cokernelCompShortComplex (F.map f) (F.map g)).g =
      F.map (cokernel.π (f ≫ g)) ≫ F.map (a3sv_cokernelCompShortComplex f g).g ≫ e3.hom
    rw [reassoc_of% h2]
    have hs : cokernel.π (f ≫ g) ≫ (a3sv_cokernelCompShortComplex f g).g =
        cokernel.π g := by simp [a3sv_cokernelCompShortComplex]
    rw [← Category.assoc (F.map (cokernel.π (f ≫ g))), ← F.map_comp (cokernel.π (f ≫ g)) (a3sv_cokernelCompShortComplex f g).g, hs, h3]
    simp [a3sv_cokernelCompShortComplex]

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: representatives in two successive filtration terms
compute the connecting map of their three quotient complexes. -/
theorem a3sv_cokernelComp_delta_representatives
    {D : Type u} [Category D] [Abelian D] {ι : Type*} {c : ComplexShape ι}
    {X Y Z : HomologicalComplex D c} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Mono f] [Mono g] (i j : ι) (hij : c.Rel i j) {A : D}
    (a : A ⟶ (cokernel g).cycles i) (b : A ⟶ (cokernel f).cycles j)
    (z : A ⟶ Z.X i) (y : A ⟶ Y.X j)
    (ha : a ≫ (cokernel g).iCycles i = z ≫ (cokernel.π g).f i)
    (hb : b ≫ (cokernel f).iCycles j = y ≫ (cokernel.π f).f j)
    (hyz : y ≫ g.f j = z ≫ Z.d i j) :
    a ≫ (cokernel g).homologyπ i ≫
        (a3sv_cokernelCompShortComplex_shortExact f g).δ i j hij =
      b ≫ (cokernel f).homologyπ j := by
  let S := a3sv_cokernelCompShortComplex f g
  have hf : (cokernel.π f).f j ≫ S.f.f j =
      g.f j ≫ (cokernel.π (f ≫ g)).f j := by
    have hh : cokernel.π f ≫ S.f = g ≫ cokernel.π (f ≫ g) := by
      dsimp [S, a3sv_cokernelCompShortComplex]
      simp
    exact congrArg (fun t => t.f j) hh
  have hg : (cokernel.π (f ≫ g)).f i ≫ S.g.f i = (cokernel.π g).f i := by
    have hh : cokernel.π (f ≫ g) ≫ S.g = cokernel.π g := by
      dsimp [S, a3sv_cokernelCompShortComplex]
      simp
    exact congrArg (fun t => t.f i) hh
  rw [← Category.assoc]
  apply (a3sv_cokernelCompShortComplex_shortExact f g).δ_eq' i j hij
    (a ≫ (cokernel g).homologyπ i)
    (z ≫ (cokernel.π (f ≫ g)).f i ≫ (cokernel (f ≫ g)).pOpcycles i) b
  · dsimp only [S, a3sv_cokernelCompShortComplex] at hg ⊢
    simp only [Category.assoc, HomologicalComplex.p_opcyclesMap,
      HomologicalComplex.homology_π_ι]
    rw [← Category.assoc a, ha]
    simp only [Category.assoc]
    rw [reassoc_of% hg]
  · dsimp only [S, a3sv_cokernelCompShortComplex] at hf ⊢
    rw [← cancel_mono ((cokernel (f ≫ g)).iCycles j)]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.opcyclesToCycles_iCycles, HomologicalComplex.p_fromOpcycles]
    rw [← Category.assoc b, hb]
    simp only [Category.assoc]
    rw [hf, (cokernel.π (f ≫ g)).comm i j,
      ← Category.assoc y, hyz]
    simp only [Category.assoc]

/-- IntersectionProductSV: the first map in the composable-cokernel sequence
comes from the canonical map between the corresponding cokernel sequences. -/
def a3sv_cokernelSequenceHomLeft
    {C : Type u} [Category C] [Abelian C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShortComplex.cokernelSequence f ⟶
      ShortComplex.cokernelSequence (f ≫ g) :=
  ShortComplex.homMk (𝟙 _) g
    (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
      (by simp [ShortComplex.cokernelSequence])
      (by simp [ShortComplex.cokernelSequence])

/-- IntersectionProductSV: the second map in the composable-cokernel sequence
comes from the canonical map between the corresponding cokernel sequences. -/
def a3sv_cokernelSequenceHomRight
    {C : Type u} [Category C] [Abelian C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShortComplex.cokernelSequence (f ≫ g) ⟶
      ShortComplex.cokernelSequence g :=
  ShortComplex.homMk f (𝟙 _)
    (cokernel.map (f ≫ g) g f (𝟙 _) (by simp))
      (by simp [ShortComplex.cokernelSequence])
      (by simp [ShortComplex.cokernelSequence])

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the first mapping-cone comparison descends to the
first map of the composable-cokernel short complex. -/
theorem a3sv_mappingConeComp_desc_left {B : Type u} [CommRing B]
    {X Y Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CochainComplex.mappingConeCompTriangle f g).mor₁ ≫
        CochainComplex.mappingCone.descShortComplex
          (ShortComplex.cokernelSequence (f ≫ g)) =
      CochainComplex.mappingCone.descShortComplex
          (ShortComplex.cokernelSequence f) ≫
        (a3sv_cokernelCompShortComplex f g).f := by
  change CochainComplex.mappingCone.map
      (ShortComplex.cokernelSequence f).f
      (ShortComplex.cokernelSequence (f ≫ g)).f
      (a3sv_cokernelSequenceHomLeft f g).τ₁
      (a3sv_cokernelSequenceHomLeft f g).τ₂
      (a3sv_cokernelSequenceHomLeft f g).comm₁₂.symm ≫ _ = _
  exact CochainComplex.mappingCone.descShortComplex_naturality
    (a3sv_cokernelSequenceHomLeft f g)

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the second mapping-cone comparison descends to the
second map of the composable-cokernel short complex. -/
theorem a3sv_mappingConeComp_desc_right {B : Type u} [CommRing B]
    {X Y Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CochainComplex.mappingConeCompTriangle f g).mor₂ ≫
        CochainComplex.mappingCone.descShortComplex
          (ShortComplex.cokernelSequence g) =
      CochainComplex.mappingCone.descShortComplex
          (ShortComplex.cokernelSequence (f ≫ g)) ≫
        (a3sv_cokernelCompShortComplex f g).g := by
  change CochainComplex.mappingCone.map
      (ShortComplex.cokernelSequence (f ≫ g)).f
      (ShortComplex.cokernelSequence g).f
      (a3sv_cokernelSequenceHomRight f g).τ₁
      (a3sv_cokernelSequenceHomRight f g).τ₂
      (a3sv_cokernelSequenceHomRight f g).comm₁₂.symm ≫ _ = _
  exact CochainComplex.mappingCone.descShortComplex_naturality
    (a3sv_cokernelSequenceHomRight f g)

/-- IntersectionProductSV: the third comparison from the cone triangle of two
composable maps to the cone triangle of their cokernel quotient sequence. -/
def a3sv_mappingConeCompCokernelHom₃ {B : Type u} [CommRing B]
    {X Y Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    CochainComplex.mappingCone g ⟶
      CochainComplex.mappingCone (a3sv_cokernelCompShortComplex f g).f :=
  CochainComplex.mappingCone.map g (a3sv_cokernelCompShortComplex f g).f
    (cokernel.π f) (cokernel.π (f ≫ g)) (by
      dsimp [a3sv_cokernelCompShortComplex]
      simp)

/-- IntersectionProductSV: the last cone-to-cokernel descent map, typed at the
third object of the composable-cokernel short complex. -/
def a3sv_mappingConeCompCokernelDesc₃ {B : Type u} [CommRing B]
    {X Y Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    CochainComplex.mappingCone g ⟶ (a3sv_cokernelCompShortComplex f g).X₃ := by
  change CochainComplex.mappingCone g ⟶ cokernel g
  exact CochainComplex.mappingCone.descShortComplex
    (ShortComplex.cokernelSequence g)

/-- IntersectionProductSV: the first cone-to-cokernel descent map, typed at the
first object of the composable-cokernel short complex. -/
def a3sv_mappingConeCompCokernelDesc₁ {B : Type u} [CommRing B]
    {X Y Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    CochainComplex.mappingCone f ⟶ (a3sv_cokernelCompShortComplex f g).X₁ := by
  change CochainComplex.mappingCone f ⟶ cokernel f
  exact CochainComplex.mappingCone.descShortComplex
    (ShortComplex.cokernelSequence f)

/-- IntersectionProductSV: the third cone comparison is induced by the
canonical map from the last cokernel sequence to the quotient short complex. -/
def a3sv_cokernelSequenceHomThird {B : Type u} [CommRing B]
    {X Y Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShortComplex.cokernelSequence g ⟶ a3sv_cokernelCompShortComplex f g :=
  ShortComplex.homMk (cokernel.π f) (cokernel.π (f ≫ g)) (𝟙 _)
    (by simp [a3sv_cokernelCompShortComplex, ShortComplex.cokernelSequence])
    (by simp [a3sv_cokernelCompShortComplex, ShortComplex.cokernelSequence])

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the third cone comparison followed by the quotient
cone descent is the descent map for the last original cone. -/
theorem a3sv_mappingConeCompCokernelHom₃_desc {B : Type u} [CommRing B]
    {X Y Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    a3sv_mappingConeCompCokernelHom₃ f g ≫
        CochainComplex.mappingCone.descShortComplex
          (a3sv_cokernelCompShortComplex f g) =
      CochainComplex.mappingCone.descShortComplex
        (ShortComplex.cokernelSequence g) := by
  change CochainComplex.mappingCone.map
      (ShortComplex.cokernelSequence g).f
      (a3sv_cokernelCompShortComplex f g).f
      (a3sv_cokernelSequenceHomThird f g).τ₁
      (a3sv_cokernelSequenceHomThird f g).τ₂
      (a3sv_cokernelSequenceHomThird f g).comm₁₂.symm ≫ _ = _
  simpa [a3sv_cokernelSequenceHomThird] using
    CochainComplex.mappingCone.descShortComplex_naturality
      (a3sv_cokernelSequenceHomThird f g)

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the chain-level connecting map of a mapping-cone
triangle is the connecting map of the represented short exact sequence after
the cone-to-cokernel homology comparison. -/
theorem a3sv_mappingConeShortExact_delta {B : Type u} [CommRing B]
    (S : ShortComplex (CochainComplex (ModuleCat.{u} B) ℤ))
    (hS : S.ShortExact) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingCone.triangle S.f).mor₃ n₀ n₁ (by omega) =
      HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.descShortComplex S) n₀ ≫
        hS.δ n₀ n₁ h := by
  have ht := CochainComplex.mappingCone.homologySequenceδ_triangleh hS n₀ n₁ h
  rw [CochainComplex.homologySequenceδ_quotient_mapTriangle_obj] at ht
  have hh := congrArg (fun k =>
    (HomotopyCategory.homologyFunctorFactors
      (ModuleCat.{u} B) (ComplexShape.up ℤ) n₀).inv.app _ ≫ k ≫
    (HomotopyCategory.homologyFunctorFactors
      (ModuleCat.{u} B) (ComplexShape.up ℤ) n₁).hom.app _) ht
  dsimp [CochainComplex.mappingCone.triangle] at hh
  dsimp [CochainComplex.mappingCone.triangle]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the third composable-cone comparison commutes with
the connecting maps of the two cone triangles. -/
theorem a3sv_mappingConeCompCokernelHom₃_comm {B : Type u} [CommRing B]
    {X Y Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] :
    (CochainComplex.mappingConeCompTriangle f g).mor₃ ≫
        (CochainComplex.mappingCone.descShortComplex
          (ShortComplex.cokernelSequence f))⟦1⟧' =
      a3sv_mappingConeCompCokernelHom₃ f g ≫
        (CochainComplex.mappingCone.triangle
          (a3sv_cokernelCompShortComplex f g).f).mor₃ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply CochainComplex.mappingCone.ext_from _ (n + 1) n rfl
  · simp [CochainComplex.mappingConeCompTriangle,
      a3sv_cokernelCompShortComplex, a3sv_mappingConeCompCokernelHom₃,
      CochainComplex.mappingCone.map]
    exact CochainComplex.mappingCone.inr_f_descShortComplex_f
      (ShortComplex.cokernelSequence f) (n + 1)
  · simp [CochainComplex.mappingConeCompTriangle,
      a3sv_cokernelCompShortComplex, a3sv_mappingConeCompCokernelHom₃,
      CochainComplex.mappingCone.map]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the third cone comparison commutes with the
connecting maps when the first endpoint is typed through the quotient short
complex. -/
theorem a3sv_mappingConeCompCokernelHom₃_comm_typed {B : Type u} [CommRing B]
    {X Y Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] :
    (CochainComplex.mappingConeCompTriangle f g).mor₃ ≫
        (a3sv_mappingConeCompCokernelDesc₁ f g)⟦1⟧' =
      a3sv_mappingConeCompCokernelHom₃ f g ≫
        (CochainComplex.mappingCone.triangle
          (a3sv_cokernelCompShortComplex f g).f).mor₃ := by
  exact a3sv_mappingConeCompCokernelHom₃_comm f g

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the connecting morphism of the composable-cone
triangle becomes the connecting morphism of the cokernel short exact sequence
after applying the endpoint cone-to-cokernel maps. -/
theorem a3sv_mappingConeCompCokernel_delta {B : Type u} [CommRing B]
    {X Y Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g]
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingConeCompTriangle f g).mor₃ n₀ n₁ (by omega) ≫
      HomologicalComplex.homologyMap
        (a3sv_mappingConeCompCokernelDesc₁ f g) n₁ =
    HomologicalComplex.homologyMap
        (a3sv_mappingConeCompCokernelDesc₃ f g) n₀ ≫
      (a3sv_cokernelCompShortComplex_shortExact f g).δ n₀ n₁ h := by
  subst n₁
  change (HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingConeCompTriangle f g).mor₃ n₀ (n₀ + 1) _ ≫
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
        (ComplexShape.up ℤ) 0).shift (n₀ + 1)).map
          (a3sv_mappingConeCompCokernelDesc₁ f g) = _
  rw [← Functor.shiftMap_comp]
  rw [a3sv_mappingConeCompCokernelHom₃_comm_typed]
  change (HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
      (ComplexShape.up ℤ) 0).shiftMap
        (a3sv_mappingConeCompCokernelHom₃ f g ≫
          (CochainComplex.mappingCone.triangle
            (a3sv_cokernelCompShortComplex f g).f).mor₃)
        n₀ (n₀ + 1) _ = _
  rw [Functor.shiftMap_comp']
  rw [a3sv_mappingConeShortExact_delta
    (a3sv_cokernelCompShortComplex f g)
    (a3sv_cokernelCompShortComplex_shortExact f g) n₀ (n₀ + 1) rfl]
  change HomologicalComplex.homologyMap
      (a3sv_mappingConeCompCokernelHom₃ f g) n₀ ≫
        HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.descShortComplex
            (a3sv_cokernelCompShortComplex f g)) n₀ ≫
        (a3sv_cokernelCompShortComplex_shortExact f g).δ
          n₀ (n₀ + 1) (by simp) =
      HomologicalComplex.homologyMap
        (a3sv_mappingConeCompCokernelDesc₃ f g) n₀ ≫
        (a3sv_cokernelCompShortComplex_shortExact f g).δ
          n₀ (n₀ + 1) (by simp)
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    a3sv_mappingConeCompCokernelHom₃_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the connecting morphism of the direct mapping-cone
spectral object becomes the connecting morphism of the composable-cokernel
short exact sequence. -/
theorem a3sv_mappingConeSpectralCokernel_delta {B : Type u} [CommRing B]
    {X Y Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g]
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B)
      (ComplexShape.up ℤ) n₀).inv.app (CochainComplex.mappingCone g) ≫
      ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} B)).mapHomologicalFunctor
        (HomotopyCategory.homologyFunctor (ModuleCat.{u} B)
          (ComplexShape.up ℤ) 0)).δ f g n₀ n₁ h ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B)
        (ComplexShape.up ℤ) n₁).hom.app (CochainComplex.mappingCone f) ≫
      (a3sv_mappingConeCokernelHomologyIso f n₁).hom =
    (a3sv_mappingConeCokernelHomologyIso g n₀).hom ≫
      (a3sv_cokernelCompShortComplex_shortExact f g).δ n₀ n₁ h := by
  rw [a3sv_mappingConeSpectral_delta_factorization]
  dsimp only [a3sv_mappingConeCokernelHomologyIso, asIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact a3sv_mappingConeCompCokernel_delta f g n₀ n₁ h

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the filtration connecting map becomes the connecting
map of its quotient short exact sequence under the interval comparisons. -/
theorem a3sv_filtration_quotient_delta {B : Type} [CommRing B]
    (F : ℤ ⥤ CochainComplex (ModuleCat.{0} B) ℤ)
    {i j k : ℤ} (f : i ⟶ j) (g : j ⟶ k)
    [Mono (F.map f)] [Mono (F.map g)]
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    let S := ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} B)).precomp F).mapHomologicalFunctor
        (HomotopyCategory.homologyFunctor (ModuleCat.{0} B) (ComplexShape.up ℤ) 0)
    (a3sv_mappingConeSpectralHomologyIso F g n₀).inv ≫
      S.δ f g n₀ n₁ h ≫
      (a3sv_mappingConeSpectralHomologyIso F f n₁).hom ≫
      (a3sv_mappingConeCokernelHomologyIso (F.map f) n₁).hom =
      (a3sv_mappingConeCokernelHomologyIso (F.map g) n₀).hom ≫
        (a3sv_cokernelCompShortComplex_shortExact (F.map f) (F.map g)).δ n₀ n₁ h := by
  dsimp only
  rw [a3sv_mappingConePrecomp_delta_factorization]
  dsimp only [a3sv_mappingConePrecompHomologyMap, a3sv_mappingConeSpectralHomologyIso]
  simp only [Iso.app_inv, Iso.app_hom, Category.assoc]
  rw [reassoc_of% (a3sv_mappingConeMappedArrow_inv_homologyFactor F f g n₀ n₁ h)]
  simp only [a3sv_mappingConeMappedArrow_eq_id, a3sv_mappingConeMappedArrow_inv_eq_id,
    HomologicalComplex.homologyMap_id, Category.id_comp, Category.comp_id,
    Iso.inv_hom_id_app_assoc]
  exact a3sv_mappingConeCompCokernel_delta (F.map f) (F.map g) n₀ n₁ h

/-- IntersectionProductSV: the cone inclusion is invertible when its source complex is zero. -/
theorem a3sv_mappingCone_inr_isIso_of_isZero {B : Type u} [CommRing B]
    {C D : CochainComplex (ModuleCat.{u} B) ℤ} (f : C ⟶ D) (hC : IsZero C) :
    IsIso (CochainComplex.mappingCone.inr f) := by
  apply +allowSynthFailures HomologicalComplex.Hom.isIso_of_components
  intro n
  refine ⟨⟨(CochainComplex.mappingCone.snd f).v n n (add_zero n),
    CochainComplex.mappingCone.inr_f_snd_v f n, ?_⟩⟩
  have hz : (CochainComplex.mappingCone.fst f).1.v n (n + 1) rfl = 0 :=
    ((HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.up ℤ) (n + 1)).map_isZero hC).eq_of_tgt _ _
  simpa only [hz, zero_comp, zero_add] using
    CochainComplex.mappingCone.id_X f n (n + 1) rfl

open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: each column-filtration spectral page is a quotient of two interval-cohomology images. -/
def a3sv_totalColumnPageImageIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    let S := a3sv_totalColumnSpectralObject K
    let f : p - r + 1 ⟶ p := homOfLE (by omega)
    let g : p ⟶ p + 1 := homOfLE (by omega)
    let h : p + 1 ⟶ p + r := homOfLE (by omega)
    let a := ((S.H (-p-q)).map (twoδ₂Toδ₁ f g (f ≫ g) rfl)).hom
    let b := ((S.H (-p-q)).map (twoδ₂Toδ₁ (f ≫ g) h ((f ≫ g) ≫ h) rfl)).hom
    ((a3sv_totalColumnSpectralSequence K).page r hr).X (p,q) ≅
      ModuleCat.of B (b.range ⧸ (a.range.map b).comap b.range.subtype) := by
  let S := a3sv_totalColumnSpectralObject K
  letI := a3sv_homologicalFiltration_hasSpectralSequence S
  exact S.spectralSequencePageXIso a3sv_homologicalFiltrationData r hr (p,q)
    (p-r+1) p (p+1) (p+r) rfl rfl rfl rfl
    (-p-q-1) (-p-q) (-p-q+1) rfl ≪≫
      a3sv_spectralObjectEImageIso S _ _ _ (-p-q)

open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: the first column page is the interval cohomology
between consecutive filtration levels. -/
def a3sv_totalColumnFirstPageIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℤ) :
    ((a3sv_totalColumnSpectralSequence K).page 1).X (p, q) ≅
      ((a3sv_totalColumnSpectralObject K).H (-p - q)).obj
        (mk₁ (homOfLE (show p ≤ p + 1 by omega))) := by
  letI := a3sv_homologicalFiltration_hasSpectralSequence
    (a3sv_totalColumnSpectralObject K)
  letI := a3sv_homologicalFiltration_firstPage
  exact (a3sv_totalColumnSpectralObject K).spectralSequenceFirstPageXIso
    a3sv_homologicalFiltrationData (p, q) p (p + 1) rfl rfl (-p - q) rfl

open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: the first column page is the cohomology of the
quotient between successive extended column complexes. -/
def a3sv_totalColumnFirstPageCokernelIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℤ) :
    let F := (show Monotone Int.toNat from fun _ _ h => Int.toNat_le_toNat h).functor ⋙
      a3sv_totalColumnFunctor K ⋙ ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)
    ((a3sv_totalColumnSpectralSequence K).page 1).X (p, q) ≅
      (cokernel (F.map (homOfLE (show p ≤ p + 1 by omega)))).homology (-p - q) := by
  let F := (show Monotone Int.toNat from fun _ _ h => Int.toNat_le_toNat h).functor ⋙
    a3sv_totalColumnFunctor K ⋙ ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)
  let hp : p ≤ p + 1 := by omega
  let φ := (a3sv_totalColumnFunctor K).map
    (homOfLE (Int.toNat_le_toNat hp))
  have hm (i : ℕ) : Mono (φ.f i) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective
      (Submodule.inclusion ((a3sv_totalColumnFiltration K i).monotone
        (Int.toNat_le_toNat hp)))
    exact Submodule.inclusion_injective _
  letI : Mono (F.map (homOfLE hp)) := by
    apply HomologicalComplex.mono_of_mono_f
    intro j
    change Mono ((HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat).f j)
    by_cases hj : ∃ i, ComplexShape.embeddingDownNat.f i = j
    · obtain ⟨i, hi⟩ := hj
      rw [HomologicalComplex.extendMap_f _ _ hi]
      letI := hm i
      infer_instance
    · have hz := ((a3sv_totalColumnFunctor K).obj p.toNat).isZero_extend_X
        ComplexShape.embeddingDownNat j (fun i hi => hj ⟨i, hi⟩)
      letI := ModuleCat.isZero_iff_subsingleton.mp hz
      exact (ModuleCat.mono_iff_injective _).mpr (Function.injective_of_subsingleton _)
  exact a3sv_totalColumnFirstPageIso K p q ≪≫
    a3sv_mappingConeSpectralHomologyIso F (homOfLE hp) (-p - q) ≪≫
    a3sv_mappingConeCokernelHomologyIso (F.map (homOfLE hp)) (-p - q)

open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: interval cohomology starting at a zero filtration level is the homology of the upper level. -/
def a3sv_spectralIntervalFromZeroIso {B : Type u} [CommRing B]
    {ι : Type*} [Category ι] (F : ι ⥤ CochainComplex (ModuleCat.{u} B) ℤ)
    {i j : ι} (f : i ⟶ j) (hF : IsZero (F.obj i)) (n : ℤ) :
    ((((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} B)).precomp F).mapHomologicalFunctor
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ) 0)).H n).obj (mk₁ f) ≅
      (F.obj j).homology n := by
  letI := a3sv_mappingCone_inr_isIso_of_isZero (F.map f) hF
  exact a3sv_mappingConeSpectralHomologyIso F f n ≪≫
    (HomologicalComplex.homologyMapIso (asIso (CochainComplex.mappingCone.inr (F.map f))) n).symm

open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: the mapping-cone cohomology identification respects maps of filtration intervals. -/
theorem a3sv_mappingConeSpectralHomologyIso_naturality {B : Type u} [CommRing B]
    {ι : Type*} [Category ι] (F : ι ⥤ CochainComplex (ModuleCat.{u} B) ℤ)
    {i j i' j' : ι} (f : i ⟶ j) (g : i' ⟶ j') (a : mk₁ f ⟶ mk₁ g) (n : ℤ) :
    ((((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} B)).precomp F).mapHomologicalFunctor
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ) 0)).H n).map a ≫
        (a3sv_mappingConeSpectralHomologyIso F g n).hom =
      (a3sv_mappingConeSpectralHomologyIso F f n).hom ≫
        HomologicalComplex.homologyMap
          ((HomotopyCategory.composableArrowsFunctor (ModuleCat.{u} B)).map
            ((F.mapComposableArrows 1).map a)) n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (ComplexShape.up ℤ) n).hom.naturality _

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: the interval identification at a zero lower level respects interval morphisms. -/
theorem a3sv_spectralIntervalFromZeroIso_naturality {B : Type u} [CommRing B]
    {ι : Type*} [Category ι] (F : ι ⥤ CochainComplex (ModuleCat.{u} B) ℤ)
    {i j i' j' : ι} (f : i ⟶ j) (g : i' ⟶ j')
    (hf : IsZero (F.obj i)) (hg : IsZero (F.obj i'))
    (a : mk₁ f ⟶ mk₁ g) (n : ℤ) :
    ((((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} B)).precomp F).mapHomologicalFunctor
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ) 0)).H n).map a ≫
        (a3sv_spectralIntervalFromZeroIso F g hg n).hom =
      (a3sv_spectralIntervalFromZeroIso F f hf n).hom ≫
        HomologicalComplex.homologyMap (F.map (a.app 1)) n := by
  letI := a3sv_mappingCone_inr_isIso_of_isZero (F.map f) hf
  letI := a3sv_mappingCone_inr_isIso_of_isZero (F.map g) hg
  dsimp only [a3sv_spectralIntervalFromZeroIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, a3sv_mappingConeSpectralHomologyIso_naturality]
  simp only [Category.assoc]
  apply congrArg ((a3sv_mappingConeSpectralHomologyIso F f n).hom ≫ ·)
  apply (cancel_epi (HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.inr (F.map f)) n)).mp
  simp only [← Category.assoc]
  rw [← HomologicalComplex.homologyMap_comp]
  have hinr : CochainComplex.mappingCone.inr (F.map f) ≫
      (HomotopyCategory.composableArrowsFunctor (ModuleCat.{u} B)).map
        ((F.mapComposableArrows 1).map a) =
      F.map (a.app 1) ≫ CochainComplex.mappingCone.inr (F.map g) := by
    exact (CochainComplex.mappingCone.triangleMap _ _ _ _
      (ComposableArrows.naturality' ((F.mapComposableArrows 1).map a) 0 1)).comm₂
  rw [hinr, HomologicalComplex.homologyMap_comp]
  simp

/-- IntersectionProductSV: the initial column filtration complex is zero. -/
theorem a3sv_totalColumnComplex_zero {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) :
    IsZero (a3sv_totalColumnComplex K 0) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.Hom.ext
  funext i
  have hz : IsZero ((a3sv_totalColumnComplex K 0).X i) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton (a3sv_totalColumnFiltration K i 0)
    rw [(a3sv_totalColumnFiltration_endpoints K i).1]
    infer_instance
  exact hz.eq_of_src _ _

/-- IntersectionProductSV: a bound on columns gives a uniform exhaustive filtration level in every total degree. -/
theorem a3sv_totalColumnFiltration_top_of_bound {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (m p : ℕ) (hmp : m < p) (hK : ∀ a, m < a → IsZero (K.X a)) (i : ℕ) :
    a3sv_totalColumnFiltration K i p = ⊤ := by
  let S := a3sv_totalColumnFiltration K i p
  have hq : ModuleCat.ofHom S.mkQ = 0 := by
    apply HomologicalComplex₂.total.hom_ext
    intro a b hab
    by_cases ha : a < p
    · ext x
      change S.mkQ ((HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i hab).hom x) = 0
      apply (Submodule.Quotient.mk_eq_zero S).mpr
      change _ ∈ ⨆ (a : ℕ) (_ : a < p) (b : ℕ) (h : a + b = i),
        LinearMap.range (HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) a b i h).hom
      exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha
        (Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hab ⟨x, rfl⟩)))
    · exact ((HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.down ℕ) b).map_isZero
        (hK a (by omega))).eq_of_src _ _
  apply Submodule.eq_top_iff'.mpr
  intro x
  exact (Submodule.Quotient.mk_eq_zero S).mp (congrArg (fun f => f.hom x) hq)

/-- IntersectionProductSV: once the filtration index exceeds a total degree,
the corresponding component inclusion is invertible. -/
theorem a3sv_totalColumnInclusion_component_isIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p i : ℕ) (hi : i < p) :
    IsIso ((a3sv_totalColumnInclusion K p).f i) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · exact Subtype.val_injective
  · intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    have hp : a3sv_totalColumnFiltration K i p = ⊤ := by
      apply le_antisymm le_top
      simpa only [(a3sv_totalColumnFiltration_endpoints K i).2] using
        (a3sv_totalColumnFiltration K i).monotone (Nat.succ_le_iff.mpr hi)
    rw [hp]
    trivial

/-- IntersectionProductSV: degreewise exhaustion makes the filtration
inclusion an isomorphism on homology in that degree. -/
theorem a3sv_totalColumnInclusion_homologyMap_isIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p i : ℕ) (hi : i + 1 < p) :
    IsIso (HomologicalComplex.homologyMap
      (a3sv_totalColumnInclusion K p) i) := by
  rw [← quasiIsoAt_iff_isIso_homologyMap, quasiIsoAt_iff]
  let φ := ((HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} B) (ComplexShape.down ℕ) i).map
      (a3sv_totalColumnInclusion K p))
  change ShortComplex.QuasiIso φ
  haveI h1 : IsIso φ.τ₁ := by
    dsimp [φ]
    exact a3sv_totalColumnInclusion_component_isIso K p
      ((ComplexShape.down ℕ).prev i) (by
        simp only [ChainComplex.prev]
        omega)
  haveI h2 : IsIso φ.τ₂ := by
    dsimp [φ]
    exact a3sv_totalColumnInclusion_component_isIso K p i (by omega)
  haveI h3 : IsIso φ.τ₃ := by
    dsimp [φ]
    exact a3sv_totalColumnInclusion_component_isIso K p
      ((ComplexShape.down ℕ).next i) (by
        by_cases hz : i = 0
        · subst i
          rw [ChainComplex.next_nat_zero]
          omega
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
          rw [ChainComplex.next_nat_succ]
          omega)
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

/-- IntersectionProductSV: beyond the column bound, the filtration inclusion identifies the filtered and total complexes. -/
theorem a3sv_totalColumnInclusion_isIso_of_bound {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (m p : ℕ) (hmp : m < p) (hK : ∀ a, m < a → IsZero (K.X a)) :
    IsIso (a3sv_totalColumnInclusion K p) := by
  apply +allowSynthFailures HomologicalComplex.Hom.isIso_of_components
  intro i
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · exact Subtype.val_injective
  · intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [a3sv_totalColumnFiltration_top_of_bound K m p hmp hK i]
    trivial

open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: spectral intervals starting below zero compute the chain homology of the upper column level. -/
def a3sv_totalColumnIntervalHomologyIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q : ℤ) (hpq : p ≤ q) (hp : p ≤ 0) (i : ℕ) :
    ((a3sv_totalColumnSpectralObject K).H (-(i : ℤ))).obj (mk₁ (homOfLE hpq)) ≅
      ((a3sv_totalColumnFunctor K).obj q.toNat).homology i := by
  let F := (show Monotone Int.toNat from fun _ _ h => Int.toNat_le_toNat h).functor ⋙
    a3sv_totalColumnFunctor K ⋙ ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)
  have hz : IsZero (F.obj p) := by
    change IsZero ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)).obj
      ((a3sv_totalColumnFunctor K).obj p.toNat))
    rw [Int.toNat_eq_zero.mpr hp]
    apply (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)).map_isZero
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.Hom.ext
    funext j
    have hzj : IsZero (((a3sv_totalColumnFunctor K).obj 0).X j) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      change Subsingleton (a3sv_totalColumnFiltration K j 0)
      rw [(a3sv_totalColumnFiltration_endpoints K j).1]
      infer_instance
    exact hzj.eq_of_src _ _
  exact a3sv_spectralIntervalFromZeroIso F (homOfLE hpq) hz (-(i : ℤ)) ≪≫
    ((a3sv_totalColumnFunctor K).obj q.toNat).extendHomologyIso
      ComplexShape.embeddingDownNat (by rfl)

/-- IntersectionProductSV: the filtration functor and the explicit column complex have the same terms and differentials. -/
def a3sv_totalColumnFunctorObjIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p : ℕ) :
    (a3sv_totalColumnFunctor K).obj p ≅ a3sv_totalColumnComplex K p :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    rfl)

/-- IntersectionProductSV: the column-complex comparison is the identity in every degree. -/
theorem a3sv_totalColumnFunctorObjIso_hom_f {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p i : ℕ) :
    (a3sv_totalColumnFunctorObjIso K p).hom.f i =
      𝟙 (ModuleCat.of B (a3sv_totalColumnFiltration K i p)) := rfl

/-- IntersectionProductSV: each component of a column filtration transition is the inclusion of the corresponding submodules. -/
theorem a3sv_totalColumnFunctor_map_f {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q : ℕ) (hpq : p ≤ q) (i : ℕ) :
    ((a3sv_totalColumnFunctor K).map (homOfLE hpq)).f i =
      ModuleCat.ofHom (Submodule.inclusion ((a3sv_totalColumnFiltration K i).monotone hpq)) := rfl

/-- IntersectionProductSV: the cokernel of a consecutive column-filtration
transition is the newly adjoined bicomplex summand in each total degree. -/
def a3sv_totalColumnTransitionCokernelIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q i : ℕ) (h : p + q = i) :
    cokernel (((a3sv_totalColumnFunctor K).map
      (homOfLE (Nat.le_succ p))).f i) ≅ (K.X p).X q := by
  let f := ((a3sv_totalColumnFunctor K).map
    (homOfLE (Nat.le_succ p))).f i
  let g : ((a3sv_totalColumnFunctor K).obj (p + 1)).X i ⟶ (K.X p).X q :=
    a3sv_totalColumnProjectionRestrict K p q i h
  have hfg : LinearMap.range f.hom = LinearMap.ker g.hom := by
    dsimp [f, g, a3sv_totalColumnFunctor, a3sv_submoduleComplexFunctor,
      a3sv_submoduleComplexMap, a3sv_submoduleComplex]
    exact (Submodule.range_inclusion _ _ _).trans
      (a3sv_totalColumnProjectionRestrict_ker K p q i h).symm
  let e : (↥(((a3sv_totalColumnFunctor K).obj (p + 1)).X i) ⧸
      LinearMap.range f.hom) ≃ₗ[B] (K.X p).X q :=
    (Submodule.quotEquivOfEq _ _ hfg).trans
      (g.hom.quotKerEquivOfSurjective
        (a3sv_totalColumnProjectionRestrict_surjective K p q i h))
  exact ModuleCat.cokernelIsoRangeQuotient _ ≪≫
    e.toModuleIso

/-- IntersectionProductSV: the consecutive-transition cokernel comparison is
induced by projection onto the newly adjoined column. -/
theorem a3sv_totalColumnTransitionCokernelIso_π {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q i : ℕ) (h : p + q = i) :
    cokernel.π (((a3sv_totalColumnFunctor K).map
      (homOfLE (Nat.le_succ p))).f i) ≫
        (a3sv_totalColumnTransitionCokernelIso K p q i h).hom =
      a3sv_totalColumnProjectionRestrict K p q i h := by
  dsimp only [a3sv_totalColumnTransitionCokernelIso]
  rw [Iso.trans_hom, ← Category.assoc,
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- IntersectionProductSV: below the new column, consecutive filtration
transitions have zero cokernel components. -/
theorem a3sv_totalColumnTransitionCokernel_isZero_of_lt
    {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p i : ℕ) (hi : i < p) :
    IsZero ((cokernel ((a3sv_totalColumnFunctor K).map
      (homOfLE (Nat.le_succ p)))).X i) := by
  have hp : a3sv_totalColumnFiltration K i p = ⊤ := by
    apply le_antisymm le_top
    rw [← (a3sv_totalColumnFiltration_endpoints K i).2]
    exact (a3sv_totalColumnFiltration K i).monotone (by omega)
  have hepi : Epi (((a3sv_totalColumnFunctor K).map
      (homOfLE (Nat.le_succ p))).f i) := by
    rw [a3sv_totalColumnFunctor_map_f K p (p + 1) (Nat.le_succ p) i]
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    dsimp [a3sv_totalColumnFunctor, a3sv_submoduleComplexFunctor,
      a3sv_submoduleComplex] at x ⊢
    refine ⟨⟨x.val, ?_⟩, ?_⟩
    · rw [hp]
      trivial
    · apply Subtype.ext
      rfl
  exact IsZero.of_iso (isZero_cokernel_of_epi
      (((a3sv_totalColumnFunctor K).map
        (homOfLE (Nat.le_succ p))).f i))
    (PreservesCokernel.iso
      (HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.down ℕ) i)
      ((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p))))

/-- IntersectionProductSV: the cokernel of two consecutive column complexes,
reindexed so degree `q` is total degree `p + q`. -/
def a3sv_totalColumnCokernelComplex {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p : ℕ) :
    ChainComplex (ModuleCat.{u} B) ℕ := by
  let C := cokernel ((a3sv_totalColumnFunctor K).map
    (homOfLE (Nat.le_succ p)))
  exact
    { X := fun q => C.X (p + q)
      d := fun q r => C.d (p + q) (p + r)
      shape := by
        intro q r hqr
        apply C.shape
        intro hsum
        apply hqr
        change r + 1 = q
        change p + r + 1 = p + q at hsum
        omega
      d_comp_d' := by
        intro q r s _ _
        exact C.d_comp_d (p + q) (p + r) (p + s) }

/-- IntersectionProductSV: one bicomplex column with the vertical sign used by
the total-complex convention. -/
def a3sv_signedColumn {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p : ℕ) :
    ChainComplex (ModuleCat.{u} B) ℕ where
  X := (K.X p).X
  d q r := (ComplexShape.down ℕ).ε p • (K.X p).d q r
  shape q r h := by rw [(K.X p).shape q r h, smul_zero]
  d_comp_d' q r s hqr hrs := by
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, ← smul_smul,
      (K.X p).d_comp_d q r s, smul_zero]

/-- IntersectionProductSV: on the newly adjoined column, the total differential
followed by column projection is the signed vertical differential. -/
theorem a3sv_ιTotal_d_totalColumnProjection {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q r : ℕ) (hqr : (ComplexShape.down ℕ).Rel q r) :
    HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) p q (p + q) rfl ≫
        (HomologicalComplex₂.total K (ComplexShape.down ℕ)).d (p + q) (p + r) ≫
        a3sv_totalColumnProjection K p r (p + r) rfl =
      (ComplexShape.down ℕ).ε p • (K.X p).d q r := by
  change r + 1 = q at hqr
  rw [← Category.assoc]
  change (_ ≫ (HomologicalComplex₂.D₁ K (ComplexShape.down ℕ) (p + q) (p + r) +
    HomologicalComplex₂.D₂ K (ComplexShape.down ℕ) (p + q) (p + r))) ≫ _ = _
  rw [Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
    HomologicalComplex₂.ι_D₂, Preadditive.add_comp]
  cases p with
  | zero =>
      rw [HomologicalComplex₂.d₁_eq_zero K (ComplexShape.down ℕ) 0 q (0 + r) (by simp)]
      rw [HomologicalComplex₂.d₂_eq K (ComplexShape.down ℕ) 0 hqr (0 + r) (by simp)]
      simp [a3sv_ιTotal_totalColumnProjection]
  | succ p =>
      rw [HomologicalComplex₂.d₁_eq K (ComplexShape.down ℕ) (i₁' := p) (by simp) q
        (p + 1 + r) (by change p + q = p + 1 + r; omega)]
      rw [HomologicalComplex₂.d₂_eq K (ComplexShape.down ℕ) (p + 1) hqr
        (p + 1 + r) (by simp)]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [a3sv_ιTotal_totalColumnProjection_eq_zero K p q (p + 1) r
        (p + 1 + r) (by omega) rfl (by omega), comp_zero, smul_zero, zero_add]
      rw [a3sv_ιTotal_totalColumnProjection, Category.comp_id]
      rfl

/-- IntersectionProductSV: the adjacent lower column of the total differential
is the horizontal differential of the bicomplex. -/
theorem a3sv_ιTotal_d_lowerColumnProjection {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) (p + 1) q (p + 1 + q) rfl ≫
        (HomologicalComplex₂.total K (ComplexShape.down ℕ)).d (p + 1 + q) (p + q) ≫
        a3sv_totalColumnProjection K p q (p + q) rfl =
      (K.d (p + 1) p).f q := by
  rw [← Category.assoc]
  change (_ ≫ (HomologicalComplex₂.D₁ K (ComplexShape.down ℕ) (p + 1 + q) (p + q) +
    HomologicalComplex₂.D₂ K (ComplexShape.down ℕ) (p + 1 + q) (p + q))) ≫ _ = _
  rw [Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
    HomologicalComplex₂.ι_D₂, Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq K (ComplexShape.down ℕ) (i₁' := p) (by simp) q
    (p + q) rfl]
  cases q with
  | zero =>
      rw [HomologicalComplex₂.d₂_eq_zero K (ComplexShape.down ℕ) (p + 1) 0 (p + 0)
        (by simp)]
      simp [a3sv_ιTotal_totalColumnProjection]
  | succ q =>
      rw [HomologicalComplex₂.d₂_eq K (ComplexShape.down ℕ) (p + 1)
        (show (ComplexShape.down ℕ).Rel (q + 1) q by rfl)
        (p + (q + 1)) (by change p + 1 + q = p + (q + 1); omega)]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [a3sv_ιTotal_totalColumnProjection_eq_zero K (p + 1) q p (q + 1)
        (p + (q + 1)) (by omega) rfl (by omega), comp_zero, smul_zero, add_zero]
      rw [a3sv_ιTotal_totalColumnProjection, Category.comp_id]
      simp

/-- IntersectionProductSV: on vertical cycles, the total differential of a
column summand is precisely its horizontal differential. -/
theorem a3sv_iCycles_ιTotal_d {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    (K.X (p + 1)).iCycles q ≫
      HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) (p + 1) q (p + 1 + q) rfl ≫
        (HomologicalComplex₂.total K (ComplexShape.down ℕ)).d (p + 1 + q) (p + q) =
      (K.X (p + 1)).iCycles q ≫ (K.d (p + 1) p).f q ≫
        HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) p q (p + q) rfl := by
  change _ ≫ _ ≫ (HomologicalComplex₂.D₁ K (ComplexShape.down ℕ) (p + 1 + q) (p + q) +
    HomologicalComplex₂.D₂ K (ComplexShape.down ℕ) (p + 1 + q) (p + q)) = _
  rw [Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
    HomologicalComplex₂.ι_D₂, Preadditive.comp_add]
  rw [HomologicalComplex₂.d₁_eq K (ComplexShape.down ℕ) (i₁' := p) (by simp) q
    (p + q) rfl]
  cases q with
  | zero =>
      rw [HomologicalComplex₂.d₂_eq_zero K (ComplexShape.down ℕ) (p + 1) 0 (p + 0)
        (by simp)]
      simp
  | succ q =>
      rw [HomologicalComplex₂.d₂_eq K (ComplexShape.down ℕ) (p + 1)
        (show (ComplexShape.down ℕ).Rel (q + 1) q by rfl)
        (p + (q + 1)) (by change p + 1 + q = p + (q + 1); omega)]
      simp [Linear.comp_units_smul, ← Category.assoc]

/-- IntersectionProductSV: the differential of a lifted vertical cycle is its
horizontal differential lifted into the same filtration term. -/
theorem a3sv_iCycles_totalColumnSummandInclusion_d {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (b p q : ℕ)
    (hp : p + 1 < b) :
    (K.X (p + 1)).iCycles q ≫
      a3sv_totalColumnSummandInclusion K b (p + 1) q (p + 1 + q) hp rfl ≫
        ((a3sv_totalColumnFunctor K).obj b).d (p + 1 + q) (p + q) =
      (K.X (p + 1)).iCycles q ≫ (K.d (p + 1) p).f q ≫
        a3sv_totalColumnSummandInclusion K b p q (p + q) (by omega) rfl := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (a3sv_iCycles_ιTotal_d K p q) x

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: vertical cycles in the zeroth column have zero total differential. -/
theorem a3sv_iCycles_zeroColumn_d {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (q : ℕ) :
    (K.X 0).iCycles q ≫
      HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ) 0 q (0 + q) rfl ≫
      (HomologicalComplex₂.total K (ComplexShape.down ℕ)).d (0 + q) (0 + q - 1) = 0 := by
  cases q with
  | zero => simp
  | succ q =>
    change _ ≫ _ ≫ (HomologicalComplex₂.D₁ K (ComplexShape.down ℕ) (0 + (q + 1)) (0 + (q + 1) - 1) +
      HomologicalComplex₂.D₂ K (ComplexShape.down ℕ) (0 + (q + 1)) (0 + (q + 1) - 1)) = _
    rw [Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂, Preadditive.comp_add]
    rw [HomologicalComplex₂.d₁_eq_zero K (ComplexShape.down ℕ) 0 (q + 1) (0 + (q + 1) - 1) (by simp)]
    rw [HomologicalComplex₂.d₂_eq K (ComplexShape.down ℕ) 0
      (show (ComplexShape.down ℕ).Rel (q + 1) q by rfl) (0 + (q + 1) - 1)
      (by change 0 + q = 0 + (q + 1) - 1; omega)]
    simp [Linear.comp_units_smul, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: a vertical cycle in a positive column represents
a cycle in that column's consecutive filtration quotient. -/
theorem a3sv_columnQuotient_cycle {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    let g := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ (p + 1)))
    (K.X (p + 1)).iCycles q ≫
      a3sv_totalColumnSummandInclusion K (p + 2) (p + 1) q (p + 1 + q) (by omega) rfl ≫
      (cokernel.π g).f (p + 1 + q) ≫ (cokernel g).d (p + 1 + q) (p + q) = 0 := by
  dsimp only
  let g := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ (p + 1)))
  rw [(cokernel.π g).comm]
  rw [reassoc_of% (a3sv_iCycles_totalColumnSummandInclusion_d K (p + 2) p q (by omega))]
  have hinc : a3sv_totalColumnSummandInclusion K (p + 2) p q (p + q) (by omega) rfl =
      a3sv_totalColumnSummandInclusion K (p + 1) p q (p + q) (by omega) rfl ≫
        g.f (p + q) := by
    rfl
  have hg : g.f (p + q) ≫ (cokernel.π g).f (p + q) = 0 :=
    congrArg (fun t => t.f (p + q)) (cokernel.condition g)
  rw [hinc]
  simp only [Category.assoc, hg, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: vertical cycles in any column descend to cycles
in the corresponding consecutive filtration quotient. -/
theorem a3sv_columnQuotient_cycle_all {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    let g := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p))
    (K.X p).iCycles q ≫
      a3sv_totalColumnSummandInclusion K (p + 1) p q (p + q) (by omega) rfl ≫
      (cokernel.π g).f (p + q) ≫ (cokernel g).d (p + q) (p + q - 1) = 0 := by
  cases p with
  | zero =>
    dsimp only
    let g := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ 0))
    have hh : (K.X 0).iCycles q ≫
        a3sv_totalColumnSummandInclusion K 1 0 q (0 + q) (by omega) rfl ≫
        ((a3sv_totalColumnFunctor K).obj 1).d (0 + q) (0 + q - 1) = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (a3sv_iCycles_zeroColumn_d K q) x
    rw [(cokernel.π g).comm, reassoc_of% hh, zero_comp]
  | succ p =>
    dsimp only
    rw [show p.succ + q - 1 = p + q by omega]
    exact a3sv_columnQuotient_cycle K p q

/-- IntersectionProductSV: the canonical map from vertical cycles to cycles
of a consecutive column-filtration quotient. -/
def a3sv_columnQuotientCycles {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    (K.X p).cycles q ⟶
      (cokernel ((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p)))).cycles (p + q) :=
  (cokernel ((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p)))).liftCycles
    ((K.X p).iCycles q ≫
      a3sv_totalColumnSummandInclusion K (p + 1) p q (p + q) (by omega) rfl ≫
      (cokernel.π ((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p)))).f (p + q))
    (p + q - 1)
    (by cases h : p + q <;> simp [ChainComplex.next_nat_zero, ChainComplex.next_nat_succ])
    (by simpa only [Category.assoc] using a3sv_columnQuotient_cycle_all K p q)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: on vertical cycle representatives, the connecting
map of consecutive column quotients is the horizontal homology differential. -/
theorem a3sv_columnQuotientCycles_delta {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    let f := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p))
    let g := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ (p + 1)))
    a3sv_columnQuotientCycles K (p + 1) q ≫ (cokernel g).homologyπ (p + 1 + q) ≫
        (a3sv_cokernelCompShortComplex_shortExact f g).δ (p + 1 + q) (p + q)
          (by change p + q + 1 = p + 1 + q; omega) =
      HomologicalComplex.cyclesMap (K.d (p + 1) p) q ≫
        a3sv_columnQuotientCycles K p q ≫ (cokernel f).homologyπ (p + q) := by
  dsimp only
  let f := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p))
  let g := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ (p + 1)))
  simpa only [Category.assoc] using
    (a3sv_cokernelComp_delta_representatives f g (p + 1 + q) (p + q)
      (by change p + q + 1 = p + 1 + q; omega)
      (a3sv_columnQuotientCycles K (p + 1) q)
      (HomologicalComplex.cyclesMap (K.d (p + 1) p) q ≫ a3sv_columnQuotientCycles K p q)
      ((K.X (p + 1)).iCycles q ≫
        a3sv_totalColumnSummandInclusion K (p + 2) (p + 1) q (p + 1 + q) (by omega) rfl)
      ((K.X (p + 1)).iCycles q ≫ (K.d (p + 1) p).f q ≫
        a3sv_totalColumnSummandInclusion K (p + 1) p q (p + q) (by omega) rfl)
      (by simp only [f, g, a3sv_columnQuotientCycles, HomologicalComplex.liftCycles_i,
        Category.assoc])
      (by simp only [f, g, a3sv_columnQuotientCycles, Category.assoc,
        HomologicalComplex.liftCycles_i, HomologicalComplex.cyclesMap_i_assoc])
      (by
        simp only [Category.assoc]
        rw [a3sv_iCycles_totalColumnSummandInclusion_d]
        rfl))

/-- IntersectionProductSV: projection from a successive filtration term
intertwines its total differential with the signed vertical differential. -/
theorem a3sv_totalColumnProjectionRestrict_d {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q r : ℕ) (hqr : (ComplexShape.down ℕ).Rel q r) :
    (a3sv_totalColumnComplex K (p + 1)).d (p + q) (p + r) ≫
        a3sv_totalColumnProjectionRestrict K p r (p + r) rfl =
      a3sv_totalColumnProjectionRestrict K p q (p + q) rfl ≫
        (a3sv_signedColumn K p).d q r := by
  dsimp [a3sv_totalColumnComplex, a3sv_submoduleComplex]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hxmem : x.val ∈ a3sv_totalColumnFiltration K (p + q) p ⊔
      LinearMap.range (HomologicalComplex₂.ιTotal K
        (ComplexShape.down ℕ) p q (p + q) rfl).hom := by
    rw [← a3sv_totalColumnFiltration_succ K p q (p + q) rfl]
    exact x.property
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxmem
  obtain ⟨w, rfl⟩ := hz
  have hy' : y ∈ a3sv_totalColumnFiltration K (p + q) (p + 1) :=
    (a3sv_totalColumnFiltration K (p + q)).monotone (Nat.le_succ p) hy
  have hz' : (HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ)
      p q (p + q) rfl).hom w ∈ a3sv_totalColumnFiltration K (p + q) (p + 1) := by
    rw [a3sv_totalColumnFiltration_succ K p q (p + q) rfl]
    exact Submodule.mem_sup_right ⟨w, rfl⟩
  let y' : a3sv_totalColumnFiltration K (p + q) (p + 1) := ⟨y, hy'⟩
  let z' : a3sv_totalColumnFiltration K (p + q) (p + 1) :=
    ⟨(HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ)
      p q (p + q) rfl).hom w, hz'⟩
  have hx : x = y' + z' := by
    apply Subtype.ext
    exact hyz.symm
  subst x
  simp only [map_add]
  dsimp [y', z']
  congr 1
  · change (a3sv_totalColumnProjection K p r (p + r) rfl).hom
        ((HomologicalComplex₂.total K (ComplexShape.down ℕ)).d (p + q) (p + r) y) =
      (ComplexShape.down ℕ).ε p • (K.X p).d q r
        ((a3sv_totalColumnProjection K p q (p + q) rfl).hom y)
    rw [a3sv_totalColumnFiltration_le_projection_ker K p q (p + q) rfl hy,
      map_zero, smul_zero]
    exact a3sv_totalColumnFiltration_le_projection_ker K p r (p + r) rfl
      (a3sv_totalColumnFiltration_d K (p + q) (p + r) p hy)
  · change (a3sv_totalColumnProjection K p r (p + r) rfl).hom
        ((HomologicalComplex₂.total K (ComplexShape.down ℕ)).d (p + q) (p + r)
          ((HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ)
            p q (p + q) rfl).hom w)) =
      ((ComplexShape.down ℕ).ε p • (K.X p).d q r).hom
        ((a3sv_totalColumnProjection K p q (p + q) rfl).hom
          ((HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ)
            p q (p + q) rfl).hom w))
    have hpw := ConcreteCategory.congr_hom
      (a3sv_ιTotal_totalColumnProjection K p q (p + q) rfl) w
    change (a3sv_totalColumnProjection K p q (p + q) rfl).hom
      ((HomologicalComplex₂.ιTotal K (ComplexShape.down ℕ)
        p q (p + q) rfl).hom w) = w at hpw
    rw [hpw]
    have he := ConcreteCategory.congr_hom
      (a3sv_ιTotal_d_totalColumnProjection K p q r hqr) w
    simpa only [ModuleCat.comp_apply, LinearMap.coe_comp, Function.comp_apply] using he

/-- IntersectionProductSV: each term of the reindexed consecutive-column
cokernel identifies with the corresponding signed-column term. -/
def a3sv_totalColumnCokernelComponentIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    (a3sv_totalColumnCokernelComplex K p).X q ≅ (a3sv_signedColumn K p).X q := by
  exact PreservesCokernel.iso
      (HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.down ℕ) (p + q))
      ((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p))) ≪≫
    a3sv_totalColumnTransitionCokernelIso K p q (p + q) rfl

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: projection of a canonical quotient cycle is its
original vertical cycle representative. -/
theorem a3sv_columnQuotientCycles_component {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    a3sv_columnQuotientCycles K p q ≫
      (cokernel ((a3sv_totalColumnFunctor K).map
        (homOfLE (Nat.le_succ p)))).iCycles (p + q) ≫
      (a3sv_totalColumnCokernelComponentIso K p q).hom = (K.X p).iCycles q := by
  dsimp only [a3sv_columnQuotientCycles]
  rw [HomologicalComplex.liftCycles_i_assoc]
  dsimp only [a3sv_totalColumnCokernelComponentIso, Iso.trans_hom]
  have hπ := PreservesCokernel.π_iso_hom
    (G := HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.down ℕ) (p + q))
    (f := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p)))
  change (cokernel.π ((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p)))).f (p + q) ≫
      (PreservesCokernel.iso
        (HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.down ℕ) (p + q))
        ((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p)))).hom =
    cokernel.π (((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p))).f (p + q)) at hπ
  simp only [Category.assoc]
  rw [reassoc_of% hπ, a3sv_totalColumnTransitionCokernelIso_π,
    a3sv_totalColumnSummandInclusion_projection, Category.comp_id]

/-- IntersectionProductSV: the degreewise consecutive-cokernel comparisons
commute with the reindexed and signed differentials. -/
theorem a3sv_totalColumnCokernelComponentIso_naturality {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q r : ℕ) (hqr : (ComplexShape.down ℕ).Rel q r) :
    (a3sv_totalColumnCokernelComponentIso K p q).hom ≫
        (a3sv_signedColumn K p).d q r =
      (a3sv_totalColumnCokernelComplex K p).d q r ≫
        (a3sv_totalColumnCokernelComponentIso K p r).hom := by
  dsimp [a3sv_totalColumnCokernelComplex,
    a3sv_totalColumnCokernelComponentIso, a3sv_signedColumn]
  let f := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p))
  apply (cancel_epi ((cokernel.π f).f (p + q))).1
  dsimp [f]
  have hq := PreservesCokernel.π_iso_hom
    (G := HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.down ℕ) (p + q))
    (f := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p)))
  change (cokernel.π ((a3sv_totalColumnFunctor K).map
      (homOfLE (Nat.le_succ p)))).f (p + q) ≫
      (PreservesCokernel.iso
        (HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.down ℕ) (p + q))
        ((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p)))).hom =
    cokernel.π (((a3sv_totalColumnFunctor K).map
      (homOfLE (Nat.le_succ p))).f (p + q)) at hq
  simp only [← Category.assoc]
  rw [hq]
  have htq := a3sv_totalColumnTransitionCokernelIso_π K p q (p + q) rfl
  rw [htq]
  have hc := (cokernel.π ((a3sv_totalColumnFunctor K).map
    (homOfLE (Nat.le_succ p)))).comm (p + q) (p + r)
  rw [hc]
  have hr := PreservesCokernel.π_iso_hom
    (G := HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.down ℕ) (p + r))
    (f := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p)))
  change (cokernel.π ((a3sv_totalColumnFunctor K).map
      (homOfLE (Nat.le_succ p)))).f (p + r) ≫
      (PreservesCokernel.iso
        (HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.down ℕ) (p + r))
        ((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p)))).hom =
    cokernel.π (((a3sv_totalColumnFunctor K).map
      (homOfLE (Nat.le_succ p))).f (p + r)) at hr
  have htr := a3sv_totalColumnTransitionCokernelIso_π K p r (p + r) rfl
  simp only [Category.assoc]
  rw [reassoc_of% hr, htr]
  exact (a3sv_totalColumnProjectionRestrict_d K p q r hqr).symm

/-- IntersectionProductSV: the reindexed cokernel of a consecutive column
filtration transition is the corresponding signed vertical column complex. -/
def a3sv_totalColumnCokernelComplexIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p : ℕ) :
    a3sv_totalColumnCokernelComplex K p ≅ a3sv_signedColumn K p :=
  HomologicalComplex.Hom.isoOfComponents
    (a3sv_totalColumnCokernelComponentIso K p)
    (fun q r hqr => a3sv_totalColumnCokernelComponentIso_naturality K p q r hqr)

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: reindexing a consecutive column quotient gives a
comparison of its local homology diagrams, with identity in the middle term. -/
def a3sv_totalColumnReindexShortComplex {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    (cokernel ((a3sv_totalColumnFunctor K).map
      (homOfLE (Nat.le_succ p)))).sc (p + q) ⟶
        (a3sv_totalColumnCokernelComplex K p).sc q := by
  let C := cokernel ((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p)))
  let R := a3sv_totalColumnCokernelComplex K p
  let e1 : (C.sc (p + q)).X₁ ≅ (R.sc q).X₁ := by
    change C.X _ ≅ C.X _
    exact C.XIsoOfEq (by simp only [ChainComplex.prev]; omega)
  cases q with
  | succ q =>
    let e3 : (C.sc (p + (q + 1))).X₃ ≅ (R.sc (q + 1)).X₃ := by
      change C.X _ ≅ C.X _
      exact C.XIsoOfEq (by
        rw [show p + (q + 1) = (p + q) + 1 by omega,
          ChainComplex.next_nat_succ]
        simp only [ChainComplex.next_nat_succ])
    refine (ShortComplex.isoMk e1 (Iso.refl _) e3 ?_ ?_).hom
    · dsimp [e1, R, a3sv_totalColumnCokernelComplex]
      rw [Category.comp_id]
      apply C.XIsoOfEq_hom_comp_d
    · dsimp [e3, R, a3sv_totalColumnCokernelComplex]
      rw [Category.id_comp]
      exact (C.d_comp_XIsoOfEq_hom _ _).symm
  | zero =>
    by_cases hp : p = 0
    · subst p
      let e3 : (C.sc 0).X₃ ≅ (R.sc 0).X₃ := by
        change C.X _ ≅ C.X _
        exact C.XIsoOfEq (by simp only [Nat.zero_add])
      refine (ShortComplex.isoMk e1 (Iso.refl _) e3 ?_ ?_).hom
      · dsimp [e1, R, a3sv_totalColumnCokernelComplex]
        rw [Category.comp_id]
        exact C.XIsoOfEq_hom_comp_d _ _
      · have hC : (C.sc 0).g = 0 := by
          change C.d 0 ((ComplexShape.down ℕ).next 0) = 0
          rw [ChainComplex.next_nat_zero]
          exact C.shape 0 0 (by simp)
        have hR : (R.sc 0).g = 0 := by
          change R.d 0 ((ComplexShape.down ℕ).next 0) = 0
          rw [ChainComplex.next_nat_zero]
          exact R.shape 0 0 (by simp)
        change (𝟙 _) ≫ (R.sc 0).g = (C.sc 0).g ≫ e3.hom
        rw [hC, hR, comp_zero, zero_comp]
    · refine ShortComplex.homMk e1.hom (𝟙 _) 0 ?_ ?_
      · dsimp [e1, R, a3sv_totalColumnCokernelComplex]
        rw [Category.comp_id]
        exact C.XIsoOfEq_hom_comp_d _ _
      · change (𝟙 _) ≫ R.d 0 ((ComplexShape.down ℕ).next 0) = _ ≫ 0
        rw [ChainComplex.next_nat_zero, R.shape 0 0 (by simp), comp_zero, comp_zero]

/-- IntersectionProductSV: the quotient reindexing comparison is the identity
on the term whose homology is being computed. -/
theorem a3sv_totalColumnReindexShortComplex_τ₂ {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    (a3sv_totalColumnReindexShortComplex K p q).τ₂ = 𝟙 _ := by
  cases q with
  | zero =>
    by_cases hp : p = 0
    · subst p; simp only [a3sv_totalColumnReindexShortComplex, dite_eq_left rfl]; rfl
    · simp only [a3sv_totalColumnReindexShortComplex, dite_eq_right hp]; rfl
  | succ q => rfl

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: quotient reindexing induces an isomorphism on homology. -/
instance a3sv_totalColumnReindexShortComplex_homologyMap_isIso
    {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    IsIso (ShortComplex.homologyMap (a3sv_totalColumnReindexShortComplex K p q)) := by
  cases q with
  | succ q =>
    dsimp [a3sv_totalColumnReindexShortComplex]
    infer_instance
  | zero =>
    by_cases hp : p = 0
    · subst p
      dsimp [a3sv_totalColumnReindexShortComplex, Nat.casesAuxOn]
      infer_instance
    · let C := cokernel ((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p)))
      apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
      · dsimp only [a3sv_totalColumnReindexShortComplex, Nat.casesAuxOn]
        simp only [dite_eq_right hp]
        change Epi (C.XIsoOfEq (show (ComplexShape.down ℕ).prev (p + 0) =
          p + (ComplexShape.down ℕ).prev 0 by simp [ChainComplex.prev])).hom
        infer_instance
      · dsimp only [a3sv_totalColumnReindexShortComplex, Nat.casesAuxOn]
        simp only [dite_eq_right hp]
        change IsIso (𝟙 (C.X (p + 0)))
        infer_instance
      · have hz : IsZero ((C.sc (p + 0)).X₃) := by
          change IsZero (C.X ((ComplexShape.down ℕ).next p))
          obtain ⟨p', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
          rw [ChainComplex.next_nat_succ]
          exact a3sv_totalColumnTransitionCokernel_isZero_of_lt K (p' + 1) p' (by omega)
        letI := ModuleCat.isZero_iff_subsingleton.mp hz
        exact (ModuleCat.mono_iff_injective _).mpr (Function.injective_of_subsingleton _)

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: a signed column has the same local homology diagram
as its unsigned column, with identity comparison in the middle degree. -/
def a3sv_signedColumnShortComplexIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    (a3sv_signedColumn K p).sc q ≅ (K.X p).sc q := by
  let e (r : ℕ) : (K.X p).X r ≅ (K.X p).X r :=
    { hom := (ComplexShape.down ℕ).ε p • 𝟙 _
      inv := (ComplexShape.down ℕ).ε p • 𝟙 _
      hom_inv_id := by
        simp only [Linear.comp_units_smul, Category.comp_id, smul_smul,
          Int.units_mul_self, one_smul]
      inv_hom_id := by
        simp only [Linear.comp_units_smul, Category.comp_id, smul_smul,
          Int.units_mul_self, one_smul] }
  refine ShortComplex.isoMk (e _) (Iso.refl _) (e _) ?_ ?_
  · change ((ComplexShape.down ℕ).ε p • 𝟙 _) ≫
        (K.X p).d ((ComplexShape.down ℕ).prev q) q =
      ((ComplexShape.down ℕ).ε p • (K.X p).d ((ComplexShape.down ℕ).prev q) q) ≫ 𝟙 _
    simp only [Linear.units_smul_comp, Category.id_comp, Category.comp_id]
  · change (𝟙 _) ≫ (K.X p).d q ((ComplexShape.down ℕ).next q) =
      ((ComplexShape.down ℕ).ε p • (K.X p).d q ((ComplexShape.down ℕ).next q)) ≫
        ((ComplexShape.down ℕ).ε p • 𝟙 _)
    simp only [Linear.units_smul_comp, Linear.comp_units_smul,
      Category.id_comp, Category.comp_id, smul_smul, Int.units_mul_self, one_smul]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: consecutive-column quotient homology identifies
with vertical homology by a comparison preserving middle-degree representatives. -/
def a3sv_columnQuotientHomologyIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    (cokernel ((a3sv_totalColumnFunctor K).map
      (homOfLE (Nat.le_succ p)))).homology (p + q) ≅ (K.X p).homology q := by
  letI := a3sv_totalColumnReindexShortComplex_homologyMap_isIso K p q
  exact asIso (ShortComplex.homologyMap (a3sv_totalColumnReindexShortComplex K p q)) ≪≫
    ShortComplex.homologyMapIso
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) q).mapIso
        (a3sv_totalColumnCokernelComplexIso K p)) ≪≫
    ShortComplex.homologyMapIso (a3sv_signedColumnShortComplexIso K p q)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the canonical quotient homology comparison sends
a lifted vertical cycle to its original homology class. -/
theorem a3sv_columnQuotientHomologyIso_cycles {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    a3sv_columnQuotientCycles K p q ≫
      (cokernel ((a3sv_totalColumnFunctor K).map
        (homOfLE (Nat.le_succ p)))).homologyπ (p + q) ≫
      (a3sv_columnQuotientHomologyIso K p q).hom = (K.X p).homologyπ q := by
  let C := cokernel ((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p)))
  let φ : C.sc (p + q) ⟶ (K.X p).sc q :=
    a3sv_totalColumnReindexShortComplex K p q ≫
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) q).map
        (a3sv_totalColumnCokernelComplexIso K p).hom ≫
      (a3sv_signedColumnShortComplexIso K p q).hom
  have hφ : φ.τ₂ = (a3sv_totalColumnCokernelComponentIso K p q).hom := by
    change (a3sv_totalColumnReindexShortComplex K p q).τ₂ ≫
      (a3sv_totalColumnCokernelComponentIso K p q).hom ≫ 𝟙 _ = _
    rw [a3sv_totalColumnReindexShortComplex_τ₂, Category.id_comp, Category.comp_id]
  have he : (a3sv_columnQuotientHomologyIso K p q).hom = ShortComplex.homologyMap φ := by
    simp only [a3sv_columnQuotientHomologyIso, Iso.trans_hom, asIso_hom,
      ShortComplex.homologyMapIso_hom, Functor.mapIso_hom, φ, ShortComplex.homologyMap_comp]
  have hc : a3sv_columnQuotientCycles K p q ≫ ShortComplex.cyclesMap φ =
      𝟙 ((K.X p).cycles q) := by
    apply (cancel_mono ((K.X p).iCycles q)).mp
    change (a3sv_columnQuotientCycles K p q ≫ ShortComplex.cyclesMap φ) ≫
      ((K.X p).sc q).iCycles = (𝟙 _) ≫ ((K.X p).sc q).iCycles
    rw [Category.assoc, ShortComplex.cyclesMap_i, hφ, Category.id_comp]
    exact a3sv_columnQuotientCycles_component K p q
  rw [he]
  change a3sv_columnQuotientCycles K p q ≫ (C.sc (p + q)).homologyπ ≫
    ShortComplex.homologyMap φ = ((K.X p).sc q).homologyπ
  rw [ShortComplex.homologyπ_naturality, ← Category.assoc, hc, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the quotient connecting map is the horizontal map
on vertical homology under the canonical homology comparisons. -/
theorem a3sv_columnQuotientHomologyIso_delta {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    let f := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p))
    let g := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ (p + 1)))
    (a3sv_columnQuotientHomologyIso K (p + 1) q).inv ≫
      (a3sv_cokernelCompShortComplex_shortExact f g).δ (p + 1 + q) (p + q)
        (by change p + q + 1 = p + 1 + q; omega) ≫
      (a3sv_columnQuotientHomologyIso K p q).hom =
        HomologicalComplex.homologyMap (K.d (p + 1) p) q := by
  dsimp only
  apply (cancel_epi ((K.X (p + 1)).homologyπ q)).mp
  have hs : (K.X (p + 1)).homologyπ q ≫
      (a3sv_columnQuotientHomologyIso K (p + 1) q).inv =
    a3sv_columnQuotientCycles K (p + 1) q ≫
      (cokernel ((a3sv_totalColumnFunctor K).map
        (homOfLE (Nat.le_succ (p + 1))))).homologyπ (p + 1 + q) := by
    rw [← a3sv_columnQuotientHomologyIso_cycles K (p + 1) q]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [reassoc_of% hs, reassoc_of% (a3sv_columnQuotientCycles_delta K p q),
    a3sv_columnQuotientHomologyIso_cycles]
  exact (HomologicalComplex.homologyπ_naturality (K.d (p + 1) p) q).symm

/-- IntersectionProductSV: the degreewise sign correction from a signed
vertical column to its underlying bicomplex column. -/
def a3sv_signedColumnComponentIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    (a3sv_signedColumn K p).X q ≅ (K.X p).X q := by
  dsimp [a3sv_signedColumn]
  exact
    { hom := ((ComplexShape.down ℕ).ε p ^ q) • 𝟙 _
      inv := ((ComplexShape.down ℕ).ε p ^ q)⁻¹ • 𝟙 _
      hom_inv_id := by
        simp only [Linear.comp_units_smul, Category.comp_id, smul_smul]
        simp
      inv_hom_id := by
        simp only [Linear.comp_units_smul, Category.comp_id, smul_smul]
        simp }

/-- IntersectionProductSV: a signed vertical column is isomorphic to the
original bicomplex column by alternating degreewise sign corrections. -/
def a3sv_signedColumnIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p : ℕ) :
    a3sv_signedColumn K p ≅ K.X p :=
  HomologicalComplex.Hom.isoOfComponents (a3sv_signedColumnComponentIso K p) (by
    intro q r hqr
    dsimp [a3sv_signedColumnComponentIso, a3sv_signedColumn]
    change r + 1 = q at hqr
    subst q
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.id_comp,
      Category.comp_id, pow_succ', smul_smul, mul_comm])

/-- IntersectionProductSV: the horizontal differential between adjacent signed
columns is obtained by conjugating the bicomplex horizontal differential by the
degreewise sign corrections. -/
def a3sv_signedColumnHorizontal {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p : ℕ) :
    a3sv_signedColumn K (p + 1) ⟶ a3sv_signedColumn K p :=
  (a3sv_signedColumnIso K (p + 1)).hom ≫ K.d (p + 1) p ≫
    (a3sv_signedColumnIso K p).inv

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: in vertical degree `q`, the signed-column
horizontal map is the bicomplex horizontal differential with sign `(-1)^q`. -/
theorem a3sv_signedColumnHorizontal_f {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    (a3sv_signedColumnHorizontal K p).f q =
      ((ComplexShape.down ℕ).ε q) • (K.d (p + 1) p).f q := by
  dsimp [a3sv_signedColumnHorizontal, a3sv_signedColumnIso,
    a3sv_signedColumnComponentIso]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul,
    Category.comp_id, smul_smul]
  congr 1
  rw [pow_add, neg_pow]
  simp [← mul_pow]

/-- IntersectionProductSV: after removing the column signs, the map on
homology induced by the signed horizontal differential is the original
horizontal homology map. -/
theorem a3sv_signedColumnHorizontal_homology {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    (HomologicalComplex.homologyMapIso (a3sv_signedColumnIso K (p + 1)) q).inv ≫
        HomologicalComplex.homologyMap (a3sv_signedColumnHorizontal K p) q ≫
        (HomologicalComplex.homologyMapIso (a3sv_signedColumnIso K p) q).hom =
      HomologicalComplex.homologyMap (K.d (p + 1) p) q := by
  dsimp only [a3sv_signedColumnHorizontal, HomologicalComplex.homologyMapIso,
    Iso.symm_hom]
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  simp

/-- IntersectionProductSV: consecutive quotient-column complexes are linked by
the horizontal differential of the underlying bicomplex. -/
def a3sv_totalColumnCokernelHorizontal {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p : ℕ) :
    a3sv_totalColumnCokernelComplex K (p + 1) ⟶
      a3sv_totalColumnCokernelComplex K p :=
  (a3sv_totalColumnCokernelComplexIso K (p + 1)).hom ≫
    a3sv_signedColumnHorizontal K p ≫
    (a3sv_totalColumnCokernelComplexIso K p).inv

/-- IntersectionProductSV: the quotient-column comparison intertwines the
packaged quotient horizontal map with the signed column map degreewise. -/
theorem a3sv_totalColumnCokernelHorizontal_f {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    (a3sv_totalColumnCokernelComponentIso K (p + 1) q).inv ≫
        (a3sv_totalColumnCokernelHorizontal K p).f q ≫
        (a3sv_totalColumnCokernelComponentIso K p q).hom =
      (a3sv_signedColumnHorizontal K p).f q := by
  dsimp [a3sv_totalColumnCokernelHorizontal,
    a3sv_totalColumnCokernelComplexIso]
  simp

/-- IntersectionProductSV: the quotient-column horizontal map induces the
usual horizontal map after both quotient and sign comparisons. -/
theorem a3sv_totalColumnCokernelHorizontal_homology {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    (HomologicalComplex.homologyMapIso
          (a3sv_totalColumnCokernelComplexIso K (p + 1) ≪≫
            a3sv_signedColumnIso K (p + 1)) q).inv ≫
        HomologicalComplex.homologyMap
          (a3sv_totalColumnCokernelHorizontal K p) q ≫
        (HomologicalComplex.homologyMapIso
          (a3sv_totalColumnCokernelComplexIso K p ≪≫
            a3sv_signedColumnIso K p) q).hom =
      HomologicalComplex.homologyMap (K.d (p + 1) p) q := by
  dsimp only [a3sv_totalColumnCokernelHorizontal, Iso.trans_hom,
    Iso.trans_inv, HomologicalComplex.homologyMapIso, Iso.symm_hom]
  simp only [Category.assoc, ← HomologicalComplex.homologyMap_comp]
  rw [show
    (a3sv_signedColumnIso K (p + 1)).inv ≫
        (a3sv_totalColumnCokernelComplexIso K (p + 1)).inv ≫
        (a3sv_totalColumnCokernelComplexIso K (p + 1)).hom ≫
        a3sv_signedColumnHorizontal K p ≫
        (a3sv_totalColumnCokernelComplexIso K p).inv ≫
        (a3sv_totalColumnCokernelComplexIso K p).hom ≫
        (a3sv_signedColumnIso K p).hom =
      (a3sv_signedColumnIso K (p + 1)).inv ≫
        a3sv_signedColumnHorizontal K p ≫
        (a3sv_signedColumnIso K p).hom by simp]
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  change (HomologicalComplex.homologyMapIso
      (a3sv_signedColumnIso K (p + 1)) q).inv ≫
        HomologicalComplex.homologyMap (a3sv_signedColumnHorizontal K p) q ≫
        (HomologicalComplex.homologyMapIso
          (a3sv_signedColumnIso K p) q).hom = _
  exact a3sv_signedColumnHorizontal_homology K p q

/-- IntersectionProductSV: extension's opcycle comparison is natural in complex maps. -/
theorem a3sv_extendOpcyclesIso_hom_naturality
    {D : Type u} [Category D] [Abelian D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {K L : HomologicalComplex D c} (φ : K ⟶ L) (e : c.Embedding c')
    {j : ι} {j' : ι'} (hj : e.f j = j') :
    HomologicalComplex.opcyclesMap (HomologicalComplex.extendMap φ e) j' ≫
        (L.extendOpcyclesIso e hj).hom =
      (K.extendOpcyclesIso e hj).hom ≫ HomologicalComplex.opcyclesMap φ j := by
  simp [← cancel_epi ((K.extend e).pOpcycles j'),
    HomologicalComplex.extendMap_f φ e hj]

/-- IntersectionProductSV: extension's cycle and opcycle comparisons
intertwine the differential factored through opcycles and cycles. -/
theorem a3sv_extend_opcyclesToCycles
    {D : Type u} [Category D] [Abelian D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (K : HomologicalComplex D c) (e : c.Embedding c')
    {i j : ι} {i' j' : ι'} (hi : e.f i = i') (hj : e.f j = j') :
    (K.extend e).opcyclesToCycles i' j' ≫ (K.extendCyclesIso e hj).hom =
      (K.extendOpcyclesIso e hi).hom ≫ K.opcyclesToCycles i j := by
  rw [← cancel_epi ((K.extend e).pOpcycles i'),
    ← cancel_mono (K.iCycles j)]
  simp only [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles,
    HomologicalComplex.opcyclesToCycles_iCycles_assoc,
    HomologicalComplex.p_fromOpcycles_assoc,
    HomologicalComplex.pOpcycles_extendOpcyclesIso_hom_assoc,
    HomologicalComplex.opcyclesToCycles_iCycles,
    HomologicalComplex.p_fromOpcycles]
  rw [K.extend_d_eq e hi hj]
  simp

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the homology, opcycle, and cycle comparisons for
extension form a morphism between the two homology-sequence snake diagrams. -/
def a3sv_extendSnakeInput
    {D : Type u} [Category D] [Abelian D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (S : ShortComplex (HomologicalComplex D c)) (hS : S.ShortExact)
    (e : c.Embedding c') (hE : (S.map (e.extendFunctor D)).ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    HomologicalComplex.HomologySequence.snakeInput hE (e.f i) (e.f j) (e.rel hij) ⟶
      HomologicalComplex.HomologySequence.snakeInput hS i j hij where
  f₀ := ShortComplex.homMk
    (S.X₁.extendHomologyIso e rfl).hom
    (S.X₂.extendHomologyIso e rfl).hom
    (S.X₃.extendHomologyIso e rfl).hom
    (by exact (HomologicalComplex.extendHomologyIso_hom_naturality S.f e rfl).symm)
    (by exact (HomologicalComplex.extendHomologyIso_hom_naturality S.g e rfl).symm)
  f₁ := ShortComplex.homMk
    (S.X₁.extendOpcyclesIso e rfl).hom
    (S.X₂.extendOpcyclesIso e rfl).hom
    (S.X₃.extendOpcyclesIso e rfl).hom
    (by exact (a3sv_extendOpcyclesIso_hom_naturality S.f e rfl).symm)
    (by exact (a3sv_extendOpcyclesIso_hom_naturality S.g e rfl).symm)
  f₂ := ShortComplex.homMk
    (S.X₁.extendCyclesIso e rfl).hom
    (S.X₂.extendCyclesIso e rfl).hom
    (S.X₃.extendCyclesIso e rfl).hom
    (by exact (HomologicalComplex.extendCyclesIso_hom_naturality S.f e rfl).symm)
    (by exact (HomologicalComplex.extendCyclesIso_hom_naturality S.g e rfl).symm)
  f₃ := ShortComplex.homMk
    (S.X₁.extendHomologyIso e rfl).hom
    (S.X₂.extendHomologyIso e rfl).hom
    (S.X₃.extendHomologyIso e rfl).hom
    (by exact (HomologicalComplex.extendHomologyIso_hom_naturality S.f e rfl).symm)
    (by exact (HomologicalComplex.extendHomologyIso_hom_naturality S.g e rfl).symm)
  comm₀₁ := by
    ext <;> exact HomologicalComplex.extendHomologyIso_hom_homologyι _ e rfl
  comm₁₂ := by
    ext <;> exact (a3sv_extend_opcyclesToCycles _ e rfl rfl).symm
  comm₂₃ := by
    ext <;> exact (HomologicalComplex.homologyπ_extendHomologyIso_hom _ e rfl).symm

/-- IntersectionProductSV: extension along a complex-shape embedding preserves
short exact sequences of complexes. -/
theorem a3sv_extend_shortExact
    {D : Type u} [Category D] [Abelian D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (S : ShortComplex (HomologicalComplex D c)) (hS : S.ShortExact)
    (e : c.Embedding c') : (S.map (e.extendFunctor D)).ShortExact := by
  letI := hS.mono_f
  letI := hS.epi_g
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j'
  by_cases hj : ∃ j, e.f j = j'
  · obtain ⟨j, hj⟩ := hj
    exact (ShortComplex.shortExact_iff_of_iso
      (S.mapNatIso (e.extendFunctorCompEvalIso D hj))).mpr
        (hS.map (HomologicalComplex.eval D c j))
  · have hz (K : HomologicalComplex D c) : IsZero ((K.extend e).X j') :=
      K.isZero_extend_X e j' (fun j h => hj ⟨j, h⟩)
    exact
      { exact := ShortComplex.exact_of_isZero_X₂ _ (hz S.X₂)
        mono_f := (hz S.X₁).mono _
        epi_g := (hz S.X₃).epi _ }

/-- IntersectionProductSV: extension preserves homology connecting maps under
the canonical homology comparisons. -/
theorem a3sv_extend_delta
    {D : Type u} [Category D] [Abelian D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (S : ShortComplex (HomologicalComplex D c)) (hS : S.ShortExact)
    (e : c.Embedding c') (hE : (S.map (e.extendFunctor D)).ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    hE.δ (e.f i) (e.f j) (e.rel hij) ≫ (S.X₁.extendHomologyIso e rfl).hom =
      (S.X₃.extendHomologyIso e rfl).hom ≫ hS.δ i j hij :=
  ShortComplex.SnakeInput.naturality_δ (a3sv_extendSnakeInput S hS e hE i j hij)

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: extending a cokernel complex and then taking homology
agrees with the homology of the cokernel of the extended map. -/
def a3sv_extendCokernelHomologyIso
    {D : Type u} [Category D] [Abelian D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') [PreservesColimitsOfShape WalkingParallelPair (e.extendFunctor D)]
    {X Y : HomologicalComplex D c} (f : X ⟶ Y) (i : ι) {i' : ι'} (hi : e.f i = i') :
    (cokernel ((e.extendFunctor D).map f)).homology i' ≅ (cokernel f).homology i :=
  (HomologicalComplex.homologyMapIso (PreservesCokernel.iso (e.extendFunctor D) f)
    i').symm ≪≫ (cokernel f).extendHomologyIso e hi

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the quotient connecting map commutes with extension
under the canonical cokernel and homology comparisons. -/
theorem a3sv_extendCokernelHomologyIso_delta
    {D : Type u} [Category D] [Abelian D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') [PreservesColimitsOfShape WalkingParallelPair (e.extendFunctor D)]
    {X Y Z : HomologicalComplex D c} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Mono f] [Mono g] [Mono ((e.extendFunctor D).map f)] [Mono ((e.extendFunctor D).map g)]
    (i j : ι) (hij : c.Rel i j) {i' j' : ι'}
    (hi : e.f i = i') (hj : e.f j = j') :
    (a3sv_extendCokernelHomologyIso e g i hi).inv ≫
      (a3sv_cokernelCompShortComplex_shortExact
        ((e.extendFunctor D).map f) ((e.extendFunctor D).map g)).δ
          i' j' (by rw [← hi, ← hj]; exact e.rel hij) ≫
      (a3sv_extendCokernelHomologyIso e f j hj).hom =
        (a3sv_cokernelCompShortComplex_shortExact f g).δ i j hij := by
  subst i' j'
  let E := e.extendFunctor D
  let S := a3sv_cokernelCompShortComplex f g
  let hS := a3sv_cokernelCompShortComplex_shortExact f g
  let hE := a3sv_extend_shortExact S hS e
  let hT := a3sv_cokernelCompShortComplex_shortExact (E.map f) (E.map g)
  let φ := (a3sv_cokernelCompShortComplexMapIso E f g).hom
  have hn : hE.δ (e.f i) (e.f j) (e.rel hij) ≫
      (HomologicalComplex.homologyMapIso (PreservesCokernel.iso E f) (e.f j)).hom =
    (HomologicalComplex.homologyMapIso (PreservesCokernel.iso E g) (e.f i)).hom ≫
      hT.δ (e.f i) (e.f j) (e.rel hij) :=
    HomologicalComplex.HomologySequence.δ_naturality φ hE hT (e.f i) (e.f j) (e.rel hij)
  have he : hE.δ (e.f i) (e.f j) (e.rel hij) ≫
      ((cokernel f).extendHomologyIso e rfl).hom =
    ((cokernel g).extendHomologyIso e rfl).hom ≫ hS.δ i j hij :=
    a3sv_extend_delta S hS e hE i j hij
  dsimp only [a3sv_extendCokernelHomologyIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, Iso.hom_inv_id_assoc, he, Iso.inv_hom_id_assoc]

/-- IntersectionProductSV: extension by zero along the downward natural-number
embedding preserves parallel-pair colimits. -/
theorem a3sv_extendDownNat_preserves_parallelPair {B : Type u} [CommRing B] :
    PreservesColimitsOfShape WalkingParallelPair
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun j => by
    by_cases hj : ∃ i, ComplexShape.embeddingDownNat.f i = j
    · obtain ⟨i, hi⟩ := hj
      exact preservesColimitsOfShape_of_natIso
        (ComplexShape.embeddingDownNat.extendFunctorCompEvalIso (ModuleCat.{u} B) hi).symm
    · apply Functor.preservesColimitsOfShape_of_isZero _ _ _
      rw [IsZero.iff_id_eq_zero]
      apply NatTrans.ext
      funext K
      exact (K.isZero_extend_X ComplexShape.embeddingDownNat j
        (fun i hi => hj ⟨i, hi⟩)).eq_of_src _ _)

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the first page is vertical homology through
canonical quotient-cycle and extension comparisons. -/
def a3sv_totalColumnFirstPageColumnIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    ((a3sv_totalColumnSpectralSequence K).page 1).X ((p : ℤ), (q : ℤ)) ≅
      (K.X p).homology q := by
  letI := a3sv_extendDownNat_preserves_parallelPair (B := B)
  exact a3sv_totalColumnFirstPageCokernelIso K (p : ℤ) (q : ℤ) ≪≫
    a3sv_extendCokernelHomologyIso ComplexShape.embeddingDownNat
      ((a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p))) (p + q)
      (by change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ); omega) ≪≫
    a3sv_columnQuotientHomologyIso K p q

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the first column differential is the spectral
connecting morphism between the two adjacent filtration intervals. -/
theorem a3sv_totalColumn_firstPage_d_eq {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    let S := a3sv_totalColumnSpectralObject K
    ((a3sv_totalColumnSpectralSequence K).page 1).d
        (((p + 1 : ℕ) : ℤ), (q : ℤ)) ((p : ℤ), (q : ℤ)) =
      (a3sv_totalColumnFirstPageIso K ((p + 1 : ℕ) : ℤ) (q : ℤ)).hom ≫ S.δ
        (homOfLE (show (p : ℤ) ≤ p + 1 by omega))
        (homOfLE (show ((p + 1 : ℕ) : ℤ) ≤ p + 2 by omega))
        (-((p + 1 : ℕ) : ℤ) - (q : ℤ)) (-(p : ℤ) - (q : ℤ)) (by omega) ≫
      (a3sv_totalColumnFirstPageIso K (p : ℤ) (q : ℤ)).inv := by
  letI := a3sv_homologicalFiltration_hasSpectralSequence
    (a3sv_totalColumnSpectralObject K)
  letI := a3sv_homologicalFiltration_firstPage
  dsimp only [a3sv_totalColumnSpectralSequence]
  dsimp only [a3sv_totalColumnFirstPageIso]
  convert CategoryTheory.Abelian.SpectralObject.spectralSequence_first_page_d_eq
    (a3sv_totalColumnSpectralObject K) a3sv_homologicalFiltrationData
    (((p + 1 : ℕ) : ℤ), (q : ℤ)) ((p : ℤ), (q : ℤ)) (by
      change ((((p + 1 : ℕ) : ℤ), (q : ℤ)) + (-1, 0)) =
        ((p : ℤ), (q : ℤ))
      ext <;> simp)
    (p : ℤ) ((p + 1 : ℕ) : ℤ) ((p + 2 : ℕ) : ℤ)
    rfl rfl (by dsimp [a3sv_homologicalFiltrationData]; omega)
      (-((p + 1 : ℕ) : ℤ) - (q : ℤ)) (-(p : ℤ) - (q : ℤ)) rfl (by omega) using 1 <;>
    simp <;> congr 1

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the first column differential is the connecting map
for the short exact sequence of the two consecutive quotient columns. -/
theorem a3sv_totalColumnFirstPageCokernel_d {B : Type} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{0} B) ℕ) ℕ) (p q : ℕ) :
    let F := a3sv_totalColumnExtendedFunctor K
    let f : (p : ℤ) ⟶ p + 1 := homOfLE (by omega)
    let g : ((p + 1 : ℕ) : ℤ) ⟶ p + 2 := homOfLE (by omega)
    (a3sv_totalColumnFirstPageCokernelIso K ((p + 1 : ℕ) : ℤ) (q : ℤ)).inv ≫
        ((a3sv_totalColumnSpectralSequence K).page 1).d
          (((p + 1 : ℕ) : ℤ), (q : ℤ)) ((p : ℤ), (q : ℤ)) ≫
        (a3sv_totalColumnFirstPageCokernelIso K (p : ℤ) (q : ℤ)).hom =
      (a3sv_cokernelCompShortComplex_shortExact (F.map f) (F.map g)).δ
        (-((p + 1 : ℕ) : ℤ) - (q : ℤ)) (-(p : ℤ) - (q : ℤ)) (by
          change -((p + 1 : ℕ) : ℤ) - (q : ℤ) + 1 = -(p : ℤ) - (q : ℤ)
          omega) := by
  dsimp only
  rw [a3sv_totalColumn_firstPage_d_eq]
  dsimp only [a3sv_totalColumnFirstPageCokernelIso, Iso.trans_hom, Iso.trans_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hh := a3sv_filtration_quotient_delta (a3sv_totalColumnExtendedFunctor K)
    (homOfLE (show (p : ℤ) ≤ p + 1 by omega))
    (homOfLE (show ((p + 1 : ℕ) : ℤ) ≤ p + 2 by omega))
    (-((p + 1 : ℕ) : ℤ) - (q : ℤ)) (-(p : ℤ) - (q : ℤ)) (by omega)
  have hh' := congrArg (fun a =>
    (a3sv_mappingConeCokernelHomologyIso
      ((a3sv_totalColumnExtendedFunctor K).map
        (homOfLE (show ((p + 1 : ℕ) : ℤ) ≤ p + 2 by omega)))
      (-((p + 1 : ℕ) : ℤ) - (q : ℤ))).inv ≫ a) hh
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, a3sv_totalColumnSpectralObject,
    a3sv_totalColumnExtendedFunctor] using hh'

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the first spectral differential is the horizontal
map induced on vertical homology. -/
theorem a3sv_totalColumn_firstPage_horizontal {B : Type} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{0} B) ℕ) ℕ) (p q : ℕ) :
    (a3sv_totalColumnFirstPageColumnIso K (p + 1) q).inv ≫
      ((a3sv_totalColumnSpectralSequence K).page 1).d
        (((p + 1 : ℕ) : ℤ), (q : ℤ)) ((p : ℤ), (q : ℤ)) ≫
      (a3sv_totalColumnFirstPageColumnIso K p q).hom =
        HomologicalComplex.homologyMap (K.d (p + 1) p) q := by
  letI := a3sv_extendDownNat_preserves_parallelPair (B := B)
  let E := ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{0} B)
  let f := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p))
  let g := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ (p + 1)))
  haveI : Mono (E.map f) := a3sv_totalColumnExtendedFunctor_map_mono K
    (homOfLE (show (p : ℤ) ≤ p + 1 by omega))
  haveI : Mono (E.map g) := a3sv_totalColumnExtendedFunctor_map_mono K
    (homOfLE (show ((p + 1 : ℕ) : ℤ) ≤ p + 2 by omega))
  dsimp only [a3sv_totalColumnFirstPageColumnIso, Iso.trans_inv, Iso.trans_hom]
  simp only [Category.assoc]
  rw [reassoc_of% (a3sv_totalColumnFirstPageCokernel_d K p q)]
  have hh := a3sv_extendCokernelHomologyIso_delta ComplexShape.embeddingDownNat f g
    (p + 1 + q) (p + q) (by change p + q + 1 = p + 1 + q; omega)
    (show ComplexShape.embeddingDownNat.f (p + 1 + q) =
        -((p + 1 : ℕ) : ℤ) - (q : ℤ) by change -((p + 1 + q : ℕ) : ℤ) = _; omega)
    (show ComplexShape.embeddingDownNat.f (p + q) = -(p : ℤ) - (q : ℤ) by
      change -((p + q : ℕ) : ℤ) = _; omega)
  rw [reassoc_of% hh]
  exact a3sv_columnQuotientHomologyIso_delta K p q

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the first column-filtration page vanishes in
negative columns. -/
theorem a3sv_totalColumnFirstPage_isZero_of_neg_column {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q : ℤ) (hp : p < 0) :
    IsZero (((a3sv_totalColumnSpectralSequence K).page 1).X (p, q)) := by
  let f : p ⟶ p + 1 := homOfLE (by omega)
  let a : p.toNat ⟶ (p + 1).toNat :=
    homOfLE (Int.toNat_le_toNat (show p ≤ p + 1 by omega))
  have ha : a = eqToHom (show p.toNat = (p + 1).toNat by omega) := Subsingleton.elim _ _
  haveI : IsIso a := by rw [ha]; infer_instance
  haveI : IsIso ((a3sv_totalColumnExtendedFunctor K).map f) := by
    change IsIso ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)).map
      ((a3sv_totalColumnFunctor K).map a))
    infer_instance
  apply IsZero.of_iso _ (a3sv_totalColumnFirstPageCokernelIso K p q)
  exact (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ)
    (-p - q)).map_isZero (isZero_cokernel_of_epi ((a3sv_totalColumnExtendedFunctor K).map f))

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the first column-filtration page vanishes in
negative rows above every natural-number column. -/
theorem a3sv_totalColumnFirstPage_isZero_of_neg_row {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p : ℕ) (q : ℤ) (hq : q < 0) :
    IsZero (((a3sv_totalColumnSpectralSequence K).page 1).X ((p : ℤ), q)) := by
  letI := a3sv_extendDownNat_preserves_parallelPair (B := B)
  let E := ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)
  let f := (a3sv_totalColumnFunctor K).map (homOfLE (Nat.le_succ p))
  let C := cokernel f
  apply IsZero.of_iso _ (a3sv_totalColumnFirstPageCokernelIso K (p : ℤ) q)
  change IsZero ((cokernel (E.map f)).homology (-(p : ℤ) - q))
  apply IsZero.of_iso _
    (HomologicalComplex.homologyMapIso (PreservesCokernel.iso E f).symm (-(p : ℤ) - q))
  apply ((C.extend ComplexShape.embeddingDownNat).sc (-(p : ℤ) - q)).isZero_homology_of_isZero_X₂
  change IsZero ((C.extend ComplexShape.embeddingDownNat).X (-(p : ℤ) - q))
  by_cases h : ∃ n, ComplexShape.embeddingDownNat.f n = -(p : ℤ) - q
  · obtain ⟨n, hn⟩ := h
    apply IsZero.of_iso _ (C.extendXIso ComplexShape.embeddingDownNat hn)
    apply a3sv_totalColumnTransitionCokernel_isZero_of_lt K p n
    change -(n : ℤ) = -(p : ℤ) - q at hn
    omega
  · exact C.isZero_extend_X ComplexShape.embeddingDownNat (-(p : ℤ) - q)
      (fun n hn => h ⟨n, hn⟩)

/-- IntersectionProductSV: the first-page comparisons intertwine adjacent
horizontal differentials. -/
theorem a3sv_totalColumn_firstPage_horizontal_comm {B : Type} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{0} B) ℕ) ℕ) (p q : ℕ) :
    (a3sv_totalColumnFirstPageColumnIso K (p + 1) q).hom ≫
      HomologicalComplex.homologyMap (K.d (p + 1) p) q =
    ((a3sv_totalColumnSpectralSequence K).page 1).d
      (((p + 1 : ℕ) : ℤ), (q : ℤ)) ((p : ℤ), (q : ℤ)) ≫
      (a3sv_totalColumnFirstPageColumnIso K p q).hom := by
  have h := congrArg (fun a =>
    (a3sv_totalColumnFirstPageColumnIso K (p + 1) q).hom ≫ a)
    (a3sv_totalColumn_firstPage_horizontal K p q)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h.symm

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the second column-filtration page is horizontal
homology of vertical homology, including the boundary column. -/
def a3sv_totalColumnSecondPageIso {B : Type} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{0} B) ℕ) ℕ) (p q : ℕ) :
    ((a3sv_totalColumnSpectralSequence K).page 2).X ((p : ℤ), (q : ℤ)) ≅
      (((HomologicalComplex.homologyFunctor (ModuleCat.{0} B) (ComplexShape.down ℕ) q).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology p := by
  let P := (a3sv_totalColumnSpectralSequence K).page 1
  let R := ((HomologicalComplex.homologyFunctor (ModuleCat.{0} B) (ComplexShape.down ℕ) q).mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  refine ((a3sv_totalColumnSpectralSequence K).iso 1 2 ((p : ℤ), (q : ℤ)) rfl).symm ≪≫ ?_
  cases p with
  | succ p =>
    let i : ℤ × ℤ := (((p + 2 : ℕ) : ℤ), (q : ℤ))
    let j : ℤ × ℤ := (((p + 1 : ℕ) : ℤ), (q : ℤ))
    let k : ℤ × ℤ := ((p : ℤ), (q : ℤ))
    let e : P.sc' i j k ≅ R.sc' (p + 2) (p + 1) p :=
      ShortComplex.isoMk (a3sv_totalColumnFirstPageColumnIso K (p + 2) q)
        (a3sv_totalColumnFirstPageColumnIso K (p + 1) q)
        (a3sv_totalColumnFirstPageColumnIso K p q)
        (by exact a3sv_totalColumn_firstPage_horizontal_comm K (p + 1) q)
        (by exact a3sv_totalColumn_firstPage_horizontal_comm K p q)
    refine P.homologyIsoSc' i j k ?_ ?_ ≪≫ ShortComplex.homologyMapIso e ≪≫
      (R.homologyIsoSc' (p + 2) (p + 1) p ?_ ?_).symm
    · apply ComplexShape.prev_eq'
      change ((((p + 2 : ℕ) : ℤ), (q : ℤ)) + (-1, 1 - 1)) =
        (((p + 1 : ℕ) : ℤ), (q : ℤ))
      ext <;> dsimp <;> omega
    · apply ComplexShape.next_eq'
      change ((((p + 1 : ℕ) : ℤ), (q : ℤ)) + (-1, 1 - 1)) = ((p : ℤ), (q : ℤ))
      ext <;> dsimp <;> omega
    · simp [ChainComplex.prev]
    · exact ChainComplex.next_nat_succ p
  | zero =>
    let i : ℤ × ℤ := (1, (q : ℤ))
    let j : ℤ × ℤ := (0, (q : ℤ))
    let k : ℤ × ℤ := (-1, (q : ℤ))
    let φ : P.sc' i j k ⟶ R.sc' 1 0 0 :=
      ShortComplex.homMk (a3sv_totalColumnFirstPageColumnIso K 1 q).hom
        (a3sv_totalColumnFirstPageColumnIso K 0 q).hom 0
        (by exact a3sv_totalColumn_firstPage_horizontal_comm K 0 q)
        (by
          change (a3sv_totalColumnFirstPageColumnIso K 0 q).hom ≫ R.d 0 0 = P.d j k ≫ 0
          rw [R.shape 0 0 (by simp), comp_zero, comp_zero])
    haveI : Epi φ.τ₁ := by change Epi (a3sv_totalColumnFirstPageColumnIso K 1 q).hom; infer_instance
    haveI : IsIso φ.τ₂ := by change IsIso (a3sv_totalColumnFirstPageColumnIso K 0 q).hom; infer_instance
    haveI : Mono φ.τ₃ :=
      (a3sv_totalColumnFirstPage_isZero_of_neg_column K (-1) (q : ℤ) (by omega)).mono _
    refine P.homologyIsoSc' i j k ?_ ?_ ≪≫ asIso (ShortComplex.homologyMap φ) ≪≫
      (R.homologyIsoSc' 1 0 0 ?_ ?_).symm
    · apply ComplexShape.prev_eq'
      change ((1, (q : ℤ)) + (-1, 1 - 1)) = (0, (q : ℤ))
      ext <;> simp
    · apply ComplexShape.next_eq'
      change ((0, (q : ℤ)) + (-1, 1 - 1)) = (-1, (q : ℤ))
      ext <;> simp
    · exact ChainComplex.prev ℕ 0
    · exact ChainComplex.next_nat_zero

/-- IntersectionProductSV: the second column-filtration page vanishes outside
the first quadrant. -/
theorem a3sv_totalColumnSecondPage_isZero_of_negative {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q : ℤ) (hpq : p < 0 ∨ q < 0) :
    IsZero (((a3sv_totalColumnSpectralSequence K).page 2).X (p, q)) := by
  apply IsZero.of_iso _ ((a3sv_totalColumnSpectralSequence K).iso 1 2 (p, q) rfl).symm
  apply (((a3sv_totalColumnSpectralSequence K).page 1).sc (p, q)).isZero_homology_of_isZero_X₂
  rcases hpq with hp | hq
  · exact a3sv_totalColumnFirstPage_isZero_of_neg_column K p q hp
  · by_cases hp : p < 0
    · exact a3sv_totalColumnFirstPage_isZero_of_neg_column K p q hp
    · have hp' : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (le_of_not_gt hp)
      rw [← hp']
      exact a3sv_totalColumnFirstPage_isZero_of_neg_row K p.toNat q hq

/-- IntersectionProductSV: finite length and a fixed finite support persist
from any chosen page through all later pages. -/
theorem a3sv_spectralSequence_finite_after {B : Type u} [CommRing B] {ι : Type*}
    {c : ℤ → ComplexShape ι} {r₀ : ℤ}
    (E : SpectralSequence (ModuleCat.{u} B) c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (s : Finset ι)
    (hfinite : ∀ i ∈ s, Module.length B ((E.page r hr).X i) ≠ ⊤)
    (hbounded : ∀ i ∉ s, IsZero ((E.page r hr).X i)) (k : ℕ) :
    (∀ i ∈ s, Module.length B ((E.page (r + k) (by omega)).X i) ≠ ⊤) ∧
      (∀ i ∉ s, IsZero ((E.page (r + k) (by omega)).X i)) := by
  induction k with
  | zero =>
    constructor
    · intro i hi
      rw [← (E.pageXIsoOfEq i r (r + (0 : ℕ)) (by omega) hr).toLinearEquiv.length_eq]
      exact hfinite i hi
    · intro i hi
      exact IsZero.of_iso (hbounded i hi)
        (E.pageXIsoOfEq i r (r + (0 : ℕ)) (by omega) hr).symm
  | succ k ih =>
    have h := a3sv_spectralSequence_page_finite E (r + k) (by omega) s ih.1 ih.2
    constructor
    · intro i hi
      rw [← (E.pageXIsoOfEq i (r + k + 1) (r + (k + 1 : ℕ))
        (by omega) (by omega)).toLinearEquiv.length_eq]
      exact h.1 i hi
    · intro i hi
      exact IsZero.of_iso (h.2 i hi)
        (E.pageXIsoOfEq i (r + k + 1) (r + (k + 1 : ℕ)) (by omega) (by omega)).symm

/-- IntersectionProductSV: a finite-length spectral Euler sum can be started
at any page with finite support. -/
theorem a3sv_spectralSequence_euler_from {B : Type u} [CommRing B] {ι : Type*}
    {c : ℤ → ComplexShape ι} {r₀ : ℤ}
    (E : SpectralSequence (ModuleCat.{u} B) c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (s : Finset ι) (sign : ι → ℤ)
    (hsign : ∀ t, r ≤ t → ∀ i j, (c t).Rel i j → sign i = -sign j)
    (hfinite : ∀ i ∈ s, Module.length B ((E.page r hr).X i) ≠ ⊤)
    (hbounded : ∀ i ∉ s, IsZero ((E.page r hr).X i)) (k : ℕ) :
    (∑ i ∈ s, sign i * ((Module.length B ((E.page (r + k) (by omega)).X i)).toNat : ℤ)) =
      ∑ i ∈ s, sign i * ((Module.length B ((E.page r hr).X i)).toNat : ℤ) := by
  let E' : SpectralSequence (ModuleCat.{u} B) c r :=
    { page t ht := E.page t (hr.trans ht)
      iso t t' i htt' ht := E.iso t t' i htt' (hr.trans ht) }
  exact a3sv_spectralSequence_euler E' s sign hsign hfinite hbounded k

/-- IntersectionProductSV: a triangular degree sum of a rectangularly
supported function equals its rectangular double sum. -/
theorem a3sv_triangle_sum_eq_rectangle (F : ℕ → ℕ → ℤ) (m n : ℕ)
    (hz : ∀ p q, m < p ∨ n < q → F p q = 0) :
    (∑ i ∈ Finset.range (m + n + 1), ∑ p ∈ Finset.range (i + 1), F p (i - p)) =
      ∑ p ∈ Finset.range (m + 1), ∑ q ∈ Finset.range (n + 1), F p q := by
  rw [Finset.sum_sigma' (Finset.range (m + n + 1))
      (fun i => Finset.range (i + 1)) (fun i p => F p (i - p)),
    ← Finset.sum_product' (Finset.range (m + 1)) (Finset.range (n + 1)) F]
  refine Finset.sum_bij_ne_zero (fun a _ _ => (a.2, a.1 - a.2)) ?_ ?_ ?_ ?_
  · intro a ha hF
    have hp : a.2 ≤ m := by
      by_contra h
      exact hF (hz _ _ (Or.inl (by omega)))
    have hq : a.1 - a.2 ≤ n := by
      by_contra h
      exact hF (hz _ _ (Or.inr (by omega)))
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  · rintro ⟨i, p⟩ hi hFi ⟨j, q⟩ hj hFj he
    simp only [Finset.mem_sigma, Finset.mem_range] at hi hj
    have hpq : p = q := congrArg Prod.fst he
    have hs : i - p = j - q := congrArg Prod.snd he
    exact Sigma.ext (by change i = j; omega) (heq_of_eq hpq)
  · rintro ⟨p, q⟩ hpq hF
    simp only [Finset.mem_product, Finset.mem_range] at hpq
    refine ⟨⟨p + q, p⟩, ?_, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · simpa using hF
    · simp
  · intro a ha hF
    rfl

/-- IntersectionProductSV: the integer bidegrees in a bounded first-quadrant rectangle. -/
def a3sv_columnRectangle (m n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.range (m + 1)) ×ˢ (Finset.range (n + 1))).map
    ⟨fun pq => ((pq.1 : ℤ), (pq.2 : ℤ)), by
      intro a b h
      apply Prod.ext
      · exact Int.ofNat.inj (congrArg Prod.fst h)
      · exact Int.ofNat.inj (congrArg Prod.snd h)⟩

/-- IntersectionProductSV: membership of a natural bidegree in the column rectangle. -/
theorem a3sv_mem_columnRectangle (m n p q : ℕ) :
    ((p : ℤ), (q : ℤ)) ∈ a3sv_columnRectangle m n ↔ p ≤ m ∧ q ≤ n := by
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_map.mp h
    have ha : a = p := Int.ofNat.inj (congrArg Prod.fst he)
    have hb : b = q := Int.ofNat.inj (congrArg Prod.snd he)
    subst a; subst b
    simpa only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] using hab
  · intro h
    apply Finset.mem_map.mpr
    refine ⟨(p, q), ?_, rfl⟩
    simpa only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] using h

/-- IntersectionProductSV: summation over the integer column rectangle is the
corresponding natural-number double sum. -/
theorem a3sv_columnRectangle_sum (m n : ℕ) (f : ℤ × ℤ → ℤ) :
    (∑ i ∈ a3sv_columnRectangle m n, f i) =
      ∑ p ∈ Finset.range (m + 1), ∑ q ∈ Finset.range (n + 1), f ((p : ℤ), (q : ℤ)) := by
  simp only [a3sv_columnRectangle, Finset.sum_map, Finset.sum_product]
  rfl

/-- IntersectionProductSV: the first total-column differential factors through
the packaged homology map of consecutive filtration cones. -/
theorem a3sv_totalColumn_firstPage_d_factorization {B : Type} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{0} B) ℕ) ℕ) (p q : ℕ) :
    let F := a3sv_totalColumnExtendedFunctor K
    let f : (p : ℤ) ⟶ p + 1 := homOfLE (by omega)
    let g : ((p + 1 : ℕ) : ℤ) ⟶ p + 2 := homOfLE (by omega)
    ((a3sv_totalColumnSpectralSequence K).page 1).d
        (((p + 1 : ℕ) : ℤ), (q : ℤ)) ((p : ℤ), (q : ℤ)) =
      (a3sv_totalColumnFirstPageIso K ((p + 1 : ℕ) : ℤ) (q : ℤ)).hom ≫
        a3sv_mappingConePrecompHomologyMap F f g
          (-((p + 1 : ℕ) : ℤ) - (q : ℤ)) (-(p : ℤ) - (q : ℤ)) (by omega) ≫
      (a3sv_totalColumnFirstPageIso K (p : ℤ) (q : ℤ)).inv := by
  dsimp only
  rw [a3sv_totalColumn_firstPage_d_eq]
  rw [a3sv_totalColumn_delta_factorization]
  congr 1

/-- IntersectionProductSV: the first total-column differential transported to
the vertical homology of adjacent bicomplex columns. -/
def a3sv_totalColumnVerticalHomologyDifferential {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p q : ℕ) :
    (K.X (p + 1)).homology q ⟶ (K.X p).homology q :=
  (a3sv_totalColumnFirstPageColumnIso K (p + 1) q).inv ≫
    ((a3sv_totalColumnSpectralSequence K).page 1).d
      (((p + 1 : ℕ) : ℤ), (q : ℤ)) ((p : ℤ), (q : ℤ)) ≫
    (a3sv_totalColumnFirstPageColumnIso K p q).hom

/-- IntersectionProductSV: each component of the inclusion into the total complex is the submodule subtype map. -/
theorem a3sv_totalColumnInclusion_f {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ) (p i : ℕ) :
    (a3sv_totalColumnInclusion K p).f i =
      ModuleCat.ofHom (a3sv_totalColumnFiltration K i p).subtype := rfl

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the column filtration inclusions form a cocone over the filtration functor. -/
theorem a3sv_totalColumnFunctorInclusion_naturality {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q : ℕ) (hpq : p ≤ q) :
    (a3sv_totalColumnFunctor K).map (homOfLE hpq) ≫
      (a3sv_totalColumnFunctorObjIso K q).hom ≫ a3sv_totalColumnInclusion K q =
    (a3sv_totalColumnFunctorObjIso K p).hom ≫ a3sv_totalColumnInclusion K p := by
  apply HomologicalComplex.Hom.ext
  funext i
  rewrite [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, a3sv_totalColumnFunctorObjIso_hom_f,
    a3sv_totalColumnFunctorObjIso_hom_f, a3sv_totalColumnFunctor_map_f,
    a3sv_totalColumnInclusion_f, a3sv_totalColumnInclusion_f]
  have h (M : ModuleCat.{u} B) (S T : Submodule B M) (hST : S ≤ T) :
      ModuleCat.ofHom (Submodule.inclusion hST) ≫ 𝟙 (ModuleCat.of B T) ≫
        ModuleCat.ofHom T.subtype =
      𝟙 (ModuleCat.of B S) ≫ ModuleCat.ofHom S.subtype := by
    ext x
    rfl
  exact h _ _ _ _

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: maps of column intervals with zero lower endpoint induce the homology maps of filtration inclusions. -/
theorem a3sv_totalColumnIntervalHomologyIso_naturality {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q r : ℤ) (hpq : p ≤ q) (hqr : q ≤ r) (hp : p ≤ 0) (i : ℕ) :
    ((a3sv_totalColumnSpectralObject K).H (-(i : ℤ))).map
        (twoδ₂Toδ₁ (homOfLE hpq) (homOfLE hqr) (homOfLE (hpq.trans hqr)) rfl) ≫
      (a3sv_totalColumnIntervalHomologyIso K p r (hpq.trans hqr) hp i).hom =
    (a3sv_totalColumnIntervalHomologyIso K p q hpq hp i).hom ≫
      HomologicalComplex.homologyMap
        ((a3sv_totalColumnFunctor K).map (homOfLE (Int.toNat_le_toNat hqr))) i := by
  let F := (show Monotone Int.toNat from fun _ _ h => Int.toNat_le_toNat h).functor ⋙
    a3sv_totalColumnFunctor K ⋙ ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)
  have hz : IsZero (F.obj p) := by
    change IsZero ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)).obj
      ((a3sv_totalColumnFunctor K).obj p.toNat))
    rw [Int.toNat_eq_zero.mpr hp]
    exact (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)).map_isZero
      (IsZero.of_iso (a3sv_totalColumnComplex_zero K) (a3sv_totalColumnFunctorObjIso K 0))
  dsimp only [a3sv_totalColumnIntervalHomologyIso, Iso.trans_hom, a3sv_totalColumnSpectralObject]
  rw [← Category.assoc, a3sv_spectralIntervalFromZeroIso_naturality (hf := hz)]
  simp only [Category.assoc]
  congr 1
  exact HomologicalComplex.extendHomologyIso_hom_naturality
    ((a3sv_totalColumnFunctor K).map (homOfLE (Int.toNat_le_toNat hqr)))
    ComplexShape.embeddingDownNat rfl

open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: an interval containing the entire bounded column filtration computes total-complex homology. -/
def a3sv_totalColumnIntervalTotalHomologyIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (m : ℕ) (hK : ∀ a, m < a → IsZero (K.X a))
    (p q : ℤ) (hpq : p ≤ q) (hp : p ≤ 0) (hmq : m < q.toNat) (i : ℕ) :
    ((a3sv_totalColumnSpectralObject K).H (-(i : ℤ))).obj (mk₁ (homOfLE hpq)) ≅
      (HomologicalComplex₂.total K (ComplexShape.down ℕ)).homology i := by
  letI := a3sv_totalColumnInclusion_isIso_of_bound K m q.toNat hmq hK
  exact a3sv_totalColumnIntervalHomologyIso K p q hpq hp i ≪≫
    HomologicalComplex.homologyMapIso (a3sv_totalColumnFunctorObjIso K q.toNat) i ≪≫
      HomologicalComplex.homologyMapIso (asIso (a3sv_totalColumnInclusion K q.toNat)) i

/-- IntersectionProductSV: an interval whose upper endpoint exhausts the
three terms around one total degree computes homology in that degree. -/
def a3sv_totalColumnIntervalDegreeHomologyIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q : ℤ) (hpq : p ≤ q) (hp : p ≤ 0) (i : ℕ) (hiq : i + 1 < q.toNat) :
    ((a3sv_totalColumnSpectralObject K).H (-(i : ℤ))).obj
        (CategoryTheory.ComposableArrows.mk₁ (homOfLE hpq)) ≅
      (HomologicalComplex₂.total K (ComplexShape.down ℕ)).homology i := by
  letI := a3sv_totalColumnInclusion_homologyMap_isIso K q.toNat i hiq
  exact a3sv_totalColumnIntervalHomologyIso K p q hpq hp i ≪≫
    HomologicalComplex.homologyMapIso (a3sv_totalColumnFunctorObjIso K q.toNat) i ≪≫
      asIso (HomologicalComplex.homologyMap
        (a3sv_totalColumnInclusion K q.toNat) i)

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: an interval map into an exhaustive column interval is the homology map of the column inclusion. -/
theorem a3sv_totalColumnIntervalTotalHomologyIso_naturality {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (m : ℕ) (hK : ∀ a, m < a → IsZero (K.X a))
    (p q r : ℤ) (hpq : p ≤ q) (hqr : q ≤ r) (hp : p ≤ 0)
    (hmr : m < r.toNat) (i : ℕ) :
    ((a3sv_totalColumnSpectralObject K).H (-(i : ℤ))).map
        (twoδ₂Toδ₁ (homOfLE hpq) (homOfLE hqr) (homOfLE (hpq.trans hqr)) rfl) ≫
      (a3sv_totalColumnIntervalTotalHomologyIso K m hK p r (hpq.trans hqr) hp hmr i).hom =
    (a3sv_totalColumnIntervalHomologyIso K p q hpq hp i).hom ≫
      HomologicalComplex.homologyMap (a3sv_totalColumnFunctorObjIso K q.toNat).hom i ≫
      HomologicalComplex.homologyMap (a3sv_totalColumnInclusion K q.toNat) i := by
  dsimp only [a3sv_totalColumnIntervalTotalHomologyIso, Iso.trans_hom,
    HomologicalComplex.homologyMapIso_hom, asIso_hom]
  rw [← Category.assoc, ← Category.assoc,
    a3sv_totalColumnIntervalHomologyIso_naturality]
  have h := congrArg (fun f => HomologicalComplex.homologyMap f i)
    (a3sv_totalColumnFunctorInclusion_naturality K q.toNat r.toNat
      (Int.toNat_le_toNat hqr))
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc] at h ⊢
  simpa only [HomologicalComplex.homologyMapIso_hom, asIso_hom] using
    congrArg ((a3sv_totalColumnIntervalHomologyIso K p q hpq hp i).hom ≫ ·) h

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: a map into a degreewise exhaustive interval agrees
with the homology map of the column inclusion. -/
theorem a3sv_totalColumnIntervalDegreeHomologyIso_naturality
    {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q r : ℤ) (hpq : p ≤ q) (hqr : q ≤ r) (hp : p ≤ 0)
    (i : ℕ) (hir : i + 1 < r.toNat) :
    ((a3sv_totalColumnSpectralObject K).H (-(i : ℤ))).map
        (twoδ₂Toδ₁ (homOfLE hpq) (homOfLE hqr)
          (homOfLE (hpq.trans hqr)) rfl) ≫
      (a3sv_totalColumnIntervalDegreeHomologyIso K p r
        (hpq.trans hqr) hp i hir).hom =
    (a3sv_totalColumnIntervalHomologyIso K p q hpq hp i).hom ≫
      HomologicalComplex.homologyMap
        (a3sv_totalColumnFunctorObjIso K q.toNat).hom i ≫
      HomologicalComplex.homologyMap
        (a3sv_totalColumnInclusion K q.toNat) i := by
  dsimp only [a3sv_totalColumnIntervalDegreeHomologyIso, Iso.trans_hom,
    HomologicalComplex.homologyMapIso_hom, asIso_hom]
  rw [← Category.assoc, ← Category.assoc,
    a3sv_totalColumnIntervalHomologyIso_naturality]
  have h := congrArg (fun f => HomologicalComplex.homologyMap f i)
    (a3sv_totalColumnFunctorInclusion_naturality K q.toNat r.toNat
      (Int.toNat_le_toNat hqr))
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc] at h ⊢
  simpa only [HomologicalComplex.homologyMapIso_hom] using
    congrArg ((a3sv_totalColumnIntervalHomologyIso K p q hpq hp i).hom ≫ ·) h

open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: the image of a column interval inside an exhaustive interval is the induced homology filtration. -/
theorem a3sv_totalColumnInterval_range {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (m : ℕ) (hK : ∀ a, m < a → IsZero (K.X a))
    (p q r : ℤ) (hpq : p ≤ q) (hqr : q ≤ r) (hp : p ≤ 0)
    (hmr : m < r.toNat) (i : ℕ) :
    (((a3sv_totalColumnSpectralObject K).H (-(i : ℤ))).map
      (twoδ₂Toδ₁ (homOfLE hpq) (homOfLE hqr) (homOfLE (hpq.trans hqr)) rfl)).hom.range.map
        (a3sv_totalColumnIntervalTotalHomologyIso K m hK p r (hpq.trans hqr) hp hmr i).hom.hom =
    a3sv_homologyFiltration (HomologicalComplex₂.total K (ComplexShape.down ℕ))
      i (a3sv_totalColumnFiltration K i) q.toNat := by
  have he : (a3sv_totalColumnIntervalHomologyIso K p q hpq hp i).hom.hom.range = ⊤ :=
    LinearMap.range_eq_top.mpr
      (a3sv_totalColumnIntervalHomologyIso K p q hpq hp i).toLinearEquiv.surjective
  have hq : (HomologicalComplex.homologyMap
      (a3sv_totalColumnFunctorObjIso K q.toNat).hom i).hom.range = ⊤ :=
    LinearMap.range_eq_top.mpr
      (HomologicalComplex.homologyMapIso
        (a3sv_totalColumnFunctorObjIso K q.toNat) i).toLinearEquiv.surjective
  have h := congrArg (fun f => f.hom.range)
    (a3sv_totalColumnIntervalTotalHomologyIso_naturality K m hK p q r hpq hqr hp hmr i)
  rw [← a3sv_totalColumn_homologyMap_range K q.toNat i]
  simpa only [ModuleCat.hom_comp, LinearMap.range_comp, he, hq, Submodule.map_top] using h

open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: the image inside a degreewise exhaustive interval
is the induced filtration on total homology. -/
theorem a3sv_totalColumnIntervalDegree_range {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (p q r : ℤ) (hpq : p ≤ q) (hqr : q ≤ r) (hp : p ≤ 0)
    (i : ℕ) (hir : i + 1 < r.toNat) :
    (((a3sv_totalColumnSpectralObject K).H (-(i : ℤ))).map
      (twoδ₂Toδ₁ (homOfLE hpq) (homOfLE hqr)
        (homOfLE (hpq.trans hqr)) rfl)).hom.range.map
        (a3sv_totalColumnIntervalDegreeHomologyIso K p r
          (hpq.trans hqr) hp i hir).hom.hom =
    a3sv_homologyFiltration (HomologicalComplex₂.total K (ComplexShape.down ℕ))
      i (a3sv_totalColumnFiltration K i) q.toNat := by
  have he : (a3sv_totalColumnIntervalHomologyIso K p q hpq hp i).hom.hom.range = ⊤ :=
    LinearMap.range_eq_top.mpr
      (a3sv_totalColumnIntervalHomologyIso K p q hpq hp i).toLinearEquiv.surjective
  have hq : (HomologicalComplex.homologyMap
      (a3sv_totalColumnFunctorObjIso K q.toNat).hom i).hom.range = ⊤ :=
    LinearMap.range_eq_top.mpr
      (HomologicalComplex.homologyMapIso
        (a3sv_totalColumnFunctorObjIso K q.toNat) i).toLinearEquiv.surjective
  have h := congrArg (fun f => f.hom.range)
    (a3sv_totalColumnIntervalDegreeHomologyIso_naturality
      K p q r hpq hqr hp i hir)
  rw [← a3sv_totalColumn_homologyMap_range K q.toNat i]
  simpa only [ModuleCat.hom_comp, LinearMap.range_comp, he, hq,
    Submodule.map_top] using h

/-- IntersectionProductSV: an ambient linear equivalence transports quotients of submodules by their intersections with another submodule. -/
def a3sv_subquotientEquiv {B : Type u} [CommRing B]
    {M N : Type u} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (e : M ≃ₗ[B] N) (S T : Submodule B M) (S' T' : Submodule B N)
    (hS : S.map e.toLinearMap = S') (hT : T.map e.toLinearMap = T') :
    (T ⧸ S.comap T.subtype) ≃ₗ[B] (T' ⧸ S'.comap T'.subtype) := by
  let eT := e.ofSubmodules T T' hT
  apply Submodule.Quotient.equiv _ _ eT
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change e (y : M) ∈ S'
    rw [← hS]
    exact ⟨y, hy, rfl⟩
  · intro hx
    refine ⟨eT.symm x, ?_, eT.apply_symm_apply x⟩
    change ((eT.symm x : T) : M) ∈ S
    change (x : N) ∈ S' at hx
    rw [← hS] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have he : e ((eT.symm x : T) : M) = (x : N) :=
      congrArg Subtype.val (eT.apply_symm_apply x)
    rw [e.injective (he.trans hxy.symm)]
    exact hy

/-- IntersectionProductSV: a commutative square with invertible vertical maps transports the image submodule. -/
theorem a3sv_range_map_of_iso_square {B : Type u} [CommRing B]
    {M N M' N' : ModuleCat.{u} B} (f : M ⟶ N) (g : M' ⟶ N')
    (eM : M ≅ M') (eN : N ≅ N') (h : f ≫ eN.hom = eM.hom ≫ g) :
    f.hom.range.map eN.hom.hom = g.hom.range := by
  have he : eM.hom.hom.range = ⊤ :=
    LinearMap.range_eq_top.mpr eM.toLinearEquiv.surjective
  have hr := congrArg (fun k => k.hom.range) h
  simpa only [ModuleCat.hom_comp, LinearMap.range_comp, he, Submodule.map_top] using hr

/-- IntersectionProductSV: isomorphic diagrams of two linear maps have isomorphic image subquotients. -/
def a3sv_imageSubquotientIso {B : Type u} [CommRing B]
    {L M N L' M' N' : ModuleCat.{u} B}
    (a : L ⟶ M) (b : M ⟶ N) (a' : L' ⟶ M') (b' : M' ⟶ N')
    (eL : L ≅ L') (eM : M ≅ M') (eN : N ≅ N')
    (ha : a ≫ eM.hom = eL.hom ≫ a') (hb : b ≫ eN.hom = eM.hom ≫ b') :
    ModuleCat.of B (b.hom.range ⧸ (a.hom.range.map b.hom).comap b.hom.range.subtype) ≅
      ModuleCat.of B (b'.hom.range ⧸ (a'.hom.range.map b'.hom).comap b'.hom.range.subtype) := by
  have hab : (a ≫ b) ≫ eN.hom = eL.hom ≫ (a' ≫ b') := by
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]
  have hS : (a.hom.range.map b.hom).map eN.hom.hom = a'.hom.range.map b'.hom := by
    simpa only [ModuleCat.hom_comp, LinearMap.range_comp] using
      a3sv_range_map_of_iso_square (a ≫ b) (a' ≫ b') eL eN hab
  exact (a3sv_subquotientEquiv eN.toLinearEquiv
    (a.hom.range.map b.hom) b.hom.range
    (a'.hom.range.map b'.hom) b'.hom.range hS
    (a3sv_range_map_of_iso_square b b' eM eN hb)).toModuleIso

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: a column spectral page beyond both filtration endpoints is a successive quotient of total homology. -/
def a3sv_totalColumnStablePageIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (m : ℕ) (hK : ∀ a, m < a → IsZero (K.X a))
    (r : ℤ) (hr : 1 ≤ r) (p i : ℕ)
    (hp : (p : ℤ) - r + 1 ≤ 0) (hmr : m < ((p : ℤ) + r).toNat) :
    ((a3sv_totalColumnSpectralSequence K).page r hr).X ((p : ℤ), (i : ℤ) - p) ≅
      a3sv_filteredHomologyPiece (HomologicalComplex₂.total K (ComplexShape.down ℕ))
        i (a3sv_totalColumnFiltration K i) p := by
  let S := a3sv_totalColumnSpectralObject K
  let t : ℤ := (p : ℤ) - r + 1
  let f : t ⟶ (p : ℤ) := homOfLE (by dsimp [t]; omega)
  let g : (p : ℤ) ⟶ (p : ℤ) + 1 := homOfLE (by omega)
  let h : (p : ℤ) + 1 ⟶ (p : ℤ) + r := homOfLE (by omega)
  let a := (S.H (-(i : ℤ))).map (twoδ₂Toδ₁ f g (f ≫ g) rfl)
  let b := (S.H (-(i : ℤ))).map (twoδ₂Toδ₁ (f ≫ g) h ((f ≫ g) ≫ h) rfl)
  let c := (S.H (-(i : ℤ))).map (twoδ₂Toδ₁ f (g ≫ h) (f ≫ g ≫ h) rfl)
  let T := HomologicalComplex₂.total K (ComplexShape.down ℕ)
  let H := a3sv_homologyFiltration T i (a3sv_totalColumnFiltration K i)
  let e := a3sv_totalColumnIntervalTotalHomologyIso K m hK t ((p : ℤ) + r)
    (by dsimp [t]; omega) hp hmr i
  have epage : ((a3sv_totalColumnSpectralSequence K).page r hr).X
      ((p : ℤ), (i : ℤ) - p) ≅
      ModuleCat.of B (b.hom.range ⧸ (a.hom.range.map b.hom).comap b.hom.range.subtype) := by
    have hn : -(p : ℤ) - ((i : ℤ) - p) = -(i : ℤ) := by omega
    have ee := a3sv_totalColumnPageImageIso K r hr (p : ℤ) ((i : ℤ) - p)
    dsimp only at ee
    rw [hn] at ee
    exact ee
  have hb : b.hom.range.map e.hom.hom = H (p + 1) := by
    have hn : ((p : ℤ) + 1).toNat = p + 1 := by omega
    have hh := a3sv_totalColumnInterval_range K m hK t ((p : ℤ) + 1)
      ((p : ℤ) + r) (by dsimp [t]; omega) (by omega) hp hmr i
    rw [hn] at hh
    exact hh
  have hc : c.hom.range.map e.hom.hom = H p := by
    have hh := a3sv_totalColumnInterval_range K m hK t (p : ℤ)
      ((p : ℤ) + r) (by dsimp [t]; omega) (by omega) hp hmr i
    rw [Int.toNat_natCast] at hh
    exact hh
  have hab : a ≫ b = c := by
    dsimp only [a, b, c]
    rw [← Functor.map_comp]
    congr 1
  have hs : (a.hom.range.map b.hom).map e.hom.hom = H p := by
    rw [← LinearMap.range_comp, ← ModuleCat.hom_comp, hab]
    exact hc
  refine epage ≪≫ (a3sv_subquotientEquiv e.toLinearEquiv
    (a.hom.range.map b.hom) b.hom.range (H p) (H (p + 1)) hs hb).toModuleIso ≪≫ ?_
  have ee := (a3sv_filteredHomologyPieceIso T i (a3sv_totalColumnFiltration K i) p).symm
  rw [Submodule.range_inclusion] at ee
  exact ee

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.ComposableArrows in
/-- IntersectionProductSV: a column page whose defining interval exhausts one
total degree is the corresponding filtered homology piece. -/
def a3sv_totalColumnStablePageDegreeIso {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (r : ℤ) (hr : 1 ≤ r) (p i : ℕ)
    (hp : (p : ℤ) - r + 1 ≤ 0)
    (hir : i + 1 < ((p : ℤ) + r).toNat) :
    ((a3sv_totalColumnSpectralSequence K).page r hr).X
        ((p : ℤ), (i : ℤ) - p) ≅
      a3sv_filteredHomologyPiece (HomologicalComplex₂.total K
        (ComplexShape.down ℕ)) i (a3sv_totalColumnFiltration K i) p := by
  let S := a3sv_totalColumnSpectralObject K
  let t : ℤ := (p : ℤ) - r + 1
  let f : t ⟶ (p : ℤ) := homOfLE (by dsimp [t]; omega)
  let g : (p : ℤ) ⟶ (p : ℤ) + 1 := homOfLE (by omega)
  let h : (p : ℤ) + 1 ⟶ (p : ℤ) + r := homOfLE (by omega)
  let a := (S.H (-(i : ℤ))).map (twoδ₂Toδ₁ f g (f ≫ g) rfl)
  let b := (S.H (-(i : ℤ))).map
    (twoδ₂Toδ₁ (f ≫ g) h ((f ≫ g) ≫ h) rfl)
  let c := (S.H (-(i : ℤ))).map
    (twoδ₂Toδ₁ f (g ≫ h) (f ≫ g ≫ h) rfl)
  let T := HomologicalComplex₂.total K (ComplexShape.down ℕ)
  let H := a3sv_homologyFiltration T i (a3sv_totalColumnFiltration K i)
  let e := a3sv_totalColumnIntervalDegreeHomologyIso K t ((p : ℤ) + r)
    (by dsimp [t]; omega) hp i hir
  have epage : ((a3sv_totalColumnSpectralSequence K).page r hr).X
      ((p : ℤ), (i : ℤ) - p) ≅
      ModuleCat.of B
        (b.hom.range ⧸ (a.hom.range.map b.hom).comap b.hom.range.subtype) := by
    have hn : -(p : ℤ) - ((i : ℤ) - p) = -(i : ℤ) := by omega
    have ee := a3sv_totalColumnPageImageIso K r hr (p : ℤ) ((i : ℤ) - p)
    dsimp only at ee
    rw [hn] at ee
    exact ee
  have hb : b.hom.range.map e.hom.hom = H (p + 1) := by
    have hn : ((p : ℤ) + 1).toNat = p + 1 := by omega
    have hh := a3sv_totalColumnIntervalDegree_range K t ((p : ℤ) + 1)
      ((p : ℤ) + r) (by dsimp [t]; omega) (by omega) hp i hir
    rw [hn] at hh
    exact hh
  have hc : c.hom.range.map e.hom.hom = H p := by
    have hh := a3sv_totalColumnIntervalDegree_range K t (p : ℤ)
      ((p : ℤ) + r) (by dsimp [t]; omega) (by omega) hp i hir
    rw [Int.toNat_natCast] at hh
    exact hh
  have hab : a ≫ b = c := by
    dsimp only [a, b, c]
    rw [← Functor.map_comp]
    congr 1
  have hs : (a.hom.range.map b.hom).map e.hom.hom = H p := by
    rw [← LinearMap.range_comp, ← ModuleCat.hom_comp, hab]
    exact hc
  refine epage ≪≫ (a3sv_subquotientEquiv e.toLinearEquiv
    (a.hom.range.map b.hom) b.hom.range (H p) (H (p + 1)) hs hb).toModuleIso ≪≫ ?_
  have ee := (a3sv_filteredHomologyPieceIso T i
    (a3sv_totalColumnFiltration K i) p).symm
  rw [Submodule.range_inclusion] at ee
  exact ee

/-- IntersectionProductSV: a finite-length stable column page computes the Euler characteristic of total homology. -/
theorem a3sv_totalEuler_eq_stablePage {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (m n : ℕ) (hK : ∀ a, m < a → IsZero (K.X a))
    (r : ℤ) (hr : 1 ≤ r) (hnr : (n : ℤ) < r) (hmr : (m : ℤ) < r)
    (hfinite : ∀ i ≤ n, ∀ p < i + 1, Module.length B
      (((a3sv_totalColumnSpectralSequence K).page r hr).X ((p : ℤ), (i : ℤ) - p)) ≠ ⊤) :
    a3i_complexEuler n (HomologicalComplex₂.total K (ComplexShape.down ℕ)) =
      ∑ i ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (i + 1),
        (-1 : ℤ) ^ i * ((Module.length B
          (((a3sv_totalColumnSpectralSequence K).page r hr).X
            ((p : ℤ), (i : ℤ) - p))).toNat : ℤ) := by
  have he (i p : ℕ) (hi : i ≤ n) (hp : p < i + 1) :
      Module.length B (((a3sv_totalColumnSpectralSequence K).page r hr).X
        ((p : ℤ), (i : ℤ) - p)) =
      Module.length B (a3sv_filteredHomologyPiece
        (HomologicalComplex₂.total K (ComplexShape.down ℕ)) i
        (a3sv_totalColumnFiltration K i) p) :=
    (a3sv_totalColumnStablePageIso K m hK r hr p i (by omega) (by omega)).toLinearEquiv.length_eq
  rw [a3sv_totalEuler_eq_filteredPieces K n (fun i hi p hp => by
    rw [← he i p hi hp]
    exact hfinite i hi p hp)]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro p hp
  rw [he i p (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi)
    (Finset.mem_range.mp hp)]

/-- IntersectionProductSV: a degreewise stable finite-length column page
computes the Euler characteristic of total homology in a bounded degree range. -/
theorem a3sv_totalEuler_eq_stablePage_degreewise {B : Type u} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{u} B) ℕ) ℕ)
    (n : ℕ) (r : ℤ) (hr : 1 ≤ r) (hnr : (n : ℤ) + 1 < r)
    (hfinite : ∀ i ≤ n, ∀ p < i + 1, Module.length B
      (((a3sv_totalColumnSpectralSequence K).page r hr).X
        ((p : ℤ), (i : ℤ) - p)) ≠ ⊤) :
    a3i_complexEuler n (HomologicalComplex₂.total K (ComplexShape.down ℕ)) =
      ∑ i ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (i + 1),
        (-1 : ℤ) ^ i * ((Module.length B
          (((a3sv_totalColumnSpectralSequence K).page r hr).X
            ((p : ℤ), (i : ℤ) - p))).toNat : ℤ) := by
  have he (i p : ℕ) (hi : i ≤ n) (hp : p < i + 1) :
      Module.length B (((a3sv_totalColumnSpectralSequence K).page r hr).X
        ((p : ℤ), (i : ℤ) - p)) =
      Module.length B (a3sv_filteredHomologyPiece
        (HomologicalComplex₂.total K (ComplexShape.down ℕ)) i
        (a3sv_totalColumnFiltration K i) p) :=
    (a3sv_totalColumnStablePageDegreeIso K r hr p i
      (by omega) (by omega)).toLinearEquiv.length_eq
  rw [a3sv_totalEuler_eq_filteredPieces K n (fun i hi p hp => by
    rw [← he i p hi hp]
    exact hfinite i hi p hp)]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro p hp
  rw [he i p (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi)
    (Finset.mem_range.mp hp)]

/-- IntersectionProductSV: adjacent boundary contributions cancel in an
alternating sum, leaving only the upper boundary. -/
theorem a3sv_alternating_sum_terms (a h b : ℕ → ℤ) (n : ℕ)
    (h0 : a 0 = h 0 + b 0)
    (hs : ∀ i, i + 1 ≤ n → a (i + 1) = h (i + 1) + b (i + 1) + b i) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * a i) =
      (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * h i) + (-1) ^ n * b n := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    rw [Finset.sum_range_succ (n := n + 1), Finset.sum_range_succ (n := n + 1),
      ih (fun i hi => hs i (by omega)), hs n (by omega), pow_succ]
    ring

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: for a bounded complex of finite-length modules, the
Euler sum of homology equals the Euler sum of the terms. -/
theorem a3sv_complexEuler_eq_terms {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (n : ℕ)
    (hfinite : ∀ i ≤ n, Module.length B (C.X i) ≠ ⊤)
    (hbounded : IsZero (C.X (n + 1))) :
    a3i_complexEuler n C = ∑ i ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ i * ((Module.length B (C.X i)).toNat : ℤ) := by
  let b : ℕ → ℤ := fun i => ((Module.length B (C.d (i + 1) i).hom.range).toNat : ℤ)
  have hlen (i : ℕ) (hi : i ≤ n) :
      ((Module.length B (C.X i)).toNat : ℤ) =
        ((Module.length B (C.homology i)).toNat : ℤ) +
        ((Module.length B (C.sc i).f.hom.range).toNat : ℤ) +
        ((Module.length B (C.sc i).g.hom.range).toNat : ℤ) := by
    have he := a3sv_length_shortComplex (C.sc i)
    have hpair : Module.length B (C.sc i).homology +
        Module.length B (C.sc i).f.hom.range ≠ ⊤ := by
      intro h
      apply hfinite i hi
      exact he.trans (by rw [h, top_add])
    have hp := WithTop.add_ne_top.mp hpair
    have hn := a3s_toNat_add he (hfinite i hi)
    rw [ENat.toNat_add hp.1 hp.2] at hn
    push_cast at hn
    exact hn
  have he := a3sv_alternating_sum_terms
    (fun i => ((Module.length B (C.X i)).toNat : ℤ))
    (fun i => ((Module.length B (C.homology i)).toNat : ℤ)) b n ?_ ?_
  · have hz : C.d (n + 1) n = 0 := hbounded.eq_of_src _ _
    have hb : b n = 0 := by
      dsimp only [b]
      rw [hz]
      rw [ModuleCat.hom_zero, LinearMap.range_zero, Module.length_bot]
      rfl
    rw [hb, mul_zero, add_zero] at he
    exact he.symm
  · have h := hlen 0 (Nat.zero_le n)
    have hz : C.d 0 0 = 0 := C.shape _ _ (by simp)
    change ((Module.length B (C.X 0)).toNat : ℤ) =
      ((Module.length B (C.homology 0)).toNat : ℤ) +
      ((Module.length B (C.d ((ComplexShape.down ℕ).prev 0) 0).hom.range).toNat : ℤ) +
      ((Module.length B (C.d 0 ((ComplexShape.down ℕ).next 0)).hom.range).toNat : ℤ) at h
    rw [ChainComplex.prev, ChainComplex.next_nat_zero, hz] at h
    rw [ModuleCat.hom_zero, LinearMap.range_zero, Module.length_bot] at h
    simpa only [ENat.toNat_zero, Nat.cast_zero, add_zero, b] using h
  · intro i hi
    have h := hlen (i + 1) hi
    change ((Module.length B (C.X (i + 1))).toNat : ℤ) =
      ((Module.length B (C.homology (i + 1))).toNat : ℤ) +
      ((Module.length B (C.d ((ComplexShape.down ℕ).prev (i + 1)) (i + 1)).hom.range).toNat : ℤ) +
      ((Module.length B (C.d (i + 1) ((ComplexShape.down ℕ).next (i + 1))).hom.range).toNat : ℤ) at h
    rw [ChainComplex.prev, ChainComplex.next_nat_succ] at h
    exact h

/-- IntersectionProductSV: the homology pairing identity for a projective
resolution, with the Tor sum truncated above the regular local dimension. -/
theorem a3sv_tensor_euler_homology_resolution {B : Type} [CommRing B]
    [IsRegularLocalRing B] (M N : ModuleCat.{0} B) [Module.Finite B N]
    (Q : ProjectiveResolution M) (n m : ℕ) (hm : ringKrullDim B ≤ m) :
    a3i_complexEuler (n + m) (a3c_tensC N Q.complex) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * a3s_chi m (Q.complex.homology i) N := by
  rw [← a3i_tor_eq_euler N M Q (n + m), a3s_chi_symm (n + m) N M,
    ← a3w_chi_eq_of_le M N hm (show m ≤ n + m by omega)]
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul]
    exact (a3s_chi_congr (isoOfQuasiIsoAt Q.π 0 ≪≫
      HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 M) N m).symm
  · intro i hi hi0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    have : Subsingleton (Q.complex.homology (j + 1)) :=
      ModuleCat.isZero_iff_subsingleton.mp (Q.complex_exactAt_succ j).isZero_homology
    have hz : a3s_chi m (Q.complex.homology (j + 1)) N = 0 := by
      unfold a3s_chi
      apply Finset.sum_eq_zero
      intro k hk
      rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
        (a3c_isZero_tor_of_subsingleton _ N k))]
      simp
    rw [hz, mul_zero]
  · intro h
    exact (h (by simp)).elim

/-- IntersectionProductSV: additivity of the Tor pairing for finite modules when
the second factor is supported at the maximal ideal. -/
theorem a3sv_chi_ses_supported {B : Type} [CommRing B] [IsRegularLocalRing B]
    (S : ShortComplex (ModuleCat.{0} B)) (hS : S.ShortExact)
    [Module.Finite B S.X₁] [Module.Finite B S.X₂] [Module.Finite B S.X₃]
    (N : ModuleCat.{0} B) [Module.Finite B N] (m : ℕ) (hm : ringKrullDim B ≤ m)
    (hN : ∀ P : PrimeSpectrum B, Module.annihilator B N ≤ P.asIdeal →
      P = IsLocalRing.closedPoint B) :
    a3s_chi m S.X₂ N = a3s_chi m S.X₁ N + a3s_chi m S.X₃ N := by
  exact a3s_chi_ses S hS N m
    (fun i _ => a3s_length_tor_ne_top _ _ i fun P _ h => hN P h)
    (fun i _ => a3s_length_tor_ne_top _ _ i fun P _ h => hN P h)
    (fun i _ => a3s_length_tor_ne_top _ _ i fun P _ h => hN P h)
    (a3e_isZero_tor_regular _ _ (m + 1)
      (lt_of_le_of_lt hm (by exact_mod_cast Nat.lt_succ_self m)))

/-- IntersectionProductSV: kernel and image decomposition of the Tor pairing. -/
theorem a3sv_chi_ker_range {B : Type} [CommRing B] [IsRegularLocalRing B]
    {M L : ModuleCat.{0} B} [Module.Finite B M] (f : M →ₗ[B] L)
    (N : ModuleCat.{0} B) [Module.Finite B N] (m : ℕ) (hm : ringKrullDim B ≤ m)
    (hN : ∀ P : PrimeSpectrum B, Module.annihilator B N ≤ P.asIdeal →
      P = IsLocalRing.closedPoint B) :
    a3s_chi m M N = a3s_chi m (ModuleCat.of B f.ker) N +
      a3s_chi m (ModuleCat.of B f.range) N := by
  let : Module.Finite B (a3e_kerSES f.rangeRestrict).X₁ :=
    Module.Finite.of_injective f.rangeRestrict.ker.subtype (Submodule.injective_subtype _)
  let : Module.Finite B (a3e_kerSES f.rangeRestrict).X₂ := ‹Module.Finite B M›
  let : Module.Finite B (a3e_kerSES f.rangeRestrict).X₃ :=
    Module.Finite.of_surjective f.rangeRestrict f.surjective_rangeRestrict
  have h := a3sv_chi_ses_supported (a3e_kerSES f.rangeRestrict)
    (a3e_kerSES_shortExact _ f.surjective_rangeRestrict) N m hm hN
  change a3s_chi m M N = a3s_chi m (ModuleCat.of B f.rangeRestrict.ker) N +
    a3s_chi m (ModuleCat.of B f.range) N at h
  rw [LinearMap.ker_rangeRestrict] at h
  exact h

/-- IntersectionProductSV: decomposition of the Tor pairing into homology and
adjacent images for finite modules. -/
theorem a3sv_chi_shortComplex {B : Type} [CommRing B] [IsRegularLocalRing B]
    (S : ShortComplex (ModuleCat.{0} B)) [Module.Finite B S.X₂]
    (N : ModuleCat.{0} B) [Module.Finite B N] (m : ℕ) (hm : ringKrullDim B ≤ m)
    (hN : ∀ P : PrimeSpectrum B, Module.annihilator B N ≤ P.asIdeal →
      P = IsLocalRing.closedPoint B) :
    a3s_chi m S.X₂ N = a3s_chi m S.homology N +
      a3s_chi m (ModuleCat.of B S.f.hom.range) N +
      a3s_chi m (ModuleCat.of B S.g.hom.range) N := by
  let : Module.Finite B S.g.hom.ker := Module.Finite.of_injective
    S.g.hom.ker.subtype (Submodule.injective_subtype _)
  let D := S.moduleCatToCycles.range
  let T := ModuleCat.shortComplexOfCompEqZero D.subtype D.mkQ
    (LinearMap.exact_subtype_mkQ D).linearMap_comp_eq_zero
  have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T
    (LinearMap.exact_subtype_mkQ D) D.injective_subtype D.mkQ_surjective
  let : Module.Finite B T.X₁ := Module.Finite.of_injective
    D.subtype D.injective_subtype
  let : Module.Finite B T.X₂ := ‹Module.Finite B S.g.hom.ker›
  let : Module.Finite B T.X₃ := Module.Finite.of_surjective D.mkQ D.mkQ_surjective
  have he := a3sv_chi_ses_supported T hT N m hm hN
  change a3s_chi m (ModuleCat.of B S.g.hom.ker) N =
    a3s_chi m (ModuleCat.of B S.moduleCatToCycles.range) N +
    a3s_chi m (ModuleCat.of B (S.g.hom.ker ⧸ S.moduleCatToCycles.range)) N at he
  have hr : a3s_chi m (ModuleCat.of B S.moduleCatToCycles.range) N =
      a3s_chi m (ModuleCat.of B S.f.hom.range) N := by
    have hk : S.moduleCatToCycles.ker = S.f.hom.ker := by
      ext x
      change S.moduleCatToCycles x = 0 ↔ S.f.hom x = 0
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have h₁ := a3s_chi_congr S.moduleCatToCycles.quotKerEquivRange.toModuleIso N m
    have h₂ := a3s_chi_congr S.f.hom.quotKerEquivRange.toModuleIso N m
    rw [hk] at h₁
    exact h₁.symm.trans h₂
  have hh := a3s_chi_congr S.moduleCatHomologyIso N m
  change a3s_chi m S.homology N =
    a3s_chi m (ModuleCat.of B (S.g.hom.ker ⧸ S.moduleCatToCycles.range)) N at hh
  rw [a3sv_chi_ker_range S.g.hom N m hm hN, he, hr, ← hh]
  ring


/-- IntersectionProductSV: a zero module has zero Tor Euler pairing. -/
theorem a3sv_chi_isZero {B : Type} [CommRing B]
    (M N : ModuleCat.{0} B) (hM : IsZero M) (m : ℕ) : a3s_chi m M N = 0 := by
  let : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp hM
  unfold a3s_chi
  apply Finset.sum_eq_zero
  intro i hi
  rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
    (a3c_isZero_tor_of_subsingleton M N i))]
  simp


/-- IntersectionProductSV: the alternating Tor pairing of a bounded finite complex
is unchanged on passing to homology when the second module has maximal support. -/
theorem a3sv_chi_homology_eq_terms {B : Type} [CommRing B] [IsRegularLocalRing B]
    (C : ChainComplex (ModuleCat.{0} B) ℕ) (N : ModuleCat.{0} B) [Module.Finite B N]
    (n m : ℕ) (hm : ringKrullDim B ≤ m)
    (hfinite : ∀ i, Module.Finite B (C.X i)) (hbounded : IsZero (C.X (n + 1)))
    (hN : ∀ P : PrimeSpectrum B, Module.annihilator B N ≤ P.asIdeal →
      P = IsLocalRing.closedPoint B) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * a3s_chi m (C.homology i) N) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * a3s_chi m (C.X i) N := by
  let b : ℕ → ℤ := fun i => a3s_chi m (ModuleCat.of B (C.d (i + 1) i).hom.range) N
  have hterm (i : ℕ) := by
    let : Module.Finite B (C.sc i).X₂ := hfinite i
    exact a3sv_chi_shortComplex (C.sc i) N m hm hN
  have he := a3sv_alternating_sum_terms
    (fun i => a3s_chi m (C.X i) N) (fun i => a3s_chi m (C.homology i) N) b n ?_ ?_
  · have hz : C.d (n + 1) n = 0 := hbounded.eq_of_src _ _
    have hb : b n = 0 := by
      dsimp only [b]
      rw [hz, ModuleCat.hom_zero, LinearMap.range_zero]
      exact a3sv_chi_isZero _ N (ModuleCat.isZero_iff_subsingleton.mpr inferInstance) m
    rw [hb, mul_zero, add_zero] at he
    exact he.symm
  · have h := hterm 0
    have hz : C.d 0 0 = 0 := C.shape _ _ (by simp)
    change a3s_chi m (C.X 0) N = a3s_chi m (C.homology 0) N +
      a3s_chi m (ModuleCat.of B (C.d ((ComplexShape.down ℕ).prev 0) 0).hom.range) N +
      a3s_chi m (ModuleCat.of B (C.d 0 ((ComplexShape.down ℕ).next 0)).hom.range) N at h
    rw [ChainComplex.prev, ChainComplex.next_nat_zero, hz,
      ModuleCat.hom_zero, LinearMap.range_zero,
      a3sv_chi_isZero (ModuleCat.of B (⊥ : Submodule B (C.X 0))) N
        (ModuleCat.isZero_iff_subsingleton.mpr inferInstance) m,
      add_zero] at h
    exact h
  · intro i hi
    have h := hterm (i + 1)
    change a3s_chi m (C.X (i + 1)) N = a3s_chi m (C.homology (i + 1)) N +
      a3s_chi m (ModuleCat.of B
        (C.d ((ComplexShape.down ℕ).prev (i + 1)) (i + 1)).hom.range) N +
      a3s_chi m (ModuleCat.of B
        (C.d (i + 1) ((ComplexShape.down ℕ).next (i + 1))).hom.range) N at h
    rw [ChainComplex.prev, ChainComplex.next_nat_succ] at h
    exact h


/-- IntersectionProductSV: the tensor homology pairing for a bounded finite
projective complex and a module supported at the maximal ideal. -/
theorem a3sv_tensor_euler_homology_supported {B : Type} [CommRing B] [IsRegularLocalRing B]
    (C : ChainComplex (ModuleCat.{0} B) ℕ) (N : ModuleCat.{0} B) [Module.Finite B N]
    (n m : ℕ) (hm : ringKrullDim B ≤ m)
    (hproj : ∀ i, Projective (C.X i)) (hfinite : ∀ i, Module.Finite B (C.X i))
    (hbounded : ∀ i, n < i → IsZero (C.X i))
    (hN : ∀ P : PrimeSpectrum B, Module.annihilator B N ≤ P.asIdeal →
      P = IsLocalRing.closedPoint B) :
    a3i_complexEuler (n + m) (a3c_tensC N C) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * a3s_chi m (C.homology i) N := by
  rw [a3sv_complexEuler_eq_of_le (a3c_tensC N C) n (n + m) (by omega)
    (fun i hi => (MonoidalCategory.tensorLeft N).map_isZero (hbounded i hi)),
    a3sv_chi_homology_eq_terms C N n m hm hfinite (hbounded _ (by omega)) hN]
  rw [a3sv_complexEuler_eq_terms (a3c_tensC N C) n ?_
    ((MonoidalCategory.tensorLeft N).map_isZero (hbounded _ (by omega)))]
  · apply Finset.sum_congr rfl
    intro i hi
    let : Projective (C.X i) := hproj i
    let : Module.Projective B (C.X i) :=
      (IsProjective.iff_projective (R := B) (C.X i)).2 (hproj i)
    let : Module.Flat B (C.X i) := inferInstance
    rw [a3s_chi_symm, a3sv_chi_flat_right]
    congr 2
    exact congrArg ENat.toNat (TensorProduct.comm B N (C.X i)).length_eq
  · intro i hi
    let : Module.Finite B (C.X i) := hfinite i
    change Module.length B (MonoidalCategory.tensorObj N (C.X i) : ModuleCat B) ≠ ⊤
    rw [← (a3c_tor0Iso N (C.X i)).toLinearEquiv.length_eq]
    exact a3s_length_tor_ne_top N (C.X i) 0 fun P h _ => hN P h


open scoped ZeroObject in
/-- IntersectionProductSV: tensoring an acyclic complex of projective modules
with an arbitrary module preserves acyclicity. -/
theorem a3sv_tensor_exact_of_projective {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (N : ModuleCat.{u} B)
    (hproj : ∀ i, Projective (C.X i)) (hex : ∀ i, C.ExactAt i) (i : ℕ) :
    (a3c_tensC N C).ExactAt i := by
  let Q : ProjectiveResolution (0 : ModuleCat.{u} B) := {
    complex := C
    projective := hproj
    π := 0
    quasiIso := by
      rw [quasiIso_iff]
      intro j
      apply (quasiIsoAt_iff_exactAt _ j (hex j)).mpr
      exact HomologicalComplex.acyclic_of_isZero _
        ((ChainComplex.single₀ (ModuleCat.{u} B)).map_isZero (isZero_zero _)) j }
  have : Subsingleton (0 : ModuleCat.{u} B) :=
    ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
  have hz : IsZero (((Tor (ModuleCat.{u} B) i).obj N).obj (0 : ModuleCat.{u} B)) :=
    a3e_isZero_tor_symm _ _ i (a3c_isZero_tor_of_subsingleton _ N i)
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (IsZero.of_iso hz (a3c_torIso N 0 Q i).symm)

/-- IntersectionProductSV: after a flat scalar extension, vanishing of the
homology of a projective complex implies vanishing of its tensor homology. -/
theorem a3sv_tensor_homology_baseChange_isZero {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (C : ChainComplex (ModuleCat.{u} A) ℕ)
    (N : ModuleCat.{u} A) (hproj : ∀ i, Projective (C.X i))
    (hvan : ∀ i, IsZero ((ModuleCat.extendScalars.{u, u, u} f).obj (C.homology i)))
    (i : ℕ) :
    IsZero ((ModuleCat.extendScalars.{u, u, u} f).obj ((a3c_tensC N C).homology i)) := by
  let F := ModuleCat.extendScalars.{u, u, u} f
  have : F.PreservesHomology := a3q_extendScalars_preservesHomology f hf
  let D := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C
  have hp (j : ℕ) : Projective (D.X j) := by
    have := hproj j
    change Projective (F.obj (C.X j))
    infer_instance
  have he (j : ℕ) : D.ExactAt j := by
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    exact IsZero.of_iso (hvan j) ((C.sc j).mapHomologyIso F)
  have ht := (a3sv_tensor_exact_of_projective D (F.obj N) hp he i).isZero_homology
  exact IsZero.of_iso ht
    (((HomologicalComplex.homologyMapIso (a3q_tensCIso f N C) i) ≪≫
      ((a3c_tensC N C).sc i).mapHomologyIso F).symm)

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: localization by extension of scalars detects absence
from the support of a module. -/
theorem a3sv_notMem_support_iff_extendScalars_isZero {B : Type u} [CommRing B]
    (M : ModuleCat.{u} B) (P : PrimeSpectrum B) :
    P ∉ Module.support B M ↔
      IsZero ((ModuleCat.extendScalars.{u, u, u}
        (algebraMap B (Localization.AtPrime P.asIdeal))).obj M) := by
  rw [Module.notMem_support_iff, ModuleCat.isZero_iff_subsingleton]
  change Subsingleton (LocalizedModule P.asIdeal.primeCompl M) ↔
    Subsingleton (@TensorProduct B _ (Localization.AtPrime P.asIdeal) M _ _
      (Module.compHom (Localization.AtPrime P.asIdeal)
        (algebraMap B (Localization.AtPrime P.asIdeal))) _)
  have hm : Module.compHom (Localization.AtPrime P.asIdeal)
      (algebraMap B (Localization.AtPrime P.asIdeal)) =
      (inferInstance : Module B (Localization.AtPrime P.asIdeal)) := by
    apply Module.ext
    funext r x
    exact algebraMap_smul (Localization.AtPrime P.asIdeal) r x
  rw [hm]
  let e := IsLocalizedModule.iso P.asIdeal.primeCompl
    (TensorProduct.mk B (Localization.AtPrime P.asIdeal) M 1)
  constructor
  · intro h
    exact e.symm.injective.subsingleton
  · intro h
    exact e.injective.subsingleton

/-- IntersectionProductSV: a prime supporting tensor homology supports some
homology module of the original projective complex. -/
theorem a3sv_mem_support_tensor_homology {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (N : ModuleCat.{u} B)
    (hproj : ∀ i, Projective (C.X i)) (i : ℕ) (P : PrimeSpectrum B)
    (hP : P ∈ Module.support B ((a3c_tensC N C).homology i)) :
    ∃ j, P ∈ Module.support B (C.homology j) := by
  classical
  by_contra h
  have hvan (j : ℕ) : IsZero ((ModuleCat.extendScalars.{u, u, u}
      (algebraMap B (Localization.AtPrime P.asIdeal))).obj (C.homology j)) :=
    (a3sv_notMem_support_iff_extendScalars_isZero _ P).mp (fun hj => h ⟨j, hj⟩)
  have hz := a3sv_tensor_homology_baseChange_isZero
    (algebraMap B (Localization.AtPrime P.asIdeal))
    (RingHom.flat_algebraMap_iff.mpr inferInstance) C N hproj hvan i
  exact (a3sv_notMem_support_iff_extendScalars_isZero _ P).mpr hz hP

/-- IntersectionProductSV: a prime supporting tensor homology contains the
annihilator of the tensor factor. -/
theorem a3sv_annihilator_le_of_mem_support_tensor_homology {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (N : ModuleCat.{u} B)
    (i : ℕ) (P : PrimeSpectrum B)
    (hP : P ∈ Module.support B ((a3c_tensC N C).homology i)) :
    Module.annihilator B N ≤ P.asIdeal := by
  let D := a3c_tensC N C
  have hs : Module.support B (D.homology i) ⊆ Module.support B (D.X i) :=
    (Module.support_subset_of_surjective (D.homologyπ i).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)).trans
    (Module.support_subset_of_injective (D.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance))
  have ht : P ∈ Module.support B (((Tor (ModuleCat.{u} B) 0).obj N).obj (C.X i)) := by
    rw [(a3c_tor0Iso N (C.X i)).toLinearEquiv.support_eq]
    exact hs hP
  exact (a3s_annihilator_le_of_mem_support_tor N (C.X i) 0 P ht).1

/-- IntersectionProductSV: proper homology support gives finite length for each
homology module after tensoring a finite projective complex. -/
theorem a3sv_tensor_homology_length_ne_top {B : Type} [CommRing B]
    [IsNoetherianRing B] [IsLocalRing B]
    (C : ChainComplex (ModuleCat.{0} B) ℕ) (N : ModuleCat.{0} B) [Module.Finite B N]
    (hproj : ∀ i, Projective (C.X i)) (hfinite : ∀ i, Module.Finite B (C.X i))
    (hproper : ∀ i, ∀ P ∈ Module.support B (C.homology i),
      Module.annihilator B N ≤ P.asIdeal → P = IsLocalRing.closedPoint B)
    (i : ℕ) : Module.length B ((a3c_tensC N C).homology i) ≠ ⊤ := by
  have : Module.Finite B (C.X i) := hfinite i
  have : Module.Finite B ((a3c_tensC N C).X i) := by
    change Module.Finite B (TensorProduct B N (C.X i))
    infer_instance
  have := a3sv_finite_homology (a3c_tensC N C) i
  apply a3e_length_ne_top_of_support
  intro P hP
  obtain ⟨j, hj⟩ := a3sv_mem_support_tensor_homology C N hproj i P hP
  exact hproper j P hj (a3sv_annihilator_le_of_mem_support_tensor_homology C N i P hP)

/-- IntersectionProductSV: tensor Euler characteristics are additive on a short
exact sequence of finite modules meeting the homology support properly. -/
theorem a3sv_tensor_euler_ses {B : Type} [CommRing B]
    [IsNoetherianRing B] [IsLocalRing B]
    (C : ChainComplex (ModuleCat.{0} B) ℕ)
    (S : ShortComplex (ModuleCat.{0} B)) (hS : S.ShortExact)
    [Module.Finite B S.X₁] [Module.Finite B S.X₂] [Module.Finite B S.X₃]
    (n : ℕ) (hproj : ∀ i, Projective (C.X i))
    (hfinite : ∀ i, Module.Finite B (C.X i))
    (hbounded : IsZero (C.X (n + 1)))
    (hproper : ∀ i, ∀ P ∈ Module.support B (C.homology i),
      Module.annihilator B S.X₂ ≤ P.asIdeal → P = IsLocalRing.closedPoint B) :
    a3i_complexEuler n (a3c_tensC S.X₂ C) =
      a3i_complexEuler n (a3c_tensC S.X₁ C) +
        a3i_complexEuler n (a3c_tensC S.X₃ C) := by
  have hproper₁ : ∀ i, ∀ P ∈ Module.support B (C.homology i),
      Module.annihilator B S.X₁ ≤ P.asIdeal → P = IsLocalRing.closedPoint B := by
    intro i P hP hN
    apply hproper i P hP
    exact Module.annihilator_le_of_mem_support
      (Module.support_subset_of_injective S.f.hom
        ((ModuleCat.mono_iff_injective _).mp hS.mono_f)
          ((Module.mem_support_iff_of_finite).mpr hN))
  have hproper₃ : ∀ i, ∀ P ∈ Module.support B (C.homology i),
      Module.annihilator B S.X₃ ≤ P.asIdeal → P = IsLocalRing.closedPoint B := by
    intro i P hP hN
    apply hproper i P hP
    exact Module.annihilator_le_of_mem_support
      (Module.support_subset_of_surjective S.g.hom
        ((ModuleCat.epi_iff_surjective _).mp hS.epi_g)
          ((Module.mem_support_iff_of_finite).mpr hN))
  apply a3i_complex_euler (a3c_sesC S C) (a3c_sesC_shortExact S hS C hproj) n
  · exact fun i _ => a3sv_tensor_homology_length_ne_top C S.X₁ hproj hfinite hproper₁ i
  · exact fun i _ => a3sv_tensor_homology_length_ne_top C S.X₂ hproj hfinite hproper i
  · exact fun i _ => a3sv_tensor_homology_length_ne_top C S.X₃ hproj hfinite hproper₃ i
  · exact ((a3c_tensC S.X₃ C).sc (n + 1)).isZero_homology_of_isZero_X₂
      ((MonoidalCategory.tensorLeft S.X₃).map_isZero hbounded)

/-- IntersectionProductSV: an isomorphism of tensor factors preserves the tensor
Euler characteristic in every degree range. -/
theorem a3sv_tensor_euler_congr {B : Type u} [CommRing B]
    (C : ChainComplex (ModuleCat.{u} B) ℕ) {M N : ModuleCat.{u} B}
    (e : M ≅ N) (n : ℕ) :
    a3i_complexEuler n (a3c_tensC M C) = a3i_complexEuler n (a3c_tensC N C) := by
  let eC := (NatIso.mapHomologicalComplex
    ((MonoidalCategory.tensoringLeft (ModuleCat.{u} B)).mapIso e)
      (ComplexShape.down ℕ)).app C
  unfold a3i_complexEuler
  apply Finset.sum_congr rfl
  intro i hi
  rw [(HomologicalComplex.homologyMapIso eC i).toLinearEquiv.length_eq]

/-- IntersectionProductSV: prime filtration expresses a tensor Euler
characteristic as a finite sum of its values on prime quotients. -/
theorem a3sv_tensor_euler_prime_filtration {B : Type} [CommRing B]
    [IsNoetherianRing B] [IsLocalRing B]
    (C : ChainComplex (ModuleCat.{0} B) ℕ) (n : ℕ)
    (hproj : ∀ i, Projective (C.X i))
    (hfinite : ∀ i, Module.Finite B (C.X i))
    (hbounded : IsZero (C.X (n + 1)))
    (Z : Set (PrimeSpectrum B))
    (hfin : ∀ i, ∀ P ∈ Module.support B (C.homology i),
      P ∈ Z → P = IsLocalRing.closedPoint B)
    (N : Type) [AddCommGroup N] [Module B N] [Module.Finite B N]
    (hN : Module.support B N ⊆ Z) :
    ∃ L : List (PrimeSpectrum B), (∀ P ∈ L, P ∈ Z) ∧
      a3i_complexEuler n (a3c_tensC (ModuleCat.of B N) C) =
        (L.map (fun P => a3i_complexEuler n
          (a3c_tensC (ModuleCat.of B (B ⧸ P.asIdeal)) C))).sum := by
  revert hN
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime B
    (inferInstance : Module.Finite B N)
    (motive := fun X _ _ _ => Module.support B X ⊆ Z →
      ∃ L : List (PrimeSpectrum B), (∀ P ∈ L, P ∈ Z) ∧
        a3i_complexEuler n (a3c_tensC (ModuleCat.of B X) C) =
          (L.map (fun P => a3i_complexEuler n
            (a3c_tensC (ModuleCat.of B (B ⧸ P.asIdeal)) C))).sum) ?_ ?_ ?_
  · intro X _ _ _ _ hX
    refine ⟨[], by simp, ?_⟩
    simp only [List.map_nil, List.sum_nil]
    unfold a3i_complexEuler
    apply Finset.sum_eq_zero
    intro i hi
    have hzero : IsZero ((a3c_tensC (ModuleCat.of B X) C).X i) :=
      (MonoidalCategory.tensorRight (C.X i)).map_isZero
        (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)
    have hhom := ((a3c_tensC (ModuleCat.of B X) C).sc i).isZero_homology_of_isZero_X₂ hzero
    have hlen : Module.length B ((a3c_tensC (ModuleCat.of B X) C).homology i) = 0 :=
      Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hhom)
    rw [hlen]
    simp
  · intro X _ _ _ P e hX
    have hP : P ∈ Module.support B X := by
      rw [e.support_eq, Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
    refine ⟨[P], ?_, ?_⟩
    · simpa only [List.mem_singleton, forall_eq] using hX hP
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
        a3sv_tensor_euler_congr C e.toModuleIso n
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ hX
    obtain ⟨L₁, hL₁, e₁⟩ := h₁ ((Module.support_subset_of_injective f hf).trans hX)
    obtain ⟨L₃, hL₃, e₃⟩ := h₃ ((Module.support_subset_of_surjective g hg).trans hX)
    let S : ShortComplex (ModuleCat.{0} B) :=
      ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (by ext x; exact hfg.apply_apply_eq_zero x)
    have hS : S.ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hfg
        mono_f := (ModuleCat.mono_iff_injective _).2 hf
        epi_g := (ModuleCat.epi_iff_surjective _).2 hg }
    refine ⟨L₁ ++ L₃, ?_, ?_⟩
    · intro P hP
      exact (List.mem_append.mp hP).elim (hL₁ P) (hL₃ P)
    · rw [List.map_append, List.sum_append, ← e₁, ← e₃]
      exact a3sv_tensor_euler_ses C S hS n hproj hfinite hbounded
        (fun i P hi hP => hfin i P hi (hX ((Module.mem_support_iff_of_finite).mpr hP)))

/-- IntersectionProductSV: the homology Tor pairing is additive in a short exact
sequence whose middle module meets the homology support properly. -/
theorem a3sv_homology_chi_ses {B : Type} [CommRing B] [IsRegularLocalRing B]
    (C : ChainComplex (ModuleCat.{0} B) ℕ)
    (S : ShortComplex (ModuleCat.{0} B)) (hS : S.ShortExact)
    [Module.Finite B S.X₁] [Module.Finite B S.X₂] [Module.Finite B S.X₃]
    (m : ℕ) (hm : ringKrullDim B ≤ m)
    (hfinite : ∀ i, Module.Finite B (C.X i))
    (hproper : ∀ i, ∀ P ∈ Module.support B (C.homology i),
      Module.annihilator B S.X₂ ≤ P.asIdeal → P = IsLocalRing.closedPoint B)
    (i : ℕ) :
    a3s_chi m (C.homology i) S.X₂ =
      a3s_chi m (C.homology i) S.X₁ + a3s_chi m (C.homology i) S.X₃ := by
  let : Module.Finite B (C.X i) := hfinite i
  let : Module.Finite B (C.homology i) := a3sv_finite_homology C i
  have hlen (M : ModuleCat.{0} B) [Module.Finite B M]
      (hM : Module.support B M ⊆ Module.support B S.X₂) (j : ℕ) :
      Module.length B (((Tor (ModuleCat.{0} B) j).obj M).obj (C.homology i)) ≠ ⊤ := by
    apply a3s_length_tor_ne_top M (C.homology i) j
    intro P hP hH
    exact hproper i P ((Module.mem_support_iff_of_finite).mpr hH)
      (Module.annihilator_le_of_mem_support (hM ((Module.mem_support_iff_of_finite).mpr hP)))
  rw [a3s_chi_symm m (C.homology i) S.X₂,
    a3s_chi_symm m (C.homology i) S.X₁,
    a3s_chi_symm m (C.homology i) S.X₃]
  exact a3s_chi_ses S hS (C.homology i) m
    (fun j _ => hlen S.X₁ (Module.support_subset_of_injective S.f.hom
      ((ModuleCat.mono_iff_injective _).mp hS.mono_f)) j)
    (fun j _ => hlen S.X₂ subset_rfl j)
    (fun j _ => hlen S.X₃ (Module.support_subset_of_surjective S.g.hom
      ((ModuleCat.epi_iff_surjective _).mp hS.epi_g)) j)
    (a3e_isZero_tor_regular _ _ (m + 1)
      (lt_of_le_of_lt hm (by exact_mod_cast Nat.lt_succ_self m)))

/-- IntersectionProductSV: one prime filtration simultaneously expands the tensor
Euler characteristic and every homology Tor pairing. -/
theorem a3sv_tensor_and_tor_prime_filtration {B : Type} [CommRing B]
    [IsRegularLocalRing B]
    (C : ChainComplex (ModuleCat.{0} B) ℕ) (n m : ℕ)
    (hm : ringKrullDim B ≤ m)
    (hproj : ∀ i, Projective (C.X i))
    (hfinite : ∀ i, Module.Finite B (C.X i))
    (hbounded : IsZero (C.X (n + 1)))
    (Z : Set (PrimeSpectrum B))
    (hfin : ∀ i, ∀ P ∈ Module.support B (C.homology i),
      P ∈ Z → P = IsLocalRing.closedPoint B)
    (N : Type) [AddCommGroup N] [Module B N] [Module.Finite B N]
    (hN : Module.support B N ⊆ Z) :
    ∃ L : List (PrimeSpectrum B), (∀ P ∈ L, P ∈ Z) ∧
      a3i_complexEuler n (a3c_tensC (ModuleCat.of B N) C) =
        (L.map (fun P => a3i_complexEuler n
          (a3c_tensC (ModuleCat.of B (B ⧸ P.asIdeal)) C))).sum ∧
      ∀ i, a3s_chi m (C.homology i) (ModuleCat.of B N) =
        (L.map (fun P => a3s_chi m (C.homology i)
          (ModuleCat.of B (B ⧸ P.asIdeal)))).sum := by
  revert hN
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime B
    (inferInstance : Module.Finite B N)
    (motive := fun X _ _ _ => Module.support B X ⊆ Z →
      ∃ L : List (PrimeSpectrum B), (∀ P ∈ L, P ∈ Z) ∧
        a3i_complexEuler n (a3c_tensC (ModuleCat.of B X) C) =
          (L.map (fun P => a3i_complexEuler n
            (a3c_tensC (ModuleCat.of B (B ⧸ P.asIdeal)) C))).sum ∧
        ∀ i, a3s_chi m (C.homology i) (ModuleCat.of B X) =
          (L.map (fun P => a3s_chi m (C.homology i)
            (ModuleCat.of B (B ⧸ P.asIdeal)))).sum) ?_ ?_ ?_
  · intro X _ _ _ _ hX
    refine ⟨[], by simp, ?_, ?_⟩
    · simp only [List.map_nil, List.sum_nil]
      unfold a3i_complexEuler
      apply Finset.sum_eq_zero
      intro i hi
      have hzero : IsZero ((a3c_tensC (ModuleCat.of B X) C).X i) :=
        (MonoidalCategory.tensorRight (C.X i)).map_isZero
          (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)
      have hhom := ((a3c_tensC (ModuleCat.of B X) C).sc i).isZero_homology_of_isZero_X₂ hzero
      have hlen : Module.length B ((a3c_tensC (ModuleCat.of B X) C).homology i) = 0 :=
        Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hhom)
      rw [hlen]
      simp
    · intro i
      simp only [List.map_nil, List.sum_nil]
      rw [a3s_chi_symm]
      exact a3sv_chi_isZero _ _ (ModuleCat.isZero_iff_subsingleton.mpr inferInstance) m
  · intro X _ _ _ P e hX
    have hP : P ∈ Module.support B X := by
      rw [e.support_eq, Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
    refine ⟨[P], ?_, ?_, ?_⟩
    · simpa only [List.mem_singleton, forall_eq] using hX hP
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
        a3sv_tensor_euler_congr C e.toModuleIso n
    · intro i
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [a3s_chi_symm m (C.homology i) (ModuleCat.of B X),
        a3s_chi_symm m (C.homology i) (ModuleCat.of B (B ⧸ P.asIdeal))]
      exact a3s_chi_congr e.toModuleIso (C.homology i) m
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ hX
    obtain ⟨L₁, hL₁, e₁, t₁⟩ := h₁ ((Module.support_subset_of_injective f hf).trans hX)
    obtain ⟨L₃, hL₃, e₃, t₃⟩ := h₃ ((Module.support_subset_of_surjective g hg).trans hX)
    let S : ShortComplex (ModuleCat.{0} B) :=
      ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (by ext x; exact hfg.apply_apply_eq_zero x)
    have hS : S.ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hfg
        mono_f := (ModuleCat.mono_iff_injective _).2 hf
        epi_g := (ModuleCat.epi_iff_surjective _).2 hg }
    refine ⟨L₁ ++ L₃, ?_, ?_, ?_⟩
    · intro P hP
      exact (List.mem_append.mp hP).elim (hL₁ P) (hL₃ P)
    · rw [List.map_append, List.sum_append, ← e₁, ← e₃]
      exact a3sv_tensor_euler_ses C S hS n hproj hfinite hbounded
        (fun i P hi hP => hfin i P hi (hX ((Module.mem_support_iff_of_finite).mpr hP)))

    · intro i
      rw [List.map_append, List.sum_append, ← t₁ i, ← t₃ i]
      exact a3sv_homology_chi_ses C S hS m hm hfinite
        (fun j P hj hP => hfin j P hj (hX ((Module.mem_support_iff_of_finite).mpr hP))) i

/-- IntersectionProductSV: the bicomplex obtained by tensoring two module complexes. -/
def a3sv_tensorBicomplex {B : Type u} [CommRing B]
    (Q C : ChainComplex (ModuleCat.{u} B) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} B) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (((MonoidalCategory.curriedTensor (ModuleCat.{u} B)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj Q).obj C

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: taking vertical homology of a tensor bicomplex
with flat horizontal terms gives the tensor complex of the homology module. -/
def a3sv_tensorBicomplexHomologyIso {B : Type u} [CommRing B]
    (Q C : ChainComplex (ModuleCat.{u} B) ℕ)
    (hflat : ∀ j, Module.Flat B (Q.X j)) (i : ℕ) :
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) i).mapHomologicalComplex (ComplexShape.down ℕ)).obj (a3sv_tensorBicomplex Q C) ≅
      ((MonoidalCategory.tensorRight (C.homology i)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj Q := by
  letI (j : ℕ) : Module.Flat B (Q.X j) := hflat j
  refine HomologicalComplex.Hom.isoOfComponents
    (fun j => a3sv_tensorHomologyIso C (Q.X j) i) ?_
  intro j k hjk
  have h := NatTrans.app_homology
    ((MonoidalCategory.curriedTensor (ModuleCat.{u} B)).map (Q.d j k)) (C.sc i)
  change (a3sv_tensorHomologyIso C (Q.X j) i).hom ≫
    ((MonoidalCategory.curriedTensor (ModuleCat.{u} B)).map (Q.d j k)).app (C.sc i).homology = _
  rw [h]
  exact Iso.hom_inv_id_assoc _ _

/-- IntersectionProductSV: the iterated homology of a resolution tensor
bicomplex is the Tor module of the vertical homology. -/
def a3sv_tensorBicomplexIteratedHomologyIso {B : Type u} [CommRing B]
    (N : ModuleCat.{u} B) (Q : ProjectiveResolution N)
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (i j : ℕ) :
    (((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) i).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (a3sv_tensorBicomplex Q.complex C)).homology j ≅
      ((Tor (ModuleCat.{u} B) j).obj (C.homology i)).obj N := by
  have hflat (k : ℕ) : Module.Flat B (Q.complex.X k) := by
    let : Module.Projective B (Q.complex.X k) :=
      (IsProjective.iff_projective (R := B) (Q.complex.X k)).2 (Q.projective k)
    infer_instance
  exact HomologicalComplex.homologyMapIso
    (a3sv_tensorBicomplexHomologyIso Q.complex C hflat i ≪≫
      (NatIso.mapHomologicalComplex
        (BraidedCategory.tensorLeftIsoTensorRight (C.homology i)).symm
        (ComplexShape.down ℕ)).app Q.complex) j ≪≫
    (a3c_torIso (C.homology i) N Q j).symm

/-- IntersectionProductSV: proper support bounds the lengths on the iterated
homology of the resolution tensor bicomplex. -/
theorem a3sv_tensorBicomplexIteratedHomology_length_ne_top {B : Type} [CommRing B]
    [IsRegularLocalRing B] (N : ModuleCat.{0} B) [Module.Finite B N]
    (Q : ProjectiveResolution N) (C : ChainComplex (ModuleCat.{0} B) ℕ)
    (hfinite : ∀ i, Module.Finite B (C.X i))
    (hproper : ∀ i, ∀ P ∈ Module.support B (C.homology i),
      Module.annihilator B N ≤ P.asIdeal → P = IsLocalRing.closedPoint B)
    (i j : ℕ) :
    Module.length B
      ((((HomologicalComplex.homologyFunctor (ModuleCat.{0} B) (ComplexShape.down ℕ) i).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (a3sv_tensorBicomplex Q.complex C)).homology j) ≠ ⊤ := by
  rw [(a3sv_tensorBicomplexIteratedHomologyIso N Q C i j).toLinearEquiv.length_eq]
  exact a3sv_homology_tor_length_ne_top C N hfinite hproper i j

/-- IntersectionProductSV: the iterated homology is supported in the rectangle
bounded by the original complex and the regular local dimension. -/
theorem a3sv_tensorBicomplexIteratedHomology_isZero {B : Type} [CommRing B]
    [IsRegularLocalRing B] (N : ModuleCat.{0} B) [Module.Finite B N]
    (Q : ProjectiveResolution N) (C : ChainComplex (ModuleCat.{0} B) ℕ)
    (n m : ℕ) (hm : ringKrullDim B ≤ m)
    (hbounded : ∀ i, n < i → IsZero (C.X i))
    (i j : ℕ) (hij : n < i ∨ m < j) :
    IsZero ((((HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
      (ComplexShape.down ℕ) i).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (a3sv_tensorBicomplex Q.complex C)).homology j) := by
  apply IsZero.of_iso _ (a3sv_tensorBicomplexIteratedHomologyIso N Q C i j)
  rcases hij with hi | hj
  · let : Subsingleton (C.homology i) := ModuleCat.isZero_iff_subsingleton.mp
      ((C.sc i).isZero_homology_of_isZero_X₂ (hbounded i hi))
    exact a3c_isZero_tor_of_subsingleton (C.homology i) N j
  · exact a3e_isZero_tor_regular (C.homology i) N j
      (lt_of_le_of_lt hm (by exact_mod_cast hj))

/-- IntersectionProductSV: the signed length sum of the iterated tensor
bicomplex homology is the alternating Tor pairing of the original homology. -/
theorem a3sv_tensorBicomplexIteratedHomology_euler {B : Type u} [CommRing B]
    (N : ModuleCat.{u} B) (Q : ProjectiveResolution N)
    (C : ChainComplex (ModuleCat.{u} B) ℕ) (n m : ℕ) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ (i + j) * ((Module.length B
        ((((HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
          (ComplexShape.down ℕ) i).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (a3sv_tensorBicomplex Q.complex C)).homology j)).toNat : ℤ)) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * a3s_chi m (C.homology i) N := by
  apply Finset.sum_congr rfl
  intro i hi
  simp only [a3s_chi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(a3sv_tensorBicomplexIteratedHomologyIso N Q C i j).toLinearEquiv.length_eq,
    pow_add, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: horizontal homology of a tensor bicomplex with flat
vertical terms is the tensor complex of the horizontal homology. -/
def a3sv_tensorBicomplexHorizontalHomologyIso {B : Type u} [CommRing B]
    (Q C : ChainComplex (ModuleCat.{u} B) ℕ)
    (hflat : ∀ j, Module.Flat B (C.X j)) (i : ℕ) :
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) i).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (a3sv_tensorBicomplex Q C).flip ≅
      a3c_tensC (Q.homology i) C := by
  letI (j : ℕ) : Module.Flat B (C.X j) := hflat j
  refine HomologicalComplex.Hom.isoOfComponents
    (fun j => (Q.sc i).mapHomologyIso (MonoidalCategory.tensorRight (C.X j))) ?_
  intro j k hjk
  have h := NatTrans.app_homology
    ((MonoidalCategory.curriedTensor (ModuleCat.{u} B)).flip.map (C.d j k)) (Q.sc i)
  change ((Q.sc i).mapHomologyIso (MonoidalCategory.tensorRight (C.X j))).hom ≫
    ((MonoidalCategory.curriedTensor (ModuleCat.{u} B)).flip.map (C.d j k)).app
      (Q.sc i).homology = _
  rw [h]
  exact Iso.hom_inv_id_assoc _ _

/-- IntersectionProductSV: degree-zero horizontal homology of a resolution
tensor bicomplex identifies with the original tensor complex. -/
def a3sv_tensorBicomplexHorizontalHomologyZeroIso {B : Type u} [CommRing B]
    (N : ModuleCat.{u} B) (Q : ProjectiveResolution N)
    (C : ChainComplex (ModuleCat.{u} B) ℕ)
    (hproj : ∀ j, Projective (C.X j)) :
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) 0).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (a3sv_tensorBicomplex Q.complex C).flip ≅
      a3c_tensC N C := by
  have hflat (j : ℕ) : Module.Flat B (C.X j) := by
    let : Module.Projective B (C.X j) :=
      (IsProjective.iff_projective (R := B) (C.X j)).2 (hproj j)
    infer_instance
  let e : Q.complex.homology 0 ≅ N :=
    isoOfQuasiIsoAt Q.π 0 ≪≫
      HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 N
  exact a3sv_tensorBicomplexHorizontalHomologyIso Q.complex C hflat 0 ≪≫
    (NatIso.mapHomologicalComplex
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} B)).mapIso e)
      (ComplexShape.down ℕ)).app C

/-- IntersectionProductSV: positive horizontal homology of a resolution tensor
bicomplex vanishes when the vertical terms are projective. -/
theorem a3sv_tensorBicomplexHorizontalHomology_isZero {B : Type u} [CommRing B]
    (N : ModuleCat.{u} B) (Q : ProjectiveResolution N)
    (C : ChainComplex (ModuleCat.{u} B) ℕ)
    (hproj : ∀ j, Projective (C.X j)) (i j : ℕ) :
    IsZero
      ((((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ)
        (i + 1)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (a3sv_tensorBicomplex Q.complex C).flip).X j) := by
  have hflat (k : ℕ) : Module.Flat B (C.X k) := by
    let : Module.Projective B (C.X k) :=
      (IsProjective.iff_projective (R := B) (C.X k)).2 (hproj k)
    infer_instance
  apply IsZero.of_iso _
    ((HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.down ℕ) j).mapIso
      (a3sv_tensorBicomplexHorizontalHomologyIso Q.complex C hflat (i + 1)))
  exact (MonoidalCategory.tensorRight (C.X j)).map_isZero
    (Q.complex_exactAt_succ i).isZero_homology

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the Euler sum after horizontal then vertical homology
of a resolution tensor bicomplex is the tensor complex Euler characteristic. -/
theorem a3sv_tensorBicomplexHorizontalIteratedHomology_euler {B : Type u} [CommRing B]
    (N : ModuleCat.{u} B) (Q : ProjectiveResolution N)
    (C : ChainComplex (ModuleCat.{u} B) ℕ)
    (hproj : ∀ j, Projective (C.X j)) (m n : ℕ) :
    (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ (i + j) * ((Module.length B
        ((((HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
          (ComplexShape.down ℕ) i).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (a3sv_tensorBicomplex Q.complex C).flip).homology j)).toNat : ℤ)) =
      a3i_complexEuler n (a3c_tensC N C) := by
  rw [Finset.sum_eq_single 0]
  · unfold a3i_complexEuler
    apply Finset.sum_congr rfl
    intro j hj
    rw [(HomologicalComplex.homologyMapIso
      (a3sv_tensorBicomplexHorizontalHomologyZeroIso N Q C hproj) j).toLinearEquiv.length_eq]
    simp only [zero_add]
  · intro i hi hi0
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    apply Finset.sum_eq_zero
    intro j hj
    have hz :=
      ((((HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
        (ComplexShape.down ℕ) (k + 1)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (a3sv_tensorBicomplex Q.complex C).flip).sc j).isZero_homology_of_isZero_X₂
        (a3sv_tensorBicomplexHorizontalHomology_isZero N Q C hproj k j)
    have hlen : Module.length B
        ((((HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
          (ComplexShape.down ℕ) k.succ).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (a3sv_tensorBicomplex Q.complex C).flip).homology j) = 0 :=
      Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hz)
    rw [hlen]
    simp only [ENat.toNat_zero, Nat.cast_zero, mul_zero]
  · intro h
    exact (h (by simp)).elim

/-- IntersectionProductSV: every column spectral differential reverses the
sign determined by total degree. -/
theorem a3sv_columnPage_sign (r : ℤ) (i j : ℤ × ℤ)
    (h : (ComplexShape.up' ((-r, r - 1) : ℤ × ℤ)).Rel i j) :
    (Int.negOnePow (i.1 + i.2) : ℤ) = -(Int.negOnePow (j.1 + j.2) : ℤ) := by
  change i + (-r, r - 1) = j at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp at h1 h2
  have ht : i.1 + i.2 = j.1 + j.2 + 1 := by omega
  rw [ht, Int.negOnePow_succ, Units.val_neg]

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: finite-length iterated homology supported in a
rectangle computes the Euler characteristic of total homology. -/
theorem a3sv_totalEuler_eq_iteratedHomology {B : Type} [CommRing B]
    (K : ChainComplex (ChainComplex (ModuleCat.{0} B) ℕ) ℕ) (m n : ℕ)
    (hfinite : ∀ p q, Module.length B
      ((((HomologicalComplex.homologyFunctor (ModuleCat.{0} B) (ComplexShape.down ℕ) q).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology p) ≠ ⊤)
    (hbounded : ∀ p q, m < p ∨ n < q → IsZero
      ((((HomologicalComplex.homologyFunctor (ModuleCat.{0} B) (ComplexShape.down ℕ) q).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology p)) :
    a3i_complexEuler (m + n) (HomologicalComplex₂.total K (ComplexShape.down ℕ)) =
      ∑ p ∈ Finset.range (m + 1), ∑ q ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (p + q) * ((Module.length B
          ((((HomologicalComplex.homologyFunctor (ModuleCat.{0} B) (ComplexShape.down ℕ) q).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology p)).toNat : ℤ) := by
  classical
  let E := a3sv_totalColumnSpectralSequence K
  let s := a3sv_columnRectangle m n
  let sign : ℤ × ℤ → ℤ := fun i => Int.negOnePow (i.1 + i.2)
  have hf : ∀ i ∈ s, Module.length B ((E.page 2).X i) ≠ ⊤ := by
    intro i hi
    dsimp only [s, a3sv_columnRectangle] at hi
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_map.mp hi
    change Module.length B ((E.page 2).X ((p : ℤ), (q : ℤ))) ≠ ⊤
    rw [(a3sv_totalColumnSecondPageIso K p q).toLinearEquiv.length_eq]
    exact hfinite p q
  have hb : ∀ i ∉ s, IsZero ((E.page 2).X i) := by
    rintro ⟨p, q⟩ hi
    by_cases hp : p < 0
    · exact a3sv_totalColumnSecondPage_isZero_of_negative K p q (Or.inl hp)
    by_cases hq : q < 0
    · exact a3sv_totalColumnSecondPage_isZero_of_negative K p q (Or.inr hq)
    lift p to ℕ using (le_of_not_gt hp)
    lift q to ℕ using (le_of_not_gt hq)
    apply IsZero.of_iso _ (a3sv_totalColumnSecondPageIso K p q)
    apply hbounded p q
    by_contra h
    exact hi ((a3sv_mem_columnRectangle m n p q).mpr (by omega))
  let k : ℕ := m + n + 2
  let r : ℤ := 2 + k
  have hr : 1 ≤ r := by dsimp [r, k]; omega
  have hdata := a3sv_spectralSequence_finite_after E 2 (by omega) s hf hb k
  have hfr (i : ℤ × ℤ) : Module.length B ((E.page r hr).X i) ≠ ⊤ := by
    by_cases hi : i ∈ s
    · exact hdata.1 i hi
    · rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp (hdata.2 i hi))]
      simp
  let F : ℕ → ℕ → ℤ := fun p q =>
    (-1 : ℤ) ^ (p + q) * ((Module.length B ((E.page r hr).X ((p : ℤ), (q : ℤ)))).toNat : ℤ)
  have hF : ∀ p q, m < p ∨ n < q → F p q = 0 := by
    intro p q hpq
    have hi : ((p : ℤ), (q : ℤ)) ∉ s := by
      intro hi
      have h := (a3sv_mem_columnRectangle m n p q).mp hi
      omega
    dsimp only [F]
    rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp (hdata.2 _ hi))]
    simp
  have he : (∑ p ∈ Finset.range (m + 1), ∑ q ∈ Finset.range (n + 1), F p q) =
      ∑ p ∈ Finset.range (m + 1), ∑ q ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (p + q) * ((Module.length B ((E.page 2).X ((p : ℤ), (q : ℤ)))).toNat : ℤ) := by
    have h := a3sv_spectralSequence_euler_from E 2 (by omega) s sign
      (fun t ht i j hij => a3sv_columnPage_sign t i j hij) hf hb k
    simpa only [s, a3sv_columnRectangle_sum, sign, F, ← Nat.cast_add,
      Int.coe_negOnePow_natCast] using h
  calc
    _ = ∑ i ∈ Finset.range (m + n + 1), ∑ p ∈ Finset.range (i + 1),
        (-1 : ℤ) ^ i * ((Module.length B ((E.page r hr).X ((p : ℤ), (i : ℤ) - p))).toNat : ℤ) :=
      a3sv_totalEuler_eq_stablePage_degreewise K (m + n) r hr
        (by dsimp [r, k]; omega) (fun i hi p hp => hfr _)
    _ = ∑ i ∈ Finset.range (m + n + 1), ∑ p ∈ Finset.range (i + 1), F p (i - p) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro p hp
      have hpi : p ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
      have hc : ((i - p : ℕ) : ℤ) = (i : ℤ) - p := by omega
      simp only [F, Nat.add_sub_of_le hpi]
      rw [hc]
    _ = ∑ p ∈ Finset.range (m + 1), ∑ q ∈ Finset.range (n + 1), F p q :=
      a3sv_triangle_sum_eq_rectangle F m n hF
    _ = _ := by
      rw [he]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [(a3sv_totalColumnSecondPageIso K p q).toLinearEquiv.length_eq]

/-- IntersectionProductSV: the opposite iterated homology of the resolution
tensor bicomplex has finite length under proper homology support. -/
theorem a3sv_tensorBicomplexHorizontalIteratedHomology_length_ne_top
    {B : Type} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (N : ModuleCat.{0} B) [Module.Finite B N] (Q : ProjectiveResolution N)
    (C : ChainComplex (ModuleCat.{0} B) ℕ)
    (hproj : ∀ i, Projective (C.X i)) (hfinite : ∀ i, Module.Finite B (C.X i))
    (hproper : ∀ i, ∀ P ∈ Module.support B (C.homology i),
      Module.annihilator B N ≤ P.asIdeal → P = IsLocalRing.closedPoint B)
    (i j : ℕ) :
    Module.length B
      ((((HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
        (ComplexShape.down ℕ) i).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (a3sv_tensorBicomplex Q.complex C).flip).homology j) ≠ ⊤ := by
  cases i with
  | zero =>
    rw [(HomologicalComplex.homologyMapIso
      (a3sv_tensorBicomplexHorizontalHomologyZeroIso N Q C hproj) j).toLinearEquiv.length_eq]
    exact a3sv_tensor_homology_length_ne_top C N hproj hfinite hproper j
  | succ i =>
    have hz :=
      ((((HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
        (ComplexShape.down ℕ) (i + 1)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (a3sv_tensorBicomplex Q.complex C).flip).sc j).isZero_homology_of_isZero_X₂
        (a3sv_tensorBicomplexHorizontalHomology_isZero N Q C hproj i j)
    have hlen : Module.length B
        ((((HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
          (ComplexShape.down ℕ) (i + 1)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (a3sv_tensorBicomplex Q.complex C).flip).homology j) = 0 :=
      Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hz)
    rw [hlen]
    simp

/-- IntersectionProductSV: the opposite iterated homology is concentrated in
row zero and in the degrees where the original complex can be nonzero. -/
theorem a3sv_tensorBicomplexHorizontalIteratedHomology_isZero
    {B : Type u} [CommRing B] (N : ModuleCat.{u} B) (Q : ProjectiveResolution N)
    (C : ChainComplex (ModuleCat.{u} B) ℕ)
    (hproj : ∀ i, Projective (C.X i)) (n : ℕ)
    (hbounded : ∀ i, n < i → IsZero (C.X i))
    (i j : ℕ) (hij : 0 < i ∨ n < j) :
    IsZero
      ((((HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
        (ComplexShape.down ℕ) i).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (a3sv_tensorBicomplex Q.complex C).flip).homology j) := by
  cases i with
  | zero =>
    apply IsZero.of_iso _ (HomologicalComplex.homologyMapIso
      (a3sv_tensorBicomplexHorizontalHomologyZeroIso N Q C hproj) j)
    apply ((a3c_tensC N C).sc j).isZero_homology_of_isZero_X₂
    exact (MonoidalCategory.tensorLeft N).map_isZero (hbounded j (by omega))
  | succ i =>
    exact
      ((((HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
        (ComplexShape.down ℕ) (i + 1)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (a3sv_tensorBicomplex Q.complex C).flip).sc j).isZero_homology_of_isZero_X₂
        (a3sv_tensorBicomplexHorizontalHomology_isZero N Q C hproj i j)

/-- IntersectionProductSV: the Koszul sign gives symmetry of natural-degree
total complexes. -/
def a3sv_downNatTotalSymmetry : TotalComplexShapeSymmetry
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    intro p p' h q
    change p' + 1 = p at h
    subst p
    dsimp
    rw [mul_one, add_mul, one_mul, pow_add, mul_comm]
  σ_ε₂ := by
    intro p q q' h
    change q' + 1 = q at h
    subst q
    dsimp
    rw [one_mul, mul_add, mul_one, pow_add, mul_assoc,
      Int.units_mul_self, mul_one]

/-- IntersectionProductLoc2 S4b: the tensor Euler characteristic is the alternating
homology pairing for a bounded complex of finite projective modules. -/
theorem a3i_tensor_euler_homology {B : Type} [CommRing B] [IsRegularLocalRing B]
    (C : ChainComplex (ModuleCat.{0} B) ℕ) (N : ModuleCat.{0} B) [Module.Finite B N]
    (n m : ℕ) (hm : ringKrullDim B ≤ m)
    (hproj : ∀ i, Projective (C.X i)) (hfinite : ∀ i, Module.Finite B (C.X i))
    (hbounded : ∀ i, n < i → IsZero (C.X i))
    (hproper : ∀ i, ∀ P ∈ Module.support B (C.homology i),
      Module.annihilator B N ≤ P.asIdeal → P = IsLocalRing.closedPoint B) :
    a3i_complexEuler (n + m) (a3c_tensC N C) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * a3s_chi m (C.homology i) N := by
  classical
  letI := a3sv_downNatTotalSymmetry
  let Q := ProjectiveResolution.of N
  let K := a3sv_tensorBicomplex Q.complex C
  have hv := a3sv_totalEuler_eq_iteratedHomology K m n
    (fun p q => a3sv_tensorBicomplexIteratedHomology_length_ne_top
      N Q C hfinite hproper q p)
    (fun p q h => a3sv_tensorBicomplexIteratedHomology_isZero
      N Q C n m hm hbounded q p h.symm)
  have hh := a3sv_totalEuler_eq_iteratedHomology K.flip n m
    (fun p q => a3sv_tensorBicomplexHorizontalIteratedHomology_length_ne_top
      N Q C hproj hfinite hproper q p)
    (fun p q h => a3sv_tensorBicomplexHorizontalIteratedHomology_isZero
      N Q C hproj n hbounded q p (by omega))
  have hflip : a3i_complexEuler (n + m) (K.flip.total (ComplexShape.down ℕ)) =
      a3i_complexEuler (m + n) (K.total (ComplexShape.down ℕ)) := by
    rw [Nat.add_comm n m]
    unfold a3i_complexEuler
    apply Finset.sum_congr rfl
    intro i hi
    rw [(HomologicalComplex.homologyMapIso
      (K.totalFlipIso (ComplexShape.down ℕ)) i).toLinearEquiv.length_eq]
  rw [Finset.sum_comm] at hh
  simp only [Nat.add_comm] at hh
  rw [a3sv_tensorBicomplexHorizontalIteratedHomology_euler N Q C hproj m n] at hh
  rw [a3sv_complexEuler_eq_of_le (a3c_tensC N C) n (n + m) (by omega)
    (fun i hi => (MonoidalCategory.tensorLeft N).map_isZero (hbounded i hi))]
  rw [← hh, hflip, hv, Finset.sum_comm]
  simp only [Nat.add_comm]
  exact a3sv_tensorBicomplexIteratedHomology_euler N Q C n m

/-- IntersectionProductLoc2 S4: the tensor Euler characteristic depends on the
localized homology cycle; primes below the selected dimension contribute zero by S3. -/
theorem a3i_topCycle (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (T : X.left) (C : ChainComplex (ModuleCat.{0} (X.left.presheaf.stalk T)) ℕ)
    (N : ModuleCat.{0} (X.left.presheaf.stalk T)) [Module.Finite (X.left.presheaf.stalk T) N]
    (n m : ℕ) (hm : ringKrullDim (X.left.presheaf.stalk T) ≤ m)
    (hproj : ∀ i, Projective (C.X i))
    (hfinite : ∀ i, Module.Finite (X.left.presheaf.stalk T) (C.X i))
    (hhom : ∀ i, Module.Finite (X.left.presheaf.stalk T) (C.homology i))
    (hbounded : ∀ i, n < i → IsZero (C.X i))
    (Z : Set (PrimeSpectrum (X.left.presheaf.stalk T)))
    (F : Finset (PrimeSpectrum (X.left.presheaf.stalk T)))
    (hZ : ∀ P ∈ Z, ∀ Q, P ≤ Q → Q ∈ Z)
    (hsupport : ∀ i, Module.support (X.left.presheaf.stalk T) (C.homology i) ⊆ Z)
    (hfin : ∀ P ∈ Z, Module.annihilator (X.left.presheaf.stalk T) N ≤ P.asIdeal →
      P = IsLocalRing.closedPoint (X.left.presheaf.stalk T))
    (hmin : ∀ P ∈ Z, ∀ D ∈ F, P ≤ D → P = D)
    (hdim : ∀ P ∈ Z, P ∉ F → ∀ Q ∈ Module.support (X.left.presheaf.stalk T) N,
      ringKrullDim (X.left.presheaf.stalk T ⧸ P.asIdeal) +
        ringKrullDim (X.left.presheaf.stalk T ⧸ Q.asIdeal) <
          ringKrullDim (X.left.presheaf.stalk T)) :
    a3i_complexEuler (n + m) (a3c_tensC N C) =
      ∑ P ∈ F, a3i_complexCycleCoeff n C P *
        a3s_chi m (ModuleCat.of _ (X.left.presheaf.stalk T ⧸ P.asIdeal)) N := by
  have := a3c_isRegularLocalRing_stalk X T
  rw [a3i_tensor_euler_homology C N n m hm hproj hfinite hbounded
    (fun i P hP => hfin P (hsupport i hP))]
  apply a3i_homology_topCycle m n
    (lt_of_le_of_lt hm (by exact_mod_cast Nat.lt_succ_self m)) N Z F hfin hmin
    ?_ C hhom hsupport
  intro P hP hPF
  apply a3i_local_vanishing X T (X.left.presheaf.stalk T ⧸ P.asIdeal) N
    ?_ ?_ m hm
  · intro Q hQ R hR D hQD hRD
    have hPQ : P ≤ Q := by
      change P.asIdeal ≤ Q.asIdeal
      simpa only [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] using hQ
    exact hfin D (hZ P hP D (hPQ.trans hQD))
      ((Module.annihilator_le_of_mem_support hR).trans hRD)
  · intro Q hQ R hR
    have hPQ : P ≤ Q := by
      change P.asIdeal ≤ Q.asIdeal
      simpa only [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] using hQ
    have hQF : Q ∉ F := fun h => hPF ((hmin P hP Q h hPQ).symm ▸ h)
    exact hdim Q (hZ P hP Q hPQ) hQF R hR

/-- IntersectionProductSV: proper intersection with every component of the
second pair bounds the codimension of every common specialization. -/
theorem a3sv_triple_coheight_le (X : Scheme) [IsLocallyNoetherian X]
    (u v w z : X) (hvw : a3i_MeetProperly X v w)
    (ht : ∀ t ∈ a3y_comps v w, a3i_MeetProperly X u t)
    (hu : u ⤳ z) (hv : v ⤳ z) (hw : w ⤳ z) :
    Order.coheight u + Order.coheight v + Order.coheight w ≤ Order.coheight z := by
  obtain ⟨t, htmem, htz⟩ := a3y_exists_comp v w hv hw
  obtain ⟨q, hqmem, hqz⟩ := a3y_exists_comp u t hu htz
  have hq := a3y_coheight_comps u t (ht t htmem) hqmem
  have htc := a3y_coheight_comps v w hvw htmem
  have hle := Order.coheight_anti (Scheme.le_iff_specializes.mpr hqz)
  rw [hq, htc, ← add_assoc] at hle
  exact hle

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: exchanging the two resolution directions while
keeping the middle tensor factor fixed. -/
def a3sv_tensorBicomplexExchangeIso {B : Type u} [CommRing B]
    (P Q : ChainComplex (ModuleCat.{u} B) ℕ) (N : ModuleCat.{u} B) :
    a3sv_tensorBicomplex P (a3c_tensC N Q) ≅
      (a3sv_tensorBicomplex Q (a3c_tensC N P)).flip := by
  refine HomologicalComplex.Hom.isoOfComponents (fun p =>
    HomologicalComplex.Hom.isoOfComponents (fun q =>
      (TensorProduct.assoc B (P.X p) N (Q.X q)).symm.toModuleIso ≪≫
        (TensorProduct.comm B ((P.X p) ⊗[B] N) (Q.X q)).toModuleIso ≪≫
        (TensorProduct.congr (LinearEquiv.refl B (Q.X q))
          (TensorProduct.comm B (P.X p) N)).toModuleIso) ?_) ?_
  · intro q r hqr
    apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold'
    intro p n q
    rfl
  · intro p r hpr
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold'
    intro p n t
    rfl
/-- IntersectionProductSV: the second page for two resolutions and a middle
module is an iterated Tor module. -/
def a3sv_tripleIteratedHomologyIso {B : Type u} [CommRing B]
    (L M N : ModuleCat.{u} B) (P : ProjectiveResolution L) (Q : ProjectiveResolution M)
    (i j : ℕ) :
    ((((HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
      (ComplexShape.down ℕ) i).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (a3sv_tensorBicomplex P.complex (a3c_tensC N Q.complex))).homology j) ≅
      ((Tor (ModuleCat.{u} B) j).obj (((Tor (ModuleCat.{u} B) i).obj N).obj M)).obj L :=
  a3sv_tensorBicomplexIteratedHomologyIso L P (a3c_tensC N Q.complex) i j ≪≫
    (((Tor (ModuleCat.{u} B) j).mapIso (a3c_torIso N M Q i).symm).app L)

/-- IntersectionProductSV: the total Euler characteristic of two resolutions
around a middle module is the iterated Tor Euler pairing. -/
theorem a3sv_tripleTotalEuler {B : Type} [CommRing B] [IsRegularLocalRing B]
    (L M N : ModuleCat.{0} B) [Module.Finite B L] [Module.Finite B M]
    (P : ProjectiveResolution L) (Q : ProjectiveResolution M) (m : ℕ)
    (hm : ringKrullDim B ≤ m)
    (hfinite : ∀ i j, Module.length B
      (((Tor (ModuleCat.{0} B) j).obj (((Tor (ModuleCat.{0} B) i).obj N).obj M)).obj L) ≠ ⊤) :
    a3i_complexEuler (m + m)
      ((a3sv_tensorBicomplex P.complex (a3c_tensC N Q.complex)).total (ComplexShape.down ℕ)) =
      ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        a3s_chi m (((Tor (ModuleCat.{0} B) i).obj N).obj M) L := by
  let C := a3c_tensC N Q.complex
  let K := a3sv_tensorBicomplex P.complex C
  have hf (p q : ℕ) : Module.length B
      ((((HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
        (ComplexShape.down ℕ) q).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology p) ≠ ⊤ := by
    rw [(a3sv_tripleIteratedHomologyIso L M N P Q q p).toLinearEquiv.length_eq]
    exact hfinite q p
  have hb (p q : ℕ) (h : m < p ∨ m < q) : IsZero
      ((((HomologicalComplex.homologyFunctor (ModuleCat.{0} B)
        (ComplexShape.down ℕ) q).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology p) := by
    apply IsZero.of_iso _ (a3sv_tripleIteratedHomologyIso L M N P Q q p)
    rcases h with hp | hq
    · exact a3e_isZero_tor_regular _ L p (lt_of_le_of_lt hm (by exact_mod_cast hp))
    · letI : Subsingleton (((Tor (ModuleCat.{0} B) q).obj N).obj M) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (a3e_isZero_tor_regular N M q (lt_of_le_of_lt hm (by exact_mod_cast hq)))
      exact a3c_isZero_tor_of_subsingleton _ L p
  rw [a3sv_totalEuler_eq_iteratedHomology K m m hf hb, Finset.sum_comm]
  have he := a3sv_tensorBicomplexIteratedHomology_euler L P C m m
  simp only [Nat.add_comm] at he ⊢
  rw [he]
  apply Finset.sum_congr rfl
  intro i hi
  rw [a3s_chi_congr (a3c_torIso N M Q i).symm L m]

/-- IntersectionProductSV: exchanging the outer modules preserves the
iterated Tor Euler pairing when both second pages have finite lengths. -/
theorem a3sv_iteratedTor_euler_exchange {B : Type} [CommRing B] [IsRegularLocalRing B]
    (L M N : ModuleCat.{0} B) [Module.Finite B L] [Module.Finite B M]
    (m : ℕ) (hm : ringKrullDim B ≤ m)
    (hleft : ∀ i j, Module.length B
      (((Tor (ModuleCat.{0} B) j).obj (((Tor (ModuleCat.{0} B) i).obj N).obj M)).obj L) ≠ ⊤)
    (hright : ∀ i j, Module.length B
      (((Tor (ModuleCat.{0} B) j).obj (((Tor (ModuleCat.{0} B) i).obj N).obj L)).obj M) ≠ ⊤) :
    (∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
      a3s_chi m (((Tor (ModuleCat.{0} B) i).obj N).obj M) L) =
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
      a3s_chi m (((Tor (ModuleCat.{0} B) i).obj N).obj L) M := by
  letI := a3sv_downNatTotalSymmetry
  let P := ProjectiveResolution.of L
  let Q := ProjectiveResolution.of M
  let K := a3sv_tensorBicomplex P.complex (a3c_tensC N Q.complex)
  let K' := a3sv_tensorBicomplex Q.complex (a3c_tensC N P.complex)
  let e : K.total (ComplexShape.down ℕ) ≅ K'.total (ComplexShape.down ℕ) :=
    HomologicalComplex₂.total.mapIso (a3sv_tensorBicomplexExchangeIso P.complex Q.complex N)
      (ComplexShape.down ℕ) ≪≫ K'.totalFlipIso (ComplexShape.down ℕ)
  have he : a3i_complexEuler (m + m) (K.total (ComplexShape.down ℕ)) =
      a3i_complexEuler (m + m) (K'.total (ComplexShape.down ℕ)) := by
    unfold a3i_complexEuler
    apply Finset.sum_congr rfl
    intro i hi
    rw [(HomologicalComplex.homologyMapIso e i).toLinearEquiv.length_eq]
  rw [a3sv_tripleTotalEuler L M N P Q m hm hleft,
    a3sv_tripleTotalEuler M L N Q P m hm hright] at he
  exact he

/-- IntersectionProductSV: common support at the maximal ideal gives finite
length to the second page of the triple tensor calculation. -/
theorem a3sv_iteratedTor_length_ne_top {B : Type u} [CommRing B]
    [IsNoetherianRing B] [IsLocalRing B]
    (L M N : ModuleCat.{u} B) [Module.Finite B L] [Module.Finite B M] [Module.Finite B N]
    (hproper : ∀ P : PrimeSpectrum B, Module.annihilator B L ≤ P.asIdeal →
      Module.annihilator B M ≤ P.asIdeal → Module.annihilator B N ≤ P.asIdeal →
      P = IsLocalRing.closedPoint B) (i j : ℕ) :
    Module.length B
      (((Tor (ModuleCat.{u} B) j).obj (((Tor (ModuleCat.{u} B) i).obj N).obj M)).obj L) ≠ ⊤ := by
  have := a3e_tor_finite i N M
  apply a3s_length_tor_ne_top _ L j
  intro P hP hL
  have hs := (Module.mem_support_iff_of_finite).mpr hP
  obtain ⟨hN, hM⟩ := a3s_annihilator_le_of_mem_support_tor N M i P hs
  exact hproper P hL hM hN

/-- IntersectionProductSV: proper common support suffices for the exchange
identity of the iterated Tor Euler pairings. -/
theorem a3sv_iteratedTor_euler_exchange_supported {B : Type} [CommRing B]
    [IsRegularLocalRing B] (L M N : ModuleCat.{0} B)
    [Module.Finite B L] [Module.Finite B M] [Module.Finite B N]
    (m : ℕ) (hm : ringKrullDim B ≤ m)
    (hproper : ∀ P : PrimeSpectrum B, Module.annihilator B L ≤ P.asIdeal →
      Module.annihilator B M ≤ P.asIdeal → Module.annihilator B N ≤ P.asIdeal →
      P = IsLocalRing.closedPoint B) :
    (∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
      a3s_chi m (((Tor (ModuleCat.{0} B) i).obj N).obj M) L) =
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
      a3s_chi m (((Tor (ModuleCat.{0} B) i).obj N).obj L) M :=
  a3sv_iteratedTor_euler_exchange L M N m hm
    (a3sv_iteratedTor_length_ne_top L M N hproper)
    (a3sv_iteratedTor_length_ne_top M L N (fun P hM hL hN => hproper P hL hM hN))

/-- IntersectionProductSV: a stalk prime contains the ideal of a generization
exactly when its image specializes from that generization. -/
theorem a3sv_stalkIdeal_le_prime_iff (X : Scheme) (T u : X) (hu : u ⤳ T)
    (P : PrimeSpectrum (X.presheaf.stalk T)) :
    a3i_stalkIdeal X T u ≤ P.asIdeal ↔ u ⤳ X.fromSpecStalk T P := by
  change a3y_pt T u hu ≤ P ↔ u ⤳ X.fromSpecStalk T P
  simpa only [a3y_pt_fromSpecStalk] using
    (a3y_pt_le_iff T u (X.fromSpecStalk T P) hu (a3y_specializes_fromSpecStalk T P))

/-- IntersectionProductSV: a triple intersection of the expected codimension
has only maximal common support in its stalk. -/
theorem a3sv_triple_stalk_support (X : Scheme) [IsLocallyNoetherian X]
    (u v w T : X) (hvw : a3i_MeetProperly X v w)
    (ht : ∀ t ∈ a3y_comps v w, a3i_MeetProperly X u t)
    (hu : u ⤳ T) (hv : v ⤳ T) (hw : w ⤳ T)
    (hT : Order.coheight T = Order.coheight u + Order.coheight v + Order.coheight w)
    (P : PrimeSpectrum (X.presheaf.stalk T))
    (hP : a3i_stalkIdeal X T u ≤ P.asIdeal)
    (hQ : a3i_stalkIdeal X T v ≤ P.asIdeal)
    (hR : a3i_stalkIdeal X T w ≤ P.asIdeal) : P = IsLocalRing.closedPoint _ := by
  have huq := (a3sv_stalkIdeal_le_prime_iff X T u hu P).mp hP
  have hvq := (a3sv_stalkIdeal_le_prime_iff X T v hv P).mp hQ
  have hwq := (a3sv_stalkIdeal_le_prime_iff X T w hw P).mp hR
  have hqT := a3y_specializes_fromSpecStalk T P
  have heq : X.fromSpecStalk T P = T :=
    a3y_eq_of_specializes hqT (by
      rw [hT]
      exact a3sv_triple_coheight_le X u v w _ hvw ht huq hvq hwq)
  rw [← a3y_pt_fromSpecStalk T P]
  have he : a3y_pt T (X.fromSpecStalk T P) hqT = a3y_pt T T (specializes_refl T) := by
    apply PrimeSpectrum.ext
    change a3i_stalkIdeal X T (X.fromSpecStalk T P) = a3i_stalkIdeal X T T
    rw [heq]
  rw [he, a3y_pt_self]

/-- IntersectionProductSV: primes outside the components of a proper pair
have too small a quotient dimension to contribute to a proper triple. -/
theorem a3sv_pair_quotient_dimension_lt (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (u v w T : X.left)
    (huv : a3i_MeetProperly X.left u v)
    (hu : u ⤳ T) (hv : v ⤳ T) (hw : w ⤳ T)
    (hT : Order.coheight T = Order.coheight u + Order.coheight v + Order.coheight w)
    (P Q : PrimeSpectrum (X.left.presheaf.stalk T))
    (hPu : a3i_stalkIdeal X.left T u ≤ P.asIdeal)
    (hPv : a3i_stalkIdeal X.left T v ≤ P.asIdeal)
    (hQw : a3i_stalkIdeal X.left T w ≤ Q.asIdeal)
    (hnot : X.left.fromSpecStalk T P ∉ a3y_comps u v) :
    ringKrullDim (X.left.presheaf.stalk T ⧸ P.asIdeal) +
      ringKrullDim (X.left.presheaf.stalk T ⧸ Q.asIdeal) <
      ringKrullDim (X.left.presheaf.stalk T) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hup := (a3sv_stalkIdeal_le_prime_iff X.left T u hu P).mp hPu
  have hvp := (a3sv_stalkIdeal_le_prime_iff X.left T v hv P).mp hPv
  have hwq := (a3sv_stalkIdeal_le_prime_iff X.left T w hw Q).mp hQw
  obtain ⟨s, hs, hsp⟩ := a3y_exists_comp u v hup hvp
  have hne : s ≠ X.left.fromSpecStalk T P := fun he => hnot (he ▸ hs)
  have hlt := a3y_coheight_lt hsp hne
  rw [a3y_coheight_comps u v huv hs] at hlt
  have hle := Order.coheight_anti (Scheme.le_iff_specializes.mpr hwq)
  obtain ⟨cp, ct, dp, hcp, hct, hdp, hpd⟩ :=
    a3y_dims X (a3y_specializes_fromSpecStalk T P)
  obtain ⟨cq, ct', dq, hcq, hct', hdq, hqd⟩ :=
    a3y_dims X (a3y_specializes_fromSpecStalk T Q)
  obtain ⟨cu, hcu⟩ := ENat.ne_top_iff_exists.mp (a3c_coheight_ne_top X.left u)
  obtain ⟨cv, hcv⟩ := ENat.ne_top_iff_exists.mp (a3c_coheight_ne_top X.left v)
  obtain ⟨cw, hcw⟩ := ENat.ne_top_iff_exists.mp (a3c_coheight_ne_top X.left w)
  rw [← hcu, ← hcv, hcp] at hlt
  rw [← hcw, hcq] at hle
  rw [hct, ← hcu, ← hcv, ← hcw] at hT
  have hlt' : cu + cv < cp := by exact_mod_cast hlt
  have hle' : cw ≤ cq := by exact_mod_cast hle
  have hT' : ct = cu + cv + cw := by exact_mod_cast hT
  have hcteq : ct' = ct := by exact_mod_cast (hct'.symm.trans hct)
  have hPi : a3i_stalkIdeal X.left T (X.left.fromSpecStalk T P) = P.asIdeal :=
    congrArg PrimeSpectrum.asIdeal (a3y_pt_fromSpecStalk T P)
  have hQi : a3i_stalkIdeal X.left T (X.left.fromSpecStalk T Q) = Q.asIdeal :=
    congrArg PrimeSpectrum.asIdeal (a3y_pt_fromSpecStalk T Q)
  rw [hPi] at hdp
  rw [hQi] at hdq
  rw [hdp, hdq, ringKrullDim_stalk_eq_coheight, hct]
  exact_mod_cast (show dp + dq < ct by omega)

/-- IntersectionProductSV: the lower-dimensional primes of a proper pair
have zero Tor Euler pairing with the third factor. -/
theorem a3sv_pair_prime_vanishing (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (u v w T : X.left)
    (huv : a3i_MeetProperly X.left u v)
    (hu : u ⤳ T) (hv : v ⤳ T) (hw : w ⤳ T)
    (hT : Order.coheight T = Order.coheight u + Order.coheight v + Order.coheight w)
    (hproper : ∀ D : PrimeSpectrum (X.left.presheaf.stalk T),
      a3i_stalkIdeal X.left T u ≤ D.asIdeal → a3i_stalkIdeal X.left T v ≤ D.asIdeal →
      a3i_stalkIdeal X.left T w ≤ D.asIdeal → D = IsLocalRing.closedPoint _)
    (P : PrimeSpectrum (X.left.presheaf.stalk T))
    (hPu : a3i_stalkIdeal X.left T u ≤ P.asIdeal)
    (hPv : a3i_stalkIdeal X.left T v ≤ P.asIdeal)
    (hnot : X.left.fromSpecStalk T P ∉ a3y_comps u v)
    (m : ℕ) (hm : ringKrullDim (X.left.presheaf.stalk T) ≤ m) :
    a3s_chi m (ModuleCat.of (X.left.presheaf.stalk T) (X.left.presheaf.stalk T ⧸ P.asIdeal))
      (ModuleCat.of (X.left.presheaf.stalk T) (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T w)) = 0 := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  apply a3i_local_vanishing X T _ _ ?_ ?_ m hm
  · intro Q hQ R hR D hQD hRD
    have hPQ : P.asIdeal ≤ Q.asIdeal := by
      simpa only [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] using hQ
    have hwR : a3i_stalkIdeal X.left T w ≤ R.asIdeal := by
      simpa only [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] using hR
    exact hproper D
      (hPu.trans (hPQ.trans hQD)) (hPv.trans (hPQ.trans hQD)) (hwR.trans hRD)
  · intro Q hQ R hR
    have hPQ : P.asIdeal ≤ Q.asIdeal := by
      simpa only [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] using hQ
    have hwR : a3i_stalkIdeal X.left T w ≤ R.asIdeal := by
      simpa only [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] using hR
    apply a3sv_pair_quotient_dimension_lt X u v w T huv hu hv hw hT Q R
      (hPu.trans hPQ) (hPv.trans hPQ) hwR
    intro hcomp
    have hup := (a3sv_stalkIdeal_le_prime_iff X.left T u hu P).mp hPu
    have hvp := (a3sv_stalkIdeal_le_prime_iff X.left T v hv P).mp hPv
    have hpq : X.left.fromSpecStalk T P ⤳ X.left.fromSpecStalk T Q :=
      ((PrimeSpectrum.le_iff_specializes P Q).mp hPQ).map (X.left.fromSpecStalk T).continuous
    have he := (a3y_comps_spec u v hcomp).2.2 _ hup hvp hpq
    exact hnot (he.symm ▸ hcomp)

/-- IntersectionProductSV: devissage of a finite stalk module onto the
components of a proper pair in a triple intersection. -/
theorem a3sv_stalk_pair_devissage (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (u v w T : X.left)
    (huv : a3i_MeetProperly X.left u v)
    (hu : u ⤳ T) (hv : v ⤳ T) (hw : w ⤳ T)
    (hT : Order.coheight T = Order.coheight u + Order.coheight v + Order.coheight w)
    (hproper : ∀ D : PrimeSpectrum (X.left.presheaf.stalk T),
      a3i_stalkIdeal X.left T u ≤ D.asIdeal → a3i_stalkIdeal X.left T v ≤ D.asIdeal →
      a3i_stalkIdeal X.left T w ≤ D.asIdeal → D = IsLocalRing.closedPoint _)
    (m : ℕ) (hm : ringKrullDim (X.left.presheaf.stalk T) ≤ m)
    (M : ModuleCat.{0} (X.left.presheaf.stalk T)) [Module.Finite (X.left.presheaf.stalk T) M]
    (hM : ∀ P ∈ Module.support (X.left.presheaf.stalk T) M,
      a3i_stalkIdeal X.left T u ≤ P.asIdeal ∧ a3i_stalkIdeal X.left T v ≤ P.asIdeal) :
    a3s_chi m M (ModuleCat.of (X.left.presheaf.stalk T)
      (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T w)) =
      ∑ t ∈ a3y_compsAt X u v T, ((a3e_locLen (a3y_ptOr X T t) M).toNat : ℤ) *
        a3s_chi m (ModuleCat.of (X.left.presheaf.stalk T)
          (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T t))
          (ModuleCat.of (X.left.presheaf.stalk T)
            (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T w)) := by
  classical
  have := a3c_isRegularLocalRing_stalk X T
  let A := X.left.presheaf.stalk T
  let W := ModuleCat.of A (A ⧸ a3i_stalkIdeal X.left T w)
  let Z : Set (PrimeSpectrum A) := {P | a3i_stalkIdeal X.left T u ≤ P.asIdeal ∧
    a3i_stalkIdeal X.left T v ≤ P.asIdeal}
  let F := (a3y_compsAt X u v T).image (a3y_ptOr X T)
  have hmem (t : X.left) (ht : t ∈ a3y_compsAt X u v T) :
      t ∈ a3y_comps u v ∧ t ⤳ T := by
    simpa only [a3y_compsAt, Finset.mem_filter, Set.Finite.mem_toFinset] using ht
  have hpt (t : X.left) (ht : t ⤳ T) : a3y_ptOr X T t = a3y_pt T t ht := by
    simp only [a3y_ptOr, dite_eq_left ht]
  have hmin : ∀ P ∈ Z, ∀ D ∈ F, P ≤ D → P = D := by
    intro P hP D hD hPD
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hD
    rw [hpt t (hmem t ht).2] at hPD ⊢
    have hup := (a3sv_stalkIdeal_le_prime_iff X.left T u hu P).mp hP.1
    have hvp := (a3sv_stalkIdeal_le_prime_iff X.left T v hv P).mp hP.2
    have hpt' : X.left.fromSpecStalk T P ⤳ t := by
      have h := ((PrimeSpectrum.le_iff_specializes _ _).mp hPD).map
        (X.left.fromSpecStalk T).continuous
      simpa only [a3y_fromSpecStalk_pt] using h
    have he := (a3y_comps_spec u v (hmem t ht).1).2.2 _ hup hvp hpt'
    rw [← a3y_pt_fromSpecStalk T P]
    apply PrimeSpectrum.ext
    change a3i_stalkIdeal X.left T (X.left.fromSpecStalk T P) = a3i_stalkIdeal X.left T t
    rw [he]
  have hlow : ∀ P ∈ Z, P ∉ F → a3s_chi m (ModuleCat.of A (A ⧸ P.asIdeal)) W = 0 := by
    intro P hP hPF
    apply a3sv_pair_prime_vanishing X u v w T huv hu hv hw hT hproper P hP.1 hP.2 ?_ m hm
    intro hcomp
    apply hPF
    have ht : X.left.fromSpecStalk T P ∈ a3y_compsAt X u v T := by
      simp only [a3y_compsAt, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨hcomp, a3y_specializes_fromSpecStalk T P⟩
    refine Finset.mem_image.mpr ⟨_, ht, ?_⟩
    rw [hpt _ (a3y_specializes_fromSpecStalk T P), a3y_pt_fromSpecStalk]
  have he := (a3w_chi_devissage_top m
    (lt_of_le_of_lt hm (by exact_mod_cast Nat.lt_succ_self m)) W Z F
    (fun P hP hW => hproper P hP.1 hP.2 (by
      simpa only [W, A, Ideal.annihilator_quotient] using hW)) hmin hlow M hM).1
  rw [he]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [hpt t (hmem t ht).2]
    rfl
  · intro t ht t' ht' heq
    rw [hpt t (hmem t ht).2, hpt t' (hmem t' ht').2] at heq
    exact a3y_pt_injective T t t' _ _ heq

/-- IntersectionProductSV: the iterated Tor pairing expands over the Serre
multiplicities of the first intersection. -/
theorem a3sv_iteratedTor_pair_cycle (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (u v w T : X.left)
    (huv : a3i_MeetProperly X.left u v)
    (hu : u ⤳ T) (hv : v ⤳ T) (hw : w ⤳ T)
    (hT : Order.coheight T = Order.coheight u + Order.coheight v + Order.coheight w)
    (hproper : ∀ D : PrimeSpectrum (X.left.presheaf.stalk T),
      a3i_stalkIdeal X.left T u ≤ D.asIdeal → a3i_stalkIdeal X.left T v ≤ D.asIdeal →
      a3i_stalkIdeal X.left T w ≤ D.asIdeal → D = IsLocalRing.closedPoint _)
    (m : ℕ) (hm : ringKrullDim (X.left.presheaf.stalk T) ≤ m) :
    (∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
      a3s_chi m (a3i_torModule X.left T u v i)
        (ModuleCat.of (X.left.presheaf.stalk T)
          (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T w))) =
      ∑ t ∈ a3y_compsAt X u v T, a3i_serreMult X.left t u v *
        a3s_chi m (ModuleCat.of (X.left.presheaf.stalk T)
          (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T t))
          (ModuleCat.of (X.left.presheaf.stalk T)
            (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T w)) := by
  classical
  have := a3c_isRegularLocalRing_stalk X T
  let A := X.left.presheaf.stalk T
  let U := ModuleCat.of A (A ⧸ a3i_stalkIdeal X.left T u)
  let V := ModuleCat.of A (A ⧸ a3i_stalkIdeal X.left T v)
  let W := ModuleCat.of A (A ⧸ a3i_stalkIdeal X.left T w)
  have hdev (i : ℕ) : a3s_chi m (a3i_torModule X.left T u v i) W =
      ∑ t ∈ a3y_compsAt X u v T,
        ((a3e_locLen (a3y_ptOr X T t) (a3i_torModule X.left T u v i)).toNat : ℤ) *
        a3s_chi m (ModuleCat.of A (A ⧸ a3i_stalkIdeal X.left T t)) W := by
    have : Module.Finite (X.left.presheaf.stalk T) (a3i_torModule X.left T u v i) :=
      a3e_tor_finite i U V
    apply a3sv_stalk_pair_devissage X u v w T huv hu hv hw hT hproper m hm
    intro P hP
    have h := a3s_annihilator_le_of_mem_support_tor U V i P hP
    simpa only [U, V, A, Ideal.annihilator_quotient] using h
  change (∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
    a3s_chi m (a3i_torModule X.left T u v i) W) = _
  simp only [hdev, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ∈ a3y_comps u v ∧ t ⤳ T := by
    simpa only [a3y_compsAt, Finset.mem_filter, Set.Finite.mem_toFinset] using ht
  obtain ⟨hut, hvt, _⟩ := a3y_comps_spec u v ht'.1
  have htm : Order.coheight t ≤ m := by
    have hle := Order.coheight_anti (Scheme.le_iff_specializes.mpr ht'.2)
    have hTm : Order.coheight T ≤ m := by
      rw [ringKrullDim_stalk_eq_coheight] at hm
      exact_mod_cast hm
    exact hle.trans hTm
  simp only [← mul_assoc, ← Finset.sum_mul]
  congr 1
  rw [a3y_serreMult_comp X ht'.2 hut hvt m htm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [a3y_ptOr, dite_eq_left ht'.2]
  rfl

/-- IntersectionProductSV: properness for one iterated intersection implies
properness for the other parenthesization. -/
theorem a3sv_meetProperly_components_left (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (u v w : X.left)
    (huv : a3i_MeetProperly X.left u v) (hvw : a3i_MeetProperly X.left v w)
    (ht : ∀ t ∈ a3y_comps v w, a3i_MeetProperly X.left u t)
    (s : X.left) (hs : s ∈ a3y_comps u v) : a3i_MeetProperly X.left s w := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  intro y hy
  apply le_antisymm (a3m_coheight_component_le_of_smooth X s w y hy)
  obtain ⟨hsy, hwy, _⟩ := a3m_component_spec s w y hy
  obtain ⟨hus, hvs, _⟩ := a3y_comps_spec u v hs
  rw [a3y_coheight_comps u v huv hs]
  exact a3sv_triple_coheight_le X.left u v w _ hvw ht
    (hus.trans hsy) (hvs.trans hsy) hwy

/-- IntersectionProductSV: the coefficient of an iterated proper cycle
intersection is a finite sum of products of Serre multiplicities. -/
theorem a3sv_pair_cycle_coeff_sum (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (u v w T : X.left)
    (huv : a3i_MeetProperly X.left u v)
    (htw : ∀ t ∈ a3y_comps u v, a3i_MeetProperly X.left t w)
    (hw : w ⤳ T)
    (hT : Order.coheight T = Order.coheight u + Order.coheight v + Order.coheight w) :
    (∑ᶠ t : X.left, a3i_intersectPrime X.left u v t * a3i_intersectPrime X.left t w T) =
      ∑ t ∈ a3y_compsAt X u v T,
        (a3i_serreMult X.left t u v : ℚ) * (a3i_serreMult X.left T t w : ℚ) := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := a3y_compsAt X u v T)]
  · apply Finset.sum_congr rfl
    intro t ht
    have ht' : t ∈ a3y_comps u v ∧ t ⤳ T := by
      simpa only [a3y_compsAt, Finset.mem_filter, Set.Finite.mem_toFinset] using ht
    have hfirst : a3i_intersectPrime X.left u v t = (a3i_serreMult X.left t u v : ℚ) := by
      rw [a3y_intersectPrime_apply]
      exact ite_eq_left ht'.1
    rw [hfirst, a3z_intersectPrime_apply_of_proper X.left t w T (htw t ht'.1) ht'.2 hw]
    rw [a3y_coheight_comps u v huv ht'.1, hT]
  · intro t ht
    have hne : a3i_intersectPrime X.left u v t ≠ 0 ∧
        a3i_intersectPrime X.left t w T ≠ 0 := mul_ne_zero_iff.mp ht
    have hc := a3z_intersectPrime_ne_zero X.left u v t hne.1
    have hspec := (a3y_comps_spec t w
      (a3z_intersectPrime_ne_zero X.left t w T hne.2)).1
    change t ∈ a3y_compsAt X u v T
    simp only [a3y_compsAt, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hc, hspec⟩

/-- IntersectionProductSV: the iterated Tor Euler pairing is associative
under proper common support. -/
theorem a3sv_iteratedTor_assoc {B : Type} [CommRing B] [IsRegularLocalRing B]
    (U V W : ModuleCat.{0} B) [Module.Finite B U] [Module.Finite B V] [Module.Finite B W]
    (m : ℕ) (hm : ringKrullDim B ≤ m)
    (hproper : ∀ P : PrimeSpectrum B, Module.annihilator B U ≤ P.asIdeal →
      Module.annihilator B V ≤ P.asIdeal → Module.annihilator B W ≤ P.asIdeal →
      P = IsLocalRing.closedPoint B) :
    (∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
      a3s_chi m (((Tor (ModuleCat.{0} B) i).obj U).obj V) W) =
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
      a3s_chi m (((Tor (ModuleCat.{0} B) i).obj V).obj W) U := by
  calc
    _ = ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        a3s_chi m (((Tor (ModuleCat.{0} B) i).obj V).obj U) W := by
      apply Finset.sum_congr rfl
      intro i hi
      obtain ⟨e⟩ := a3c_tor_symm U i V
      rw [a3s_chi_congr e W m]
    _ = _ := a3sv_iteratedTor_euler_exchange_supported W U V m hm
      (fun P hW hU hV => hproper P hU hV hW)

theorem a3i_serreMult_symm_aux (X : Scheme.{u}) (z u v : X) :
    a3i_serreMult X z u v = a3i_serreMult X z v u := by
  unfold a3i_serreMult a3i_torModule
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [a3c_length_tor_symm]

theorem a3i_intersectPrime_symm_aux (X : Scheme.{u}) (u v : X) :
    a3i_intersectPrime X u v = a3i_intersectPrime X v u := by
  classical
  have key : ∀ J K : X.IdealSheafData, J = K → ∀ m₁ m₂ : X → ℚ, m₁ = m₂ →
      (∑ᶠ y : J.subscheme, if closure ({y} : Set J.subscheme) ∈ irreducibleComponents J.subscheme
        then Function.locallyFinsuppWithin.single (J.subschemeι y) (m₁ (J.subschemeι y)) else 0) =
      ∑ᶠ y : K.subscheme, if closure ({y} : Set K.subscheme) ∈ irreducibleComponents K.subscheme
        then Function.locallyFinsuppWithin.single (K.subschemeι y) (m₂ (K.subschemeι y)) else 0 := by
    rintro J K rfl m _ rfl
    rfl
  exact key _ _ (sup_comm _ _) (fun z => ((a3i_serreMult X z u v : ℤ) : ℚ))
    (fun z => ((a3i_serreMult X z v u : ℤ) : ℚ)) (funext fun z => by rw [a3i_serreMult_symm_aux])

/-- IntersectionProductLoc2 S5: the local coefficient identity for three prime cycles.
The last premise imposes properness against every component of the second intersection. -/
theorem a3i_assoc_local (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (u v w z : X.left)
    (huv : a3i_MeetProperly X.left u v) (hvw : a3i_MeetProperly X.left v w)
    (huw : a3i_MeetProperly X.left u w)
    (ht : ∀ t : (ccm3_primeIdeal X.left v ⊔ ccm3_primeIdeal X.left w).subscheme,
      closure ({t} : Set (ccm3_primeIdeal X.left v ⊔ ccm3_primeIdeal X.left w).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left v ⊔ ccm3_primeIdeal X.left w).subscheme →
      a3i_MeetProperly X.left u
        ((ccm3_primeIdeal X.left v ⊔ ccm3_primeIdeal X.left w).subschemeι t)) :
    (∑ᶠ t : X.left, a3i_intersectPrime X.left u v t * a3i_intersectPrime X.left t w z) =
      ∑ᶠ t : X.left, a3i_intersectPrime X.left v w t * a3i_intersectPrime X.left u t z := by
  classical
  have ht' : ∀ t ∈ a3y_comps v w, a3i_MeetProperly X.left u t := by
    rintro t ⟨y, hy, rfl⟩
    exact ht y hy
  have htw := a3sv_meetProperly_components_left X u v w huv hvw ht'
  have htu : ∀ t ∈ a3y_comps v w, a3i_MeetProperly X.left t u :=
    fun t htmem => IntersectionProductRing.meetProperly_symm X.left u t (ht' t htmem)
  have hrhs : (∑ᶠ t : X.left,
      a3i_intersectPrime X.left v w t * a3i_intersectPrime X.left u t z) =
      ∑ᶠ t : X.left, a3i_intersectPrime X.left v w t * a3i_intersectPrime X.left t u z := by
    apply finsum_congr
    intro t
    rw [a3i_intersectPrime_symm_aux X.left u t]
  rw [hrhs]
  by_cases hg : u ⤳ z ∧ v ⤳ z ∧ w ⤳ z ∧
      Order.coheight z = Order.coheight u + Order.coheight v + Order.coheight w
  · obtain ⟨hu, hv, hw, hdim⟩ := hg
    have := a3c_isRegularLocalRing_stalk X z
    let A := X.left.presheaf.stalk z
    let U := ModuleCat.of A (A ⧸ a3i_stalkIdeal X.left z u)
    let V := ModuleCat.of A (A ⧸ a3i_stalkIdeal X.left z v)
    let W := ModuleCat.of A (A ⧸ a3i_stalkIdeal X.left z w)
    let m := (Order.coheight z).toNat
    have hzm : Order.coheight z = (m : ℕ∞) :=
      (ENat.natCast_toNat (a3c_coheight_ne_top X.left z)).symm
    have hm : ringKrullDim A ≤ m := by
      change ringKrullDim (X.left.presheaf.stalk z) ≤ m
      rw [ringKrullDim_stalk_eq_coheight, hzm]
      rfl
    have hp := a3sv_triple_stalk_support X.left u v w z hvw ht' hu hv hw hdim
    have hp' : ∀ P : PrimeSpectrum A, Module.annihilator A U ≤ P.asIdeal →
        Module.annihilator A V ≤ P.asIdeal → Module.annihilator A W ≤ P.asIdeal →
        P = IsLocalRing.closedPoint A := by
      simpa only [U, V, W, A, Ideal.annihilator_quotient] using hp
    have hd' : Order.coheight z = Order.coheight v + Order.coheight w + Order.coheight u := by
      simpa only [add_comm, add_left_comm, add_assoc] using hdim
    have he₁ := a3sv_iteratedTor_pair_cycle X u v w z huv hu hv hw hdim hp m hm
    have he₂ := a3sv_iteratedTor_pair_cycle X v w u z hvw hv hw hu hd'
      (fun P hV hW hU => hp P hU hV hW) m hm
    have ha := a3sv_iteratedTor_assoc U V W m hm hp'
    change (∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
      a3s_chi m (a3i_torModule X.left z u v i) W) =
      ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        a3s_chi m (a3i_torModule X.left z v w i) U at ha
    rw [he₁, he₂] at ha
    change (∑ t ∈ a3y_compsAt X u v z,
      a3i_serreMult X.left t u v * a3i_serreMult X.left z t w) =
      ∑ t ∈ a3y_compsAt X v w z,
        a3i_serreMult X.left t v w * a3i_serreMult X.left z t u at ha
    rw [a3sv_pair_cycle_coeff_sum X u v w z huv htw hw hdim,
      a3sv_pair_cycle_coeff_sum X v w u z hvw htu hu hd']
    exact_mod_cast ha
  · have hz₁ : ∀ t : X.left,
        a3i_intersectPrime X.left u v t * a3i_intersectPrime X.left t w z = 0 := by
      intro t
      by_contra hn
      obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hn
      have hc₁ := a3z_intersectPrime_ne_zero X.left u v t h₁
      have hc₂ := a3z_intersectPrime_ne_zero X.left t w z h₂
      obtain ⟨hut, hvt, _⟩ := a3y_comps_spec u v hc₁
      obtain ⟨htz, hwz, _⟩ := a3y_comps_spec t w hc₂
      apply hg
      refine ⟨hut.trans htz, hvt.trans htz, hwz, ?_⟩
      rw [a3y_coheight_comps t w (htw t hc₁) hc₂,
        a3y_coheight_comps u v huv hc₁]
    have hz₂ : ∀ t : X.left,
        a3i_intersectPrime X.left v w t * a3i_intersectPrime X.left t u z = 0 := by
      intro t
      by_contra hn
      obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hn
      have hc₁ := a3z_intersectPrime_ne_zero X.left v w t h₁
      have hc₂ := a3z_intersectPrime_ne_zero X.left t u z h₂
      obtain ⟨hvt, hwt, _⟩ := a3y_comps_spec v w hc₁
      obtain ⟨htz, huz, _⟩ := a3y_comps_spec t u hc₂
      apply hg
      refine ⟨huz, hvt.trans htz, hwt.trans htz, ?_⟩
      rw [a3y_coheight_comps t u (htu t hc₁) hc₂,
        a3y_coheight_comps v w hvw hc₁]
      ac_rfl
    rw [finsum_eq_zero_of_forall_eq_zero hz₁, finsum_eq_zero_of_forall_eq_zero hz₂]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: restriction along a flat local map weights every
Tor length by the residue-field degree. -/
theorem a3sv_tor_length_restrictScalars {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] (hf : (algebraMap A B).Flat)
    (M : ModuleCat.{u} B) (N : ModuleCat.{u} A) (i : ℕ) :
    Module.length A (((Tor (ModuleCat.{u} A) i).obj
      ((ModuleCat.restrictScalars (algebraMap A B)).obj M)).obj N) =
      Module.length B (((Tor (ModuleCat.{u} B) i).obj M).obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj N)) *
        Module.length (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
  obtain ⟨e⟩ := a3f_tor_restrict (algebraMap A B) hf M N i
  rw [← e.toLinearEquiv.length_eq]
  let T := ((Tor (ModuleCat.{u} B) i).obj M).obj
    ((ModuleCat.extendScalars (algebraMap A B)).obj N)
  letI : Module A T := Module.compHom T (algebraMap A B)
  letI : IsScalarTower A B T := ⟨fun a b t => by
    change (a • b) • t = (algebraMap A B a) • (b • t)
    rw [Algebra.smul_def, mul_smul]⟩
  exact IsLocalRing.length_restrictScalars A B T

/-- IntersectionProductSV: the Tor Euler pairing transforms under a flat
local map by the residue-field degree. -/
theorem a3sv_chi_restrictScalars {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] (hf : (algebraMap A B).Flat)
    (M : ModuleCat.{u} B) (N : ModuleCat.{u} A) (m : ℕ) :
    a3s_chi m ((ModuleCat.restrictScalars (algebraMap A B)).obj M) N =
      a3s_chi m M ((ModuleCat.extendScalars (algebraMap A B)).obj N) *
        ((Module.length (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B)).toNat : ℤ) := by
  unfold a3s_chi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [a3sv_tor_length_restrictScalars hf M N i, ENat.toNat_mul, Nat.cast_mul, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the flat stalk Tor pairing transforms with the
residue degree used in cycle pushforward. -/
theorem a3sv_chi_stalk_restrictScalars {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (x : X) (M : ModuleCat.{u} (X.presheaf.stalk x))
    (N : ModuleCat.{u} (Y.presheaf.stalk (f x))) (m : ℕ) :
    a3s_chi m ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj M) N =
      a3s_chi m M ((ModuleCat.extendScalars (f.stalkMap x).hom).obj N) *
        (a1p_degree f x : ℤ) := by
  letI := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have h := a3sv_chi_restrictScalars (A := Y.presheaf.stalk (f x))
    (B := X.presheaf.stalk x) (Flat.stalkMap f x) M N m
  have hmod : (f.residueFieldMap x).hom.toAlgebra.toModule =
      (inferInstance : Module (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
        (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
    apply Module.ext
    funext a b
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := Y.presheaf.stalk (f x)) a
    rfl
  have hd : (Module.length (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x))).toNat = a1p_degree f x := by
    rw [Module.length_eq_rank, Cardinal.toNat_toENat]
    unfold a1p_degree Module.finrank
    rw [hmod]
    rfl
  rw [hd] at h
  exact h

/-- IntersectionProductSV: length after restriction of scalars decomposes over
an antichain containing the support of a finite module. -/
theorem a3sv_length_restrictScalars_sum {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing B] (f : A →+* B) (F : Finset (PrimeSpectrum B))
    (hF : ∀ P ∈ F, ∀ Q ∈ F, P ≤ Q → P = Q)
    (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hM : Module.support B M ⊆ (F : Set (PrimeSpectrum B))) :
    @Module.length A M _ _ (Module.compHom M f) =
      ∑ P ∈ F, a3e_locLen P M *
        @Module.length A (B ⧸ P.asIdeal) _ _ (Module.compHom (B ⧸ P.asIdeal) f) := by
  classical
  revert hM
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime B
    (inferInstance : Module.Finite B M)
    (motive := fun X _ _ _ => Module.support B X ⊆ (F : Set (PrimeSpectrum B)) →
      @Module.length A X _ _ (Module.compHom X f) =
        ∑ P ∈ F, a3e_locLen P X *
          @Module.length A (B ⧸ P.asIdeal) _ _ (Module.compHom (B ⧸ P.asIdeal) f)) ?_ ?_ ?_
  · intro X _ _ _ _ _
    have hz : ∀ P : PrimeSpectrum B, a3e_locLen P X = 0 := fun _ => Module.length_eq_zero
    simp [hz, Module.length_eq_zero]
  · intro X _ _ _ Q e hX
    letI : Module A X := Module.compHom X f
    letI : Module A (B ⧸ Q.asIdeal) := Module.compHom (B ⧸ Q.asIdeal) f
    have hQ : Q ∈ Module.support B X := by
      rw [e.support_eq, Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
    have he : @Module.length A X _ _ (Module.compHom X f) =
        @Module.length A (B ⧸ Q.asIdeal) _ _ (Module.compHom (B ⧸ Q.asIdeal) f) :=
      (show X ≃ₗ[A] (B ⧸ Q.asIdeal) from
        { e.toAddEquiv with map_smul' := fun a x => e.map_smul (f a) x }).length_eq
    rw [he]
    simp only [a3e_locLen_congr _ e]
    rw [Finset.sum_eq_single Q]
    · rw [a3e_locLen_quotient_self, one_mul]
    · intro P hP hne
      have hnle : ¬ Q ≤ P := fun h => hne (hF Q (hX hQ) P hP h).symm
      obtain ⟨s, hs, hs'⟩ := Set.not_subset.mp hnle
      rw [a3e_locLen_eq_zero P (B ⧸ Q.asIdeal) s hs']
      · exact zero_mul _
      · intro x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
          Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ hs
    · exact fun h => False.elim (h (hX hQ))
  · intro X₁ _ _ _ X₂ _ _ _ X₃ _ _ _ g h hg hh hex h₁ h₃ hX
    letI : Module A X₁ := Module.compHom X₁ f
    letI : Module A X₂ := Module.compHom X₂ f
    letI : Module A X₃ := Module.compHom X₃ f
    let g' : X₁ →ₗ[A] X₂ := { g.toAddHom with map_smul' := fun a x => g.map_smul (f a) x }
    let h' : X₂ →ₗ[A] X₃ := { h.toAddHom with map_smul' := fun a x => h.map_smul (f a) x }
    have e₁ := h₁ ((Module.support_subset_of_injective g hg).trans hX)
    have e₃ := h₃ ((Module.support_subset_of_surjective h hh).trans hX)
    rw [Module.length_eq_add_of_exact g' h' hg hh hex,
      e₁, e₃, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun P _ => by rw [a3e_locLen_ses P g h hg hh hex, add_mul]

/-- IntersectionProductSV: finite modules supported on incomparable primes have finite length. -/
theorem a3sv_length_ne_top_of_antichain_support {B : Type u} [CommRing B]
    [IsNoetherianRing B] (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hM : ∀ P ∈ Module.support B M, ∀ Q ∈ Module.support B M, P ≤ Q → P = Q) :
    Module.length B M ≠ ⊤ := by
  rw [Module.length_ne_top_iff]
  apply a3c_isFiniteLength_of_supportDim_le_zero
  apply Order.krullDim_nonpos_iff_forall_isMax.mpr
  intro P Q hPQ
  have h := hM P P.2 Q Q.2 hPQ
  exact le_of_eq (Subtype.ext h.symm)

/-- IntersectionProductSV: localized lengths are finite on finite antichain support. -/
theorem a3sv_locLen_ne_top_of_antichain_support {B : Type u} [CommRing B]
    [IsNoetherianRing B] (F : Finset (PrimeSpectrum B))
    (hF : ∀ P ∈ F, ∀ Q ∈ F, P ≤ Q → P = Q)
    (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hM : Module.support B M ⊆ (F : Set (PrimeSpectrum B)))
    (P : PrimeSpectrum B) (hP : P ∈ F) : a3e_locLen P M ≠ ⊤ := by
  have hlen := a3sv_length_ne_top_of_antichain_support M
    (fun P hP Q hQ => hF P (hM hP) Q (hM hQ))
  have hid := a3sv_length_restrictScalars_sum (RingHom.id B) F hF M hM
  change Module.length B M =
    ∑ Q ∈ F, a3e_locLen Q M * Module.length B (B ⧸ Q.asIdeal) at hid
  apply ne_top_of_le_ne_top hlen
  calc
    a3e_locLen P M ≤ a3e_locLen P M * Module.length B (B ⧸ P.asIdeal) :=
      ENat.self_le_mul_right _ Module.length_pos.ne'
    _ ≤ ∑ Q ∈ F, a3e_locLen Q M * Module.length B (B ⧸ Q.asIdeal) :=
      Finset.single_le_sum (f := fun Q : PrimeSpectrum B =>
        a3e_locLen Q M * Module.length B (B ⧸ Q.asIdeal)) (fun Q _ => bot_le) hP
    _ = Module.length B M := hid.symm

/-- IntersectionProductSV: finite restricted lengths give a natural-number
sum of local multiplicities weighted by quotient lengths. -/
theorem a3sv_length_restrictScalars_toNat_sum {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing B] (f : A →+* B) (F : Finset (PrimeSpectrum B))
    (hF : ∀ P ∈ F, ∀ Q ∈ F, P ≤ Q → P = Q)
    (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hM : Module.support B M ⊆ (F : Set (PrimeSpectrum B)))
    (hlen : @Module.length A M _ _ (Module.compHom M f) ≠ ⊤) :
    (@Module.length A M _ _ (Module.compHom M f)).toNat =
      ∑ P ∈ F, (a3e_locLen P M).toNat *
        (@Module.length A (B ⧸ P.asIdeal) _ _ (Module.compHom (B ⧸ P.asIdeal) f)).toNat := by
  have he := a3sv_length_restrictScalars_sum f F hF M hM
  rw [he] at hlen ⊢
  rw [ENat.toNat_sum (ENat.sum_ne_top.mp hlen)]
  simp only [ENat.toNat_mul]

/-- IntersectionProductSV: the quotient length at a maximal prime is the
residue-field length for the associated local ring map. -/
theorem a3sv_quotient_length_residue {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [Algebra A B] (P : Ideal B) [P.IsMaximal]
    [IsLocalHom (algebraMap A (Localization.AtPrime P))] :
    Module.length A (B ⧸ P) =
      Module.length (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (Localization.AtPrime P)) := by
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)
  have he := (e.restrictScalars A).toLinearEquiv.length_eq
  change Module.length A (B ⧸ P) = Module.length A (IsLocalRing.ResidueField (Localization.AtPrime P)) at he
  have hl : Module.length (Localization.AtPrime P) (IsLocalRing.ResidueField (Localization.AtPrime P)) = 1 := by
    rw [Module.length_eq_of_surjective (R := IsLocalRing.ResidueField (Localization.AtPrime P))
      (IsLocalRing.residue_surjective (R := Localization.AtPrime P))]
    exact Module.length_eq_one _ _
  rw [he, IsLocalRing.length_restrictScalars A (Localization.AtPrime P), hl, one_mul]

/-- IntersectionProductSV: restriction of scalars expresses the Euler characteristic
as the sum of localized homology-cycle coefficients with quotient-length weights. -/
theorem a3sv_complexEuler_restrictScalars_sum {A B : Type} [CommRing A] [CommRing B]
    [IsNoetherianRing B] (f : A →+* B) (F : Finset (PrimeSpectrum B))
    (hF : ∀ P ∈ F, ∀ Q ∈ F, P ≤ Q → P = Q)
    (C : ChainComplex (ModuleCat.{0} B) ℕ) (m : ℕ)
    (hfinite : ∀ i, Module.Finite B (C.homology i))
    (hsupport : ∀ i ≤ m, Module.support B (C.homology i) ⊆ (F : Set (PrimeSpectrum B)))
    (hlen : ∀ i ≤ m, Module.length A
      ((ModuleCat.restrictScalars f).obj (C.homology i)) ≠ ⊤) :
    a3i_complexEuler m (((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj C) =
      ∑ P ∈ F, a3i_complexCycleCoeff m C P *
        ((@Module.length A (B ⧸ P.asIdeal) _ _
          (Module.compHom (B ⧸ P.asIdeal) f)).toNat : ℤ) := by
  have hlen_eq (i : ℕ) :
      Module.length A ((((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj C).homology i) =
        Module.length A ((ModuleCat.restrictScalars f).obj (C.homology i)) :=
    ((C.sc i).mapHomologyIso (ModuleCat.restrictScalars f)).toLinearEquiv.length_eq
  unfold a3i_complexEuler a3i_complexCycleCoeff
  simp only [hlen_eq, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have := hfinite i
  have he := a3sv_length_restrictScalars_toNat_sum f F hF (C.homology i)
    (hsupport i hi') (hlen i hi')
  change (Module.length A ((ModuleCat.restrictScalars f).obj (C.homology i))).toNat = _ at he
  rw [he]
  simp only [Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun P _ => by ring

/-- IntersectionProductSV: a prime over the maximal ideal gives a local map
from the base ring to the localization. -/
theorem a3sv_isLocalHom_atPrime {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [Algebra A B] (P : Ideal B) [P.IsPrime]
    (hP : P.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) :
    IsLocalHom (algebraMap A (Localization.AtPrime P)) := by
  apply (IsLocalRing.isLocalHom_iff_comap_closedPoint _).mpr
  apply PrimeSpectrum.ext
  change (IsLocalRing.maximalIdeal (Localization.AtPrime P)).comap
    (algebraMap A (Localization.AtPrime P)) = IsLocalRing.maximalIdeal A
  rw [IsScalarTower.algebraMap_eq A B (Localization.AtPrime P), ← Ideal.comap_comap]
  change ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).under B).comap (algebraMap A B) = _
  rw [IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P, hP]

/-- IntersectionProductSV: a point of positive residue degree is a closed
point of its fiber under a separated morphism. -/
theorem a3sv_isClosed_asFiber_of_degree_pos {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] (x : X) (hx : 0 < a1p_degree f x) : IsClosed {f.asFiber x} := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  haveI : Module.Finite (Y.residueField (f x)) (X.residueField x) :=
    Module.finite_of_finrank_pos hx
  haveI : IsFinite (Spec.map (f.residueFieldMap x)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  haveI : IsProper (f.asFiberHom x ≫ f.fiberToSpecResidueField _) := by
    rw [f.asFiberHom_fiberToSpecResidueField]
    infer_instance
  haveI : IsSeparated (f.fiberToSpecResidueField (f x)) := by
    change IsSeparated (CategoryTheory.Limits.pullback.snd f (Y.fromSpecResidueField (f x)))
    infer_instance
  haveI : IsProper (f.asFiberHom x) := IsProper.of_comp _ (f.fiberToSpecResidueField _)
  rw [← f.range_asFiberHom x]
  exact (f.asFiberHom x).isClosedMap.isClosed_range

/-- IntersectionProductSV: a closed point with no proper generalization in a
Noetherian sober space is isolated. -/
theorem a3sv_isOpen_singleton_of_no_generalization {T : Type*} [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] [QuasiSober T] (x : T) (hc : IsClosed ({x} : Set T))
    (hm : ∀ y : T, y ⤳ x → y = x) : IsOpen ({x} : Set T) := by
  have hg := (isIrreducible_irreducibleComponent (x := x)).isGenericPoint_genericPoint
    isClosed_irreducibleComponent
  have he := hm _ (hg.specializes mem_irreducibleComponent)
  have hcomp : irreducibleComponent x = {x} := by
    rw [← hg.def, he, hc.closure_eq]
  obtain ⟨U, hU, ⟨y, hy⟩, hsub⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)
  rw [hcomp] at hsub
  have hyx : y = x := hsub hy
  subst y
  have hUeq : U = {x} := hsub.antisymm (Set.singleton_subset_iff.mpr hy)
  rwa [hUeq] at hU

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: a quasi-finite point has positive residue degree. -/
theorem a3sv_degree_pos_of_quasiFiniteAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (hx : f.QuasiFiniteAt x) : 0 < a1p_degree f x := by
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  letI : Algebra A B := (f.stalkMap x).hom.toAlgebra
  haveI : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  haveI : Algebra.QuasiFinite A B := RingHom.quasiFinite_algebraMap.mp hx
  haveI : Algebra.QuasiFinite A (IsLocalRing.ResidueField B) :=
    inferInstanceAs (Algebra.QuasiFinite A (B ⧸ IsLocalRing.maximalIdeal B))
  haveI : Algebra.QuasiFinite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    Algebra.QuasiFinite.of_restrictScalars A _ _
  haveI : Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    Module.Finite.of_quasiFinite
  have hmod : (f.residueFieldMap x).hom.toAlgebra.toModule =
      (inferInstance : Module (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) := by
    apply Module.ext
    funext a b
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) a
    rfl
  unfold a1p_degree Module.finrank
  rw [hmod]
  exact Module.finrank_pos (R := IsLocalRing.ResidueField A) (M := IsLocalRing.ResidueField B)

/-- IntersectionProductSV: every point in a prime pullback cycle maps to a
specialization of that prime. -/
theorem a3sv_flatPullback_specializes {X Y : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (v : Y.left) (w : X.left)
    (hw : ccm3_flatPullbackPrime f.left v w ≠ 0) : v ⤳ f.left w := by
  obtain ⟨y, rfl, _⟩ := (ccm3_flatPullbackPrime_support_aux f v w).mp hw
  have hy : y.val ∈
      (ccm3_inverseIdeal f.left v).support := y.property
  have hs := Scheme.IdealSheafData.support_comap (ccm3_primeIdeal Y.left v) f.left
  change (ccm3_inverseIdeal f.left v).support = _ at hs
  exact specializes_iff_mem_closure.mpr (hs.le hy)

/-- IntersectionProductSV: a point over the closure of a prime specializes
from a component with nonzero pullback coefficient. -/
theorem a3sv_exists_pullback_component {X Y : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (v : Y.left) (x : X.left) (hx : v ⤳ f.left x) :
    ∃ w : X.left, ccm3_flatPullbackPrime f.left v w ≠ 0 ∧ w ⤳ x := by
  have hx' : x ∈ (ccm3_inverseIdeal f.left v).support := by
    rw [ccm3_inverseIdeal, Scheme.IdealSheafData.support_comap]
    exact specializes_iff_mem_closure.mp hx
  let x' : (ccm3_inverseIdeal f.left v).subscheme := ⟨x, hx'⟩
  let C : irreducibleComponents (ccm3_inverseIdeal f.left v).subscheme :=
    ⟨irreducibleComponent x', irreducibleComponent_mem_irreducibleComponents x'⟩
  let w := genericPoints.ofComponent C
  refine ⟨(ccm3_inverseIdeal f.left v).subschemeι w.1,
    (ccm3_flatPullbackPrime_support_aux f v _).mpr ⟨w.1, rfl, w.2⟩, ?_⟩
  exact ((genericPoints.isGenericPoint_ofComponent C).specializes
    (show x' ∈ (C : Set _) from mem_irreducibleComponent)).map
      (ccm3_inverseIdeal f.left v).subschemeι.continuous

/-- IntersectionProductSV: a fiber-minimal point of positive degree is
quasi-finite on a Noetherian source. -/
theorem a3sv_quasiFiniteAt_of_fiber_minimal {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsSeparated f] (x : X)
    (hx : 0 < a1p_degree f x)
    (hm : ∀ y : X, f y = f x → y ⤳ x → y = x) : f.QuasiFiniteAt x := by
  letI : TopologicalSpace.NoetherianSpace (f.fiber (f x)) :=
    (f.fiberι (f x)).isEmbedding.isInducing.noetherianSpace
  apply Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr
  apply a3sv_isOpen_singleton_of_no_generalization _
    (a3sv_isClosed_asFiber_of_degree_pos f x hx)
  intro y hy
  apply (f.fiberι (f x)).isEmbedding.injective
  rw [f.fiberι_asFiber]
  apply hm
  · exact (f.fiberHomeo (f x) y).property
  · simpa only [f.fiberι_asFiber] using hy.map (f.fiberι (f x)).continuous

/-- IntersectionProductSV: properness against every pullback component makes
an expected-codimension intersection point minimal in the whole inverse image. -/
theorem a3sv_pullback_intersection_minimal {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] (u : X.left) (v : Y.left) (t : X.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (ht : Order.coheight t = Order.coheight u + Order.coheight v)
    (q : X.left) (huq : u ⤳ q) (hvq : v ⤳ f.left q) (hqt : q ⤳ t) : q = t := by
  obtain ⟨w, hw, hwq⟩ := a3sv_exists_pullback_component f v q hvq
  obtain ⟨s, hs, hsq⟩ := a3y_exists_comp u w huq hwq
  have hwcodim : Order.coheight w = Order.coheight v := by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (a3c_coheight_ne_top Y.left v)
    rw [← hn]
    exact ccm3_flatPullbackPrime_codimension_aux f n v hn.symm w hw
  have hst : s = t := a3y_eq_of_specializes (hsq.trans hqt) (by
    rw [a3y_coheight_comps u w (hp w hw) hs, hwcodim, ht])
  subst s
  exact (hqt.antisymm hsq).eq

/-- IntersectionProductSV: a positive-degree point of a proper pullback
intersection forces the source prime to have positive degree. -/
theorem a3sv_degree_pos_of_proper_pullback_point {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] [IsProper f.left]
    (u : X.left) (v : Y.left) (t : X.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (hut : u ⤳ t) (hvt : v ⤳ f.left t)
    (ht : Order.coheight t = Order.coheight u + Order.coheight v)
    (hd : 0 < a1p_degree f.left t) : 0 < a1p_degree f.left u := by
  obtain ⟨tU, htU⟩ := a3z_exists_pt u hut
  let ι := cycleComponentι X.left u
  let j : a3m_component X u ⟶ X := Over.homMk ι rfl
  let g : a3m_component X u ⟶ Y := j ≫ f
  haveI : IsProper g.left := by
    change IsProper (cycleComponentι X.left u ≫ f.left)
    infer_instance
  have hgt : 0 < a1p_degree g.left tU := by
    apply (a1d_degree_pos_iff g tU).mpr
    change Order.height (f.left (ι tU)) = Order.height tU
    rw [show ι tU = t from htU, (a1d_degree_pos_iff f t).mp hd]
    rw [← htU]
    exact a3m_height_cycleComponentι X.left u tU
  have hg : g.left.QuasiFiniteAt tU := by
    apply a3sv_quasiFiniteAt_of_fiber_minimal g.left tU hgt
    intro y hgy hyt
    apply ι.isClosedEmbedding.injective
    have huy : u ⤳ ι y := by
      have h := ((genericPoint_spec (cycleComponent X.left u)).specializes
        (Set.mem_univ y)).map ι.continuous
      simpa only [ι, a3m_cycleComponentι_genericPoint] using h
    have hvy : v ⤳ f.left (ι y) := by
      have he : f.left (ι y) = f.left t := by
        change f.left (ι y) = f.left (ι tU) at hgy
        simpa only [show ι tU = t from htU] using hgy
      rw [he]
      exact hvt
    have hyit : ι y ⤳ t := by
      simpa only [show ι tU = t from htU] using hyt.map ι.continuous
    exact (a3sv_pullback_intersection_minimal f u v t hp ht (ι y) huy hvy hyit).trans htU.symm
  have hgen : g.left.QuasiFiniteAt (genericPoint (cycleComponent X.left u)) :=
    ((genericPoint_spec (cycleComponent X.left u)).specializes (Set.mem_univ tU)).mem_open
      g.left.isOpen_quasiFiniteAt hg
  have hpos := a3sv_degree_pos_of_quasiFiniteAt g.left _ hgen
  change 0 < a1p_degree (ι ≫ f.left) (genericPoint (cycleComponent X.left u)) at hpos
  rw [a1p_degree_comp_aux, a3m_cycleComponentι_genericPoint] at hpos
  by_contra hzero
  have hz : a1p_degree f.left u = 0 := Nat.eq_zero_of_not_pos hzero
  simp only [hz, zero_mul, lt_self_iff_false] at hpos

/-- IntersectionProductSV: a contracted prime has no nonzero degree-weighted
coefficient in its proper intersection with a prime pullback. -/
theorem a3sv_weighted_pullback_intersect_eq_zero_of_degree_zero
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] [IsProper f.left] (u : X.left) (v : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (hu0 : a1p_degree f.left u = 0) (w t : X.left) :
    ccm3_flatPullbackPrime f.left v w * a3i_intersectPrime X.left u w t *
      (a1p_degree f.left t : ℚ) = 0 := by
  by_cases hw : ccm3_flatPullbackPrime f.left v w = 0
  · simp only [hw, zero_mul]
  by_cases hi : a3i_intersectPrime X.left u w t = 0
  · simp only [hi, mul_zero, zero_mul]
  by_cases hd : a1p_degree f.left t = 0
  · simp only [hd, Nat.cast_zero, mul_zero]
  have hcomp := a3z_intersectPrime_ne_zero X.left u w t hi
  obtain ⟨hut, hwt, _⟩ := a3y_comps_spec u w hcomp
  have hvt := (a3sv_flatPullback_specializes f v w hw).trans (hwt.map f.left.continuous)
  have ht : Order.coheight t = Order.coheight u + Order.coheight v := by
    rw [a3y_coheight_comps u w (hp w hw) hcomp]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (a3c_coheight_ne_top Y.left v)
    rw [ccm3_flatPullbackPrime_codimension_aux f n v hn.symm w hw, hn]
  have hpos := a3sv_degree_pos_of_proper_pullback_point f u v t hp hut hvt ht
    (Nat.pos_of_ne_zero hd)
  simp only [hu0, lt_self_iff_false] at hpos

/-- IntersectionProductSV: the prime projection coefficient identity when
the source prime is contracted. -/
theorem a3sv_proper_pushforward_mult_of_degree_zero {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    [IsProjective Y.hom] (f : X ⟶ Y) [Flat f.left] [IsProper f.left]
    (u : X.left) (v z : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (hu0 : a1p_degree f.left u = 0) :
    (∑ᶠ t : f.left ⁻¹' {z},
      (∑ᶠ w : X.left, ccm3_flatPullbackPrime f.left v w * a3i_intersectPrime X.left u w t) *
        (a1p_degree f.left t : ℚ)) =
      (a1p_degree f.left u : ℚ) * a3i_intersectPrime Y.left (f.left u) v z := by
  rw [hu0, Nat.cast_zero, zero_mul]
  apply finsum_eq_zero_of_forall_eq_zero
  intro t
  rw [finsum_mul]
  exact finsum_eq_zero_of_forall_eq_zero fun w =>
    a3sv_weighted_pullback_intersect_eq_zero_of_degree_zero f u v hp hu0 w t


/-- IntersectionProductSV: a finite-type morphism over the ground field cannot
increase the dimension of the closure of a point. -/
theorem a3sv_height_image_le {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (x : X.left) :
    Order.height (f.left x) ≤ Order.height x := by
  let : Algebra ℂ (X.left.residueField x) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appTop ≫ X.left.Γevaluation x).hom.toAlgebra
  let : Algebra ℂ (Y.left.residueField (f.left x)) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ Y.hom.appTop ≫
      Y.left.Γevaluation (f.left x)).hom.toAlgebra
  let : Algebra (Y.left.residueField (f.left x)) (X.left.residueField x) :=
    (f.left.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower ℂ (Y.left.residueField (f.left x)) (X.left.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = f.left.residueFieldMap x (Y.left.Γevaluation (f.left x) (Y.hom.appTop _))
    rw [Scheme.Γevaluation_naturality_apply]
    change _ = X.left.Γevaluation x ((Y.hom.appTop ≫ f.left.appTop) _)
    rw [← Scheme.Hom.comp_appTop, Over.w f]
    rfl
  obtain ⟨hfg, n, hn, htr⟩ := a1d_height_eq_trdeg x
  obtain ⟨-, m, hm, htr'⟩ := a1d_height_eq_trdeg (f.left x)
  have hadd := trdeg_add_eq ℂ (Y.left.residueField (f.left x)) (A := X.left.residueField x)
  rw [htr, htr'] at hadd
  rw [hn, hm]
  have hle : (m : Cardinal) ≤ n := le_self_add.trans hadd.le
  exact_mod_cast hle

/-- IntersectionProductSV: a codimension increment subtracts the same amount
from the dimension of a prime closure. -/
theorem a3sv_height_add_of_coheight_add (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [LocallyOfFiniteType X.hom] (u t : X.left) (c : ℕ∞)
    (ht : Order.coheight t = Order.coheight u + c) :
    Order.height t + c = Order.height u := by
  have he : (Order.height t + c) + Order.coheight u =
      Order.height u + Order.coheight u := by
    calc
      (Order.height t + c) + Order.coheight u = Order.height t + Order.coheight t := by
        rw [ht]
        ac_rfl
      _ = Order.height u + Order.coheight u :=
        (a3m_height_add_coheight X t).trans (a3m_height_add_coheight X u).symm
  have hfin := a3c_coheight_ne_top X.left u
  exact le_antisymm ((ENat.add_le_add_iff_right hfin).mp he.le)
    ((ENat.add_le_add_iff_right hfin).mp he.ge)

/-- IntersectionProductSV: a dimension bound for a common specialization
translates into the corresponding codimension bound. -/
theorem a3sv_coheight_add_le_of_height_add_le (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [LocallyOfFiniteType X.hom] (u t : X.left) (c : ℕ∞)
    (ht : Order.height t + c ≤ Order.height u) :
    Order.coheight u + c ≤ Order.coheight t := by
  obtain ⟨_, n, hn, _⟩ := a1d_height_eq_trdeg t
  have hfin : Order.height t ≠ ⊤ := by rw [hn]; exact ENat.natCast_ne_top n
  apply (ENat.add_le_add_iff_left hfin).mp
  calc
    Order.height t + (Order.coheight u + c) =
        (Order.height t + c) + Order.coheight u := by ac_rfl
    _ ≤ Order.height u + Order.coheight u := add_le_add ht le_rfl
    _ = Order.height t + Order.coheight t :=
      (a3m_height_add_coheight X u).trans (a3m_height_add_coheight X t).symm

/-- IntersectionProductSV: proper maps lift specializations from the image of
a point to its closure. -/
theorem a3sv_lift_specialization_of_proper {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (u : X) (z : Y) (hz : f u ⤳ z) :
    ∃ t : X, u ⤳ t ∧ f t = z := by
  have hz' : z ∈ closure (f '' ({u} : Set X)) := by
    simpa only [Set.image_singleton] using specializes_iff_mem_closure.mp hz
  obtain ⟨t, ht, hft⟩ := f.isClosedMap.closure_image_subset {u} hz'
  exact ⟨t, specializes_iff_mem_closure.mpr ht, hft⟩

/-- IntersectionProductSV: proper intersection with all pullback components
bounds the dimension of every image point in that intersection. -/
theorem a3sv_height_common_pullback_le {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] (u : X.left) (v : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (q : X.left) (huq : u ⤳ q) (hvq : v ⤳ f.left q) :
    Order.height (f.left q) + Order.coheight v ≤ Order.height u := by
  obtain ⟨w, hw, hwq⟩ := a3sv_exists_pullback_component f v q hvq
  obtain ⟨s, hs, hsq⟩ := a3y_exists_comp u w huq hwq
  have hcs : Order.coheight s = Order.coheight u + Order.coheight v := by
    rw [a3y_coheight_comps u w (hp w hw) hs]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (a3c_coheight_ne_top Y.left v)
    rw [ccm3_flatPullbackPrime_codimension_aux f n v hn.symm w hw, hn]
  calc
    Order.height (f.left q) + Order.coheight v ≤ Order.height q + Order.coheight v :=
      add_le_add (a3sv_height_image_le f q) le_rfl
    _ ≤ Order.height s + Order.coheight v :=
      add_le_add (Order.height_mono (Scheme.le_iff_specializes.mpr hsq)) le_rfl
    _ = Order.height u := a3sv_height_add_of_coheight_add X u s _ hcs

/-- IntersectionProductSV: properness of the source pullback intersections
descends to the image prime when its residue degree is positive. -/
theorem a3sv_image_meetProperly {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] [IsProper f.left] (u : X.left) (v : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (hd : 0 < a1p_degree f.left u) : a3i_MeetProperly Y.left (f.left u) v := by
  intro z hz
  apply le_antisymm (a3m_coheight_component_le_of_smooth Y (f.left u) v z hz)
  obtain ⟨huz, hvz, _⟩ := a3m_component_spec (f.left u) v z hz
  obtain ⟨q, huq, hfq⟩ := a3sv_lift_specialization_of_proper f.left u _ huz
  have hvq : v ⤳ f.left q := hfq.symm ▸ hvz
  have hbound := a3sv_height_common_pullback_le f u v hp q huq hvq
  rw [hfq, ← (a1d_degree_pos_iff f u).mp hd] at hbound
  exact a3sv_coheight_add_le_of_height_add_le Y (f.left u) _ _ hbound

/-- IntersectionProductSV: over a component of the target intersection,
every point of the source prime is itself a source intersection component. -/
theorem a3sv_point_over_image_component {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] [IsProper f.left] (u : X.left) (v z : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (hd : 0 < a1p_degree f.left u) (hz : z ∈ a3y_comps (f.left u) v)
    (q : X.left) (huq : u ⤳ q) (hfq : f.left q = z) :
    ∃ w : X.left, ccm3_flatPullbackPrime f.left v w ≠ 0 ∧ q ∈ a3y_comps u w := by
  have hvq : v ⤳ f.left q := hfq.symm ▸ (a3y_comps_spec (f.left u) v hz).2.1
  obtain ⟨w, hw, hwq⟩ := a3sv_exists_pullback_component f v q hvq
  obtain ⟨s, hs, hsq⟩ := a3y_exists_comp u w huq hwq
  have hcs : Order.coheight s = Order.coheight u + Order.coheight v := by
    rw [a3y_coheight_comps u w (hp w hw) hs]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (a3c_coheight_ne_top Y.left v)
    rw [ccm3_flatPullbackPrime_codimension_aux f n v hn.symm w hw, hn]
  have hsz : Order.height s ≤ Order.height z := by
    apply (ENat.add_le_add_iff_right (a3c_coheight_ne_top Y.left v)).mp
    rw [a3sv_height_add_of_coheight_add X u s _ hcs,
      a3sv_height_add_of_coheight_add Y (f.left u) z _
        (a3y_coheight_comps (f.left u) v (a3sv_image_meetProperly f u v hp hd) hz),
      (a1d_degree_pos_iff f u).mp hd]
  have hsq' : Order.height s ≤ Order.height q :=
    hsz.trans (by simpa only [hfq] using a3sv_height_image_le f q)
  have hcq : Order.coheight q ≤ Order.coheight s := by
    simpa only [add_zero] using a3sv_coheight_add_le_of_height_add_le X q s 0
      (by simpa only [add_zero] using hsq')
  have he : s = q := a3y_eq_of_specializes hsq hcq
  exact ⟨w, hw, he ▸ hs⟩

/-- IntersectionProductSV: the part of a fiber lying in the source prime is
finite over a target intersection component of positive generic degree. -/
theorem a3sv_finite_source_prime_fiber {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] [IsProper f.left] (u : X.left) (v z : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (hd : 0 < a1p_degree f.left u) (hz : z ∈ a3y_comps (f.left u) v) :
    {q : X.left | u ⤳ q ∧ f.left q = z}.Finite := by
  have hfin := (a3c_support_finite (ccm3_flatPullbackPrime f.left v)).biUnion
    (fun w _ => a3y_comps_finite u w)
  apply hfin.subset
  intro q hq
  obtain ⟨w, hw, hqw⟩ := a3sv_point_over_image_component f u v z hp hd hz q hq.1 hq.2
  exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hw, hqw⟩⟩

/-- IntersectionProductSV: the source prime maps finitely near each target
intersection component when its generic degree is positive. -/
theorem a3sv_exists_finite_source_prime_neighborhood {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] [IsProper f.left] (u : X.left) (v z : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (hd : 0 < a1p_degree f.left u) (hz : z ∈ a3y_comps (f.left u) v) :
    ∃ V : Y.left.Opens, z ∈ V ∧
      IsFinite ((cycleComponentι X.left u ≫ f.left) ∣_ V) := by
  let ι := cycleComponentι X.left u
  have hfin : ((ι ≫ f.left) ⁻¹' {z}).Finite := by
    apply Set.Finite.of_finite_image (f := ι) _ ι.isClosedEmbedding.injective.injOn
    apply (a3sv_finite_source_prime_fiber f u v z hp hd hz).subset
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨?_, hq⟩
    have h := ((genericPoint_spec (cycleComponent X.left u)).specializes
      (Set.mem_univ q)).map ι.continuous
    simpa only [ι, a3m_cycleComponentι_genericPoint] using h
  exact exists_isFinite_morphismRestrict_of_finite_preimage_singleton (ι ≫ f.left) z hfin

/-- IntersectionProductSV: every nonzero degree-weighted source intersection
coefficient maps to a component of the target intersection. -/
theorem a3sv_weighted_pullback_intersect_support {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] [IsProper f.left] (u : X.left) (v : Y.left) (w t : X.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (hw : ccm3_flatPullbackPrime f.left v w ≠ 0)
    (hi : a3i_intersectPrime X.left u w t ≠ 0) (hd : 0 < a1p_degree f.left t) :
    f.left t ∈ a3y_comps (f.left u) v := by
  have hcomp := a3z_intersectPrime_ne_zero X.left u w t hi
  obtain ⟨hut, hwt, _⟩ := a3y_comps_spec u w hcomp
  have hvt := (a3sv_flatPullback_specializes f v w hw).trans (hwt.map f.left.continuous)
  have ht : Order.coheight t = Order.coheight u + Order.coheight v := by
    rw [a3y_coheight_comps u w (hp w hw) hcomp]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (a3c_coheight_ne_top Y.left v)
    rw [ccm3_flatPullbackPrime_codimension_aux f n v hn.symm w hw, hn]
  have hdu := a3sv_degree_pos_of_proper_pullback_point f u v t hp hut hvt ht hd
  obtain ⟨s, hs, hsf⟩ := a3y_exists_comp (f.left u) v (hut.map f.left.continuous) hvt
  have hcs := a3y_coheight_comps (f.left u) v (a3sv_image_meetProperly f u v hp hdu) hs
  have hheight : Order.height s ≤ Order.height (f.left t) := by
    apply (ENat.add_le_add_iff_right (a3c_coheight_ne_top Y.left v)).mp
    rw [a3sv_height_add_of_coheight_add Y (f.left u) s _ hcs,
      (a1d_degree_pos_iff f t).mp hd, a3sv_height_add_of_coheight_add X u t _ ht,
      (a1d_degree_pos_iff f u).mp hdu]
  have hco : Order.coheight (f.left t) ≤ Order.coheight s := by
    simpa only [add_zero] using a3sv_coheight_add_le_of_height_add_le Y (f.left t) s 0
      (by simpa only [add_zero] using hheight)
  exact (a3y_eq_of_specializes hsf hco) ▸ hs

/-- IntersectionProductSV: the prime projection coefficient identity away
from components of the target intersection. -/
theorem a3sv_proper_pushforward_mult_of_not_component {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    [IsProjective Y.hom] (f : X ⟶ Y) [Flat f.left] [IsProper f.left]
    (u : X.left) (v z : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (hz : z ∉ a3y_comps (f.left u) v) :
    (∑ᶠ t : f.left ⁻¹' {z},
      (∑ᶠ w : X.left, ccm3_flatPullbackPrime f.left v w * a3i_intersectPrime X.left u w t) *
        (a1p_degree f.left t : ℚ)) =
      (a1p_degree f.left u : ℚ) * a3i_intersectPrime Y.left (f.left u) v z := by
  have hz0 : a3i_intersectPrime Y.left (f.left u) v z = 0 := by
    by_contra h
    exact hz (a3z_intersectPrime_ne_zero Y.left (f.left u) v z h)
  rw [hz0, mul_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro t
  rw [finsum_mul]
  apply finsum_eq_zero_of_forall_eq_zero
  intro w
  by_contra h
  obtain ⟨hwi, hd⟩ := mul_ne_zero_iff.mp h
  obtain ⟨hw, hi⟩ := mul_ne_zero_iff.mp hwi
  have hd' : 0 < a1p_degree f.left t := Nat.pos_of_ne_zero fun h0 => hd (by simp [h0])
  have hs := a3sv_weighted_pullback_intersect_support f u v w t hp hw hi hd'
  exact hz (by simpa only [show f.left t = z from t.property] using hs)


/-- IntersectionProductSV: extension of a resolution along an arbitrary ring
map retains the algebra action on Tor over the base ring. -/
def a3sv_baseTorComplex {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (N : ModuleCat.{u} A) : ChainComplex (ModuleCat.{u} B) ℕ :=
  ((ModuleCat.extendScalars f).mapHomologicalComplex _).obj (ProjectiveResolution.of N).complex


set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: homology of the extended resolution is base-ring
Tor after restriction of scalars, without a flatness requirement. -/
def a3sv_baseTorHomologyIso {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (N : ModuleCat.{u} A) (i : ℕ) :
    (ModuleCat.restrictScalars f).obj ((a3sv_baseTorComplex f N).homology i) ≅
      ((Tor (ModuleCat.{u} A) i).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))).obj N :=
  (((a3sv_baseTorComplex f N).sc i).mapHomologyIso (ModuleCat.restrictScalars f)).symm ≪≫
    (a3c_torIso ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) N
      (ProjectiveResolution.of N) i).symm

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: a finite algebra over a Noetherian base gives
finite homology modules in the base Tor complex. -/
theorem a3sv_baseTor_homology_finite {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] (f : A →+* B) (hf : f.Finite)
    (N : ModuleCat.{u} A) [Module.Finite A N] (i : ℕ) :
    Module.Finite B ((a3sv_baseTorComplex f N).homology i) := by
  letI := f.toAlgebra
  haveI : Module.Finite A B := hf
  haveI : Module.Finite A ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) :=
    inferInstanceAs (Module.Finite A B)
  haveI := a3e_tor_finite i ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) N
  let H := (a3sv_baseTorComplex f N).homology i
  letI : Module A H := Module.compHom H f
  haveI : IsScalarTower A B H := ⟨fun a b x => mul_smul (f a) b x⟩
  haveI : Module.Finite A H := Module.Finite.of_surjective
    (a3sv_baseTorHomologyIso f N i).inv.hom
    ((a3sv_baseTorHomologyIso f N i).symm.toLinearEquiv.surjective)
  exact Module.Finite.of_restrictScalars_finite A B H

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the Euler characteristic of the base Tor complex
after restriction is the Tor pairing of the algebra with the base module. -/
theorem a3sv_baseTorEuler_eq_chi {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (N : ModuleCat.{u} A) (m : ℕ) :
    a3i_complexEuler m (((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj
      (a3sv_baseTorComplex f N)) =
      a3s_chi m ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) N := by
  unfold a3i_complexEuler a3s_chi
  apply Finset.sum_congr rfl
  intro i hi
  rw [(a3c_torIso ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) N
    (ProjectiveResolution.of N) i).toLinearEquiv.length_eq]
  rfl

/-- IntersectionProductSV: further extension of the base Tor complex agrees
with extension along the composite ring map. -/
def a3sv_baseTorComplexMapIso {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    (f : A →+* B) (g : B →+* D) (N : ModuleCat.{u} A) :
    ((ModuleCat.extendScalars g).mapHomologicalComplex _).obj (a3sv_baseTorComplex f N) ≅
      a3sv_baseTorComplex (g.comp f) N :=
  (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f g).symm
    (ComplexShape.down ℕ)).app (ProjectiveResolution.of N).complex

/-- IntersectionProductSV: flat extension commutes with the algebra-valued
homology of the base Tor complex. -/
def a3sv_baseTorMapHomologyIso {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    (f : A →+* B) (g : B →+* D) (hg : g.Flat) (N : ModuleCat.{u} A) (i : ℕ) :
    (ModuleCat.extendScalars g).obj ((a3sv_baseTorComplex f N).homology i) ≅
      (a3sv_baseTorComplex (g.comp f) N).homology i := by
  haveI := a3q_extendScalars_preservesHomology g hg
  exact (((a3sv_baseTorComplex f N).sc i).mapHomologyIso (ModuleCat.extendScalars g)).symm ≪≫
    HomologicalComplex.homologyMapIso (a3sv_baseTorComplexMapIso f g N) i

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: proper common support over the local base confines
base Tor homology to the fiber over its maximal ideal. -/
theorem a3sv_baseTor_support_over_closedPoint {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsNoetherianRing A] (f : A →+* B) (hf : f.Finite)
    (N : ModuleCat.{u} A) [Module.Finite A N]
    (hproper : ∀ Q : PrimeSpectrum A,
      Module.annihilator A ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) ≤ Q.asIdeal →
      Module.annihilator A N ≤ Q.asIdeal → Q = IsLocalRing.closedPoint A)
    (i : ℕ) (P : PrimeSpectrum B)
    (hP : P ∈ Module.support B ((a3sv_baseTorComplex f N).homology i)) :
    PrimeSpectrum.comap f P = IsLocalRing.closedPoint A := by
  haveI : Module.Finite A ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) := hf
  haveI := a3e_tor_finite i ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) N
  let H := (a3sv_baseTorComplex f N).homology i
  let e := a3sv_baseTorHomologyIso f N i
  haveI : Module.Finite A ((ModuleCat.restrictScalars f).obj H) :=
    Module.Finite.of_surjective e.inv.hom e.symm.toLinearEquiv.surjective
  haveI : Module.Finite B H := a3sv_baseTor_homology_finite f hf N i
  have hA : PrimeSpectrum.comap f P ∈
      Module.support A ((ModuleCat.restrictScalars f).obj H) := by
    apply Module.mem_support_iff_of_finite.mpr
    intro a ha
    apply (Module.mem_support_iff_of_finite.mp hP)
    rw [Module.mem_annihilator] at ha ⊢
    exact ha
  rw [e.toLinearEquiv.support_eq] at hA
  have hAnn := a3s_annihilator_le_of_mem_support_tor
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) N i _ hA
  exact hproper _ hAnn.1 hAnn.2

/-- IntersectionProductSV: the finite set of primes in a fiber of a finite
ring map. -/
def a3sv_finiteAlgebraFiber {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Finite) (P : PrimeSpectrum A) : Finset (PrimeSpectrum B) := by
  classical
  letI := f.toAlgebra
  haveI : Module.Finite A B := hf
  exact (Algebra.QuasiFinite.finite_comap_preimage_singleton (R := A) (S := B) P).toFinset


set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: localized homology lengths of a base Tor complex
are lengths of the same construction over the localized algebra. -/
theorem a3sv_baseTor_locLen_model {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    [Algebra B D]
    (f : A →+* B) (N : ModuleCat.{u} A) (P : PrimeSpectrum B)
    [IsLocalization.AtPrime D P.asIdeal] (i : ℕ) :
    a3e_locLen P ((a3sv_baseTorComplex f N).homology i) =
      Module.length (D)
        ((a3sv_baseTorComplex ((algebraMap B (D)).comp f) N).homology i) := by
  haveI : Module.Flat B D := IsLocalization.flat D P.asIdeal.primeCompl
  let g := algebraMap B D
  let H := (a3sv_baseTorComplex f N).homology i
  have he := a3q_locLen_eq_length (B := D) P H (D ⊗[B] H) (TensorProduct.mk B D H 1)
  rw [he]
  have hmod : Module.compHom D g = (inferInstance : Module B D) := by
    apply Module.ext
    funext b d
    exact (Algebra.smul_def b d).symm
  have hl := (a3sv_baseTorMapHomologyIso f g
    (RingHom.flat_algebraMap_iff.mpr inferInstance) N i).toLinearEquiv.length_eq
  dsimp +instances only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj',
    ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj', ModuleCat.of] at hl
  convert hl using 1 <;> congr! 3 <;> exact hmod.symm


/-- IntersectionProductSV: membership in the finite algebra fiber is equality
of the contracted prime with the chosen base prime. -/
theorem a3sv_mem_finiteAlgebraFiber {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Finite) (P : PrimeSpectrum A) (Q : PrimeSpectrum B) :
    Q ∈ a3sv_finiteAlgebraFiber f hf P ↔ PrimeSpectrum.comap f Q = P := by
  classical
  simp only [a3sv_finiteAlgebraFiber, Set.Finite.mem_toFinset, Set.mem_preimage,
    Set.mem_singleton_iff]
  rfl

/-- IntersectionProductSV: primes in the closed fiber of a finite algebra
are maximal. -/
theorem a3sv_finiteAlgebraFiber_isMaximal {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] (f : A →+* B) (hf : f.Finite) (P : PrimeSpectrum B)
    (hP : PrimeSpectrum.comap f P = IsLocalRing.closedPoint A) : P.asIdeal.IsMaximal := by
  letI := f.toAlgebra
  haveI : Module.Finite A B := hf
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A)
  have he : P.asIdeal.under A = IsLocalRing.maximalIdeal A := congrArg PrimeSpectrum.asIdeal hP
  rw [he]
  infer_instance


/-- IntersectionProductSV: primes in any fiber of a finite algebra are
pairwise incomparable. -/
theorem a3sv_finiteAlgebraFiber_antichain {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Finite) (P : PrimeSpectrum A) :
    ∀ Q ∈ a3sv_finiteAlgebraFiber f hf P, ∀ R ∈ a3sv_finiteAlgebraFiber f hf P,
      Q ≤ R → Q = R := by
  letI := f.toAlgebra
  haveI : Module.Finite A B := hf
  intro Q hQ R hR hQR
  apply PrimeSpectrum.ext
  apply Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) Q.asIdeal R.asIdeal hQR
  exact congrArg PrimeSpectrum.asIdeal
    ((a3sv_mem_finiteAlgebraFiber f hf P Q).mp hQ |>.trans
      ((a3sv_mem_finiteAlgebraFiber f hf P R).mp hR).symm)

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: localized homology lengths of a base Tor complex
are lengths of the same construction over the localized algebra. -/
theorem a3sv_baseTor_locLen {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (N : ModuleCat.{u} A) (P : PrimeSpectrum B) (i : ℕ) :
    a3e_locLen P ((a3sv_baseTorComplex f N).homology i) =
      Module.length (Localization.AtPrime P.asIdeal)
        ((a3sv_baseTorComplex ((algebraMap B (Localization.AtPrime P.asIdeal)).comp f) N).homology i) := by
  exact a3sv_baseTor_locLen_model (D := Localization.AtPrime P.asIdeal) f N P i

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: base-ring Tor against a localized algebra has
length equal to localized Tor homology weighted by the residue-field length. -/
theorem a3sv_baseTor_length_atPrime {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [Algebra A B] (N : ModuleCat.{u} A) (P : PrimeSpectrum B)
    [IsLocalHom (algebraMap A (Localization.AtPrime P.asIdeal))] (i : ℕ) :
    Module.length A (((Tor (ModuleCat.{u} A) i).obj
      ((ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime P.asIdeal))).obj
        (ModuleCat.of (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal)))).obj N) =
      a3e_locLen P ((a3sv_baseTorComplex (algebraMap A B) N).homology i) *
        Module.length (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime P.asIdeal)) := by
  let D := Localization.AtPrime P.asIdeal
  rw [← (a3sv_baseTorHomologyIso (algebraMap A D) N i).toLinearEquiv.length_eq]
  let H := (a3sv_baseTorComplex (algebraMap A D) N).homology i
  letI : Module A H := Module.compHom H (algebraMap A D)
  haveI : IsScalarTower A D H := ⟨fun a d h => by
    change (a • d) • h = (algebraMap A D a) • (d • h)
    rw [Algebra.smul_def, mul_smul]⟩
  have hloc := a3sv_baseTor_locLen (algebraMap A B) N P i
  change a3e_locLen P ((a3sv_baseTorComplex (algebraMap A B) N).homology i) =
    Module.length D H at hloc
  exact (IsLocalRing.length_restrictScalars A D H).trans
    (congrArg (fun n => n * Module.length (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField D)) hloc.symm)

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the finite algebra Tor pairing is the sum of its
localized homology coefficients, weighted by lengths of the prime quotients. -/
theorem a3sv_baseTor_chi_sum {A B : Type} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsNoetherianRing A] (f : A →+* B) (hf : f.Finite)
    (N : ModuleCat.{0} A) [Module.Finite A N]
    (hproper : ∀ Q : PrimeSpectrum A,
      Module.annihilator A ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) ≤ Q.asIdeal →
      Module.annihilator A N ≤ Q.asIdeal → Q = IsLocalRing.closedPoint A) (m : ℕ) :
    a3s_chi m ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) N =
      ∑ P ∈ a3sv_finiteAlgebraFiber f hf (IsLocalRing.closedPoint A),
        a3i_complexCycleCoeff m (a3sv_baseTorComplex f N) P *
          ((@Module.length A (B ⧸ P.asIdeal) _ _
            (Module.compHom (B ⧸ P.asIdeal) f)).toNat : ℤ) := by
  letI := f.toAlgebra
  haveI : Module.Finite A B := hf
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  haveI : Module.Finite A ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) := hf
  rw [← a3sv_baseTorEuler_eq_chi f N m]
  apply a3sv_complexEuler_restrictScalars_sum f _
    (a3sv_finiteAlgebraFiber_antichain f hf _) _ m
    (a3sv_baseTor_homology_finite f hf N)
  · intro i hi P hP
    exact (a3sv_mem_finiteAlgebraFiber f hf _ P).mpr
      (a3sv_baseTor_support_over_closedPoint f hf N hproper i P hP)
  · intro i hi
    rw [(a3sv_baseTorHomologyIso f N i).toLinearEquiv.length_eq]
    exact a3s_length_tor_ne_top _ N i hproper

/-- IntersectionProductSV: a finite fiber of a proper morphism has an affine
target neighborhood on which the morphism is finite. -/
theorem a3sv_exists_affine_finite_neighborhood {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (y : Y) (hy : (f ⁻¹' {y}).Finite) :
    ∃ V : Y.Opens, y ∈ V ∧ IsAffineOpen V ∧ IsFinite (f ∣_ V) := by
  obtain ⟨V, hyV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y hy
  haveI : IsFinite (f ∣_ V) := hV
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show (⟨y, hyV⟩ : V.toScheme) ∈ (⊤ : V.toScheme.Opens) from trivial)
  refine ⟨V.ι ''ᵁ U, ⟨⟨y, hyV⟩, hyU, rfl⟩, hU.image_of_isOpenImmersion V.ι, ?_⟩
  haveI : MorphismProperty.RespectsIso (@AlgebraicGeometry.IsFinite.{u}) := by
    apply MorphismProperty.RespectsIso.mk
    · intro X Y Z e g hg
      letI := hg
      infer_instance
    · intro X Y Z e g hg
      letI := hg
      infer_instance
  exact (MorphismProperty.arrow_mk_iso_iff (P := @AlgebraicGeometry.IsFinite.{u})
    (morphismRestrictRestrict f V U)).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: a surjective ring map identifies the quotient by
its kernel with its target, viewed as a module over its source. -/
def a3sv_quotientModuleIso {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (I : Ideal A) (hI : RingHom.ker f = I) :
    ModuleCat.of A (A ⧸ I) ≅ (ModuleCat.restrictScalars f).obj (ModuleCat.of B B) := by
  letI := f.toAlgebra
  exact ((Ideal.quotientEquivAlgOfEq A hI.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hf)).toLinearEquiv.toModuleIso


/-- IntersectionProductSV: the stalk of a prime closed subscheme is the
quotient of the ambient stalk by the corresponding prime ideal. -/
def a3sv_componentStalkModuleIso (X : Scheme.{u}) [IsNoetherian X] (u : X)
    (t : cycleComponent X u) :
    ModuleCat.of (X.presheaf.stalk (cycleComponentι X u t))
      (X.presheaf.stalk (cycleComponentι X u t) ⧸ a3i_stalkIdeal X (cycleComponentι X u t) u) ≅
    (ModuleCat.restrictScalars ((cycleComponentι X u).stalkMap t).hom).obj
      (ModuleCat.of ((cycleComponent X u).presheaf.stalk t)
        ((cycleComponent X u).presheaf.stalk t)) :=
  a3sv_quotientModuleIso _ ((cycleComponentι X u).stalkMap_surjective t) _
    (a3y_ker_stalkMap X u t)

/-- IntersectionProductSV: the Tor pairing of a localized algebra is its
localized homology Euler coefficient times the residue-field length. -/
theorem a3sv_baseTor_chi_atPrime {A B : Type} [CommRing A] [CommRing B]
    [IsLocalRing A] [Algebra A B] (N : ModuleCat.{0} A) (P : PrimeSpectrum B)
    [IsLocalHom (algebraMap A (Localization.AtPrime P.asIdeal))] (m : ℕ) :
    a3s_chi m
      ((ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime P.asIdeal))).obj
        (ModuleCat.of (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal))) N =
      a3i_complexCycleCoeff m (a3sv_baseTorComplex (algebraMap A B) N) P *
        ((Module.length (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime P.asIdeal))).toNat : ℤ) := by
  unfold a3s_chi a3i_complexCycleCoeff
  simp only [a3sv_baseTor_length_atPrime, ENat.toNat_mul, Nat.cast_mul, Finset.sum_mul,
    mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: over a local base with proper common support,
the Tor pairing of a finite algebra is the sum of its localized Tor pairings. -/
theorem a3sv_finiteAlgebra_chi_sum {A B : Type} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsNoetherianRing A] [Algebra A B]
    (hf : (algebraMap A B).Finite) (N : ModuleCat.{0} A) [Module.Finite A N]
    (hproper : ∀ Q : PrimeSpectrum A,
      Module.annihilator A ((ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B B)) ≤ Q.asIdeal →
      Module.annihilator A N ≤ Q.asIdeal → Q = IsLocalRing.closedPoint A) (m : ℕ) :
    a3s_chi m ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) N =
      ∑ P ∈ a3sv_finiteAlgebraFiber (algebraMap A B) hf (IsLocalRing.closedPoint A),
        a3s_chi m
          ((ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime P.asIdeal))).obj
            (ModuleCat.of (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal))) N := by
  rw [a3sv_baseTor_chi_sum (algebraMap A B) hf N hproper m]
  apply Finset.sum_congr rfl
  intro P hP
  have hP' := (a3sv_mem_finiteAlgebraFiber (algebraMap A B) hf _ P).mp hP
  haveI := a3sv_finiteAlgebraFiber_isMaximal (algebraMap A B) hf P hP'
  haveI := a3sv_isLocalHom_atPrime (A := A) P.asIdeal (congrArg PrimeSpectrum.asIdeal hP')
  rw [a3sv_baseTor_chi_atPrime]
  congr 2
  have he := a3sv_quotient_length_residue (A := A) P.asIdeal
  have hmod : Module.compHom (B ⧸ P.asIdeal) (algebraMap A B) =
      (inferInstance : Module A (B ⧸ P.asIdeal)) := by
    apply Module.ext
    funext a b
    exact IsScalarTower.algebraMap_smul B a b
  simpa +instances only [hmod] using congrArg ENat.toNat he

/-- IntersectionProductSV: contraction to the maximal ideal of a localized
base is equivalent to contraction to its original prime. -/
theorem a3sv_localizationFiber_condition {R S A B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B] [IsLocalRing A]
    (P : PrimeSpectrum R) [IsLocalization.AtPrime A P.asIdeal] (Q : PrimeSpectrum B) :
    PrimeSpectrum.comap (algebraMap A B) Q = IsLocalRing.closedPoint A ↔
      PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap (algebraMap S B) Q) = P := by
  have hsq : PrimeSpectrum.comap (algebraMap R A) (PrimeSpectrum.comap (algebraMap A B) Q) =
      PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap (algebraMap S B) Q) := by
    apply PrimeSpectrum.ext
    change (Q.asIdeal.comap (algebraMap A B)).comap (algebraMap R A) =
      (Q.asIdeal.comap (algebraMap S B)).comap (algebraMap R S)
    rw [Ideal.comap_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R A B,
      ← IsScalarTower.algebraMap_eq R S B]
  have hmax : PrimeSpectrum.comap (algebraMap R A) (IsLocalRing.closedPoint A) = P :=
    PrimeSpectrum.ext (IsLocalization.AtPrime.under_maximalIdeal A P.asIdeal)
  constructor
  · intro h
    rw [← hsq, h, hmax]
  · intro h
    apply PrimeSpectrum.localization_comap_injective A P.asIdeal.primeCompl
    rw [hsq, h, hmax]


/-- IntersectionProductSV: localization of an algebra along a base prime
identifies its original fiber with the closed fiber over the localized base. -/
def a3sv_localizationFiberEquiv {R S A B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B] [IsLocalRing A]
    (P : PrimeSpectrum R) [IsLocalization.AtPrime A P.asIdeal]
    [IsLocalization (P.asIdeal.primeCompl.map (algebraMap R S)) B] :
    {Q : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) Q = IsLocalRing.closedPoint A} ≃
      {Q : PrimeSpectrum S // PrimeSpectrum.comap (algebraMap R S) Q = P} := by
  let M := P.asIdeal.primeCompl.map (algebraMap R S)
  let e := IsLocalization.primeSpectrumOrderIso M B
  refine Equiv.ofBijective (fun Q => ⟨PrimeSpectrum.comap (algebraMap S B) Q.val,
    (a3sv_localizationFiber_condition P Q.val).mp Q.property⟩) ⟨?_, ?_⟩
  · intro Q Q' h
    apply Subtype.ext
    exact PrimeSpectrum.localization_comap_injective B M (congrArg Subtype.val h)
  · intro Q
    have hd : Disjoint (M : Set S) (Q.val.asIdeal : Set S) := by
      apply Set.disjoint_left.mpr
      rintro s ⟨r, hr, rfl⟩ hs
      have he := congrArg PrimeSpectrum.asIdeal Q.property
      have : r ∈ P.asIdeal := he ▸ hs
      exact hr this
    let q := e.symm ⟨Q.val, hd⟩
    have he : PrimeSpectrum.comap (algebraMap S B) q = Q.val :=
      congrArg Subtype.val (e.apply_symm_apply ⟨Q.val, hd⟩)
    refine ⟨⟨q, (a3sv_localizationFiber_condition (S := S) P q).mpr ?_⟩, ?_⟩
    · rw [he]
      exact Q.property
    · exact Subtype.ext he

/-- IntersectionProductSV: the coordinate prime of an affine point is the
prime defining the localization of its ring of global sections. -/
theorem a3sv_affine_primeIdealOf (X : Scheme.{u}) [IsAffine X] (x : X) :
    (isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩ = X.isoSpec.hom x := by
  rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint]
  rfl

/-- IntersectionProductSV: affine coordinates identify a scheme fiber with
the fiber of the corresponding map on prime spectra. -/
def a3sv_affineFiberEquiv {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (y : Y) :
    {x : X // f x = y} ≃
      {P : PrimeSpectrum Γ(X, ⊤) // PrimeSpectrum.comap f.appTop.hom P = Y.isoSpec.hom y} := by
  have hn (x : X) : PrimeSpectrum.comap f.appTop.hom (X.isoSpec.hom x) =
      Y.isoSpec.hom (f x) := congrArg (fun g : X ⟶ Spec Γ(Y, ⊤) => g x)
        (Scheme.isoSpec_hom_naturality f)
  refine Equiv.ofBijective (fun x => ⟨X.isoSpec.hom x.val, by rw [hn, x.property]⟩) ⟨?_, ?_⟩
  · intro x x' h
    exact Subtype.ext (X.isoSpec.hom.homeomorph.injective (congrArg Subtype.val h))
  · intro P
    obtain ⟨x, hx⟩ := X.isoSpec.hom.homeomorph.surjective P.val
    change X.isoSpec.hom x = P.val at hx
    have hxy : f x = y := Y.isoSpec.hom.homeomorph.injective (by
      change Y.isoSpec.hom (f x) = Y.isoSpec.hom y
      rw [← hn, hx]
      exact P.property)
    exact ⟨⟨x, hxy⟩, Subtype.ext hx⟩


set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: a ring equivalence compatible with the base maps
identifies the corresponding restricted regular modules. -/
def a3sv_algebraUnitModuleIso {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) (e : B ≃+* C) (he : e.toRingHom.comp f = g) :
    (ModuleCat.restrictScalars f).obj (ModuleCat.of B B) ≅
      (ModuleCat.restrictScalars g).obj (ModuleCat.of C C) := by
  let l : ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) ≃ₗ[A]
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of C C)) :=
    { e.toAddEquiv with
      map_smul' := fun a b => by
        change e (f a * (show B from b)) = g a * e b
        rw [map_mul]
        exact congrArg (fun c => c * e b) (congrArg (fun h : A →+* C => h a) he) }
  exact l.toModuleIso


set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: restriction from a component stalk along a flat
ambient map gives the ambient quotient Tor pairing with its residue degree. -/
theorem a3sv_componentStalk_chi_restrict {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) [Flat f] (u : X) (t : cycleComponent X u)
    (N : ModuleCat.{u} (Y.presheaf.stalk (f (cycleComponentι X u t)))) (m : ℕ) :
    a3s_chi m
      ((ModuleCat.restrictScalars ((cycleComponentι X u ≫ f).stalkMap t).hom).obj
        (ModuleCat.of ((cycleComponent X u).presheaf.stalk t) ((cycleComponent X u).presheaf.stalk t))) N =
      a3s_chi m
        (ModuleCat.of (X.presheaf.stalk (cycleComponentι X u t))
          (X.presheaf.stalk (cycleComponentι X u t) ⧸ a3i_stalkIdeal X (cycleComponentι X u t) u))
        ((ModuleCat.extendScalars (f.stalkMap (cycleComponentι X u t)).hom).obj N) *
        (a1p_degree f (cycleComponentι X u t) : ℤ) := by
  let e := ModuleCat.restrictScalarsComp'App (f.stalkMap (cycleComponentι X u t)).hom
    ((cycleComponentι X u).stalkMap t).hom ((cycleComponentι X u ≫ f).stalkMap t).hom
    (by rw [Scheme.Hom.stalkMap_comp]; rfl)
    (ModuleCat.of ((cycleComponent X u).presheaf.stalk t) ((cycleComponent X u).presheaf.stalk t))
  rw [a3s_chi_congr e N m, a3sv_chi_stalk_restrictScalars]
  rw [← a3s_chi_congr (a3sv_componentStalkModuleIso X u t)]

/-- IntersectionProductSV: an equivalence over the original algebra is also
compatible with a localized base when both scalar towers agree. -/
theorem a3sv_localization_algEquiv_commutes {R S A C D : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra R A] [Algebra R C] [Algebra R D]
    [Algebra S C] [Algebra S D] [Algebra A C] [Algebra A D]
    [IsScalarTower R S C] [IsScalarTower R S D]
    [IsScalarTower R A C] [IsScalarTower R A D]
    (M : Submonoid R) [IsLocalization M A] (e : C ≃ₐ[S] D) :
    e.toRingHom.comp (algebraMap A C) = algebraMap A D := by
  apply IsLocalization.ringHom_ext M
  ext r
  change e (algebraMap A C (algebraMap R A r)) = algebraMap A D (algebraMap R A r)
  rw [← IsScalarTower.algebraMap_apply R A C, ← IsScalarTower.algebraMap_apply R A D,
    IsScalarTower.algebraMap_apply R S C, IsScalarTower.algebraMap_apply R S D, e.commutes]


/-- IntersectionProductSV: two localizations of the same algebra at a prime
have isomorphic regular modules over a common localized base. -/
def a3sv_localization_modelModuleIso {R S A C D : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra R A] [Algebra R C] [Algebra R D]
    [Algebra S C] [Algebra S D] [Algebra A C] [Algebra A D]
    [IsScalarTower R S C] [IsScalarTower R S D]
    [IsScalarTower R A C] [IsScalarTower R A D]
    (M : Submonoid R) [IsLocalization M A] (Q : PrimeSpectrum S)
    [IsLocalization.AtPrime C Q.asIdeal] [IsLocalization.AtPrime D Q.asIdeal] :
    (ModuleCat.restrictScalars (algebraMap A C)).obj (ModuleCat.of C C) ≅
      (ModuleCat.restrictScalars (algebraMap A D)).obj (ModuleCat.of D D) := by
  let e := IsLocalization.algEquiv Q.asIdeal.primeCompl C D
  exact a3sv_algebraUnitModuleIso _ _ e.toRingEquiv
    (a3sv_localization_algEquiv_commutes M e)

/-- IntersectionProductSV: intersecting the generic point with one prime
has that prime as its sole geometric component. -/
theorem a3sv_comps_generic (X : Scheme.{u}) [IsNoetherian X] [IsIntegral X] (u : X) :
    a3y_comps (genericPoint X) u = {u} := by
  ext z
  rw [Set.mem_singleton_iff]
  constructor
  · intro hz
    obtain ⟨_, huz, hmin⟩ := a3y_comps_spec _ _ hz
    exact (hmin u (genericPoint_specializes u) specializes_rfl huz).symm
  · intro h
    subst h
    obtain ⟨z', hz', hz'z⟩ := a3y_exists_comp (genericPoint X) z
      (genericPoint_specializes z) specializes_rfl
    obtain ⟨_, hzz', _⟩ := a3y_comps_spec _ _ hz'
    rwa [(hz'z.antisymm hzz').eq] at hz'


/-- IntersectionProductSV: the generic point meets every prime properly. -/
theorem a3sv_generic_meetProperly (X : Scheme.{u}) [IsNoetherian X] [IsIntegral X] (u : X) :
    a3i_MeetProperly X (genericPoint X) u := by
  intro w hw
  have hz : (ccm3_primeIdeal X (genericPoint X) ⊔ ccm3_primeIdeal X u).subschemeι w ∈
      a3y_comps (genericPoint X) u := ⟨w, hw, rfl⟩
  rw [a3sv_comps_generic, Set.mem_singleton_iff] at hz
  rw [hz, HodgeLean.RealDefs.coheight_genericPoint, zero_add]


/-- IntersectionProductSV: a finite module supported on one prime closure
has Tor pairing equal to its generic length times the prime pairing. -/
theorem a3sv_stalk_prime_devissage (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (u v T : X.left)
    (hu : u ⤳ T) (hv : v ⤳ T)
    (hT : Order.coheight T = Order.coheight u + Order.coheight v)
    (hproper : ∀ P : PrimeSpectrum (X.left.presheaf.stalk T),
      a3i_stalkIdeal X.left T u ≤ P.asIdeal → a3i_stalkIdeal X.left T v ≤ P.asIdeal →
        P = IsLocalRing.closedPoint _)
    (m : ℕ) (hm : ringKrullDim (X.left.presheaf.stalk T) ≤ m)
    (M : ModuleCat.{0} (X.left.presheaf.stalk T)) [Module.Finite (X.left.presheaf.stalk T) M]
    (hM : ∀ P ∈ Module.support (X.left.presheaf.stalk T) M,
      a3i_stalkIdeal X.left T u ≤ P.asIdeal) :
    a3s_chi m M (ModuleCat.of (X.left.presheaf.stalk T)
      (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T v)) =
      ((a3e_locLen (a3y_pt T u hu) M).toNat : ℤ) *
        a3s_chi m (ModuleCat.of (X.left.presheaf.stalk T)
          (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T u))
          (ModuleCat.of (X.left.presheaf.stalk T)
            (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T v)) := by
  have he := a3sv_stalk_pair_devissage X (genericPoint X.left) u v T
    (a3sv_generic_meetProperly X.left u) (genericPoint_specializes T) hu hv
    (by simpa only [HodgeLean.RealDefs.coheight_genericPoint, zero_add] using hT)
    (fun P _ hPu hPv => hproper P hPu hPv) m hm M (fun P hP => ⟨
      (a3sv_stalkIdeal_le_prime_iff X.left T (genericPoint X.left)
        (genericPoint_specializes T) P).mpr (genericPoint_specializes _), hM P hP⟩)
  have hc : a3y_compsAt X (genericPoint X.left) u T = {u} := by
    ext t
    simp only [a3y_compsAt, Finset.mem_filter, Set.Finite.mem_toFinset,
      a3sv_comps_generic, Set.mem_singleton_iff, Finset.mem_singleton]
    exact and_iff_left_of_imp (fun h => h.symm ▸ hu)
  rw [hc, Finset.sum_singleton] at he
  simpa only [a3y_ptOr, dif_pos hu] using he

/-- IntersectionProductSV: a finite stalk module supported on finitely many
prime closures expands into their generic lengths in a proper Tor pairing. -/
theorem a3sv_stalk_cycle_devissage (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (u T : X.left)
    (hu : u ⤳ T) (W : Finset X.left)
    (hw : ∀ w ∈ W, w ⤳ T)
    (hT : ∀ w ∈ W, Order.coheight T = Order.coheight w + Order.coheight u)
    (hproper : ∀ w ∈ W, ∀ P : PrimeSpectrum (X.left.presheaf.stalk T),
      a3i_stalkIdeal X.left T w ≤ P.asIdeal → a3i_stalkIdeal X.left T u ≤ P.asIdeal →
        P = IsLocalRing.closedPoint _)
    (m : ℕ) (hm : ringKrullDim (X.left.presheaf.stalk T) ≤ m)
    (M : ModuleCat.{0} (X.left.presheaf.stalk T)) [Module.Finite (X.left.presheaf.stalk T) M]
    (hM : ∀ P ∈ Module.support (X.left.presheaf.stalk T) M,
      ∃ w ∈ W, a3i_stalkIdeal X.left T w ≤ P.asIdeal) :
    a3s_chi m M (ModuleCat.of (X.left.presheaf.stalk T)
      (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T u)) =
      ∑ w ∈ W, ((a3e_locLen (a3y_ptOr X T w) M).toNat : ℤ) *
        a3s_chi m (ModuleCat.of (X.left.presheaf.stalk T)
          (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T w))
          (ModuleCat.of (X.left.presheaf.stalk T)
            (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T u)) := by
  classical
  have := a3c_isRegularLocalRing_stalk X T
  let A := X.left.presheaf.stalk T
  let U := ModuleCat.of A (A ⧸ a3i_stalkIdeal X.left T u)
  let Z : Set (PrimeSpectrum A) := {P | ∃ w ∈ W, a3i_stalkIdeal X.left T w ≤ P.asIdeal}
  let F := W.image (a3y_ptOr X T)
  have hpt (w : X.left) (h : w ∈ W) : a3y_ptOr X T w = a3y_pt T w (hw w h) := by
    simp only [a3y_ptOr, dif_pos (hw w h)]
  have hmin : ∀ P ∈ Z, ∀ Q ∈ F, P ≤ Q → P = Q := by
    rintro P ⟨w, hwW, hwP⟩ Q hQ hPQ
    obtain ⟨w', hw'W, rfl⟩ := Finset.mem_image.mp hQ
    rw [hpt w' hw'W] at hPQ ⊢
    have h1 := (a3sv_stalkIdeal_le_prime_iff X.left T w (hw w hwW) P).mp hwP
    have h2 : X.left.fromSpecStalk T P ⤳ w' := by
      have h := ((PrimeSpectrum.le_iff_specializes _ _).mp hPQ).map
        (X.left.fromSpecStalk T).continuous
      simpa only [a3y_fromSpecStalk_pt] using h
    have hew : w = w' := a3y_eq_of_specializes (h1.trans h2) (le_of_eq
      (ENat.add_left_injective_of_ne_top (a3c_coheight_ne_top X.left u)
        ((hT w' hw'W).symm.trans (hT w hwW))))
    have hep : X.left.fromSpecStalk T P = w' := (h2.antisymm (hew ▸ h1)).eq
    rw [← a3y_pt_fromSpecStalk T P]
    apply PrimeSpectrum.ext
    change a3i_stalkIdeal X.left T (X.left.fromSpecStalk T P) = a3i_stalkIdeal X.left T w'
    rw [hep]
  have hlow : ∀ P ∈ Z, P ∉ F → a3s_chi m (ModuleCat.of A (A ⧸ P.asIdeal)) U = 0 := by
    rintro P ⟨w, hwW, hwP⟩ hPF
    apply a3sv_pair_prime_vanishing X (genericPoint X.left) w u T
      (a3sv_generic_meetProperly X.left w) (genericPoint_specializes T) (hw w hwW) hu
      (by simpa only [HodgeLean.RealDefs.coheight_genericPoint, zero_add] using hT w hwW)
      (fun Q _ hwQ huQ => hproper w hwW Q hwQ huQ) P
      ((a3sv_stalkIdeal_le_prime_iff X.left T (genericPoint X.left)
        (genericPoint_specializes T) P).mpr (genericPoint_specializes _)) hwP ?_ m hm
    intro hc
    rw [a3sv_comps_generic, Set.mem_singleton_iff] at hc
    apply hPF
    apply Finset.mem_image.mpr
    refine ⟨w, hwW, ?_⟩
    rw [hpt w hwW]
    apply PrimeSpectrum.ext
    change a3i_stalkIdeal X.left T w = P.asIdeal
    rw [← hc]
    exact congrArg PrimeSpectrum.asIdeal (a3y_pt_fromSpecStalk T P)
  have he := (a3w_chi_devissage_top m
    (lt_of_le_of_lt hm (by exact_mod_cast Nat.lt_succ_self m)) U Z F
    (by
      rintro P ⟨w, hwW, hwP⟩ huP
      exact hproper w hwW P hwP (by simpa only [U, A, Ideal.annihilator_quotient] using huP))
    hmin hlow M hM).1
  rw [he, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w hwW
    rw [hpt w hwW]
    rfl
  · intro w hwW w' hw'W heq
    rw [hpt w hwW, hpt w' hw'W] at heq
    exact a3y_pt_injective T w w' _ _ heq

/-- IntersectionProductSV: at the expected codimension, a proper pair of
prime closures has common stalk support only at the maximal ideal. -/
theorem a3sv_pair_stalk_support (X : Scheme) [IsLocallyNoetherian X]
    (u v T : X) (hp : a3i_MeetProperly X u v) (hu : u ⤳ T) (hv : v ⤳ T)
    (hT : Order.coheight T = Order.coheight u + Order.coheight v)
    (P : PrimeSpectrum (X.presheaf.stalk T))
    (hP : a3i_stalkIdeal X T u ≤ P.asIdeal)
    (hQ : a3i_stalkIdeal X T v ≤ P.asIdeal) : P = IsLocalRing.closedPoint _ := by
  have hup := (a3sv_stalkIdeal_le_prime_iff X T u hu P).mp hP
  have hvp := (a3sv_stalkIdeal_le_prime_iff X T v hv P).mp hQ
  obtain ⟨s, hs, hsp⟩ := a3y_exists_comp u v hup hvp
  have hdim : Order.coheight T ≤ Order.coheight (X.fromSpecStalk T P) := by
    rw [hT, ← a3y_coheight_comps u v hp hs]
    exact Order.coheight_anti (Scheme.le_iff_specializes.mpr hsp)
  have he := a3y_eq_of_specializes (a3y_specializes_fromSpecStalk T P) hdim
  apply (X.fromSpecStalk T).isEmbedding.injective
  simpa only [Scheme.fromSpecStalk_closedPoint] using he


/-- IntersectionProductSV: the finite set of pullback components passing
through a chosen source point. -/
def a3sv_pullbackComponentsAt {X Y : Scheme} [IsNoetherian X]
    (f : X ⟶ Y) (v : Y) (T : X) : Finset X := by
  classical
  exact (a3c_support_finite (ccm3_flatPullbackPrime f v)).toFinset.filter (fun w => w ⤳ T)


/-- IntersectionProductSV: membership in the local pullback component set
means nonzero pullback coefficient and specialization to the chosen point. -/
theorem a3sv_mem_pullbackComponentsAt {X Y : Scheme} [IsNoetherian X]
    (f : X ⟶ Y) (v : Y) (T w : X) :
    w ∈ a3sv_pullbackComponentsAt f v T ↔ ccm3_flatPullbackPrime f v w ≠ 0 ∧ w ⤳ T := by
  classical
  simp only [a3sv_pullbackComponentsAt, Finset.mem_filter, Set.Finite.mem_toFinset,
    Function.mem_support]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the support of an extended prime quotient is the
inverse image of its original support on prime spectra. -/
theorem a3sv_extendQuot_support {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (P : PrimeSpectrum B) :
    P ∈ Module.support B ((ModuleCat.extendScalars f).obj (ModuleCat.of A (A ⧸ I))) ↔
      I ≤ P.asIdeal.comap f := by
  letI := f.toAlgebra
  have e : (ModuleCat.extendScalars f).obj (ModuleCat.of A (A ⧸ I)) ≅
      ModuleCat.of B (B ⧸ I.map f) := a3w_extQuot I
  rw [e.toLinearEquiv.support_eq, Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
  exact Ideal.map_le_iff_le_comap


/-- IntersectionProductSV: every prime in the support of a pulled-back stalk
quotient specializes from a component of the scheme-theoretic inverse image. -/
theorem a3sv_pullback_stalk_support {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) (v : Y.left) (T : X.left) (hv : v ⤳ f.left T)
    (P : PrimeSpectrum (X.left.presheaf.stalk T))
    (hP : P ∈ Module.support (X.left.presheaf.stalk T)
      ((ModuleCat.extendScalars (f.left.stalkMap T).hom).obj
        (ModuleCat.of (Y.left.presheaf.stalk (f.left T))
          (Y.left.presheaf.stalk (f.left T) ⧸ a3i_stalkIdeal Y.left (f.left T) v)))) :
    ∃ w : X.left, ccm3_flatPullbackPrime f.left v w ≠ 0 ∧
      w ⤳ T ∧ a3i_stalkIdeal X.left T w ≤ P.asIdeal := by
  have hI := (a3sv_extendQuot_support (f.left.stalkMap T).hom _ P).mp hP
  have hvq := (a3sv_stalkIdeal_le_prime_iff Y.left (f.left T) v hv
    (PrimeSpectrum.comap (f.left.stalkMap T).hom P)).mp hI
  have he : Y.left.fromSpecStalk (f.left T)
      (PrimeSpectrum.comap (f.left.stalkMap T).hom P) =
      f.left (X.left.fromSpecStalk T P) :=
    congrArg (fun g : Spec (X.left.presheaf.stalk T) ⟶ Y.left => g P)
      (Scheme.SpecMap_stalkMap_fromSpecStalk f.left (x := T))
  rw [he] at hvq
  obtain ⟨w, hw, hwq⟩ := a3sv_exists_pullback_component f v _ hvq
  have hwT := hwq.trans (a3y_specializes_fromSpecStalk T P)
  exact ⟨w, hw, hwT, (a3sv_stalkIdeal_le_prime_iff X.left T w hwT P).mpr hwq⟩

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: a pulled-back stalk quotient expands over the
local pullback components in a proper ambient Tor pairing. -/
theorem a3sv_pullback_stalk_devissage {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] (u T : X.left) (v : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (hu : u ⤳ T) (hv : v ⤳ f.left T)
    (hT : Order.coheight T = Order.coheight u + Order.coheight v)
    (m : ℕ) (hm : ringKrullDim (X.left.presheaf.stalk T) ≤ m) :
    let N := (ModuleCat.extendScalars (f.left.stalkMap T).hom).obj
      (ModuleCat.of (Y.left.presheaf.stalk (f.left T))
        (Y.left.presheaf.stalk (f.left T) ⧸ a3i_stalkIdeal Y.left (f.left T) v))
    a3s_chi m N (ModuleCat.of (X.left.presheaf.stalk T)
      (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T u)) =
      ∑ w ∈ a3sv_pullbackComponentsAt f.left v T,
        ((a3e_locLen (a3y_ptOr X T w) N).toNat : ℤ) *
          a3s_chi m (ModuleCat.of (X.left.presheaf.stalk T)
            (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T w))
            (ModuleCat.of (X.left.presheaf.stalk T)
              (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T u)) := by
  intro N
  letI := (f.left.stalkMap T).hom.toAlgebra
  haveI : Module.Finite (X.left.presheaf.stalk T) N := Module.Finite.of_surjective
    (a3w_extQuot (B := X.left.presheaf.stalk T) (a3i_stalkIdeal Y.left (f.left T) v)).inv.hom
    ((a3w_extQuot (B := X.left.presheaf.stalk T) (a3i_stalkIdeal Y.left (f.left T) v)).symm.toLinearEquiv.surjective)
  have hmem := a3sv_mem_pullbackComponentsAt f.left v T
  have hcodim (w : X.left) (hw : w ∈ a3sv_pullbackComponentsAt f.left v T) :
      Order.coheight w = Order.coheight v := by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (a3c_coheight_ne_top Y.left v)
    exact (ccm3_flatPullbackPrime_codimension_aux f n v hn.symm w ((hmem w).mp hw).1).trans hn
  refine a3sv_stalk_cycle_devissage X u T hu _
    (fun w hw => ((hmem w).mp hw).2)
    (fun w hw => by rw [hcodim w hw, add_comm]; exact hT) ?_ m hm N ?_
  · intro w hw P hwP huP
    apply a3sv_pair_stalk_support X.left u w T (hp w ((hmem w).mp hw).1)
      hu ((hmem w).mp hw).2 (by rw [hcodim w hw]; exact hT) P huP hwP
  · intro P hP
    obtain ⟨w, hw, hwT, hwP⟩ := a3sv_pullback_stalk_support f v T hv P hP
    exact ⟨w, (hmem w).mpr ⟨hw, hwT⟩, hwP⟩

/-- IntersectionProductSV: the map to a component stalk kills exactly the
prime of its image in the target stalk. -/
theorem a3sv_componentStalkMap_kernel {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) (u : X) (t : cycleComponent X u) :
    RingHom.ker ((cycleComponentι X u ≫ f).stalkMap t).hom =
      a3i_stalkIdeal Y (f (cycleComponentι X u t)) (f u) := by
  have hu : u ⤳ cycleComponentι X u t := by
    have h := ((genericPoint_spec (cycleComponent X u)).specializes
      (Set.mem_univ t)).map (cycleComponentι X u).continuous
    simpa only [a3m_cycleComponentι_genericPoint] using h
  rw [Scheme.Hom.stalkMap_comp]
  change (RingHom.ker ((cycleComponentι X u).stalkMap t).hom).comap
    (f.stalkMap (cycleComponentι X u t)).hom = _
  rw [a3y_ker_stalkMap, a3y_comap_stalkIdeal f hu]

/-- IntersectionProductSV: in a finite domain algebra every nonzero element
divides a nonzero element coming from the base. -/
theorem a3sv_finiteDomain_exists_base_multiple {A B : Type u} [CommRing A] [CommRing B]
    [IsDomain B] (f : A →+* B) (hf : f.Finite) (b : B) (hb : b ≠ 0) :
    ∃ a : A, a ∉ RingHom.ker f ∧ b ∣ f a := by
  letI := f.toAlgebra
  haveI : Module.Finite A B := hf
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  let R := A ⧸ RingHom.ker f
  letI : Algebra R B := f.kerLift.toAlgebra
  haveI : IsScalarTower A R B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite R B := Module.Finite.of_restrictScalars_finite A R B
  obtain ⟨c, d, hd, he⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul R (1 : B) hb
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
  refine ⟨a, fun ha => hd (Ideal.Quotient.eq_zero_iff_mem.mpr ha), c, ?_⟩
  change f a * 1 = b * c at he
  simpa only [mul_one] using he


/-- IntersectionProductSV: the fraction ring of a finite domain algebra is
obtained by inverting the base elements outside the kernel. -/
theorem a3sv_finiteDomain_fraction_localization {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [IsDomain B]
    (f : A →+* B) (hf : f.Finite) (P : PrimeSpectrum A)
    (hP : P.asIdeal = RingHom.ker f) [Algebra B C] [IsFractionRing B C] :
    IsLocalization (P.asIdeal.primeCompl.map f) C := by
  apply (IsLocalization.iff_of_le_of_exists_dvd
    (S := C) (P.asIdeal.primeCompl.map f) (nonZeroDivisors B) ?_ ?_).mpr inferInstance
  · rintro b ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (fun h => ha (hP.symm ▸ RingHom.mem_ker.mpr h))
  · intro b hb
    obtain ⟨a, ha, hd⟩ := a3sv_finiteDomain_exists_base_multiple f hf b
      (nonZeroDivisors.ne_zero hb)
    exact ⟨f a, ⟨a, by change a ∉ P.asIdeal; simpa only [hP] using ha, rfl⟩, hd⟩


/-- IntersectionProductSV: generic length of a finite domain algebra can be
computed in a fraction-ring model over any model of the localized base. -/
theorem a3sv_finiteDomain_locLen {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D] [IsDomain B]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra A D] [Algebra D C] [IsScalarTower A D C]
    (hf : (algebraMap A B).Finite) [IsFractionRing B C]
    (P : PrimeSpectrum A) (hP : P.asIdeal = RingHom.ker (algebraMap A B))
    [IsLocalization.AtPrime D P.asIdeal] :
    a3e_locLen P B = Module.length D C := by
  haveI : IsLocalization (P.asIdeal.primeCompl.map (algebraMap A B)) C :=
    a3sv_finiteDomain_fraction_localization (C := C) (algebraMap A B) hf P hP
  haveI : IsLocalizedModule P.asIdeal.primeCompl
      (IsScalarTower.toAlgHom A B C).toLinearMap :=
    by
    apply isLocalizedModule_iff_isLocalization.mpr
    change IsLocalization (P.asIdeal.primeCompl.map (algebraMap A B)) C
    exact a3sv_finiteDomain_fraction_localization (C := C) (algebraMap A B) hf P hP
  exact a3q_locLen_eq_length P B C (IsScalarTower.toAlgHom A B C).toLinearMap

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the stalk maps of a closed-immersion pullback form a commuting square. -/
theorem a3sv_closed_pullback_stalk_square
    {W Z C D : Scheme} (t : W ⟶ Z) (i : C ⟶ Z) (j : D ⟶ W) (s : D ⟶ C)
    [IsClosedImmersion i] [IsClosedImmersion j] (h : IsPullback j s t i) (d : D) :
    let e := Z.presheaf.stalkCongr (Inseparable.of_eq
      (congrArg (fun k : D ⟶ Z => k d) h.w))
    t.stalkMap (j d) ≫ (j).stalkMap d =
      e.hom ≫ i.stalkMap (s d) ≫ (s).stalkMap d := by
  dsimp only
  rw [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp]
  exact Scheme.Hom.stalkMap_congr_hom _ _ h.w d


/-- IntersectionProductSV: a morphism from a local spectrum factors through the stalk at its closed-point image. -/
theorem a3sv_factor_fromSpecStalk_at_closedPoint
    {X : Scheme} (R : CommRingCat) [IsLocalRing R]
    (k : Spec R ⟶ X) (x : X) (hx : k (IsLocalRing.closedPoint R) = x) :
    ∃ r : X.presheaf.stalk x ⟶ R,
      Spec.map r ≫ X.fromSpecStalk x = k := by
  subst x
  exact ⟨Scheme.stalkClosedPointTo k, Scheme.Spec_stalkClosedPointTo_fromSpecStalk k⟩


open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the stalk kernel of a pulled-back closed immersion is the extended stalk kernel. -/
theorem a3sv_closed_pullback_stalk_kernel
    {W Z C D : Scheme} (t : W ⟶ Z) (i : C ⟶ Z) (j : D ⟶ W) (s : D ⟶ C)
    [IsClosedImmersion i] [IsClosedImmersion j] (h : IsPullback j s t i) (d : D) :
    let e := Z.presheaf.stalkCongr (Inseparable.of_eq
      (congrArg (fun k : D ⟶ Z => k d) h.w))
    RingHom.ker ((j).stalkMap d).hom =
      (RingHom.ker (e.hom ≫ i.stalkMap (s d)).hom).map
        (t.stalkMap (j d)).hom := by
  let w := j d
  let c := s d
  let e := Z.presheaf.stalkCongr (Inseparable.of_eq
    (congrArg (fun k : D ⟶ Z => k d) h.w))
  let f := t.stalkMap w
  let p := e.hom ≫ i.stalkMap c
  let q := (j).stalkMap d
  let g := (s).stalkMap d
  have hcomm : f ≫ q = p ≫ g := a3sv_closed_pullback_stalk_square t i j s h d
  let J := (RingHom.ker p.hom).map f.hom
  have hle : J ≤ RingHom.ker q.hom := by
    rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
    change RingHom.ker p.hom ≤ RingHom.ker (f ≫ q).hom
    rw [hcomm]
    intro a ha
    change g.hom (p.hom a) = 0
    rw [ha, map_zero]
  let D := (W.presheaf.stalk w) ⧸ J
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (RingHom.ker_ne_top q.hom) hle
  letI : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr hJ
  letI : IsLocalRing D := IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  let v : W.presheaf.stalk w ⟶ CommRingCat.of D := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have : IsLocalHom v.hom := IsLocalHom.of_surjective v.hom Ideal.Quotient.mk_surjective
  have hp : Function.Surjective p.hom :=
    (i.stalkMap_surjective c).comp (ConcreteCategory.bijective_of_isIso e.hom).2
  have hpv : RingHom.ker p.hom ≤ RingHom.ker (f ≫ v).hom := by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f.hom ha)
  let l : C.presheaf.stalk c ⟶ CommRingCat.of D :=
    CommRingCat.ofHom (p.hom.liftOfSurjective hp ⟨(f ≫ v).hom, hpv⟩)
  have hpl : p ≫ l = f ≫ v := by
    exact CommRingCat.hom_ext (RingHom.liftOfSurjective_comp p.hom hp _)
  let kw := Spec.map v ≫ W.fromSpecStalk w
  let kc := Spec.map l ≫ C.fromSpecStalk c
  have hcone : kw ≫ t = kc ≫ i := by
    dsimp only [kw, kc]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc]
    have he : Spec.map e.hom ≫ Z.fromSpecStalk (t w) = Z.fromSpecStalk (i c) :=
      by
        dsimp only [e, TopCat.Presheaf.stalkCongr]
        exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
    change Spec.map (f ≫ v) ≫ Z.fromSpecStalk (t w) = _
    rw [← hpl]
    dsimp only [p]
    rw [Category.assoc, Spec.map_comp, Category.assoc, he]
  let k := h.lift kw kc hcone
  have hkd : k (IsLocalRing.closedPoint (CommRingCat.of D)) = d := by
    apply (j).isClosedEmbedding.injective
    change (k ≫ j) _ = w
    rw [h.lift_fst]
    change W.fromSpecStalk w (Spec.map v (IsLocalRing.closedPoint (CommRingCat.of D))) = w
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  obtain ⟨r, hr⟩ := a3sv_factor_fromSpecStalk_at_closedPoint (CommRingCat.of D) k d hkd
  have hqr : q ≫ r = v := by
    apply Spec.map_injective
    apply (cancel_mono (W.fromSpecStalk w)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, hr]
    exact h.lift_fst ..
  apply le_antisymm _ hle
  intro a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change v.hom a = 0
  rw [← hqr]
  change r.hom (q.hom a) = 0
  rw [ha, map_zero]


/-- IntersectionProductSV: equal scheme points give the same stalk prime
under the canonical identification of their stalks. -/
theorem a3sv_stalkIdeal_comap_congr (X : Scheme) (x y u : X) (h : x = y) :
    (a3i_stalkIdeal X y u).comap (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom =
      a3i_stalkIdeal X x u := by
  subst y
  simp [TopCat.Presheaf.stalkCongr]


open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the inverse-image subscheme stalk is cut out by
the extension of the target prime ideal along the stalk map. -/
theorem a3sv_inverseStalk_kernel {X Y : Scheme} [IsNoetherian Y]
    (f : X ⟶ Y) (v : Y) (y : (ccm3_inverseIdeal f v).subscheme) :
    RingHom.ker ((ccm3_inverseIdeal f v).subschemeι.stalkMap y).hom =
      (a3i_stalkIdeal Y (f ((ccm3_inverseIdeal f v).subschemeι y)) v).map
        (f.stalkMap ((ccm3_inverseIdeal f v).subschemeι y)).hom := by
  let I := ccm3_primeIdeal Y v
  let J := ccm3_inverseIdeal f v
  let g := Scheme.IdealSheafData.subschemeMap J I f (I.le_map_comap f)
  have h : IsPullback J.subschemeι g f I.subschemeι :=
    isPullback_of_isClosedImmersion J.subschemeι I.subschemeι g f
      (Scheme.IdealSheafData.subschemeMap_subschemeι J I f (I.le_map_comap f)).symm
      (by rw [I.ker_subschemeι, J.ker_subschemeι]; rfl)
  have hk := a3y_ker_stalkMap Y v (g y)
  change RingHom.ker (I.subschemeι.stalkMap (g y)).hom =
    a3i_stalkIdeal Y (I.subschemeι (g y)) v at hk
  rw [a3sv_closed_pullback_stalk_kernel f I.subschemeι J.subschemeι g h y]
  congr 1
  change (RingHom.ker (I.subschemeι.stalkMap (g y)).hom).comap
    (Y.presheaf.stalkCongr (Inseparable.of_eq
      (congrArg (fun k : J.subscheme ⟶ Y => k y) h.w))).hom.hom = _
  rw [hk]
  exact a3sv_stalkIdeal_comap_congr Y _ _ v
    (congrArg (fun k : J.subscheme ⟶ Y => k y) h.w)


/-- IntersectionProductSV: inverse-image multiplicity is the length of the
quotient by the extended target prime in the ambient source stalk. -/
theorem a3sv_inverseStalk_length {X Y : Scheme} [IsNoetherian Y]
    (f : X ⟶ Y) (v : Y) (y : (ccm3_inverseIdeal f v).subscheme) :
    Module.length (X.presheaf.stalk ((ccm3_inverseIdeal f v).subschemeι y))
      (X.presheaf.stalk ((ccm3_inverseIdeal f v).subschemeι y) ⧸
        (a3i_stalkIdeal Y (f ((ccm3_inverseIdeal f v).subschemeι y)) v).map
          (f.stalkMap ((ccm3_inverseIdeal f v).subschemeι y)).hom) =
      ccm3_genericLength f v y :=
  a3l_length_quot_ker _ ((ccm3_inverseIdeal f v).subschemeι.stalkMap_surjective y) _
    (a3sv_inverseStalk_kernel f v y)

/-- IntersectionProductSV: the localized length of a quotient is the length
of the quotient by its extended ideal in any local ring model. -/
theorem a3sv_locLen_quotient_model {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (P : PrimeSpectrum A) [IsLocalization.AtPrime B P.asIdeal] (I : Ideal A) :
    a3e_locLen P (A ⧸ I) = Module.length B (B ⧸ I.map (algebraMap A B)) := by
  rw [a3q_locLen_eq_length (B := B) P (A ⧸ I) (B ⊗[A] (A ⧸ I))
    (TensorProduct.mk A B (A ⧸ I) 1)]
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toLinearEquiv.length_eq


/-- IntersectionProductSV: extending a target stalk prime commutes with
specialization of the source stalk. -/
theorem a3sv_pullback_quotient_map {X Y : Scheme.{u}} (f : X ⟶ Y) {w T : X}
    (h : w ⤳ T) (v : Y) (hv : v ⤳ f w) :
    ((a3i_stalkIdeal Y (f T) v).map (f.stalkMap T).hom).map
      (X.presheaf.stalkSpecializes h).hom =
        (a3i_stalkIdeal Y (f w) v).map (f.stalkMap w).hom := by
  rw [← a3q_map_stalkIdeal Y (h.map f.continuous) hv, Ideal.map_map, Ideal.map_map]
  congr 1
  exact congrArg CommRingCat.Hom.hom (f.stalkSpecializes_stalkMap w T h).symm


/-- IntersectionProductSV: once the truncation reaches the regular local
dimension, the prime quotient Tor pairing is Serre's multiplicity. -/
theorem a3sv_chi_quotients_eq_serreMult (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (T u v : X.left) (m : ℕ)
    (hm : ringKrullDim (X.left.presheaf.stalk T) ≤ m) :
    a3s_chi m (ModuleCat.of (X.left.presheaf.stalk T)
      (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T u))
      (ModuleCat.of (X.left.presheaf.stalk T)
        (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T v)) = a3i_serreMult X.left T u v := by
  haveI := a3c_isRegularLocalRing_stalk X T
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp (a3c_coheight_ne_top X.left T)
  have hcd : ringKrullDim (X.left.presheaf.stalk T) ≤ c := by
    rw [ringKrullDim_stalk_eq_coheight, ← hc]
    rfl
  have hcm : c ≤ m := by
    rw [ringKrullDim_stalk_eq_coheight, ← hc] at hm
    exact_mod_cast hm
  rw [← a3w_chi_eq_of_le _ _ hcd hcm]
  exact (a3z_serreMult_eq_chi T u v c hc).symm


set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: localizing a pulled-back stalk quotient at a
component gives the quotient by the extended prime in the component's ambient stalk. -/
theorem a3sv_pullback_stalk_locLen {X Y : Scheme.{0}} (f : X ⟶ Y) {w T : X}
    (h : w ⤳ T) (v : Y) (hv : v ⤳ f w) :
    a3e_locLen (a3y_pt T w h)
      ((ModuleCat.extendScalars (f.stalkMap T).hom).obj
        (ModuleCat.of (Y.presheaf.stalk (f T)) (Y.presheaf.stalk (f T) ⧸ a3i_stalkIdeal Y (f T) v))) =
      Module.length (X.presheaf.stalk w)
        (X.presheaf.stalk w ⧸ (a3i_stalkIdeal Y (f w) v).map (f.stalkMap w).hom) := by
  letI := (f.stalkMap T).hom.toAlgebra
  have e : (ModuleCat.extendScalars (f.stalkMap T).hom).obj
      (ModuleCat.of (Y.presheaf.stalk (f T)) (Y.presheaf.stalk (f T) ⧸ a3i_stalkIdeal Y (f T) v)) ≅
      ModuleCat.of (X.presheaf.stalk T)
        (X.presheaf.stalk T ⧸ (a3i_stalkIdeal Y (f T) v).map (f.stalkMap T).hom) :=
    a3w_extQuot (a3i_stalkIdeal Y (f T) v)
  rw [a3e_locLen_congr _ e.toLinearEquiv]
  letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk w) (a3y_pt T w h).asIdeal :=
    a3q_isLocalization_stalkSpecializes X h
  rw [a3sv_locLen_quotient_model (B := X.presheaf.stalk w)]
  rw [show algebraMap (X.presheaf.stalk T) (X.presheaf.stalk w) =
    (X.presheaf.stalkSpecializes h).hom from rfl, a3sv_pullback_quotient_map f h v hv]

/-- IntersectionProductSV: the flat pullback cycle coefficient is the
localized length of the pulled-back quotient at any specialization. -/
theorem a3sv_pullback_coeff_locLen {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) (v : Y.left) (T w : X.left) (h : w ⤳ T)
    (hw : ccm3_flatPullbackPrime f.left v w ≠ 0) :
    ccm3_flatPullbackPrime f.left v w =
      ((a3e_locLen (a3y_pt T w h)
        ((ModuleCat.extendScalars (f.left.stalkMap T).hom).obj
          (ModuleCat.of (Y.left.presheaf.stalk (f.left T))
            (Y.left.presheaf.stalk (f.left T) ⧸ a3i_stalkIdeal Y.left (f.left T) v)))).toNat : ℚ) := by
  obtain ⟨y, rfl, hy⟩ := (ccm3_flatPullbackPrime_support_aux f v w).mp hw
  rw [ccm3_flatPullbackPrime_coeff_aux f v y hy,
    a3sv_pullback_stalk_locLen f.left h v (a3sv_flatPullback_specializes f v _ hw),
    a3sv_inverseStalk_length]

/-- IntersectionProductSV: the coefficient of intersecting a prime with a
flat pullback is the ambient stalk Tor pairing of its pulled-back quotient. -/
theorem a3sv_pullback_intersect_coeff_chi {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] (u T : X.left) (v : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (hu : u ⤳ T) (hv : v ⤳ f.left T)
    (hT : Order.coheight T = Order.coheight u + Order.coheight v)
    (m : ℕ) (hm : ringKrullDim (X.left.presheaf.stalk T) ≤ m) :
    (∑ᶠ w : X.left, ccm3_flatPullbackPrime f.left v w * a3i_intersectPrime X.left u w T) =
      (a3s_chi m (ModuleCat.of (X.left.presheaf.stalk T)
        (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T u))
        ((ModuleCat.extendScalars (f.left.stalkMap T).hom).obj
          (ModuleCat.of (Y.left.presheaf.stalk (f.left T))
            (Y.left.presheaf.stalk (f.left T) ⧸ a3i_stalkIdeal Y.left (f.left T) v))) : ℚ) := by
  classical
  let N := (ModuleCat.extendScalars (f.left.stalkMap T).hom).obj
    (ModuleCat.of (Y.left.presheaf.stalk (f.left T))
      (Y.left.presheaf.stalk (f.left T) ⧸ a3i_stalkIdeal Y.left (f.left T) v))
  let U := ModuleCat.of (X.left.presheaf.stalk T)
    (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T u)
  have hs : Function.support (fun w : X.left =>
      ccm3_flatPullbackPrime f.left v w * a3i_intersectPrime X.left u w T) ⊆
      (a3sv_pullbackComponentsAt f.left v T : Set X.left) := by
    intro w hw
    obtain ⟨hw', hi⟩ := mul_ne_zero_iff.mp hw
    exact (a3sv_mem_pullbackComponentsAt f.left v T w).mpr
      ⟨hw', (a3y_comps_spec u w (a3z_intersectPrime_ne_zero X.left u w T hi)).2.1⟩
  rw [finsum_eq_sum_of_support_subset _ hs]
  change _ = (a3s_chi m U N : ℚ)
  rw [a3s_chi_symm m U N, a3sv_pullback_stalk_devissage f u T v hp hu hv hT m hm]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro w hw
  obtain ⟨hw', hwT⟩ := (a3sv_mem_pullbackComponentsAt f.left v T w).mp hw
  have hcw : Order.coheight w = Order.coheight v := by
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp (a3c_coheight_ne_top Y.left v)
    exact (ccm3_flatPullbackPrime_codimension_aux f c v hc.symm w hw').trans hc
  rw [a3z_intersectPrime_apply_of_proper X.left u w T (hp w hw') hu hwT
    (by rw [hcw]; exact hT)]
  rw [a3y_ptOr, dif_pos hwT, ← a3sv_pullback_coeff_locLen f v T w hwT hw']
  congr 1
  rw [a3s_chi_symm m, a3sv_chi_quotients_eq_serreMult X T u w m hm]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: a degree-weighted source intersection coefficient
is the target-stalk Tor pairing of the source component stalk. -/
theorem a3sv_pullback_weighted_point {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] (u : X.left) (t : cycleComponent X.left u) (v : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (hv : v ⤳ f.left (cycleComponentι X.left u t))
    (ht : Order.coheight (cycleComponentι X.left u t) = Order.coheight u + Order.coheight v)
    (m : ℕ) (hm : ringKrullDim (X.left.presheaf.stalk (cycleComponentι X.left u t)) ≤ m) :
    (∑ᶠ w : X.left, ccm3_flatPullbackPrime f.left v w *
      a3i_intersectPrime X.left u w (cycleComponentι X.left u t)) *
        (a1p_degree f.left (cycleComponentι X.left u t) : ℚ) =
      (a3s_chi m
        ((ModuleCat.restrictScalars ((cycleComponentι X.left u ≫ f.left).stalkMap t).hom).obj
          (ModuleCat.of ((cycleComponent X.left u).presheaf.stalk t)
            ((cycleComponent X.left u).presheaf.stalk t)))
        (ModuleCat.of (Y.left.presheaf.stalk (f.left (cycleComponentι X.left u t)))
          (Y.left.presheaf.stalk (f.left (cycleComponentι X.left u t)) ⧸
            a3i_stalkIdeal Y.left (f.left (cycleComponentι X.left u t)) v)) : ℚ) := by
  have hu : u ⤳ cycleComponentι X.left u t := by
    have h := ((genericPoint_spec (cycleComponent X.left u)).specializes
      (Set.mem_univ t)).map (cycleComponentι X.left u).continuous
    simpa only [a3m_cycleComponentι_genericPoint] using h
  rw [a3sv_pullback_intersect_coeff_chi f u _ v hp hu hv ht m hm,
    a3sv_componentStalk_chi_restrict]
  simp only [Int.cast_mul, Int.cast_natCast]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: finiteness on an affine target neighborhood
gives a finite map on its rings of sections. -/
theorem a3sv_finite_restrict_sections {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (hV : IsAffineOpen V) [IsFinite (f ∣_ V)] :
    IsAffineOpen (f ⁻¹ᵁ V) ∧ (f.app V).hom.Finite := by
  haveI : IsAffine V.toScheme := hV
  refine ⟨isAffine_of_isAffineHom (f ∣_ V), ?_⟩
  have hf := (f ∣_ V).finite_appTop
  rw [morphismRestrict_appTop, CommRingCat.hom_comp,
    RingHom.finite_respectsIso.cancel_right_isIso] at hf
  have hf : (f.app (V.ι ''ᵁ ⊤)).hom.Finite := hf
  rwa [Scheme.Opens.ι_image_top] at hf


/-- IntersectionProductSV: a finite proper fiber has affine coordinates
with a finite source algebra. -/
theorem a3sv_exists_finite_affine_sections {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (y : Y) (hy : (f ⁻¹' {y}).Finite) :
    ∃ V : Y.Opens, y ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen (f ⁻¹ᵁ V) ∧
      (f.app V).hom.Finite := by
  obtain ⟨V, hyV, hV, hf⟩ := a3sv_exists_affine_finite_neighborhood f y hy
  haveI : IsFinite (f ∣_ V) := hf
  exact ⟨V, hyV, hV, a3sv_finite_restrict_sections f V hV⟩

/-- IntersectionProductSV: the natural residue-field length of a stalk map
is its cycle pushforward degree. -/
theorem a3sv_stalk_residue_length_toNat {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    (Module.length (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x))).toNat = a1p_degree f x := by
  letI := (f.stalkMap x).hom.toAlgebra
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have hmod : (f.residueFieldMap x).hom.toAlgebra.toModule =
      (inferInstance : Module (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
        (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
    apply Module.ext
    funext a b
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := Y.presheaf.stalk (f x)) a
    rfl
  rw [Module.length_eq_rank, Cardinal.toNat_toENat]
  unfold a1p_degree Module.finrank
  rw [hmod]
  rfl

/-- IntersectionProductSV: the generic stalk of an integral scheme has
restricted length equal to its residue degree over the target stalk. -/
theorem a3sv_genericStalk_length_degree {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y) :
    (Module.length (Y.presheaf.stalk (f (genericPoint X)))
      ((ModuleCat.restrictScalars (f.stalkMap (genericPoint X)).hom).obj
        (ModuleCat.of (X.presheaf.stalk (genericPoint X)) (X.presheaf.stalk (genericPoint X))))).toNat =
      a1p_degree f (genericPoint X) := by
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X))) := inferInstanceAs
    (IsLocalHom (f.stalkMap (genericPoint X)).hom)
  have hl := IsLocalRing.length_restrictScalars (Y.presheaf.stalk (f (genericPoint X)))
    (X.presheaf.stalk (genericPoint X)) (X.presheaf.stalk (genericPoint X))
  have hone : Module.length (X.presheaf.stalk (genericPoint X))
      (X.presheaf.stalk (genericPoint X)) = 1 := by
    change Module.length X.functionField X.functionField = 1
    exact Module.length_eq_one _ _
  rw [hone, one_mul] at hl
  change (Module.length (Y.presheaf.stalk (f (genericPoint X)))
    (X.presheaf.stalk (genericPoint X))).toNat = _
  rw [hl]
  exact a3sv_stalk_residue_length_toNat f _
set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: affine coordinates identify a geometric fiber
with the primes above the coordinate prime of its target point. -/
def a3sv_affineOpenFiberEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen (f ⁻¹ᵁ V))
    (y : Y) (hy : y ∈ V) :
    {x : X // f x = y} ≃
      {P : PrimeSpectrum Γ(X, f ⁻¹ᵁ V) //
        P.comap (f.app V).hom = hV.primeIdealOf ⟨y, hy⟩} := by
  let e := hW.isoSpec.hom.homeomorph
  have hn (x : f ⁻¹ᵁ V) :
      (hW.primeIdealOf x).comap (f.app V).hom =
        hV.primeIdealOf ⟨f x, x.property⟩ := by
    simpa only [Scheme.Hom.appLE_eq_app] using
      IsAffineOpen.comap_primeIdealOf_appLE V hV (f ⁻¹ᵁ V) hW le_rfl x.property
  refine Equiv.ofBijective (fun x => ⟨hW.primeIdealOf ⟨x, by
    change f x ∈ V
    rw [x.property]
    exact hy⟩, ?_⟩) ⟨?_, ?_⟩
  · rw [hn]
    congr 1
    exact Subtype.ext x.property
  · intro x x' h
    apply Subtype.ext
    have he := congrArg hW.fromSpec (congrArg Subtype.val h)
    simpa only [hW.fromSpec_primeIdealOf] using he
  · intro P
    obtain ⟨x, hx⟩ := e.surjective P.val
    change hW.primeIdealOf x = P.val at hx
    have hxy : f x.val = y := by
      have he : hV.primeIdealOf ⟨f x.val, x.property⟩ = hV.primeIdealOf ⟨y, hy⟩ := by
        rw [← hn, hx]
        exact P.property
      have he' := congrArg hV.fromSpec he
      simpa only [hV.fromSpec_primeIdealOf] using he'
    exact ⟨⟨x.val, hxy⟩, Subtype.ext hx⟩

/-- IntersectionProductSV: the affine section algebra localized along
the target stalk. -/
abbrev a3sv_affineStalkAlgebra {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (y : Y) (hy : y ∈ V) :=
  letI := (f.app V).hom.toAlgebra
  letI := Y.presheaf.algebra_section_stalk ⟨y, hy⟩
  (Y.presheaf.stalk y) ⊗[Γ(Y, V)] Γ(X, f ⁻¹ᵁ V)


/-- IntersectionProductSV: a finite affine section algebra remains finite
after passage to the target stalk. -/
theorem a3sv_affineStalkAlgebra_finite {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (y : Y) (hy : y ∈ V) (hf : (f.app V).hom.Finite) :
    (algebraMap (Y.presheaf.stalk y) (a3sv_affineStalkAlgebra f V y hy)).Finite := by
  letI := (f.app V).hom.toAlgebra
  letI := Y.presheaf.algebra_section_stalk ⟨y, hy⟩
  haveI : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hf
  apply RingHom.finite_algebraMap.mpr
  exact Module.Finite.base_change Γ(Y, V) (Y.presheaf.stalk y) Γ(X, f ⁻¹ᵁ V)


/-- IntersectionProductSV: the stalk base change of an integral affine
source is a domain whenever the chosen target point lies under a source point. -/
theorem a3sv_affineStalkAlgebra_isDomain {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V)
    (hW : IsAffineOpen (f ⁻¹ᵁ V)) (x : X) (hx : f x ∈ V) :
    IsDomain (a3sv_affineStalkAlgebra f V (f x) hx) := by
  let R := Γ(Y, V)
  let S := Γ(X, f ⁻¹ᵁ V)
  let A := Y.presheaf.stalk (f x)
  letI := (f.app V).hom.toAlgebra
  letI := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  let B := A ⊗[R] S
  letI : Algebra S B := Algebra.TensorProduct.rightAlgebra
  let P := hV.primeIdealOf ⟨f x, hx⟩
  let Q := hW.primeIdealOf ⟨x, hx⟩
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨x, hx⟩⟩
  haveI : IsLocalization.AtPrime A P.asIdeal := hV.isLocalization_stalk ⟨f x, hx⟩
  haveI : IsLocalization (P.asIdeal.primeCompl.map (algebraMap R S)) B :=
    IsLocalization.tensorRight A P.asIdeal.primeCompl
  apply IsLocalization.isDomain_of_le_nonZeroDivisors B
    (M := P.asIdeal.primeCompl.map (algebraMap R S))
  rintro s ⟨r, hr, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro he
  have hn : Q.comap (f.app V).hom = P := by
    simpa only [Scheme.Hom.appLE_eq_app] using
      IsAffineOpen.comap_primeIdealOf_appLE V hV (f ⁻¹ᵁ V) hW le_rfl hx
  apply hr
  change r ∈ P.asIdeal
  rw [← hn]
  change (f.app V).hom r ∈ Q.asIdeal
  rw [show (f.app V).hom r = 0 from he]
  exact Q.asIdeal.zero_mem

/-- IntersectionProductSV: the section algebra over the target stalk maps
naturally to every source stalk above that target point. -/
def a3sv_affineStalkAlgebra_toStalk {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (x : X) (hx : f x ∈ V) :
    a3sv_affineStalkAlgebra f V (f x) hx →+* X.presheaf.stalk x := by
  let R := Γ(Y, V)
  let S := Γ(X, f ⁻¹ᵁ V)
  let A := Y.presheaf.stalk (f x)
  let C := X.presheaf.stalk x
  letI := (f.app V).hom.toAlgebra
  letI := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  letI : Algebra A C := (f.stalkMap x).hom.toAlgebra
  letI : Algebra R C := ((f.stalkMap x).hom.comp (Y.presheaf.germ V (f x) hx).hom).toAlgebra
  haveI : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' rfl
  let g : S →ₐ[R] C :=
    { (X.presheaf.germ (f ⁻¹ᵁ V) x hx).hom with
      commutes' := fun r => (f.germ_stalkMap_apply V x hx r).symm }
  exact (Algebra.TensorProduct.lift (Algebra.ofId A C) g
    (fun _ _ => Commute.all _ _)).toRingHom


/-- IntersectionProductSV: the natural source-stalk map extends the
target stalk map. -/
theorem a3sv_affineStalkAlgebra_toStalk_left {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (x : X) (hx : f x ∈ V) :
    (a3sv_affineStalkAlgebra_toStalk f V x hx).comp
      (algebraMap (Y.presheaf.stalk (f x)) (a3sv_affineStalkAlgebra f V (f x) hx)) =
      (f.stalkMap x).hom := by
  ext a
  simp only [a3sv_affineStalkAlgebra_toStalk, RingHom.comp_apply,
    Algebra.TensorProduct.algebraMap_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl


/-- IntersectionProductSV: the natural source-stalk map extends the
source germ map on affine sections. -/
theorem a3sv_affineStalkAlgebra_toStalk_right {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (x : X) (hx : f x ∈ V) :
    letI := (f.app V).hom.toAlgebra
    letI := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
    letI : Algebra Γ(X, f ⁻¹ᵁ V) (a3sv_affineStalkAlgebra f V (f x) hx) :=
      Algebra.TensorProduct.rightAlgebra
    (a3sv_affineStalkAlgebra_toStalk f V x hx).comp
      (algebraMap Γ(X, f ⁻¹ᵁ V) (a3sv_affineStalkAlgebra f V (f x) hx)) =
      (X.presheaf.germ (f ⁻¹ᵁ V) x hx).hom := by
  ext s
  simp [a3sv_affineStalkAlgebra_toStalk,
    Algebra.TensorProduct.right_algebraMap_apply]

/-- IntersectionProductSV: compatibility over the unlocalized base
extends uniquely across localization of that base. -/
theorem a3sv_localization_scalarTower {R S A B C : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra R C]
    [Algebra S B] [Algebra S C] [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower R S B] [IsScalarTower R S C]
    [IsScalarTower R A B] [IsScalarTower R A C] [IsScalarTower S B C]
    (M : Submonoid R) [IsLocalization M A] : IsScalarTower A B C := by
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext M
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R A B,
    IsScalarTower.algebraMap_eq R S B, ← RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq S B C, ← IsScalarTower.algebraMap_eq R S C,
    ← IsScalarTower.algebraMap_eq R A C]

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: localization of the finite affine stalk algebra
at a fiber prime is the corresponding source stalk as a target-stalk module. -/
def a3sv_affineStalkAlgebra_stalkIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen (f ⁻¹ᵁ V))
    (x : X) (hx : f x ∈ V) :
    letI := (f.app V).hom.toAlgebra
    letI := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
    letI : Algebra Γ(X, f ⁻¹ᵁ V) (a3sv_affineStalkAlgebra f V (f x) hx) :=
      Algebra.TensorProduct.rightAlgebra
    ∀ (Q : PrimeSpectrum (a3sv_affineStalkAlgebra f V (f x) hx)),
      Q.comap (algebraMap Γ(X, f ⁻¹ᵁ V) (a3sv_affineStalkAlgebra f V (f x) hx)) =
        hW.primeIdealOf ⟨x, hx⟩ →
      ((ModuleCat.restrictScalars
        (algebraMap (Y.presheaf.stalk (f x)) (Localization.AtPrime Q.asIdeal))).obj
          (ModuleCat.of (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q.asIdeal)) ≅
      (ModuleCat.restrictScalars (f.stalkMap x).hom).obj
          (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))) := by
  let R := Γ(Y, V)
  let S := Γ(X, f ⁻¹ᵁ V)
  let A := Y.presheaf.stalk (f x)
  let C := X.presheaf.stalk x
  letI := (f.app V).hom.toAlgebra
  letI := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  let B := A ⊗[R] S
  letI : Algebra S B := Algebra.TensorProduct.rightAlgebra
  intro Q hQ
  let D := Localization.AtPrime Q.asIdeal
  let P := hV.primeIdealOf ⟨f x, hx⟩
  letI : Algebra S C := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  letI : Algebra A C := (f.stalkMap x).hom.toAlgebra
  letI : Algebra R C := ((X.presheaf.germ (f ⁻¹ᵁ V) x hx).hom.comp (f.app V).hom).toAlgebra
  haveI : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq fun r =>
    (f.germ_stalkMap_apply V x hx r).symm
  haveI : IsLocalization.AtPrime A P.asIdeal := hV.isLocalization_stalk ⟨f x, hx⟩
  haveI : IsLocalization (P.asIdeal.primeCompl.map (algebraMap R S)) B :=
    IsLocalization.tensorRight A P.asIdeal.primeCompl
  haveI : IsLocalization.AtPrime D (Q.comap (algebraMap S B)).asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (P.asIdeal.primeCompl.map (algebraMap R S)) D Q.asIdeal
  haveI : IsLocalization.AtPrime C (Q.comap (algebraMap S B)).asIdeal := by
    rw [hQ]
    exact hW.isLocalization_stalk ⟨x, hx⟩
  exact a3sv_localization_modelModuleIso (R := R) (S := S) (A := A)
    (C := D) (D := C) P.asIdeal.primeCompl (Q.comap (algebraMap S B))

/-- IntersectionProductSV: localization into a domain stalk is injective
when the source section ring is a domain. -/
theorem a3sv_localization_algebraMap_injective {S B C : Type u}
    [CommRing S] [CommRing B] [CommRing C] [IsDomain S]
    [Algebra S B] [Algebra S C] [Algebra B C] [IsScalarTower S B C]
    (M : Submonoid S) [IsLocalization M B]
    (hC : Function.Injective (algebraMap S C)) :
    Function.Injective (algebraMap B C) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply le_antisymm ?_ bot_le
  intro b hb
  obtain ⟨⟨s, m⟩, he⟩ := IsLocalization.surj M b
  have hs : algebraMap S C s = 0 := by
    rw [IsScalarTower.algebraMap_apply S B C, ← he, map_mul,
      RingHom.mem_ker.mp hb, zero_mul]
  have hs0 : s = 0 := hC (by simpa using hs)
  have he0 : b * algebraMap S B m = 0 := by simpa [hs0] using he
  exact (IsLocalization.map_units B m).mul_left_eq_zero.mp he0

/-- IntersectionProductSV: the natural map from an integral affine stalk
algebra to a source stalk is injective. -/
theorem a3sv_affineStalkAlgebra_toStalk_injective {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V)
    (x : X) (hx : f x ∈ V) :
    Function.Injective (a3sv_affineStalkAlgebra_toStalk f V x hx) := by
  let R := Γ(Y, V)
  let S := Γ(X, f ⁻¹ᵁ V)
  let A := Y.presheaf.stalk (f x)
  let C := X.presheaf.stalk x
  letI := (f.app V).hom.toAlgebra
  letI := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  let B := A ⊗[R] S
  letI : Algebra S B := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S C := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  letI : Algebra B C := (a3sv_affineStalkAlgebra_toStalk f V x hx).toAlgebra
  haveI : IsScalarTower S B C := IsScalarTower.of_algebraMap_eq'
    (a3sv_affineStalkAlgebra_toStalk_right f V x hx).symm
  let P := hV.primeIdealOf ⟨f x, hx⟩
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨x, hx⟩⟩
  haveI : IsLocalization.AtPrime A P.asIdeal := hV.isLocalization_stalk ⟨f x, hx⟩
  haveI : IsLocalization (P.asIdeal.primeCompl.map (algebraMap R S)) B :=
    IsLocalization.tensorRight A P.asIdeal.primeCompl
  exact a3sv_localization_algebraMap_injective (B := B) (C := C)
    (P.asIdeal.primeCompl.map (algebraMap R S)) (germ_injective_of_isIntegral X x hx)


/-- IntersectionProductSV: the finite affine stalk algebra and any source
stalk above its base point have the same kernel over the target stalk. -/
theorem a3sv_affineStalkAlgebra_kernel {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V) (x : X) (hx : f x ∈ V) :
    RingHom.ker (algebraMap (Y.presheaf.stalk (f x))
      (a3sv_affineStalkAlgebra f V (f x) hx)) = RingHom.ker (f.stalkMap x).hom := by
  rw [← a3sv_affineStalkAlgebra_toStalk_left f V x hx,
    RingHom.ker_comp_of_injective _ (a3sv_affineStalkAlgebra_toStalk_injective f V hV x hx)]

/-- IntersectionProductSV: a stalk map from an integral source has kernel
the stalk prime of the image of the generic point. -/
theorem a3sv_integral_stalkMap_kernel {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) (x : X) :
    RingHom.ker (f.stalkMap x).hom = a3i_stalkIdeal Y (f x) (f (genericPoint X)) := by
  have he := a3y_comap_stalkIdeal f (genericPoint_specializes x)
  rw [a3c_stalkIdeal_genericPoint] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the generic localized length of the finite
affine stalk algebra equals the residue degree of the source generic point. -/
theorem a3sv_affineStalkAlgebra_genericLength {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V)
    (hW : IsAffineOpen (f ⁻¹ᵁ V)) (x : X) (hx : f x ∈ V)
    (hf : (f.app V).hom.Finite) :
    (a3e_locLen (a3y_pt (f x) (f (genericPoint X))
      ((genericPoint_specializes x).map f.continuous))
      (a3sv_affineStalkAlgebra f V (f x) hx)).toNat = a1p_degree f (genericPoint X) := by
  let R := Γ(Y, V)
  let S := Γ(X, f ⁻¹ᵁ V)
  let A := Y.presheaf.stalk (f x)
  let C := X.presheaf.stalk x
  let D := Y.presheaf.stalk (f (genericPoint X))
  let K := X.functionField
  letI := (f.app V).hom.toAlgebra
  letI := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  let B := A ⊗[R] S
  letI : Algebra S B := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S C := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  letI : Algebra B K := ((algebraMap C K).comp
    (a3sv_affineStalkAlgebra_toStalk f V x hx)).toAlgebra
  let h := (genericPoint_specializes x).map f.continuous
  letI : Algebra A D := (Y.presheaf.stalkSpecializes h).hom.toAlgebra
  letI : Algebra D K := (f.stalkMap (genericPoint X)).hom.toAlgebra
  letI : Algebra A K := ((f.stalkMap (genericPoint X)).hom.comp
    (Y.presheaf.stalkSpecializes h).hom).toAlgebra
  haveI : IsScalarTower A D K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A B K := by
    apply IsScalarTower.of_algebraMap_eq'
    change (f.stalkMap (genericPoint X)).hom.comp (Y.presheaf.stalkSpecializes h).hom =
      ((algebraMap C K).comp (a3sv_affineStalkAlgebra_toStalk f V x hx)).comp
        (algebraMap A B)
    rw [RingHom.comp_assoc, a3sv_affineStalkAlgebra_toStalk_left]
    exact congrArg CommRingCat.Hom.hom
      (f.stalkSpecializes_stalkMap (genericPoint X) x (genericPoint_specializes x))
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨x, hx⟩⟩
  haveI : IsScalarTower S C K := functionField_isScalarTower X (f ⁻¹ᵁ V) ⟨x, hx⟩
  haveI : IsScalarTower S B K := by
    apply IsScalarTower.of_algebraMap_eq'
    change algebraMap S K = ((algebraMap C K).comp
      (a3sv_affineStalkAlgebra_toStalk f V x hx)).comp (algebraMap S B)
    rw [RingHom.comp_assoc, a3sv_affineStalkAlgebra_toStalk_right]
    exact IsScalarTower.algebraMap_eq S C K
  let P := hV.primeIdealOf ⟨f x, hx⟩
  haveI : IsLocalization.AtPrime A P.asIdeal := hV.isLocalization_stalk ⟨f x, hx⟩
  haveI : IsLocalization (P.asIdeal.primeCompl.map (algebraMap R S)) B :=
    IsLocalization.tensorRight A P.asIdeal.primeCompl
  haveI : IsDomain B := a3sv_affineStalkAlgebra_isDomain f V hV hW x hx
  haveI : IsFractionRing S K := functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ V) hW
  haveI : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (P.asIdeal.primeCompl.map (algebraMap R S)) B K
  let q := a3y_pt (f x) (f (genericPoint X)) h
  haveI : IsLocalization.AtPrime D q.asIdeal := a3q_isLocalization_stalkSpecializes Y h
  have hq : q.asIdeal = RingHom.ker (algebraMap A B) := by
    rw [a3sv_affineStalkAlgebra_kernel f V hV x hx, a3sv_integral_stalkMap_kernel]
    rfl
  have hl := a3sv_finiteDomain_locLen (A := A) (B := B) (C := K) (D := D)
    (a3sv_affineStalkAlgebra_finite f V (f x) hx hf) q hq
  change (a3e_locLen q B).toNat = _
  rw [hl]
  exact a3sv_genericStalk_length_degree f

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: local Tor pairings in affine fiber coordinates
are the Tor pairings of the corresponding source stalks. -/
theorem a3sv_affineStalkAlgebra_chi_atFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen (f ⁻¹ᵁ V))
    (y v : Y) (hy : y ∈ V) (t : X) (ht : f t = y) :
    letI := (f.app V).hom.toAlgebra
    letI := Y.presheaf.algebra_section_stalk ⟨y, hy⟩
    letI : Algebra Γ(X, f ⁻¹ᵁ V) (a3sv_affineStalkAlgebra f V y hy) :=
      Algebra.TensorProduct.rightAlgebra
    ∀ (Q : PrimeSpectrum (a3sv_affineStalkAlgebra f V y hy)),
      Q.comap (algebraMap Γ(X, f ⁻¹ᵁ V) (a3sv_affineStalkAlgebra f V y hy)) =
        hW.primeIdealOf ⟨t, by change f t ∈ V; rw [ht]; exact hy⟩ →
      ∀ m : ℕ,
      a3s_chi m
        ((ModuleCat.restrictScalars
          (algebraMap (Y.presheaf.stalk y) (Localization.AtPrime Q.asIdeal))).obj
            (ModuleCat.of (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q.asIdeal)))
        (ModuleCat.of (Y.presheaf.stalk y) (Y.presheaf.stalk y ⧸ a3i_stalkIdeal Y y v)) =
      a3s_chi m ((ModuleCat.restrictScalars (f.stalkMap t).hom).obj
          (ModuleCat.of (X.presheaf.stalk t) (X.presheaf.stalk t)))
        (ModuleCat.of (Y.presheaf.stalk (f t)) (Y.presheaf.stalk (f t) ⧸ a3i_stalkIdeal Y (f t) v)) := by
  subst y
  intro Q hQ m
  exact a3s_chi_congr (a3sv_affineStalkAlgebra_stalkIso f V hV hW t hy Q hQ) _ m

/-- IntersectionProductSV: the finite-algebra Euler sum can be indexed by
the subtype of primes in its closed fiber. -/
theorem a3sv_finiteAlgebra_chi_finsum {A B : Type} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsNoetherianRing A] [Algebra A B]
    (hf : (algebraMap A B).Finite) (N : ModuleCat.{0} A) [Module.Finite A N]
    (hproper : ∀ Q : PrimeSpectrum A,
      Module.annihilator A ((ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B B)) ≤ Q.asIdeal →
      Module.annihilator A N ≤ Q.asIdeal → Q = IsLocalRing.closedPoint A) (m : ℕ) :
    a3s_chi m ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) N =
      ∑ᶠ P : {P : PrimeSpectrum B //
          P.comap (algebraMap A B) = IsLocalRing.closedPoint A},
        a3s_chi m
          ((ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime P.val.asIdeal))).obj
            (ModuleCat.of (Localization.AtPrime P.val.asIdeal) (Localization.AtPrime P.val.asIdeal))) N := by
  rw [a3sv_finiteAlgebra_chi_sum hf N hproper m]
  let F (P : PrimeSpectrum B) := a3s_chi m
    ((ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime P.asIdeal))).obj
      (ModuleCat.of (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal))) N
  change (∑ P ∈ a3sv_finiteAlgebraFiber (algebraMap A B) hf (IsLocalRing.closedPoint A), F P) =
    ∑ᶠ P : {P : PrimeSpectrum B // P.comap (algebraMap A B) = IsLocalRing.closedPoint A}, F P.val
  rw [finsum_subtype_eq_finsum_cond]
  have hs : {P : PrimeSpectrum B | P.comap (algebraMap A B) = IsLocalRing.closedPoint A} =
      (a3sv_finiteAlgebraFiber (algebraMap A B) hf (IsLocalRing.closedPoint A) : Set _) := by
    ext P
    exact (a3sv_mem_finiteAlgebraFiber (algebraMap A B) hf _ P).symm
  change _ = ∑ᶠ P ∈ {P : PrimeSpectrum B | P.comap (algebraMap A B) = IsLocalRing.closedPoint A}, _
  rw [hs, finsum_mem_coe_finset]


/-- IntersectionProductSV: the annihilator of a restricted regular module
is the kernel of the defining algebra map. -/
theorem a3sv_annihilator_algebraUnit {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    Module.annihilator A ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) =
      RingHom.ker f := by
  ext a
  rw [Module.mem_annihilator, RingHom.mem_ker]
  constructor
  · intro h
    have h1 := h (1 : B)
    change f a * 1 = 0 at h1
    simpa only [mul_one] using h1
  · intro h b
    change f a * (show B from b) = 0
    rw [h, zero_mul]


set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: the finite affine algebra Tor pairing is the
sum of source-stalk Tor pairings over its geometric fiber. -/
theorem a3sv_affineStalkAlgebra_chi_fiber {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V)
    (hW : IsAffineOpen (f ⁻¹ᵁ V)) (y v : Y) (hy : y ∈ V)
    (hf : (f.app V).hom.Finite)
    (hproper : ∀ P : PrimeSpectrum (Y.presheaf.stalk y),
      RingHom.ker (algebraMap (Y.presheaf.stalk y) (a3sv_affineStalkAlgebra f V y hy)) ≤ P.asIdeal →
      a3i_stalkIdeal Y y v ≤ P.asIdeal → P = IsLocalRing.closedPoint _) (m : ℕ) :
    a3s_chi m ((ModuleCat.restrictScalars
      (algebraMap (Y.presheaf.stalk y) (a3sv_affineStalkAlgebra f V y hy))).obj
        (ModuleCat.of (a3sv_affineStalkAlgebra f V y hy) (a3sv_affineStalkAlgebra f V y hy)))
      (ModuleCat.of (Y.presheaf.stalk y) (Y.presheaf.stalk y ⧸ a3i_stalkIdeal Y y v)) =
    ∑ᶠ t : {t : X // f t = y},
      a3s_chi m ((ModuleCat.restrictScalars (f.stalkMap t.val).hom).obj
          (ModuleCat.of (X.presheaf.stalk t.val) (X.presheaf.stalk t.val)))
        (ModuleCat.of (Y.presheaf.stalk (f t.val))
          (Y.presheaf.stalk (f t.val) ⧸ a3i_stalkIdeal Y (f t.val) v)) := by
  let R := Γ(Y, V)
  let S := Γ(X, f ⁻¹ᵁ V)
  let A := Y.presheaf.stalk y
  letI := (f.app V).hom.toAlgebra
  letI := Y.presheaf.algebra_section_stalk ⟨y, hy⟩
  let B := A ⊗[R] S
  letI : Algebra S B := Algebra.TensorProduct.rightAlgebra
  let P := hV.primeIdealOf ⟨y, hy⟩
  haveI : IsLocalization.AtPrime A P.asIdeal := hV.isLocalization_stalk ⟨y, hy⟩
  haveI : IsLocalization (P.asIdeal.primeCompl.map (algebraMap R S)) B :=
    IsLocalization.tensorRight A P.asIdeal.primeCompl
  let N := ModuleCat.of A (A ⧸ a3i_stalkIdeal Y y v)
  have hp : ∀ Q : PrimeSpectrum A,
      Module.annihilator A ((ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B B)) ≤ Q.asIdeal → Module.annihilator A N ≤ Q.asIdeal →
        Q = IsLocalRing.closedPoint A := by
    simpa only [N, a3sv_annihilator_algebraUnit, Ideal.annihilator_quotient] using hproper
  rw [a3sv_finiteAlgebra_chi_finsum (a3sv_affineStalkAlgebra_finite f V y hy hf) N hp m]
  let e₁ := a3sv_localizationFiberEquiv (R := R) (S := S) (A := A) (B := B) P
  let e₂ := a3sv_affineOpenFiberEquiv f V hV hW y hy
  let e := e₁.trans e₂.symm
  apply finsum_eq_of_bijective e e.bijective
  intro Q
  have he := congrArg Subtype.val (e₂.apply_symm_apply (e₁ Q))
  change hW.primeIdealOf ⟨(e Q).val, _⟩ = Q.val.comap (algebraMap S B) at he
  exact a3sv_affineStalkAlgebra_chi_atFiber f V hV hW y v hy (e Q).val (e Q).property
    Q.val he.symm m

set_option backward.isDefEq.respectTransparency false in
/-- IntersectionProductSV: devissage of the finite affine stalk algebra
expresses its proper Tor pairing using the generic image multiplicity. -/
theorem a3sv_affineStalkAlgebra_chi_generic {X : Scheme.{0}} [IsIntegral X]
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y.left) (V : Y.left.Opens) (hV : IsAffineOpen V)
    (hW : IsAffineOpen (f ⁻¹ᵁ V)) (x : X) (hx : f x ∈ V)
    (hf : (f.app V).hom.Finite) (v : Y.left)
    (hp : a3i_MeetProperly Y.left (f (genericPoint X)) v)
    (hv : v ⤳ f x)
    (ht : Order.coheight (f x) = Order.coheight (f (genericPoint X)) + Order.coheight v)
    (m : ℕ) (hm : ringKrullDim (Y.left.presheaf.stalk (f x)) ≤ m) :
    a3s_chi m ((ModuleCat.restrictScalars
      (algebraMap (Y.left.presheaf.stalk (f x)) (a3sv_affineStalkAlgebra f V (f x) hx))).obj
        (ModuleCat.of (a3sv_affineStalkAlgebra f V (f x) hx) (a3sv_affineStalkAlgebra f V (f x) hx)))
      (ModuleCat.of (Y.left.presheaf.stalk (f x))
        (Y.left.presheaf.stalk (f x) ⧸ a3i_stalkIdeal Y.left (f x) v)) =
      (a1p_degree f (genericPoint X) : ℤ) * a3i_serreMult Y.left (f x) (f (genericPoint X)) v := by
  let A := Y.left.presheaf.stalk (f x)
  let B := a3sv_affineStalkAlgebra f V (f x) hx
  let M := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  haveI : Module.Finite A M := a3sv_affineStalkAlgebra_finite f V (f x) hx hf
  have hu := (genericPoint_specializes x).map f.continuous
  have hk : Module.annihilator A M = a3i_stalkIdeal Y.left (f x) (f (genericPoint X)) := by
    rw [a3sv_annihilator_algebraUnit, a3sv_affineStalkAlgebra_kernel f V hV x hx,
      a3sv_integral_stalkMap_kernel]
  have he := a3sv_stalk_prime_devissage Y (f (genericPoint X)) v (f x) hu hv ht
    (a3sv_pair_stalk_support Y.left _ _ _ hp hu hv ht) m hm M
    (fun P hP => hk ▸ Module.annihilator_le_of_mem_support hP)
  rw [a3sv_chi_quotients_eq_serreMult Y (f x) (f (genericPoint X)) v m hm] at he
  have hg : (a3e_locLen (a3y_pt (f x) (f (genericPoint X)) hu) M).toNat =
      a1p_degree f (genericPoint X) := by
    have hmod : Module.compHom B (algebraMap A B) = (inferInstance : Module A B) := by
      apply Module.ext
      funext a b
      exact (Algebra.smul_def a b).symm
    simpa +instances only [M, ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj',
      ModuleCat.of, hmod] using a3sv_affineStalkAlgebra_genericLength f V hV hW x hx hf
  rwa [hg] at he

/-- IntersectionProductSV: every specialization of the generic image of
a proper integral source has a point above it. -/
theorem a3sv_proper_integral_fiber_nonempty {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) [IsProper f] (y : Y) (hy : f (genericPoint X) ⤳ y) :
    ∃ x : X, f x = y := by
  apply closure_minimal (Set.singleton_subset_iff.mpr
    (show f (genericPoint X) ∈ Set.range f from ⟨genericPoint X, rfl⟩))
    f.isClosedMap.isClosed_range
  exact specializes_iff_mem_closure.mp hy


/-- IntersectionProductSV: the sum of source-stalk Tor pairings over a
finite proper fiber is the generic degree times the image-prime pairing. -/
theorem a3sv_proper_integral_tor_fiber {X : Scheme.{0}} [IsIntegral X]
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y.left) [IsProper f] (y v : Y.left)
    (hfin : (f ⁻¹' {y}).Finite) (hu : f (genericPoint X) ⤳ y)
    (hp : a3i_MeetProperly Y.left (f (genericPoint X)) v) (hv : v ⤳ y)
    (ht : Order.coheight y = Order.coheight (f (genericPoint X)) + Order.coheight v)
    (m : ℕ) (hm : ringKrullDim (Y.left.presheaf.stalk y) ≤ m) :
    (∑ᶠ t : {t : X // f t = y},
      a3s_chi m ((ModuleCat.restrictScalars (f.stalkMap t.val).hom).obj
          (ModuleCat.of (X.presheaf.stalk t.val) (X.presheaf.stalk t.val)))
        (ModuleCat.of (Y.left.presheaf.stalk (f t.val))
          (Y.left.presheaf.stalk (f t.val) ⧸ a3i_stalkIdeal Y.left (f t.val) v))) =
      (a1p_degree f (genericPoint X) : ℤ) * a3i_serreMult Y.left y (f (genericPoint X)) v := by
  obtain ⟨x, rfl⟩ := a3sv_proper_integral_fiber_nonempty f y hu
  obtain ⟨V, hx, hV, hW, hf⟩ := a3sv_exists_finite_affine_sections f (f x) hfin
  have hproper : ∀ P : PrimeSpectrum (Y.left.presheaf.stalk (f x)),
      RingHom.ker (algebraMap (Y.left.presheaf.stalk (f x))
        (a3sv_affineStalkAlgebra f V (f x) hx)) ≤ P.asIdeal →
      a3i_stalkIdeal Y.left (f x) v ≤ P.asIdeal → P = IsLocalRing.closedPoint _ := by
    rw [a3sv_affineStalkAlgebra_kernel f V hV x hx, a3sv_integral_stalkMap_kernel]
    exact a3sv_pair_stalk_support Y.left _ _ _ hp hu hv ht
  rw [← a3sv_affineStalkAlgebra_chi_fiber f V hV hW (f x) v hx hf hproper m]
  exact a3sv_affineStalkAlgebra_chi_generic Y f V hV hW x hx hf v hp hv ht m hm

/-- IntersectionProductSV: source-prime points over a target intersection
component have the expected source intersection codimension. -/
theorem a3sv_source_prime_fiber_coheight {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] [IsProper f.left] (u : X.left) (v z : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w)
    (hd : 0 < a1p_degree f.left u) (hz : z ∈ a3y_comps (f.left u) v)
    (q : X.left) (huq : u ⤳ q) (hfq : f.left q = z) :
    Order.coheight q = Order.coheight u + Order.coheight v := by
  obtain ⟨w, hw, hqw⟩ := a3sv_point_over_image_component f u v z hp hd hz q huq hfq
  rw [a3y_coheight_comps u w (hp w hw) hqw]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (a3c_coheight_ne_top Y.left v)
  rw [ccm3_flatPullbackPrime_codimension_aux f n v hn.symm w hw, hn]


/-- IntersectionProductSV: the pullback intersection coefficient vanishes
away from the closure of the source prime. -/
theorem a3sv_pullback_intersect_eq_zero_of_not_specializes
    {X Y : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Y) (u t : X) (v : Y)
    (hu : ¬ u ⤳ t) :
    (∑ᶠ w : X, ccm3_flatPullbackPrime f v w * a3i_intersectPrime X u w t) = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro w
  have hi : a3i_intersectPrime X u w t = 0 := by
    by_contra h
    exact hu (a3y_comps_spec u w (a3z_intersectPrime_ne_zero X u w t h)).1
  rw [hi, mul_zero]


/-- IntersectionProductSV: the ambient fiber coefficient sum is supported
on the source prime and can be indexed by its component scheme. -/
theorem a3sv_pullback_fiber_reindex {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) (u : X) (v z : Y) :
    (∑ᶠ t : f ⁻¹' {z},
      (∑ᶠ w : X, ccm3_flatPullbackPrime f v w * a3i_intersectPrime X u w t) *
        (a1p_degree f t : ℚ)) =
    ∑ᶠ t : {t : cycleComponent X u // (cycleComponentι X u ≫ f) t = z},
      (∑ᶠ w : X, ccm3_flatPullbackPrime f v w *
        a3i_intersectPrime X u w (cycleComponentι X u t.val)) *
          (a1p_degree f (cycleComponentι X u t.val) : ℚ) := by
  classical
  let e : {t : cycleComponent X u // (cycleComponentι X u ≫ f) t = z} → f ⁻¹' {z} :=
    fun t => ⟨cycleComponentι X u t.val, t.property⟩
  have hi : Function.Injective e := by
    intro t t' h
    have he : (e t).val = (e t').val := congrArg (fun s : f ⁻¹' {z} => s.val) h
    exact Subtype.ext ((cycleComponentι X u).isClosedEmbedding.injective he)
  let F (t : f ⁻¹' {z}) : ℚ :=
    (∑ᶠ w : X, ccm3_flatPullbackPrime f v w * a3i_intersectPrime X u w t) *
      (a1p_degree f t : ℚ)
  have hs : Function.support F ⊆ Set.range e := by
    intro t ht
    have hu : u ⤳ t.val := by
      by_contra h
      exact ht (by simp only [F, a3sv_pullback_intersect_eq_zero_of_not_specializes f u t v h, zero_mul])
    have hr : t.val ∈ Set.range (cycleComponentι X u) := by
      rw [range_cycleComponentι]
      exact specializes_iff_mem_closure.mp hu
    obtain ⟨q, hq⟩ := hr
    refine ⟨⟨q, ?_⟩, Subtype.ext hq⟩
    change f (cycleComponentι X u q) = z
    rw [hq]
    exact t.property
  change (∑ᶠ t, F t) = ∑ᶠ t, F (e t)
  rw [← finsum_mem_range hi, finsum_mem_def, Set.indicator_eq_self.mpr hs]

/-- IntersectionProductLoc2 P2: the residue-degree weighted coefficient formula
for a prime cycle and the inverse image of a prime cycle. -/
theorem a3i_proper_pushforward_mult {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    [IsProjective Y.hom] (f : X ⟶ Y) [Flat f.left] [IsProper f.left]
    (u : X.left) (v z : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w) :
    (∑ᶠ t : f.left ⁻¹' {z},
      (∑ᶠ w : X.left, ccm3_flatPullbackPrime f.left v w * a3i_intersectPrime X.left u w t) *
        (a1p_degree f.left t : ℚ)) =
      (a1p_degree f.left u : ℚ) * a3i_intersectPrime Y.left (f.left u) v z := by
  classical
  by_cases hd : a1p_degree f.left u = 0
  · exact a3sv_proper_pushforward_mult_of_degree_zero f u v z hp hd
  by_cases hz : z ∈ a3y_comps (f.left u) v
  · have hd' := Nat.pos_of_ne_zero hd
    have hpY := a3sv_image_meetProperly f u v hp hd'
    obtain ⟨huz, hvz, _⟩ := a3y_comps_spec (f.left u) v hz
    have hcz := a3y_coheight_comps (f.left u) v hpY hz
    let U := cycleComponent X.left u
    let ι := cycleComponentι X.left u
    let g := ι ≫ f.left
    have hgen : g (genericPoint U) = f.left u := by
      simp only [g, Scheme.Hom.comp_apply, ι, U, a3m_cycleComponentι_genericPoint]
    have hfin : (g ⁻¹' {z}).Finite := by
      apply Set.Finite.of_finite_image (f := ι) _ ι.isClosedEmbedding.injective.injOn
      apply (a3sv_finite_source_prime_fiber f u v z hp hd' hz).subset
      rintro _ ⟨q, hq, rfl⟩
      refine ⟨?_, hq⟩
      have h := (genericPoint_specializes q).map ι.continuous
      simpa only [ι, U, a3m_cycleComponentι_genericPoint] using h
    have hcod (t : {t : U // g t = z}) :
        Order.coheight (ι t.val) = Order.coheight u + Order.coheight v := by
      apply a3sv_source_prime_fiber_coheight f u v z hp hd' hz (ι t.val) ?_ t.property
      have h := (genericPoint_specializes t.val).map ι.continuous
      simpa only [ι, U, a3m_cycleComponentι_genericPoint] using h
    obtain ⟨nx, hnx⟩ := ENat.ne_top_iff_exists.mp
      (show Order.coheight u + Order.coheight v ≠ ⊤ from
        fun h => (ENat.add_eq_top.mp h).elim
          (a3c_coheight_ne_top X.left u) (a3c_coheight_ne_top Y.left v))
    obtain ⟨ny, hny⟩ := ENat.ne_top_iff_exists.mp (a3c_coheight_ne_top Y.left z)
    let m := nx + ny
    have hmY : ringKrullDim (Y.left.presheaf.stalk z) ≤ m := by
      rw [ringKrullDim_stalk_eq_coheight, ← hny]
      exact_mod_cast Nat.le_add_left ny nx
    have hmX (t : {t : U // g t = z}) :
        ringKrullDim (X.left.presheaf.stalk (ι t.val)) ≤ m := by
      rw [ringKrullDim_stalk_eq_coheight, hcod t, ← hnx]
      exact_mod_cast Nat.le_add_right nx ny
    have ht := a3sv_proper_integral_tor_fiber Y g z v hfin
      (by rw [hgen]; exact huz) (by rw [hgen]; exact hpY) hvz
      (by rw [hgen]; exact hcz) m hmY
    have hgdeg : a1p_degree g (genericPoint U) = a1p_degree f.left u := by
      simp only [g, a1p_degree_comp_aux, a3m_degree_closedImmersion,
        ι, U, a3m_cycleComponentι_genericPoint, one_mul, mul_one]
    rw [hgen, hgdeg] at ht
    haveI : Finite {t : U // g t = z} := hfin.to_subtype
    letI : Fintype {t : U // g t = z} := Fintype.ofFinite _
    have htQ := congrArg (fun n : ℤ => (n : ℚ)) ht
    simp only [finsum_eq_sum_of_fintype, Int.cast_sum, Int.cast_mul, Int.cast_natCast] at htQ
    rw [a3sv_pullback_fiber_reindex,
      a3z_intersectPrime_apply_of_proper Y.left (f.left u) v z hpY huz hvz hcz]
    change (∑ᶠ t : {t : U // g t = z},
      (∑ᶠ w : X.left, ccm3_flatPullbackPrime f.left v w *
        a3i_intersectPrime X.left u w (ι t.val)) * (a1p_degree f.left (ι t.val) : ℚ)) = _
    rw [finsum_eq_sum_of_fintype]
    calc
      _ = ∑ t : {t : U // g t = z},
          (a3s_chi m ((ModuleCat.restrictScalars (g.stalkMap t.val).hom).obj
            (ModuleCat.of (U.presheaf.stalk t.val) (U.presheaf.stalk t.val)))
            (ModuleCat.of (Y.left.presheaf.stalk (g t.val))
              (Y.left.presheaf.stalk (g t.val) ⧸ a3i_stalkIdeal Y.left (g t.val) v)) : ℚ) := by
        apply Finset.sum_congr rfl
        intro t _
        exact a3sv_pullback_weighted_point f u t.val v hp
          (by change v ⤳ g t.val; rw [t.property]; exact hvz) (hcod t) m (hmX t)
      _ = _ := htQ
  · exact a3sv_proper_pushforward_mult_of_not_component f u v z hp hz

theorem a3i_intersect_symm_aux (X : Scheme.{u}) [IsNoetherian X] (c d : AlgebraicCycle X ℚ) :
    a3i_intersect X c d = a3i_intersect X d c := by
  classical
  let s := (a3c_support_finite c).toFinset
  let t := (a3c_support_finite d).toFinset
  have hs : ∀ u ∉ s, c u = 0 := fun u hu => by simpa [s] using hu
  have ht : ∀ v ∉ t, d v = 0 := fun v hv => by simpa [t] using hv
  rw [a3c_intersect_eq_sum X c d s t hs ht, a3c_intersect_eq_sum X d c t s ht hs, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  rw [a3i_intersectPrime_symm_aux X u v]
  ext x
  simp only [Function.locallyFinsuppWithin.mapRange_apply]
  ring

theorem a3i_intersect_add_left_aux (X : Scheme.{u}) [IsNoetherian X]
    (c c' d : AlgebraicCycle X ℚ) :
    a3i_intersect X (c + c') d = a3i_intersect X c d + a3i_intersect X c' d := by
  classical
  let s := ((a3c_support_finite c).union (a3c_support_finite c')).toFinset
  let t := (a3c_support_finite d).toFinset
  have hs : ∀ u ∉ s, c u = 0 := fun u hu => by
    simp only [s, Set.Finite.mem_toFinset, Set.mem_union, Function.mem_support, not_or,
      not_not] at hu
    exact hu.1
  have hs' : ∀ u ∉ s, c' u = 0 := fun u hu => by
    simp only [s, Set.Finite.mem_toFinset, Set.mem_union, Function.mem_support, not_or,
      not_not] at hu
    exact hu.2
  have hs'' : ∀ u ∉ s, (c + c') u = 0 := fun u hu => by
    rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, hs u hu, hs' u hu, add_zero]
  have ht : ∀ v ∉ t, d v = 0 := fun v hv => by simpa [t] using hv
  rw [a3c_intersect_eq_sum X _ d s t hs'' ht, a3c_intersect_eq_sum X c d s t hs ht,
    a3c_intersect_eq_sum X c' d s t hs' ht, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  ext x
  simp only [Function.locallyFinsuppWithin.mapRange_apply, Function.locallyFinsuppWithin.coe_add,
    Pi.add_apply]
  ring

/-- IntersectionProductLoc2: scalar multiplication in the first cycle argument. -/
theorem a3i_intersect_smul_left (X : Scheme.{u}) [IsNoetherian X]
    (q : ℚ) (a b : AlgebraicCycle X ℚ) :
    a3i_intersect X (a3m_smul q a) b = a3m_smul q (a3i_intersect X a b) := by
  classical
  let s := (a3c_support_finite a).toFinset
  let t := (a3c_support_finite b).toFinset
  have hs : ∀ x ∉ s, a x = 0 := fun x hx => by simpa [s] using hx
  have ht : ∀ x ∉ t, b x = 0 := fun x hx => by simpa [t] using hx
  rw [a3c_intersect_eq_sum X _ b s t (fun x hx => by simp [hs x hx]) ht,
    a3c_intersect_eq_sum X a b s t hs ht, a3m_smul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [a3m_smul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ext z
  simp only [a3m_smul_apply, Function.locallyFinsuppWithin.mapRange_apply]
  ring

/-- IntersectionProductLoc2: scalar multiplication in the second cycle argument. -/
theorem a3i_intersect_smul_right (X : Scheme.{u}) [IsNoetherian X]
    (q : ℚ) (a b : AlgebraicCycle X ℚ) :
    a3i_intersect X a (a3m_smul q b) = a3m_smul q (a3i_intersect X a b) := by
  rw [a3i_intersect_symm_aux X a, a3i_intersect_smul_left, a3i_intersect_symm_aux X b]

/-- IntersectionProductLoc2: the first intersection argument as an additive map. -/
def a3i_intersectAddLeft (X : Scheme.{u}) [IsNoetherian X] (b : AlgebraicCycle X ℚ) :
    AlgebraicCycle X ℚ →+ AlgebraicCycle X ℚ :=
  AddMonoidHom.mk' (fun a => a3i_intersect X a b) (fun a a' => a3i_intersect_add_left_aux X a a' b)

/-- IntersectionProductLoc2: the second intersection argument as an additive map. -/
def a3i_intersectAddRight (X : Scheme.{u}) [IsNoetherian X] (a : AlgebraicCycle X ℚ) :
    AlgebraicCycle X ℚ →+ AlgebraicCycle X ℚ :=
  AddMonoidHom.mk' (fun b => a3i_intersect X a b) (fun b b' => by
    rw [a3i_intersect_symm_aux X a, a3i_intersect_add_left_aux,
      a3i_intersect_symm_aux X b, a3i_intersect_symm_aux X b'])

/-- IntersectionProductLoc2: finite additivity in the first cycle argument. -/
theorem a3i_intersect_sum_left (X : Scheme.{u}) [IsNoetherian X] {ι : Type*}
    (s : Finset ι) (a : ι → AlgebraicCycle X ℚ) (b : AlgebraicCycle X ℚ) :
    a3i_intersect X (∑ i ∈ s, a i) b = ∑ i ∈ s, a3i_intersect X (a i) b :=
  map_sum (a3i_intersectAddLeft X b) a s

/-- IntersectionProductLoc2: finite additivity in the second cycle argument. -/
theorem a3i_intersect_sum_right (X : Scheme.{u}) [IsNoetherian X] {ι : Type*}
    (s : Finset ι) (a : AlgebraicCycle X ℚ) (b : ι → AlgebraicCycle X ℚ) :
    a3i_intersect X a (∑ i ∈ s, b i) = ∑ i ∈ s, a3i_intersect X a (b i) :=
  map_sum (a3i_intersectAddRight X a) b s

/-- IntersectionProductLoc2: the product of basis cycles is the prime intersection. -/
theorem a3i_intersect_single_single (X : Scheme.{u}) [DecidableEq X] (u v : X) :
    a3i_intersect X (Function.locallyFinsuppWithin.single u (1 : ℚ))
      (Function.locallyFinsuppWithin.single v (1 : ℚ)) = a3i_intersectPrime X u v := by
  classical
  rw [a3c_intersect_eq_sum X _ _ {u} {v}
    (fun x hx => by simp only [Finset.mem_singleton] at hx; simp [hx])
    (fun x hx => by simp only [Finset.mem_singleton] at hx; simp [hx])]
  ext z
  simp

/-- IntersectionProductLoc2: coefficients of a product with a basis cycle. -/
theorem a3i_intersect_single_right_apply (X : Scheme.{u}) [IsNoetherian X] [DecidableEq X]
    (a : AlgebraicCycle X ℚ) (w z : X) :
    a3i_intersect X a (Function.locallyFinsuppWithin.single w (1 : ℚ)) z =
      ∑ᶠ t : X, a t * a3i_intersectPrime X t w z := by
  classical
  let s := (a3c_support_finite a).toFinset
  have hs : ∀ x ∉ s, a x = 0 := fun x hx => by simpa [s] using hx
  rw [a3c_intersect_eq_sum X _ _ s {w} hs
    (fun x hx => by simp only [Finset.mem_singleton] at hx; simp [hx]), a3m_sum_apply,
    finsum_eq_sum_of_support_subset (s := s)]
  · apply Finset.sum_congr rfl
    intro t ht
    simp
  · intro t ht
    by_contra h
    exact ht (by simp [hs t h])

/-- IntersectionProductLoc2 S6a: finite-sum assembly of local associativity.
Only the coefficients of supported prime triples enter the bilinear expansion. -/
theorem a3i_assoc_cycle_of_coeff (X : Scheme) [IsNoetherian X]
    (a b c : AlgebraicCycle X ℚ)
    (h : ∀ u v w, a u ≠ 0 → b v ≠ 0 → c w ≠ 0 → ∀ z,
      (∑ᶠ t : X, a3i_intersectPrime X u v t * a3i_intersectPrime X t w z) =
        ∑ᶠ t : X, a3i_intersectPrime X v w t * a3i_intersectPrime X u t z) :
    a3i_intersect X (a3i_intersect X a b) c =
      a3i_intersect X a (a3i_intersect X b c) := by
  classical
  let s := (a3c_support_finite a).toFinset
  let t := (a3c_support_finite b).toFinset
  let r := (a3c_support_finite c).toFinset
  have ha := a3m_eq_sum_single a s (fun x hx => by simpa [s] using hx)
  have hb := a3m_eq_sum_single b t (fun x hx => by simpa [t] using hx)
  have hc := a3m_eq_sum_single c r (fun x hx => by simpa [r] using hx)
  have hbase (u v w : X) (hu : u ∈ s) (hv : v ∈ t) (hw : w ∈ r) :
      a3i_intersect X
        (a3i_intersect X (Function.locallyFinsuppWithin.single u (1 : ℚ))
          (Function.locallyFinsuppWithin.single v (1 : ℚ)))
        (Function.locallyFinsuppWithin.single w (1 : ℚ)) =
      a3i_intersect X (Function.locallyFinsuppWithin.single u (1 : ℚ))
        (a3i_intersect X (Function.locallyFinsuppWithin.single v (1 : ℚ))
          (Function.locallyFinsuppWithin.single w (1 : ℚ))) := by
    rw [a3i_intersect_single_single, a3i_intersect_single_single]
    ext z
    rw [a3i_intersect_single_right_apply,
      a3i_intersect_symm_aux X (Function.locallyFinsuppWithin.single u 1),
      a3i_intersect_single_right_apply]
    have he := h u v w (by simpa [s] using hu) (by simpa [t] using hv)
      (by simpa [r] using hw) z
    rw [he]
    apply finsum_congr
    intro x
    rw [a3i_intersectPrime_symm_aux X x u]
  conv_lhs => rw [ha, hb, hc]
  conv_rhs => rw [ha, hb, hc]
  simp only [a3i_intersect_sum_left, a3i_intersect_sum_right,
    a3i_intersect_smul_left, a3i_intersect_smul_right, a3m_smul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  rw [hbase w v u hw hv hu]

/-- IntersectionProductLoc2 S6b: a nonzero coefficient of a product sits at a component of the
intersection of two supporting primes. -/
theorem a3i_intersect_support_comps (X : Scheme) [IsNoetherian X]
    (c d : AlgebraicCycle X ℚ) (x : X)
    (hx : a3i_intersect X c d x ≠ 0) : ∃ u v, c u ≠ 0 ∧ d v ≠ 0 ∧ x ∈ a3y_comps u v := by
  classical
  obtain ⟨u, hu⟩ := a3c_exists_of_finsum_apply_ne_zero _ x hx
  obtain ⟨v, hv⟩ := a3c_exists_of_finsum_apply_ne_zero _ x hu
  rw [Function.locallyFinsuppWithin.mapRange_apply] at hv
  exact ⟨u, v, fun h => hv (by rw [h, zero_mul, zero_mul]),
    fun h => hv (by rw [h, mul_zero, zero_mul]),
    a3z_intersectPrime_ne_zero X u v x fun h => hv (by rw [h, mul_zero])⟩

/-- Properness of a triple intersection is independent of parenthesization.
IntersectionProductSE. -/
theorem a3i_components_meet_reassoc (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (u v w : X.left)
    (huv : a3i_MeetProperly X.left u v) (hvw : a3i_MeetProperly X.left v w)
    (h : ∀ r ∈ a3y_comps v w, a3i_MeetProperly X.left u r)
    (t : X.left) (ht : t ∈ a3y_comps u v) : a3i_MeetProperly X.left t w := by
  intro z hz
  let q := (ccm3_primeIdeal X.left t ⊔ ccm3_primeIdeal X.left w).subschemeι z
  have hq : q ∈ a3y_comps t w := ⟨z, hz, rfl⟩
  obtain ⟨htq, hwq, _⟩ := a3y_comps_spec t w hq
  obtain ⟨hut, hvt, _⟩ := a3y_comps_spec u v ht
  obtain ⟨r, hr, hrq⟩ := a3y_exists_comp v w (hvt.trans htq) hwq
  obtain ⟨s, hs, hsq⟩ := a3y_exists_comp u r (hut.trans htq) hrq
  apply le_antisymm (a3m_coheight_component_le_of_smooth X t w z hz)
  have hle : Order.coheight s ≤ Order.coheight q :=
    Order.coheight_anti (Scheme.le_iff_specializes.mpr hsq)
  rw [a3y_coheight_comps u r (h r hr) hs,
    a3y_coheight_comps v w hvw hr] at hle
  rw [a3y_coheight_comps u v huv ht, add_assoc]
  exact hle

/-- A nonzero intersection coefficient comes from a supported prime pair and a
geometric intersection component. IntersectionProductSE. -/
theorem a3i_intersect_support_component (X : Scheme.{u}) [IsNoetherian X]
    (a b : AlgebraicCycle X ℚ) (z : X) (hz : a3i_intersect X a b z ≠ 0) :
    ∃ u v, a u ≠ 0 ∧ b v ≠ 0 ∧ z ∈ a3y_comps u v := by
  classical
  obtain ⟨u, hu⟩ := a3c_exists_of_finsum_apply_ne_zero _ z hz
  obtain ⟨v, hv⟩ := a3c_exists_of_finsum_apply_ne_zero _ z hu
  change a u * b v * a3i_intersectPrime X u v z ≠ 0 at hv
  have hp := (mul_ne_zero_iff.mp hv)
  refine ⟨u, v, (mul_ne_zero_iff.mp hp.1).1, (mul_ne_zero_iff.mp hp.1).2, ?_⟩
  have hi := hp.2
  rw [a3y_intersectPrime_apply] at hi
  split_ifs at hi with h
  · exact h
  · exact (hi rfl).elim

/-- Simultaneous moving against a finite set of points. IntersectionProductSE. -/
theorem a3i_move_against_finset (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (a : AlgebraicCycle X.left ℚ)
    (s : Finset X.left) :
    ∃ a', a' - a ∈ a3i_ratAll X.left ∧
      ∀ u v, a' u ≠ 0 → v ∈ s → a3i_MeetProperly X.left u v := by
  classical
  let d : AlgebraicCycle X.left ℚ :=
    ∑ v ∈ s, Function.locallyFinsuppWithin.single v 1
  obtain ⟨a', hr, hp⟩ := IntersectionProductRing.moving_total X a d
  refine ⟨a', hr, fun u v hu hv => hp u v hu ?_⟩
  simp only [d, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single v (fun w _ hw => by
    simp [Function.locallyFinsuppWithin.single_apply, Ne.symm hw])
    (fun h => (h hv).elim)]
  simp

/-- IntersectionProductLoc2 S6b: simultaneous moving in position for both iterated
products, with properness against each geometric component before taking coefficients. -/
theorem a3i_moving_assoc (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (a b c : AlgebraicCycle X.left ℚ) :
    ∃ a' b' c' : AlgebraicCycle X.left ℚ,
      a' - a ∈ a3i_ratAll X.left ∧ b' - b ∈ a3i_ratAll X.left ∧
      c' - c ∈ a3i_ratAll X.left ∧
      a3i_CyclesMeetProperly X.left a' b' ∧
      a3i_CyclesMeetProperly X.left b' c' ∧
      a3i_CyclesMeetProperly X.left a' c' ∧
      a3i_CyclesMeetProperly X.left (a3i_intersect X.left a' b') c' ∧
      a3i_CyclesMeetProperly X.left a' (a3i_intersect X.left b' c') ∧
      ∀ u v w, a' u ≠ 0 → b' v ≠ 0 → c' w ≠ 0 →
        ∀ t : (ccm3_primeIdeal X.left v ⊔ ccm3_primeIdeal X.left w).subscheme,
          closure ({t} : Set (ccm3_primeIdeal X.left v ⊔ ccm3_primeIdeal X.left w).subscheme) ∈
            irreducibleComponents (ccm3_primeIdeal X.left v ⊔ ccm3_primeIdeal X.left w).subscheme →
          a3i_MeetProperly X.left u
            ((ccm3_primeIdeal X.left v ⊔ ccm3_primeIdeal X.left w).subschemeι t) := by
  classical
  obtain ⟨c', hc, hcb⟩ := IntersectionProductRing.moving_total X c b
  have hbc := IntersectionProductRing.cyclesMeetProperly_symm X.left c' b hcb
  let S : Finset X.left :=
    ((a3c_support_finite b).union (a3c_support_finite c')).toFinset ∪
      ((a3c_support_finite b).toFinset ×ˢ (a3c_support_finite c').toFinset).biUnion
        (fun p => (a3y_comps_finite p.1 p.2).toFinset)
  let d : AlgebraicCycle X.left ℚ := ∑ x ∈ S, Function.locallyFinsuppWithin.single x 1
  obtain ⟨a', ha, had⟩ := IntersectionProductRing.moving_total X a d
  have hd : ∀ x ∈ S, d x ≠ 0 := by
    intro x hx
    simp only [d, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single x (fun z _ hzx => by
      simp [Function.locallyFinsuppWithin.single_apply, Ne.symm hzx]) (fun h => (h hx).elim)]
    simp
  have hS : ∀ u x, a' u ≠ 0 → x ∈ S → a3i_MeetProperly X.left u x :=
    fun u x hu hx => had u x hu (hd x hx)
  have hab : a3i_CyclesMeetProperly X.left a' b := fun u v hu hv =>
    hS u v hu (Finset.mem_union_left _ (by simpa using Or.inl hv))
  have hac : a3i_CyclesMeetProperly X.left a' c' := fun u w hu hw =>
    hS u w hu (Finset.mem_union_left _ (by simpa using Or.inr hw))
  have hcomp : ∀ u v w, a' u ≠ 0 → b v ≠ 0 → c' w ≠ 0 →
      ∀ t ∈ a3y_comps v w, a3i_MeetProperly X.left u t := by
    intro u v w hu hv hw t ht
    refine hS u t hu (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(v, w), ?_, ?_⟩))
    · simpa using ⟨hv, hw⟩
    · simpa using ht
  refine ⟨a', b, c', ha, by rw [sub_self]; exact zero_mem _, hc, hab, hbc, hac, ?_, ?_, ?_⟩
  · intro s w hs hw
    obtain ⟨u, v, hu, hv, hsc⟩ := a3i_intersect_support_comps _ a' b s hs
    exact a3sv_meetProperly_components_left X u v w (hab u v hu hv) (hbc v w hv hw)
      (hcomp u v w hu hv hw) s hsc
  · intro u t hu ht
    obtain ⟨v, w, hv, hw, htc⟩ := a3i_intersect_support_comps _ b c' t ht
    exact hcomp u v w hu hv hw t htc
  · intro u v w hu hv hw t ht
    exact hcomp u v w hu hv hw _ ⟨t, ht, rfl⟩

/-- IntersectionProductLoc2 P3: under a flat map, a component of the inverse image of
`closure {v}` lies over `v`, since flat maps are generalizing. -/
theorem a3i_flatPullbackPrime_image {X Y : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [Flat f.left] (v : Y.left) (w : X.left)
    (hw : ccm3_flatPullbackPrime f.left v w ≠ 0) : f.left w = v := by
  obtain ⟨y, rfl, hc⟩ := (ccm3_flatPullbackPrime_support_aux f v w).mp hw
  let I := ccm3_inverseIdeal f.left v
  have hy : I.subschemeι y ∈ I.support := by
    change I.subschemeι y ∈ (I.support : Set X.left)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  have hs := Scheme.IdealSheafData.support_comap (ccm3_primeIdeal Y.left v) f.left
  change I.support = _ at hs
  have hvy : v ⤳ f.left (I.subschemeι y) := specializes_iff_mem_closure.mpr (hs.le hy)
  obtain ⟨x, hx, hfx⟩ := Flat.generalizingMap f.left hvy
  have hxI : x ∈ I.support := by
    rw [hs]
    change f.left x ∈ closure ({v} : Set Y.left)
    rw [hfx]
    exact subset_closure (Set.mem_singleton v)
  obtain ⟨x', hx'⟩ := Set.mem_range.mp (I.range_subschemeι.symm.subset hxI)
  have hxy : x' ⤳ y := by
    apply I.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp
    simpa only [hx'] using hx
  have hsub : closure ({y} : Set I.subscheme) ⊆ closure ({x'} : Set I.subscheme) :=
    closure_minimal (Set.singleton_subset_iff.mpr
      (specializes_iff_mem_closure.mp hxy)) isClosed_closure
  have hrev := hc.2 isIrreducible_singleton.closure hsub
  have hyx : y ⤳ x' := specializes_iff_mem_closure.mpr
    (hrev (subset_closure (Set.mem_singleton x')))
  have heq : x' = y := (hxy.antisymm hyx).eq
  rw [← heq, hx', hfx]
/-- IntersectionProductLoc2 P3: pushforward of a finite sum of cycles. -/
theorem a3i_pushforward_sum {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] {ι : Type*}
    (t : Finset ι) (F : ι → AlgebraicCycle X ℚ) :
    a1p_pushforward f (∑ i ∈ t, F i) = ∑ i ∈ t, a1p_pushforward f (F i) :=
  map_sum (AddMonoidHom.mk' (a1p_pushforward f) (a1p_pushforward_add f)) F t
/-- IntersectionProductLoc2 P3: pushforward of a rational multiple of a cycle. -/
theorem a3i_pushforward_smul {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] (q : ℚ)
    (c : AlgebraicCycle X ℚ) :
    a1p_pushforward f (a3m_smul q c) = a3m_smul q (a1p_pushforward f c) :=
  a1p_pushforward_mul f q c
/-- IntersectionProductLoc2 P3: a prime cycle with coefficient `r` is `r` times the basis cycle. -/
theorem a3i_single_eq_smul {X : Scheme} [DecidableEq X] (x : X) (r : ℚ) :
    Function.locallyFinsuppWithin.single x r =
      a3m_smul r (Function.locallyFinsuppWithin.single x (1 : ℚ)) := by
  ext y
  simp only [a3m_smul_apply, Function.locallyFinsuppWithin.single_apply]
  split_ifs <;> simp

theorem a3i_flatPullback_single {X Y : Scheme} [DecidableEq Y] (f : X ⟶ Y) (v : Y) :
    ccm3_flatPullback f (Function.locallyFinsuppWithin.single v (1 : ℚ)) =
      ccm3_flatPullbackPrime f v := by
  classical
  unfold ccm3_flatPullback
  rw [finsum_eq_single _ v]
  · ext w
    simp [Function.locallyFinsuppWithin.single_apply]
  · intro v' hv'
    ext w
    simp [Function.locallyFinsuppWithin.single_apply, hv']

theorem a3i_projection_single {X Y : Over (Spec ↧ℂ)} [DecidableEq X.left]
    [DecidableEq Y.left] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [Flat f.left] [IsProper f.left]
    (hprime : ∀ (u : X.left) (v z : Y.left),
      (∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w) →
      (∑ᶠ t : f.left ⁻¹' {z},
        (∑ᶠ w : X.left, ccm3_flatPullbackPrime f.left v w * a3i_intersectPrime X.left u w t) *
          (a1p_degree f.left t : ℚ)) =
        (a1p_degree f.left u : ℚ) * a3i_intersectPrime Y.left (f.left u) v z)
    (u : X.left) (v : Y.left)
    (hp : ∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w) :
    a1p_pushforward f.left (a3i_intersect X.left
      (Function.locallyFinsuppWithin.single u (1 : ℚ)) (ccm3_flatPullbackPrime f.left v)) =
      a3i_intersect Y.left
        (a1p_pushforward f.left (Function.locallyFinsuppWithin.single u (1 : ℚ)))
        (Function.locallyFinsuppWithin.single v (1 : ℚ)) := by
  classical
  ext z
  rw [a1p_pushforward_apply,
    a3i_intersect_symm_aux X.left (Function.locallyFinsuppWithin.single u 1),
    a1p_pushforward_single]
  simp_rw [a3i_intersect_single_right_apply]
  have hsum : (∑ᶠ t : X.left, ∑ᶠ _ : t ∈ f.left ⁻¹' {z},
      (∑ᶠ w : X.left, ccm3_flatPullbackPrime f.left v w *
        a3i_intersectPrime X.left w u t) * (a1p_degree f.left t : ℚ)) =
      ∑ᶠ t : X.left, ∑ᶠ _ : t ∈ f.left ⁻¹' {z},
      (∑ᶠ w : X.left, ccm3_flatPullbackPrime f.left v w *
        a3i_intersectPrime X.left u w t) * (a1p_degree f.left t : ℚ) := by
    apply finsum_congr
    intro t
    apply finsum_congr
    intro _
    congr 1
    apply finsum_congr
    intro w
    rw [a3i_intersectPrime_symm_aux X.left w u]
  rw [hsum, ← finsum_set_coe_eq_finsum_mem, hprime u v z hp]
  rw [finsum_eq_single _ (f.left u)]
  · simp [Function.locallyFinsuppWithin.single_apply]
  · intro t ht
    simp [Function.locallyFinsuppWithin.single_apply, ht]

attribute [local instance] specializationOrder in
/-- The generic point of an inverse-image component maps to the original point.
IntersectionProductSE. -/
lemma a3i_flat_component_maps_to_point {X Y : Scheme} (f : X ⟶ Y) [Flat f]
    (v : Y) (y : (ccm3_inverseIdeal f v).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f v).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f v).subscheme) :
    f ((ccm3_inverseIdeal f v).subschemeι y) = v := by
  let I := ccm3_inverseIdeal f v
  have hyzero : Order.coheight y = 0 := by
    rw [Order.coheight_eq_zero]
    intro y' hyy'
    have hsub : closure ({y} : Set I.subscheme) ⊆ closure ({y'} : Set I.subscheme) := by
      change Specializes y' y at hyy'
      exact closure_minimal (Set.singleton_subset_iff.mpr
        (specializes_iff_mem_closure.mp hyy')) isClosed_closure
    have hrev : closure ({y'} : Set I.subscheme) ⊆ closure ({y} : Set I.subscheme) :=
      hy.2 isIrreducible_singleton.closure hsub
    change Specializes y y'
    exact specializes_iff_mem_closure.mpr
      (hrev (subset_closure (Set.mem_singleton y')))
  have hymax : IsMax y := Order.coheight_eq_zero.mp hyzero
  have hwmem : I.subschemeι y ∈ I.support := by
    change I.subschemeι y ∈ (I.support : Set X)
    rw [← I.range_subschemeι]
    exact ⟨y, rfl⟩
  have hfv : f (I.subschemeι y) ∈ closure ({v} : Set Y) := by
    change I.subschemeι y ∈ ((ccm3_primeIdeal Y v).comap f).support at hwmem
    rw [Scheme.IdealSheafData.support_comap] at hwmem
    change f (I.subschemeι y) ∈
      ((Scheme.IdealSheafData.vanishingIdeal
        ⟨closure ({v} : Set Y), isClosed_closure⟩).support : Set Y) at hwmem
    rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hwmem
  obtain ⟨w', hw', hfw'⟩ := (Flat.generalizingMap f)
    (specializes_iff_mem_closure.mpr hfv)
  have hw'mem : w' ∈ I.support := by
    change w' ∈ ((ccm3_primeIdeal Y v).comap f).support
    rw [Scheme.IdealSheafData.support_comap]
    change f w' ∈
      ((Scheme.IdealSheafData.vanishingIdeal
        ⟨closure ({v} : Set Y), isClosed_closure⟩).support : Set Y)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, hfw']
    exact subset_closure (Set.mem_singleton v)
  obtain ⟨y', hy'⟩ := Set.mem_range.mp (I.range_subschemeι.symm.subset hw'mem)
  have hyy' : y ≤ y' := by
    change Specializes y' y
    apply I.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp
    simpa only [hy'] using hw'
  have hle := hymax hyy'
  have heq : y' = y := le_antisymm hle hyy'
  simpa only [I, ← hy', heq] using hfw'

/-- The coefficient of a flat pullback at a source point receives a contribution only
from the image of that point. IntersectionProductSE. -/
theorem a3i_flatPullback_apply {X Y : Over (Spec ↧ℂ)} [IsProjective X.hom]
    [IsProjective Y.hom] (f : X ⟶ Y) [Flat f.left]
    (b : AlgebraicCycle Y.left ℚ) (w : X.left) :
    ccm3_flatPullback f.left b w =
      b (f.left w) * ccm3_flatPullbackPrime f.left (f.left w) w := by
  classical
  unfold ccm3_flatPullback
  let F := fun v : Y.left =>
    (ccm3_flatPullbackPrime f.left v).mapRange (b v * ·) (mul_zero _)
  have hF : (Function.support F).Finite := (a3c_support_finite b).subset fun v hv => by
    intro hb
    apply hv
    ext x
    simp [F, hb]
  rw [a3c_finsum_apply F hF, finsum_eq_single _ (f.left w)]
  · simp [F, Function.locallyFinsuppWithin.mapRange_apply]
  · intro v hv
    simp only [F, Function.locallyFinsuppWithin.mapRange_apply]
    by_cases hzero : ccm3_flatPullbackPrime f.left v w = 0
    · simp [hzero]
    · obtain ⟨y, hy, hycomp⟩ := (ccm3_flatPullbackPrime_support f v w).mp hzero
      have hmap := a3i_flat_component_maps_to_point f.left v y hycomp
      exact (hv (hy ▸ hmap.symm)).elim

/-- Finite basis expansion of flat pullback. IntersectionProductSE. -/
theorem a3i_flatPullback_eq_sum {X Y : Over (Spec ↧ℂ)} [IsProjective X.hom]
    [IsProjective Y.hom] (f : X ⟶ Y) [Flat f.left]
    (b : AlgebraicCycle Y.left ℚ) (s : Finset Y.left) (hs : ∀ v ∉ s, b v = 0) :
    ccm3_flatPullback f.left b =
      ∑ v ∈ s, a3m_smul (b v) (ccm3_flatPullbackPrime f.left v) := by
  classical
  ext w
  rw [a3i_flatPullback_apply]
  simp only [a3m_sum_apply, a3m_smul_apply]
  by_cases hw : f.left w ∈ s
  · rw [Finset.sum_eq_single (f.left w)]
    · intro v hv hvne
      have hz : ccm3_flatPullbackPrime f.left v w = 0 := by
        by_contra hn
        obtain ⟨y, hy, hycomp⟩ := (ccm3_flatPullbackPrime_support f v w).mp hn
        have hmap := a3i_flat_component_maps_to_point f.left v y hycomp
        exact hvne (hy ▸ hmap.symm)
      simp [hz]
    · exact fun h => (h hw).elim
  · have hsum : (∑ v ∈ s, b v * ccm3_flatPullbackPrime f.left v w) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      by_cases hvw : v = f.left w
      · subst v
        exact (hw hv).elim
      · have hz : ccm3_flatPullbackPrime f.left v w = 0 := by
          by_contra hn
          obtain ⟨y, hy, hycomp⟩ := (ccm3_flatPullbackPrime_support f v w).mp hn
          have hmap := a3i_flat_component_maps_to_point f.left v y hycomp
          exact hvw (hy ▸ hmap.symm)
        simp [hz]
    rw [hs _ hw, hsum, zero_mul]

/-- IntersectionProductLoc2 P3: bilinear extension of the residue-degree formula.
This separates finite-sum bookkeeping from the local length identity. -/
theorem a3i_projection_of_prime_coeff {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    [IsProjective Y.hom] (f : X ⟶ Y) [Flat f.left] [IsProper f.left]
    (hprime : ∀ (u : X.left) (v z : Y.left),
      (∀ w, ccm3_flatPullbackPrime f.left v w ≠ 0 → a3i_MeetProperly X.left u w) →
      (∑ᶠ t : f.left ⁻¹' {z},
        (∑ᶠ w : X.left, ccm3_flatPullbackPrime f.left v w * a3i_intersectPrime X.left u w t) *
          (a1p_degree f.left t : ℚ)) =
        (a1p_degree f.left u : ℚ) * a3i_intersectPrime Y.left (f.left u) v z)
    (a : AlgebraicCycle X.left ℚ) (b : AlgebraicCycle Y.left ℚ)
    (hp : a3i_CyclesMeetProperly X.left a (ccm3_flatPullback f.left b)) :
    a1p_pushforward f.left (a3i_intersect X.left a (ccm3_flatPullback f.left b)) =
      a3i_intersect Y.left (a1p_pushforward f.left a) b := by
  classical
  let s := (a3c_support_finite a).toFinset
  let r := (a3c_support_finite b).toFinset
  have hs : ∀ x ∉ s, a x = 0 := fun x hx => by simpa [s] using hx
  have hr : ∀ x ∉ r, b x = 0 := fun x hx => by simpa [r] using hx
  have hpb : ccm3_flatPullback f.left b =
      ∑ v ∈ r, a3m_smul (b v) (ccm3_flatPullbackPrime f.left v) := by
    unfold ccm3_flatPullback
    rw [finsum_eq_sum_of_support_subset (s := r)]
    · rfl
    · intro v hv
      by_contra hvr
      apply hv
      ext x
      simp [hr v hvr]
  have hpbw : ∀ v w, b v ≠ 0 → ccm3_flatPullbackPrime f.left v w ≠ 0 →
      ccm3_flatPullback f.left b w ≠ 0 := by
    intro v w hv hw
    rw [hpb, a3m_sum_apply, Finset.sum_eq_single v]
    · simpa using ⟨hv, hw⟩
    · intro v' _ hv'
      have h0 : ccm3_flatPullbackPrime f.left v' w = 0 := by
        by_contra h
        exact hv' ((a3i_flatPullbackPrime_image f v' w h).symm.trans
          (a3i_flatPullbackPrime_image f v w hw))
      rw [a3m_smul_apply, h0, mul_zero]
    · intro hvr
      exact absurd (hr v hvr) hv
  have hpair : ∀ u ∈ s, ∀ v ∈ r,
      a1p_pushforward f.left (a3i_intersect X.left
        (Function.locallyFinsuppWithin.single u 1) (ccm3_flatPullbackPrime f.left v)) =
      a3m_smul (a1p_degree f.left u) (a3i_intersectPrime Y.left (f.left u) v) := by
    intro u hu v hv
    have hu' : a u ≠ 0 := by simpa [s] using hu
    have hv' : b v ≠ 0 := by simpa [r] using hv
    ext z
    rw [a1p_pushforward_apply, a3m_smul_apply,
      ← hprime u v z (fun w hw => hp u w hu' (hpbw v w hv' hw)),
      ← finsum_set_coe_eq_finsum_mem]
    apply finsum_congr
    intro t
    congr 1
    rw [a3i_intersect_symm_aux, a3i_intersect_single_right_apply]
    apply finsum_congr
    intro w
    rw [a3i_intersectPrime_symm_aux X.left w u]
  have ha := a3m_eq_sum_single a s hs
  have hb := a3m_eq_sum_single b r hr
  rw [hpb]
  conv_lhs => rw [ha]
  conv_rhs => rw [ha, hb]
  simp only [a3i_intersect_sum_left, a3i_intersect_sum_right, a3i_intersect_smul_left,
    a3i_intersect_smul_right, a3i_pushforward_sum]
  simp only [a3i_pushforward_sum, a3m_smul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  rw [a3i_pushforward_smul, a3i_pushforward_smul, hpair u hu v hv, a3i_pushforward_smul,
    a1p_pushforward_single, one_mul, a3i_single_eq_smul (f.left u) (a1p_degree f.left u : ℚ),
    a3i_intersect_smul_left, a3i_intersect_smul_left, a3i_intersect_single_single]

/-- Global assembly of local associativity, after simultaneous moving of three cycles. -/
theorem a3i_assoc_global_assembly (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom]
    (hmk : ∀ (α β : AlgebraicCycle X.left ℚ), a3i_CyclesMeetProperly X.left α β →
      a3i_chowMul X.left (QuotientAddGroup.mk α) (QuotientAddGroup.mk β) =
        QuotientAddGroup.mk (a3i_intersect X.left α β))
    (a b c : a3i_ChowTotal X.left) :
    a3i_chowMul X.left (a3i_chowMul X.left a b) c =
      a3i_chowMul X.left a (a3i_chowMul X.left b c) := by
  induction a using QuotientAddGroup.induction_on with
  | _ α =>
    induction b using QuotientAddGroup.induction_on with
    | _ β =>
      induction c using QuotientAddGroup.induction_on with
      | _ γ =>
        obtain ⟨α', β', γ', hα, hβ, hγ, hab, hbc, hac, habc, habc', ht⟩ :=
          a3i_moving_assoc X α β γ
        have ea : (QuotientAddGroup.mk α' : a3i_ChowTotal X.left) = QuotientAddGroup.mk α :=
          QuotientAddGroup.eq_iff_sub_mem.mpr hα
        have eb : (QuotientAddGroup.mk β' : a3i_ChowTotal X.left) = QuotientAddGroup.mk β :=
          QuotientAddGroup.eq_iff_sub_mem.mpr hβ
        have ec : (QuotientAddGroup.mk γ' : a3i_ChowTotal X.left) = QuotientAddGroup.mk γ :=
          QuotientAddGroup.eq_iff_sub_mem.mpr hγ
        rw [← ea, ← eb, ← ec, hmk α' β' hab, hmk β' γ' hbc,
          hmk _ γ' habc, hmk α' _ habc']
        congr 1
        apply a3i_assoc_cycle_of_coeff
        intro u v w hu hv hw z
        exact a3i_assoc_local X u v w z (hab u v hu hv) (hbc v w hv hw)
          (hac u w hu hw) (ht u v w hu hv hw)

/-- Global assembly of the local proper-pushforward multiplicity formula.  The cycle-level
identity is stronger than the required equality modulo rational equivalence. -/
theorem a3i_projection_global_assembly {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    [IsProjective Y.hom] (f : X ⟶ Y) [Flat f.left] [IsProper f.left]
    (alpha : AlgebraicCycle X.left ℚ) (beta : AlgebraicCycle Y.left ℚ)
    (h1 : a3i_CyclesMeetProperly X.left alpha (ccm3_flatPullback f.left beta))
    (h2 : a3i_CyclesMeetProperly Y.left (a1p_pushforward f.left alpha) beta) :
    a1p_pushforward f.left (a3i_intersect X.left alpha (ccm3_flatPullback f.left beta)) =
      a3i_intersect Y.left (a1p_pushforward f.left alpha) beta := by
  exact a3i_projection_of_prime_coeff f (a3i_proper_pushforward_mult f) alpha beta h1

end HodgeLean.Adapters

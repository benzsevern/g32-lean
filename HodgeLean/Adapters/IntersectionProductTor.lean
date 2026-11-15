import HodgeLean.Adapters.IntersectionProductDefs

/-! # Balancing of `Tor` over a commutative ring

Mathlib's `Tor` derives `X ⊗ -` in the second variable. Over a commutative ring `R` this file
builds isomorphisms `Tor_n(M, N) ≅ Tor_n(N, M)` of `R`-modules, by dimension shifting:
* in the first variable, a short exact sequence `0 → K → P₀ → M → 0` with `P₀` projective gives a
  short exact sequence of complexes `0 → K ⊗ Q → P₀ ⊗ Q → M ⊗ Q → 0` (projectives are flat), and
  `P₀ ⊗ Q` is exact in positive degrees, so `Tor_{n+2}(M, N) ≅ Tor_{n+1}(K, N)`;
* in the second variable, the truncation of a projective resolution of `M` resolves
  `K = ker (P₀ → M)`, so `Tor_{n+2}(N, M) ≅ Tor_{n+1}(N, K)` on the nose;
* `Tor_0` is `⊗` on both sides, and both `Tor_1(M, N)` and `Tor_1(N, M)` are the kernel of
  `K ⊗ N → P₀ ⊗ N`, up to the braiding.

Source: Weibel, *An Introduction to Homological Algebra*, Theorem 2.7.2 (balancing of `Tor`),
proved here by the dimension-shifting argument of §2.4 instead of the double complex.
HC no distance; AV milestone no distance.
-/

open CategoryTheory MonoidalCategory Limits

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace HodgeLean.Adapters
universe u
variable {R : Type u} [CommRing R]

/-- The complex `X ⊗ C`. -/
abbrev a3l_tensC (X : ModuleCat.{u} R) (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  (((tensoringLeft (ModuleCat.{u} R)).obj X).mapHomologicalComplex _).obj C

/-- Projective objects of `ModuleCat R` are flat modules. -/
theorem a3l_flat_of_projective (P : ModuleCat.{u} R) [Projective P] : Module.Flat R P := by
  have : Module.Projective R P := (IsProjective.iff_projective (R := R) P).2 ‹_›
  infer_instance

/-- The chain map `f ⊗ C : X ⊗ C ⟶ Y ⊗ C`. -/
abbrev a3l_tensMap {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    a3l_tensC X C ⟶ a3l_tensC Y C :=
  (NatTrans.mapHomologicalComplex ((tensoringLeft _).map f) _).app C

/-- A short complex of modules tensored with a complex. -/
def a3l_sesC (S : ShortComplex (ModuleCat.{u} R)) (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (a3l_tensMap S.f C) (a3l_tensMap S.g C) (by
    refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
    simp [← MonoidalCategory.comp_whiskerRight, S.zero])

/-- Tensoring a short exact sequence with a complex of projectives keeps it short exact. -/
lemma a3l_sesC_shortExact (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (hC : ∀ i, Projective (C.X i)) :
    (a3l_sesC S C).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have := hC i
  have := a3l_flat_of_projective (C.X i)
  have : PreservesFiniteColimits (tensorRight (C.X i)) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (C.X i))
  refine ShortComplex.shortExact_of_iso ?_ (hS.map_of_exact (tensorRight (C.X i)))
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [a3l_sesC])
    (by simp [a3l_sesC])

section shift
variable {M : ModuleCat.{u} R} (P : ProjectiveResolution M)

/-- The augmentation `P₁ ⟶ ker (P₀ → M)` of the truncated resolution. -/
def a3l_shiftπ₀ : P.complex.X 1 ⟶ kernel (P.π.f 0) :=
  kernel.lift _ (P.complex.d 1 0) (by simp)

@[reassoc (attr := simp)]
lemma a3l_shiftπ₀_ι : a3l_shiftπ₀ P ≫ kernel.ι _ = P.complex.d 1 0 := by
  simp [a3l_shiftπ₀]

lemma a3l_shift_d : P.complex.d 2 1 ≫ a3l_shiftπ₀ P = 0 := by
  rw [← cancel_mono (kernel.ι (P.π.f 0))]; simp

lemma a3l_shift_exact₀ :
    (ShortComplex.mk _ _ (a3l_shift_d P)).Exact := by
  let α : ShortComplex.mk _ _ (a3l_shift_d P) ⟶ ShortComplex.mk _ _ (P.complex.d_comp_d 2 1 0) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι _ }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  exact P.exact_succ 0

instance a3l_shift_epi : Epi (a3l_shiftπ₀ P) :=
  (P.exact₀).epi_kernelLift

lemma a3l_truncate_exactAt (n : ℕ) :
    ((ChainComplex.truncate).obj P.complex).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  have := P.exact_succ (n + 1)
  exact (ShortComplex.exact_iff_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp))).1 this

/-- The truncation `P_{•+1}` of a projective resolution of `M` resolves `ker (P₀ → M)`. -/
def a3l_shiftRes : ProjectiveResolution (kernel (P.π.f 0)) where
  complex := (ChainComplex.truncate).obj P.complex
  projective n := P.projective (n + 1)
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨a3l_shiftπ₀ P, a3l_shift_d P⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨a3l_shift_exact₀ P, by dsimp; infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp) (by simp)
      all_goals first | rfl | simp
    · rw [quasiIsoAt_iff_exactAt']
      · exact a3l_truncate_exactAt P _
      · apply ChainComplex.exactAt_succ_single_obj⟩

end shift

/-- Tensoring with a flat module keeps a complex exact in positive degrees. -/
theorem a3l_exactAt_tensC (X : ModuleCat.{u} R) [Module.Flat R X]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (k : ℕ) (h : C.ExactAt (k + 1)) :
    (a3l_tensC X C).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp)] at h ⊢
  have := Module.Flat.lTensor_shortComplex_exact X _ h
  exact (ShortComplex.exact_iff_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp))).1 this

/-- Dimension shifting in the first variable. -/
def a3l_stepA {N : ModuleCat.{u} R} (Q : ProjectiveResolution N)
    (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) :
    (a3l_tensC S.X₃ Q.complex).homology (n + 2) ≅ (a3l_tensC S.X₁ Q.complex).homology (n + 1) :=
  have := a3l_flat_of_projective S.X₂
  (a3l_sesC_shortExact S hS Q.complex Q.projective).δIso (n + 2) (n + 1) (by simp)
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (a3l_exactAt_tensC S.X₂ _ (n + 1) (Q.complex_exactAt_succ (n + 1))))
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (a3l_exactAt_tensC S.X₂ _ n (Q.complex_exactAt_succ n)))

/-- Homology of the truncation, shifted by one. -/
def a3l_truncHomologyIso (N : ModuleCat.{u} R) (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (a3l_tensC N ((ChainComplex.truncate).obj C)).homology (n + 1) ≅
      (a3l_tensC N C).homology (n + 2) :=
  HomologicalComplex.homologyIsoSc' _ (n + 2) (n + 1) n (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso
      (show (a3l_tensC N ((ChainComplex.truncate).obj C)).sc' (n + 2) (n + 1) n ≅
          (a3l_tensC N C).sc' (n + 3) (n + 2) (n + 1) from
        ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)) ≪≫
    (HomologicalComplex.homologyIsoSc' (a3l_tensC N C) (n + 3) (n + 2) (n + 1)
      (ChainComplex.prev _ _) (ChainComplex.next_nat_succ _)).symm

/-- `Tor_n(M, N)` is the homology of `M ⊗ Q` for a projective resolution `Q` of `N`. -/
def a3l_torIso (M N : ModuleCat.{u} R) (Q : ProjectiveResolution N) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) n).obj M).obj N ≅ (a3l_tensC M Q.complex).homology n :=
  Q.isoLeftDerivedObj _ n


/-- `Tor_0(M, N) ≅ M ⊗ N`. -/
def a3l_tor0Iso (M N : ModuleCat.{u} R) : ((Tor (ModuleCat.{u} R) 0).obj M).obj N ≅ M ⊗ N :=
  ((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerivedZeroIsoSelf.app N

instance a3l_epi_whiskerLeft (X : ModuleCat.{u} R) {A B : ModuleCat.{u} R} (f : A ⟶ B) [Epi f] :
    Epi (X ◁ f) := by
  have : (tensorLeft X).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (ihom.adjunction X)
  exact (tensorLeft X).map_epi f

section base1
variable {N : ModuleCat.{u} R} (Q : ProjectiveResolution N)

lemma a3l_tens_exact₀ (X : ModuleCat.{u} R) :
    (ShortComplex.mk (X ◁ Q.complex.d 1 0) (X ◁ Q.π.f 0)
      (by rw [← MonoidalCategory.whiskerLeft_comp, Q.complex_d_comp_π_f_zero,
        MonoidalPreadditive.whiskerLeft_zero])).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (CokernelCofork.mapIsColimit _ Q.exact₀.gIsCokernel (tensorLeft X))

/-- `H_0(X ⊗ Q) ≅ X ⊗ N`. -/
def a3l_opcyclesIso (X : ModuleCat.{u} R) : (a3l_tensC X Q.complex).opcycles 0 ≅ X ⊗ N :=
  IsColimit.coconePointUniqueUpToIso ((a3l_tensC X Q.complex).opcyclesIsCokernel 1 0 (by simp))
    (a3l_tens_exact₀ Q X).gIsCokernel

@[reassoc (attr := simp)]
lemma a3l_p_opcyclesIso (X : ModuleCat.{u} R) :
    (a3l_tensC X Q.complex).pOpcycles 0 ≫ (a3l_opcyclesIso Q X).hom = X ◁ Q.π.f 0 :=
  by
    have := IsColimit.comp_coconePointUniqueUpToIso_hom
      ((a3l_tensC X Q.complex).opcyclesIsCokernel 1 0 (by simp))
      (a3l_tens_exact₀ Q X).gIsCokernel WalkingParallelPair.one
    rw [a3l_opcyclesIso]
    simpa using this

def a3l_H0Iso (X : ModuleCat.{u} R) : (a3l_tensC X Q.complex).homology 0 ≅ X ⊗ N :=
  (a3l_tensC X Q.complex).isoHomologyι₀ ≪≫ a3l_opcyclesIso Q X

lemma a3l_H0Iso_naturality {X Y : ModuleCat.{u} R} (f : X ⟶ Y) :
    HomologicalComplex.homologyMap (a3l_tensMap f Q.complex) 0 ≫ (a3l_H0Iso Q Y).hom =
      (a3l_H0Iso Q X).hom ≫ f ▷ N := by
  rw [← cancel_epi (a3l_tensC X Q.complex).isoHomologyι₀.inv]
  simp only [a3l_H0Iso, Iso.trans_hom, ChainComplex.isoHomologyι₀_inv_naturality_assoc,
    Iso.inv_hom_id_assoc]
  rw [← cancel_epi ((a3l_tensC X Q.complex).pOpcycles 0)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, HomologicalComplex.p_opcyclesMap_assoc,
    a3l_p_opcyclesIso, a3l_p_opcyclesIso_assoc]
  dsimp
  exact (MonoidalCategory.whisker_exchange f (Q.π.f 0)).symm

end base1


/-- `Tor_1(M, N)` computed from a short exact sequence `0 → K → P₀ → M → 0`, `P₀` projective. -/
def a3l_H1IsoA {N : ModuleCat.{u} R} (Q : ProjectiveResolution N)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) [Projective S.X₂] :
    (a3l_tensC S.X₃ Q.complex).homology 1 ≅ kernel (S.f ▷ N) :=
  have := a3l_flat_of_projective S.X₂
  have hT := a3l_sesC_shortExact S hS Q.complex Q.projective
  have hz : IsZero ((a3l_tensC S.X₂ Q.complex).homology 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (a3l_exactAt_tensC S.X₂ _ 0 (Q.complex_exactAt_succ 0))
  have hr : (ComplexShape.down ℕ).Rel 1 0 := rfl
  have := hT.mono_δ 1 0 hr hz
  IsLimit.conePointUniqueUpToIso (hT.homology_exact₁ 1 0 hr).fIsKernel
      (kernelIsKernel _) ≪≫
    kernel.mapIso _ _ (a3l_H0Iso Q S.X₁) (a3l_H0Iso Q S.X₂) (a3l_H0Iso_naturality Q S.f)

section shiftB
variable (N : ModuleCat.{u} R) {M : ModuleCat.{u} R} (P : ProjectiveResolution M)

lemma a3l_shift_exact₀_tens :
    (ShortComplex.mk (N ◁ P.complex.d 2 1) (N ◁ a3l_shiftπ₀ P)
      (by rw [← MonoidalCategory.whiskerLeft_comp, a3l_shift_d,
        MonoidalPreadditive.whiskerLeft_zero])).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (CokernelCofork.mapIsColimit _ (a3l_shift_exact₀ P).gIsCokernel (tensorLeft N))

def a3l_cokIso : cokernel (N ◁ P.complex.d 2 1) ≅ N ⊗ kernel (P.π.f 0) :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) (a3l_shift_exact₀_tens N P).gIsCokernel

@[reassoc (attr := simp)]
lemma a3l_π_cokIso : cokernel.π _ ≫ (a3l_cokIso N P).hom = N ◁ a3l_shiftπ₀ P := by
  have := IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel (N ◁ P.complex.d 2 1))
      (a3l_shift_exact₀_tens N P).gIsCokernel WalkingParallelPair.one
  rw [a3l_cokIso]
  simpa using this

/-- `Tor_1(N, M)` computed from a projective resolution of `M`. -/
def a3l_H1IsoB : (a3l_tensC N P.complex).homology 1 ≅ kernel (N ◁ kernel.ι (P.π.f 0)) :=
  HomologicalComplex.homologyIsoSc' _ 2 1 0 (by simp) (by simp) ≪≫
    ShortComplex.homologyIsoKernelDesc _ ≪≫
    kernel.mapIso _ _ (a3l_cokIso N P) (Iso.refl _) (by
      rw [← cancel_epi (cokernel.π _)]
      rw [Iso.refl_hom, Category.comp_id, cokernel.π_desc]
      erw [a3l_π_cokIso_assoc]
      rw [← MonoidalCategory.whiskerLeft_comp, a3l_shiftπ₀_ι]
      rfl)

end shiftB

/-- The short exact sequence `0 → ker → P₀ → M → 0` of a projective resolution. -/
abbrev a3l_sesRes {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (kernel.ι (P.π.f 0)) (P.π.f 0) (kernel.condition _)

lemma a3l_sesRes_shortExact {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    (a3l_sesRes P).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    inferInstance inferInstance

/-- `Tor_1(M, N) ≅ Tor_1(N, M)`. -/
def a3l_tor1Iso (M N : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 1).obj M).obj N ≅ ((Tor (ModuleCat.{u} R) 1).obj N).obj M :=
  let P := ProjectiveResolution.of M
  let Q := ProjectiveResolution.of N
  have : Projective (a3l_sesRes P).X₂ := P.projective 0
  a3l_torIso M N Q 1 ≪≫ a3l_H1IsoA Q (a3l_sesRes P) (a3l_sesRes_shortExact P) ≪≫
    kernel.mapIso _ _ (β_ _ N) (β_ _ N) (BraidedCategory.braiding_naturality_left _ _) ≪≫
    (a3l_H1IsoB N P).symm ≪≫ (a3l_torIso N M P 1).symm

/-- Balancing of `Tor` over a commutative ring: `Tor_n(M, N) ≅ Tor_n(N, M)`. -/
theorem a3l_tor_symm (N : ModuleCat.{u} R) :
    ∀ (n : ℕ) (M : ModuleCat.{u} R),
      Nonempty (((Tor (ModuleCat.{u} R) n).obj M).obj N ≅ ((Tor (ModuleCat.{u} R) n).obj N).obj M)
  | 0, M => ⟨a3l_tor0Iso M N ≪≫ β_ M N ≪≫ (a3l_tor0Iso N M).symm⟩
  | 1, M => ⟨a3l_tor1Iso M N⟩
  | n + 2, M => by
    let P := ProjectiveResolution.of M
    let Q := ProjectiveResolution.of N
    have : Projective (a3l_sesRes P).X₂ := P.projective 0
    obtain ⟨e⟩ := a3l_tor_symm N (n + 1) (kernel (P.π.f 0))
    exact ⟨a3l_torIso M N Q (n + 2) ≪≫
      a3l_stepA Q (a3l_sesRes P) (a3l_sesRes_shortExact P) n ≪≫
      (a3l_torIso _ N Q (n + 1)).symm ≪≫ e ≪≫ a3l_torIso N _ (a3l_shiftRes P) (n + 1) ≪≫
      a3l_truncHomologyIso N P.complex n ≪≫ (a3l_torIso N M P (n + 2)).symm⟩

/-- Isomorphic `Tor` modules have the same length. -/
theorem a3l_length_tor_symm (M N : ModuleCat.{u} R) (n : ℕ) :
    Module.length R (((Tor (ModuleCat.{u} R) n).obj M).obj N) =
      Module.length R (((Tor (ModuleCat.{u} R) n).obj N).obj M) :=
  let ⟨e⟩ := a3l_tor_symm N n M
  e.toLinearEquiv.length_eq

end HodgeLean.Adapters

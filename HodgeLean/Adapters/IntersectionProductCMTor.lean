import HodgeLean.Adapters.IntersectionProductBasic

/-! # `Tor` over a commutative ring: balancing and Serre's vanishing for Cohen–Macaulay modules

Mathlib's `Tor` derives `X ⊗ -` in the second variable. Over a commutative ring `R` this file
builds
* isomorphisms `Tor_n(M, N) ≅ Tor_n(N, M)` of `R`-modules, by dimension shifting (a short exact
  sequence `0 → K → P₀ → M → 0` with `P₀` projective in the first variable, the truncation of a
  projective resolution in the second);
* the long exact sequence of `Tor(-, N)` for a short exact sequence in the first variable (a
  projective resolution of `N` is flat termwise);
* the action of scalars: an element of the annihilator of `M` or of `N` kills `Tor_n(M, N)`;
* vanishing of `Tor_n(k, N)` above the length of a weakly regular sequence generating the maximal
  ideal of a local ring, then for every module of finite length in place of `k` (dévissage);
* Serre's vanishing `Tor_n(M, N) = 0` for `n + length rs + length ss > length xs`, where `rs`,
  `ss` are weakly regular sequences in the maximal ideal on `M`, `N`, the quotient `M ⧸ (rs) M`
  has finite length and a power of the maximal ideal kills `M ⊗ N` (`a3c_isZero_tor_cm`).

Source: Weibel, *An Introduction to Homological Algebra*, Theorem 2.7.2 (balancing of `Tor`) and
§2.4 (dimension shifting); Serre, *Algèbre locale, multiplicités*, Chapitre IV (Koszul complex,
regular local rings) and Chapitre V, B.6 (vanishing of `Tor` for Cohen–Macaulay modules).
HC no distance; AV milestone no distance.
-/

open CategoryTheory MonoidalCategory Limits

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace HodgeLean.Adapters
universe u
variable {R : Type u} [CommRing R]

/-- The complex `X ⊗ C`. -/
abbrev a3c_tensC (X : ModuleCat.{u} R) (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  (((tensoringLeft (ModuleCat.{u} R)).obj X).mapHomologicalComplex _).obj C

/-- Projective objects of `ModuleCat R` are flat modules. -/
theorem a3c_flat_of_projective (P : ModuleCat.{u} R) [Projective P] : Module.Flat R P := by
  have : Module.Projective R P := (IsProjective.iff_projective (R := R) P).2 ‹_›
  infer_instance

/-- The chain map `f ⊗ C : X ⊗ C ⟶ Y ⊗ C`. -/
abbrev a3c_tensMap {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    a3c_tensC X C ⟶ a3c_tensC Y C :=
  (NatTrans.mapHomologicalComplex ((tensoringLeft _).map f) _).app C

/-- A short complex of modules tensored with a complex. -/
def a3c_sesC (S : ShortComplex (ModuleCat.{u} R)) (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (a3c_tensMap S.f C) (a3c_tensMap S.g C) (by
    refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
    simp [← MonoidalCategory.comp_whiskerRight, S.zero])

/-- Tensoring a short exact sequence with a complex of projectives keeps it short exact. -/
lemma a3c_sesC_shortExact (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (hC : ∀ i, Projective (C.X i)) :
    (a3c_sesC S C).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have := hC i
  have := a3c_flat_of_projective (C.X i)
  have : PreservesFiniteColimits (tensorRight (C.X i)) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (C.X i))
  refine ShortComplex.shortExact_of_iso ?_ (hS.map_of_exact (tensorRight (C.X i)))
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [a3c_sesC])
    (by simp [a3c_sesC])

section shift
variable {M : ModuleCat.{u} R} (P : ProjectiveResolution M)

/-- The augmentation `P₁ ⟶ ker (P₀ → M)` of the truncated resolution. -/
def a3c_shiftπ₀ : P.complex.X 1 ⟶ kernel (P.π.f 0) :=
  kernel.lift _ (P.complex.d 1 0) (by simp)

@[reassoc (attr := simp)]
lemma a3c_shiftπ₀_ι : a3c_shiftπ₀ P ≫ kernel.ι _ = P.complex.d 1 0 := by
  simp [a3c_shiftπ₀]

lemma a3c_shift_d : P.complex.d 2 1 ≫ a3c_shiftπ₀ P = 0 := by
  rw [← cancel_mono (kernel.ι (P.π.f 0))]; simp

lemma a3c_shift_exact₀ :
    (ShortComplex.mk _ _ (a3c_shift_d P)).Exact := by
  let α : ShortComplex.mk _ _ (a3c_shift_d P) ⟶ ShortComplex.mk _ _ (P.complex.d_comp_d 2 1 0) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι _ }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  exact P.exact_succ 0

instance a3c_shift_epi : Epi (a3c_shiftπ₀ P) :=
  (P.exact₀).epi_kernelLift

lemma a3c_truncate_exactAt (n : ℕ) :
    ((ChainComplex.truncate).obj P.complex).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  have := P.exact_succ (n + 1)
  exact (ShortComplex.exact_iff_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp))).1 this

/-- The truncation `P_{•+1}` of a projective resolution of `M` resolves `ker (P₀ → M)`. -/
def a3c_shiftRes : ProjectiveResolution (kernel (P.π.f 0)) where
  complex := (ChainComplex.truncate).obj P.complex
  projective n := P.projective (n + 1)
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨a3c_shiftπ₀ P, a3c_shift_d P⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨a3c_shift_exact₀ P, by dsimp; infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp) (by simp)
      all_goals first | rfl | simp
    · rw [quasiIsoAt_iff_exactAt']
      · exact a3c_truncate_exactAt P _
      · apply ChainComplex.exactAt_succ_single_obj⟩

end shift

/-- Tensoring with a flat module keeps a complex exact in positive degrees. -/
theorem a3c_exactAt_tensC (X : ModuleCat.{u} R) [Module.Flat R X]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (k : ℕ) (h : C.ExactAt (k + 1)) :
    (a3c_tensC X C).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp)] at h ⊢
  have := Module.Flat.lTensor_shortComplex_exact X _ h
  exact (ShortComplex.exact_iff_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp))).1 this

/-- Dimension shifting in the first variable. -/
def a3c_stepA {N : ModuleCat.{u} R} (Q : ProjectiveResolution N)
    (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) :
    (a3c_tensC S.X₃ Q.complex).homology (n + 2) ≅ (a3c_tensC S.X₁ Q.complex).homology (n + 1) :=
  have := a3c_flat_of_projective S.X₂
  (a3c_sesC_shortExact S hS Q.complex Q.projective).δIso (n + 2) (n + 1) (by simp)
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (a3c_exactAt_tensC S.X₂ _ (n + 1) (Q.complex_exactAt_succ (n + 1))))
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (a3c_exactAt_tensC S.X₂ _ n (Q.complex_exactAt_succ n)))

/-- Homology of the truncation, shifted by one. -/
def a3c_truncHomologyIso (N : ModuleCat.{u} R) (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (a3c_tensC N ((ChainComplex.truncate).obj C)).homology (n + 1) ≅
      (a3c_tensC N C).homology (n + 2) :=
  HomologicalComplex.homologyIsoSc' _ (n + 2) (n + 1) n (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso
      (show (a3c_tensC N ((ChainComplex.truncate).obj C)).sc' (n + 2) (n + 1) n ≅
          (a3c_tensC N C).sc' (n + 3) (n + 2) (n + 1) from
        ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)) ≪≫
    (HomologicalComplex.homologyIsoSc' (a3c_tensC N C) (n + 3) (n + 2) (n + 1)
      (ChainComplex.prev _ _) (ChainComplex.next_nat_succ _)).symm

/-- `Tor_n(M, N)` is the homology of `M ⊗ Q` for a projective resolution `Q` of `N`. -/
def a3c_torIso (M N : ModuleCat.{u} R) (Q : ProjectiveResolution N) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) n).obj M).obj N ≅ (a3c_tensC M Q.complex).homology n :=
  Q.isoLeftDerivedObj _ n

instance a3c_epi_whiskerLeft (X : ModuleCat.{u} R) {A B : ModuleCat.{u} R} (f : A ⟶ B) [Epi f] :
    Epi (X ◁ f) := by
  have : (tensorLeft X).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (ihom.adjunction X)
  exact (tensorLeft X).map_epi f

section base1
variable {N : ModuleCat.{u} R} (Q : ProjectiveResolution N)

lemma a3c_tens_exact₀ (X : ModuleCat.{u} R) :
    (ShortComplex.mk (X ◁ Q.complex.d 1 0) (X ◁ Q.π.f 0)
      (by rw [← MonoidalCategory.whiskerLeft_comp, Q.complex_d_comp_π_f_zero,
        MonoidalPreadditive.whiskerLeft_zero])).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (CokernelCofork.mapIsColimit _ Q.exact₀.gIsCokernel (tensorLeft X))

/-- `H_0(X ⊗ Q) ≅ X ⊗ N`. -/
def a3c_opcyclesIso (X : ModuleCat.{u} R) : (a3c_tensC X Q.complex).opcycles 0 ≅ X ⊗ N :=
  IsColimit.coconePointUniqueUpToIso ((a3c_tensC X Q.complex).opcyclesIsCokernel 1 0 (by simp))
    (a3c_tens_exact₀ Q X).gIsCokernel

@[reassoc (attr := simp)]
lemma a3c_p_opcyclesIso (X : ModuleCat.{u} R) :
    (a3c_tensC X Q.complex).pOpcycles 0 ≫ (a3c_opcyclesIso Q X).hom = X ◁ Q.π.f 0 :=
  by
    have := IsColimit.comp_coconePointUniqueUpToIso_hom
      ((a3c_tensC X Q.complex).opcyclesIsCokernel 1 0 (by simp))
      (a3c_tens_exact₀ Q X).gIsCokernel WalkingParallelPair.one
    rw [a3c_opcyclesIso]
    simpa using this

def a3c_H0Iso (X : ModuleCat.{u} R) : (a3c_tensC X Q.complex).homology 0 ≅ X ⊗ N :=
  (a3c_tensC X Q.complex).isoHomologyι₀ ≪≫ a3c_opcyclesIso Q X

lemma a3c_H0Iso_naturality {X Y : ModuleCat.{u} R} (f : X ⟶ Y) :
    HomologicalComplex.homologyMap (a3c_tensMap f Q.complex) 0 ≫ (a3c_H0Iso Q Y).hom =
      (a3c_H0Iso Q X).hom ≫ f ▷ N := by
  rw [← cancel_epi (a3c_tensC X Q.complex).isoHomologyι₀.inv]
  simp only [a3c_H0Iso, Iso.trans_hom, ChainComplex.isoHomologyι₀_inv_naturality_assoc,
    Iso.inv_hom_id_assoc]
  rw [← cancel_epi ((a3c_tensC X Q.complex).pOpcycles 0)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, HomologicalComplex.p_opcyclesMap_assoc,
    a3c_p_opcyclesIso, a3c_p_opcyclesIso_assoc]
  dsimp
  exact (MonoidalCategory.whisker_exchange f (Q.π.f 0)).symm

end base1


/-- `Tor_1(M, N)` computed from a short exact sequence `0 → K → P₀ → M → 0`, `P₀` projective. -/
def a3c_H1IsoA {N : ModuleCat.{u} R} (Q : ProjectiveResolution N)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) [Projective S.X₂] :
    (a3c_tensC S.X₃ Q.complex).homology 1 ≅ kernel (S.f ▷ N) :=
  have := a3c_flat_of_projective S.X₂
  have hT := a3c_sesC_shortExact S hS Q.complex Q.projective
  have hz : IsZero ((a3c_tensC S.X₂ Q.complex).homology 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (a3c_exactAt_tensC S.X₂ _ 0 (Q.complex_exactAt_succ 0))
  have hr : (ComplexShape.down ℕ).Rel 1 0 := rfl
  have := hT.mono_δ 1 0 hr hz
  IsLimit.conePointUniqueUpToIso (hT.homology_exact₁ 1 0 hr).fIsKernel
      (kernelIsKernel _) ≪≫
    kernel.mapIso _ _ (a3c_H0Iso Q S.X₁) (a3c_H0Iso Q S.X₂) (a3c_H0Iso_naturality Q S.f)

section shiftB
variable (N : ModuleCat.{u} R) {M : ModuleCat.{u} R} (P : ProjectiveResolution M)

lemma a3c_shift_exact₀_tens :
    (ShortComplex.mk (N ◁ P.complex.d 2 1) (N ◁ a3c_shiftπ₀ P)
      (by rw [← MonoidalCategory.whiskerLeft_comp, a3c_shift_d,
        MonoidalPreadditive.whiskerLeft_zero])).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (CokernelCofork.mapIsColimit _ (a3c_shift_exact₀ P).gIsCokernel (tensorLeft N))

def a3c_cokIso : cokernel (N ◁ P.complex.d 2 1) ≅ N ⊗ kernel (P.π.f 0) :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) (a3c_shift_exact₀_tens N P).gIsCokernel

@[reassoc (attr := simp)]
lemma a3c_π_cokIso : cokernel.π _ ≫ (a3c_cokIso N P).hom = N ◁ a3c_shiftπ₀ P := by
  have := IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel (N ◁ P.complex.d 2 1))
      (a3c_shift_exact₀_tens N P).gIsCokernel WalkingParallelPair.one
  rw [a3c_cokIso]
  simpa using this

/-- `Tor_1(N, M)` computed from a projective resolution of `M`. -/
def a3c_H1IsoB : (a3c_tensC N P.complex).homology 1 ≅ kernel (N ◁ kernel.ι (P.π.f 0)) :=
  HomologicalComplex.homologyIsoSc' _ 2 1 0 (by simp) (by simp) ≪≫
    ShortComplex.homologyIsoKernelDesc _ ≪≫
    kernel.mapIso _ _ (a3c_cokIso N P) (Iso.refl _) (by
      rw [← cancel_epi (cokernel.π _)]
      rw [Iso.refl_hom, Category.comp_id, cokernel.π_desc]
      erw [a3c_π_cokIso_assoc]
      rw [← MonoidalCategory.whiskerLeft_comp, a3c_shiftπ₀_ι]
      rfl)

end shiftB

/-- The short exact sequence `0 → ker → P₀ → M → 0` of a projective resolution. -/
abbrev a3c_sesRes {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (kernel.ι (P.π.f 0)) (P.π.f 0) (kernel.condition _)

lemma a3c_sesRes_shortExact {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    (a3c_sesRes P).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    inferInstance inferInstance

/-- `Tor_1(M, N) ≅ Tor_1(N, M)`. -/
def a3c_tor1Iso (M N : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 1).obj M).obj N ≅ ((Tor (ModuleCat.{u} R) 1).obj N).obj M :=
  let P := ProjectiveResolution.of M
  let Q := ProjectiveResolution.of N
  have : Projective (a3c_sesRes P).X₂ := P.projective 0
  a3c_torIso M N Q 1 ≪≫ a3c_H1IsoA Q (a3c_sesRes P) (a3c_sesRes_shortExact P) ≪≫
    kernel.mapIso _ _ (β_ _ N) (β_ _ N) (BraidedCategory.braiding_naturality_left _ _) ≪≫
    (a3c_H1IsoB N P).symm ≪≫ (a3c_torIso N M P 1).symm

/-- Balancing of `Tor` over a commutative ring: `Tor_n(M, N) ≅ Tor_n(N, M)`. -/
theorem a3c_tor_symm (N : ModuleCat.{u} R) :
    ∀ (n : ℕ) (M : ModuleCat.{u} R),
      Nonempty (((Tor (ModuleCat.{u} R) n).obj M).obj N ≅ ((Tor (ModuleCat.{u} R) n).obj N).obj M)
  | 0, M => ⟨a3c_tor0Iso M N ≪≫ β_ M N ≪≫ (a3c_tor0Iso N M).symm⟩
  | 1, M => ⟨a3c_tor1Iso M N⟩
  | n + 2, M => by
    let P := ProjectiveResolution.of M
    let Q := ProjectiveResolution.of N
    have : Projective (a3c_sesRes P).X₂ := P.projective 0
    obtain ⟨e⟩ := a3c_tor_symm N (n + 1) (kernel (P.π.f 0))
    exact ⟨a3c_torIso M N Q (n + 2) ≪≫
      a3c_stepA Q (a3c_sesRes P) (a3c_sesRes_shortExact P) n ≪≫
      (a3c_torIso _ N Q (n + 1)).symm ≪≫ e ≪≫ a3c_torIso N _ (a3c_shiftRes P) (n + 1) ≪≫
      a3c_truncHomologyIso N P.complex n ≪≫ (a3c_torIso N M P (n + 2)).symm⟩

/-- Isomorphic `Tor` modules have the same length. -/
theorem a3c_length_tor_symm (M N : ModuleCat.{u} R) (n : ℕ) :
    Module.length R (((Tor (ModuleCat.{u} R) n).obj M).obj N) =
      Module.length R (((Tor (ModuleCat.{u} R) n).obj N).obj M) :=
  let ⟨e⟩ := a3c_tor_symm N n M
  e.toLinearEquiv.length_eq


/-! ## The long exact sequence in the first variable -/

section les
variable {N : ModuleCat.{u} R} (Q : ProjectiveResolution N)

/-- Exactness of `Tor_n(X₁, N) → Tor_n(X₂, N) → Tor_n(X₃, N)`. -/
lemma a3c_isZero_mid (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (n : ℕ)
    (h₁ : IsZero ((a3c_tensC S.X₁ Q.complex).homology n))
    (h₃ : IsZero ((a3c_tensC S.X₃ Q.complex).homology n)) :
    IsZero ((a3c_tensC S.X₂ Q.complex).homology n) :=
  ((a3c_sesC_shortExact S hS Q.complex Q.projective).homology_exact₂ n).isZero_of_both_isZero
    h₁ h₃

/-- Exactness of `Tor_{n+1}(X₂, N) → Tor_{n+1}(X₃, N) → Tor_n(X₁, N)`. -/
lemma a3c_isZero_right (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (n : ℕ)
    (h₂ : IsZero ((a3c_tensC S.X₂ Q.complex).homology (n + 1)))
    (h₁ : IsZero ((a3c_tensC S.X₁ Q.complex).homology n)) :
    IsZero ((a3c_tensC S.X₃ Q.complex).homology (n + 1)) :=
  ((a3c_sesC_shortExact S hS Q.complex Q.projective).homology_exact₃ (n + 1) n
    (by simp)).isZero_of_both_isZero h₂ h₁

/-- Exactness of `Tor_{n+1}(X₃, N) → Tor_n(X₁, N) → Tor_n(X₂, N)`. -/
lemma a3c_mono_of_isZero (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (n : ℕ)
    (h₃ : IsZero ((a3c_tensC S.X₃ Q.complex).homology (n + 1))) :
    Mono (HomologicalComplex.homologyMap (a3c_tensMap S.f Q.complex) n) :=
  ((a3c_sesC_shortExact S hS Q.complex Q.projective).homology_exact₁ (n + 1) n
    (by simp)).mono_g (h₃.eq_of_src _ _)

end les

/-! ## Scalars acting on `Tor` -/

lemma a3c_homologyMap_smul {C D : ChainComplex (ModuleCat.{u} R) ℕ} (r : R) (φ : C ⟶ D)
    (n : ℕ) :
    HomologicalComplex.homologyMap (r • φ) n = r • HomologicalComplex.homologyMap φ n := by
  unfold HomologicalComplex.homologyMap
  rw [← ShortComplex.homologyMap_smul]
  congr 1

lemma a3c_tensMap_smul (M : ModuleCat.{u} R) (r : R) (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    a3c_tensMap (r • 𝟙 M) C = r • 𝟙 (a3c_tensC M C) := by
  ext i : 1
  simp [MonoidalLinear.smul_whiskerRight]

/-- Multiplication by `r` on `M` induces multiplication by `r` on `H_n(M ⊗ C)`. -/
lemma a3c_homologyMap_tensMap_smul (M : ModuleCat.{u} R) (r : R)
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap (a3c_tensMap (r • 𝟙 M) C) n =
      r • 𝟙 ((a3c_tensC M C).homology n) := by
  rw [a3c_tensMap_smul, a3c_homologyMap_smul, HomologicalComplex.homologyMap_id]

/-- An element of the annihilator of `M` kills `Tor_n(M, N)`. -/
theorem a3c_smul_tor_eq_zero_of_mem_annihilator_left (M N : ModuleCat.{u} R) (r : R)
    (hr : r ∈ Module.annihilator R M) (n : ℕ) (t : ((Tor (ModuleCat.{u} R) n).obj M).obj N) :
    r • t = 0 := by
  let Q := ProjectiveResolution.of N
  let e := a3c_torIso M N Q n
  have h0 : r • 𝟙 M = 0 := by
    ext x
    simp [Module.mem_annihilator.mp hr x]
  have hH : ∀ s : (a3c_tensC M Q.complex).homology n, r • s = 0 := by
    intro s
    have h := a3c_homologyMap_tensMap_smul M r Q.complex n
    rw [h0] at h
    have h' : (HomologicalComplex.homologyMap (a3c_tensMap (0 : M ⟶ M) Q.complex) n).hom s =
        (r • 𝟙 ((a3c_tensC M Q.complex).homology n)).hom s := by rw [h]
    have hz : a3c_tensMap (0 : M ⟶ M) Q.complex = 0 := by
      ext i : 1
      simp
    rw [hz, HomologicalComplex.homologyMap_zero] at h'
    simp only [ModuleCat.hom_zero, ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.zero_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at h'
    exact h'.symm
  apply e.toLinearEquiv.injective
  rw [map_smul, map_zero]
  exact hH _

/-- An element of the annihilator of `N` kills `Tor_n(M, N)`, through balancing. -/
theorem a3c_smul_tor_eq_zero_of_mem_annihilator_right (M N : ModuleCat.{u} R) (r : R)
    (hr : r ∈ Module.annihilator R N) (n : ℕ) (t : ((Tor (ModuleCat.{u} R) n).obj M).obj N) :
    r • t = 0 := by
  obtain ⟨e⟩ := a3c_tor_symm N n M
  apply e.toLinearEquiv.injective
  rw [map_smul, map_zero]
  exact a3c_smul_tor_eq_zero_of_mem_annihilator_left N M r hr n _

theorem a3c_isZero_tor_of_subsingleton (M N : ModuleCat.{u} R) [Subsingleton M] (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj N) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  have h1 : ∀ t : ((Tor (ModuleCat.{u} R) n).obj M).obj N, t = 0 := fun t => by
    simpa using a3c_smul_tor_eq_zero_of_mem_annihilator_left M N 1
      (by simp [Module.mem_annihilator, Subsingleton.elim _ (0 : M)]) n t
  rw [h1 a, h1 b]

/-- Transport of the vanishing of `Tor` along an isomorphism in the first variable. -/
theorem a3c_isZero_tor_of_iso {M M' : ModuleCat.{u} R} (e : M ≅ M') (N : ModuleCat.{u} R)
    (n : ℕ) (h : IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj N)) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj M').obj N) :=
  h.of_iso (((Tor (ModuleCat.{u} R) n).mapIso e).app N).symm

/-- If `r` is regular on `M`, some power of `r` kills `Tor_n(M, N)` and
`Tor_{n+1}(M/rM, N) = 0`, then `Tor_n(M, N) = 0`. -/
theorem a3c_isZero_tor_of_isSMulRegular (M N : ModuleCat.{u} R) (r : R) (hr : IsSMulRegular M r)
    (n K : ℕ) (hK : ∀ t : ((Tor (ModuleCat.{u} R) n).obj M).obj N, r ^ K • t = 0)
    (h : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj (ModuleCat.of R (QuotSMulTop r M))).obj N)) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj N) := by
  let Q := ProjectiveResolution.of N
  let e := a3c_torIso M N Q n
  have hm := a3c_mono_of_isZero Q (M.smulShortComplex r) hr.smulShortComplex_shortExact n
    (h.of_iso (a3c_torIso _ N Q (n + 1)).symm)
  have key : HomologicalComplex.homologyMap (a3c_tensMap (M.smulShortComplex r).f Q.complex) n =
      r • 𝟙 ((a3c_tensC M Q.complex).homology n) := by
    exact a3c_homologyMap_tensMap_smul M r Q.complex n
  rw [key, ModuleCat.mono_iff_injective] at hm
  have hinj : ∀ s : (a3c_tensC M Q.complex).homology n, r • s = 0 → s = 0 := fun s hs =>
    hm (show r • s = r • (0 : (a3c_tensC M Q.complex).homology n) by rw [smul_zero]; exact hs)
  have hpow : ∀ (k : ℕ) (s : (a3c_tensC M Q.complex).homology n), r ^ k • s = 0 → s = 0 := by
    intro k
    induction k with
    | zero => intro s hs; simpa using hs
    | succ k ih =>
      intro s hs
      rw [pow_succ, mul_smul] at hs
      exact hinj s (ih _ hs)
  refine IsZero.of_iso ?_ e
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  have hz : ∀ s : (a3c_tensC M Q.complex).homology n, s = 0 := fun s => hpow K s (by
    obtain ⟨t, rfl⟩ := e.toLinearEquiv.surjective s
    have := hK t
    change r ^ K • e.toLinearEquiv t = 0
    rw [← map_smul, this, map_zero])
  rw [hz a, hz b]

/-! ## Vanishing above the length of a regular sequence -/

/-- `M ⧸ (r₁, …, rₖ) M`, as an iterated quotient `QuotSMulTop`. -/
def a3c_iterQuot : List R → ModuleCat.{u} R → ModuleCat.{u} R
  | [], M => M
  | r :: rs, M => a3c_iterQuot rs (ModuleCat.of R (QuotSMulTop r M))

/-- `Tor_n(R, N) = 0` for `n > 0`. -/
theorem a3c_isZero_tor_self (N : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj (ModuleCat.of R R)).obj N) := by
  obtain ⟨e⟩ := a3c_tor_symm N (n + 1) (ModuleCat.of R R)
  exact (isZero_Tor_succ_of_projective _ N (ModuleCat.of R R) n).of_iso e

/-- Dividing by a weakly regular sequence of length `k` raises the vanishing bound of
`Tor(-, N)` by at most `k`. -/
theorem a3c_isZero_tor_iterQuot (N : ModuleCat.{u} R) :
    ∀ (rs : List R) (M : ModuleCat.{u} R) (e : ℕ), RingTheory.Sequence.IsWeaklyRegular M rs →
      (∀ n, e < n → IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj N)) →
      ∀ n, e + rs.length < n → IsZero (((Tor (ModuleCat.{u} R) n).obj (a3c_iterQuot rs M)).obj N)
  | [], M, e, _, h, n, hn => h n (by simpa using hn)
  | r :: rs, M, e, hreg, h, n, hn => by
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hreg
    refine a3c_isZero_tor_iterQuot N rs _ (e + 1) hreg.2 ?_ n (by simp at hn; omega)
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    let Q := ProjectiveResolution.of N
    have := a3c_isZero_right Q (M.smulShortComplex r) hreg.1.smulShortComplex_shortExact k
      ((h (k + 1) (by omega)).of_iso (a3c_torIso _ N Q (k + 1)).symm)
      ((h k (by omega)).of_iso (a3c_torIso _ N Q k).symm)
    exact this.of_iso (a3c_torIso _ N Q (k + 1))


/-- `M ⧸ (r₁, …, rₖ) M` is the iterated quotient. -/
def a3c_iterQuotEquiv : ∀ (rs : List R) (M : ModuleCat.{u} R),
    a3c_iterQuot rs M ≃ₗ[R] (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M))
  | [], M => (Submodule.quotEquivOfEqBot _ (by simp)).symm
  | r :: rs, M => a3c_iterQuotEquiv rs _ ≪≫ₗ
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r rs).symm

/-! ## Finite length modules -/

open IsLocalRing

lemma a3c_nonempty_iso_residue [IsLocalRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] :
    Nonempty (ModuleCat.of R M ≅ ModuleCat.of R (R ⧸ maximalIdeal R)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹_›
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  exact ⟨e.toModuleIso⟩

/-- A module of finite length over a local ring is killed by a power of the maximal ideal. -/
theorem a3c_exists_pow_le_annihilator [IsLocalRing R] {M : Type u} [AddCommGroup M]
    [Module R M] (hM : IsFiniteLength R M) :
    ∃ K : ℕ, maximalIdeal R ^ K ≤ Module.annihilator R M := by
  induction hM with
  | of_subsingleton =>
    refine ⟨0, fun a _ => ?_⟩
    rw [Module.mem_annihilator]
    intro m
    exact Subsingleton.elim _ _
  | @of_simple_quotient M _ _ P _ _ ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨K + 1, ?_⟩
    have hs : ∀ b ∈ maximalIdeal R, ∀ m : M, b • m ∈ P := by
      intro b hb m
      obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R (M ⧸ P)›
      obtain rfl := IsLocalRing.eq_maximalIdeal hI
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      apply e.injective
      rw [map_smul, map_zero]
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk m))
      rw [← hc, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ hb
    rw [pow_succ]
    refine Ideal.mul_le.mpr fun a ha b hb => ?_
    rw [Module.mem_annihilator]
    intro m
    have h := Module.mem_annihilator.mp (hK ha) ⟨b • m, hs b hb m⟩
    rw [mul_smul]
    exact congrArg Subtype.val h

/-- Dévissage: if `Tor_n(k, N)` vanishes above `d`, so does `Tor_n(M, N)` for every module `M`
of finite length. -/
theorem a3c_isZero_tor_of_isFiniteLength [IsLocalRing R] (N : ModuleCat.{u} R) (d : ℕ)
    (hk : ∀ n, d < n →
      IsZero (((Tor (ModuleCat.{u} R) n).obj (ModuleCat.of R (R ⧸ maximalIdeal R))).obj N))
    {M : Type u} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) (n : ℕ) (hn : d < n) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj (ModuleCat.of R M)).obj N) := by
  induction hM with
  | of_subsingleton => exact a3c_isZero_tor_of_subsingleton _ _ _
  | @of_simple_quotient M _ _ P _ _ ih =>
    let S : ShortComplex (ModuleCat.{u} R) :=
      ModuleCat.shortComplexOfCompEqZero P.subtype P.mkQ
        (LinearMap.exact_subtype_mkQ P).linearMap_comp_eq_zero
    have hS : S.ShortExact :=
      { exact := ModuleCat.shortComplex_exact _ (LinearMap.exact_subtype_mkQ P)
        mono_f := by
          rw [ModuleCat.mono_iff_injective]
          exact Subtype.val_injective
        epi_g := by
          rw [ModuleCat.epi_iff_surjective]
          exact Submodule.mkQ_surjective _ }
    let Q := ProjectiveResolution.of N
    obtain ⟨e⟩ := a3c_nonempty_iso_residue (R := R) (M ⧸ P)
    have h₃ := a3c_isZero_tor_of_iso e.symm N n (hk n hn)
    exact (a3c_isZero_mid Q S hS n (ih.of_iso (a3c_torIso _ N Q n).symm)
      (h₃.of_iso (a3c_torIso _ N Q n).symm)).of_iso (a3c_torIso _ N Q n)

/-- Over a local ring whose maximal ideal is generated by a weakly regular sequence `xs`,
`Tor_n(k, N) = 0` for `n > length xs` (the Koszul resolution of the residue field). -/
theorem a3c_isZero_tor_residue [IsLocalRing R] (xs : List R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R xs) (hxs : Ideal.ofList xs = maximalIdeal R)
    (N : ModuleCat.{u} R) (n : ℕ) (hn : xs.length < n) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj (ModuleCat.of R (R ⧸ maximalIdeal R))).obj N) := by
  have h := a3c_isZero_tor_iterQuot N xs (ModuleCat.of R R) 0 hreg (fun m hm => by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact a3c_isZero_tor_self N k) n (by simpa using hn)
  refine a3c_isZero_tor_of_iso ?_ N n h
  refine (a3c_iterQuotEquiv xs _ ≪≫ₗ Submodule.quotEquivOfEq _ _ ?_).toModuleIso
  change Ideal.ofList xs • (⊤ : Ideal R) = maximalIdeal R
  rw [Ideal.smul_eq_mul, Ideal.mul_top, hxs]

lemma a3c_annihilator_le_quotSMulTop (M : ModuleCat.{u} R) (r : R) :
    Module.annihilator R M ≤ Module.annihilator R (ModuleCat.of R (QuotSMulTop r M)) := by
  intro a ha
  rw [Module.mem_annihilator] at ha ⊢
  intro m
  obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective _ m
  change a • Submodule.Quotient.mk m' = 0
  rw [← Submodule.Quotient.mk_smul, ha, Submodule.Quotient.mk_zero]

section serre
variable [IsLocalRing R] (xs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R xs)
  (hxs : Ideal.ofList xs = maximalIdeal R)
include hreg hxs

/-- Serre's vanishing with a module of finite length in the first variable:
`Tor_n(M₀, N) = 0` for `n + length ss > length xs` when `ss` is weakly regular on `N`. -/
theorem a3c_isZero_tor_of_finiteLength_left (M₀ : ModuleCat.{u} R) (hM₀ : IsFiniteLength R M₀) :
    ∀ (ss : List R) (N : ModuleCat.{u} R), RingTheory.Sequence.IsWeaklyRegular N ss →
      (∀ s ∈ ss, s ∈ maximalIdeal R) →
      ∀ n, xs.length < n + ss.length → IsZero (((Tor (ModuleCat.{u} R) n).obj M₀).obj N)
  | [], N, _, _, n, hn => a3c_isZero_tor_of_isFiniteLength N xs.length
      (fun m hm => a3c_isZero_tor_residue xs hreg hxs N m hm) hM₀ n (by simpa using hn)
  | s :: ss, N, hN, hss, n, hn => by
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hN
    obtain ⟨K, hK⟩ := a3c_exists_pow_le_annihilator hM₀
    obtain ⟨e⟩ := a3c_tor_symm N n M₀
    refine IsZero.of_iso ?_ e
    refine a3c_isZero_tor_of_isSMulRegular N M₀ s hN.1 n K (fun t =>
      a3c_smul_tor_eq_zero_of_mem_annihilator_right N M₀ _
        (hK (Ideal.pow_mem_pow (hss s (by simp)) K)) n t) ?_
    obtain ⟨e'⟩ := a3c_tor_symm (ModuleCat.of R (QuotSMulTop s N)) (n + 1) M₀
    exact (a3c_isZero_tor_of_finiteLength_left M₀ hM₀ ss _ hN.2
      (fun x hx => hss x (by simp [hx])) (n + 1) (by simp at hn; omega)).of_iso e'.symm

/-- Serre's vanishing of higher `Tor` for Cohen–Macaulay modules: over a local ring whose
maximal ideal is generated by a weakly regular sequence `xs`, if `rs` is weakly regular on `M`,
`ss` is weakly regular on `N`, `M ⧸ (rs) M` has finite length and `M ⊗ N` is killed by a power of
the maximal ideal, then `Tor_n(M, N) = 0` for `n + length rs + length ss > length xs`.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.6, Corollaire; the proof is by
induction on the regular sequences with the long exact sequence of `Tor`. -/
theorem a3c_isZero_tor_cm (N : ModuleCat.{u} R) (ss : List R)
    (hN : RingTheory.Sequence.IsWeaklyRegular N ss) (hss : ∀ s ∈ ss, s ∈ maximalIdeal R)
    (K : ℕ) :
    ∀ (rs : List R) (M : ModuleCat.{u} R), RingTheory.Sequence.IsWeaklyRegular M rs →
      (∀ r ∈ rs, r ∈ maximalIdeal R) →
      maximalIdeal R ^ K ≤ Module.annihilator R M ⊔ Module.annihilator R N →
      IsFiniteLength R (a3c_iterQuot rs M) →
      ∀ n, xs.length < n + rs.length + ss.length →
        IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj N)
  | [], M, _, _, _, hfin, n, hn =>
    a3c_isZero_tor_of_finiteLength_left xs hreg hxs M hfin ss N hN hss n (by simpa using hn)
  | r :: rs, M, hM, hrs, hK, hfin, n, hn => by
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hM
    refine a3c_isZero_tor_of_isSMulRegular M N r hM.1 n K ?_ ?_
    · intro t
      have hmem : r ^ K ∈ Module.annihilator R M ⊔ Module.annihilator R N :=
        hK (Ideal.pow_mem_pow (hrs r (by simp)) K)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
      rw [← hab, add_smul, a3c_smul_tor_eq_zero_of_mem_annihilator_left M N a ha n t,
        a3c_smul_tor_eq_zero_of_mem_annihilator_right M N b hb n t, add_zero]
    · exact a3c_isZero_tor_cm N ss hN hss K rs _ hM.2 (fun x hx => hrs x (by simp [hx]))
        (le_trans hK (sup_le_sup_right (a3c_annihilator_le_quotSMulTop M r) _)) hfin (n + 1)
        (by simp at hn; omega)

end serre

end HodgeLean.Adapters

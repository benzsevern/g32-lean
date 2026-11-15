import HodgeLean.Adapters.IntersectionProductCMQuotient

/-! # `Tor` vanishes above the dimension of a regular local ring

Over a Noetherian local ring `R` with residue field `k`, if `Tor_n(k, N) = 0` for `n > d` and `N`
is finitely generated, then `Tor_n(M, N) = 0` for every `M` and `n > d`
(`a3e_isZero_tor_of_residue`): by induction on `d`, through a syzygy `0 → K → F → N → 0` with
`F` free; for `d = 0` the local criterion (`𝔪 ⊗ N → N` injective) makes `N` free. Over a regular
local ring the Koszul resolution of `k` gives the hypothesis with `d = dim R`
(`a3e_isZero_tor_regular`).

This is the range of the alternating sum in Serre's multiplicity `a3i_serreMult`, and the
vanishing of `Tor_{d+1}` used by the Euler characteristic along a nonzerodivisor
(`a3e_euler_tor`).

Source: Serre, *Algèbre locale, multiplicités*, Chapitre IV, Théorème 9 (a regular local ring
of dimension `d` has global dimension `d`); Matsumura, *Commutative Ring Theory*, Theorem 19.2
and Theorem 7.10 (finitely generated flat modules over a local ring are free).
HC no distance; AV milestone no distance.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory IsLocalRing

noncomputable section
namespace HodgeLean.Adapters
universe u

section les
variable {R : Type u} [CommRing R]

/-- `Tor(-, N)` vanishing is symmetric in the two variables (balancing). -/
theorem a3e_isZero_tor_symm (M N : ModuleCat.{u} R) (n : ℕ)
    (h : IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj N)) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj N).obj M) :=
  let ⟨e⟩ := a3c_tor_symm N n M
  h.of_iso e.symm

/-- Exactness of `Tor_{n+1}(X₂, N) → Tor_{n+1}(X₃, N) → Tor_n(X₁, N)`, in `Tor`. -/
theorem a3e_isZero_tor_right (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (N : ModuleCat.{u} R) (n : ℕ) (h₂ : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₂).obj N))
    (h₁ : IsZero (((Tor (ModuleCat.{u} R) n).obj S.X₁).obj N)) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₃).obj N) := by
  let Q := ProjectiveResolution.of N
  exact (a3c_isZero_right Q S hS n (h₂.of_iso (a3c_torIso _ N Q (n + 1)).symm)
    (h₁.of_iso (a3c_torIso _ N Q n).symm)).of_iso (a3c_torIso _ N Q (n + 1))

/-- Exactness of `Tor_{n+1}(X₃, N) → Tor_n(X₁, N) → Tor_n(X₂, N)`, in `Tor`. -/
theorem a3e_isZero_tor_left (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (N : ModuleCat.{u} R) (n : ℕ) (h₃ : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₃).obj N))
    (h₂ : IsZero (((Tor (ModuleCat.{u} R) n).obj S.X₂).obj N)) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj S.X₁).obj N) := by
  let Q := ProjectiveResolution.of N
  have hT := a3c_sesC_shortExact S hS Q.complex Q.projective
  exact ((hT.homology_exact₁ (n + 1) n (by simp)).isZero_of_both_isZero
    (h₃.of_iso (a3c_torIso _ N Q (n + 1)).symm) (h₂.of_iso (a3c_torIso _ N Q n).symm)).of_iso
    (a3c_torIso _ N Q n)

end les

section syzygy
variable {R : Type u} [CommRing R]

/-- The short exact sequence `0 → ker f → F → N → 0` of a surjection `f`. -/
def a3e_kerSES {F N : Type u} [AddCommGroup F] [Module R F] [AddCommGroup N] [Module R N]
    (f : F →ₗ[R] N) : ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.ker f).subtype f
    (LinearMap.exact_subtype_ker_map f).linearMap_comp_eq_zero

theorem a3e_kerSES_shortExact {F N : Type u} [AddCommGroup F] [Module R F] [AddCommGroup N]
    [Module R N] (f : F →ₗ[R] N) (hf : Function.Surjective f) : (a3e_kerSES f).ShortExact where
  exact := ModuleCat.shortComplex_exact _ (LinearMap.exact_subtype_ker_map f)
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    exact hf

end syzygy

section residue
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The short exact sequence `0 → 𝔪 → R → k → 0`. -/
abbrev a3e_residueSES : ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero (maximalIdeal R).subtype (maximalIdeal R).mkQ
    (LinearMap.exact_subtype_mkQ _).linearMap_comp_eq_zero

/-- Local criterion: a finitely generated module `N` with `Tor_1(k, N) = 0` is free. -/
theorem a3e_free_of_isZero_tor_one (N : ModuleCat.{u} R) [Module.Finite R N]
    (h : IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (R ⧸ maximalIdeal R))).obj N)) :
    Module.Free R N := by
  let S := a3e_residueSES (R := R)
  have hS : S.ShortExact :=
    { exact := ModuleCat.shortComplex_exact _ (LinearMap.exact_subtype_mkQ _)
      mono_f := by
        rw [ModuleCat.mono_iff_injective]
        exact Subtype.val_injective
      epi_g := by
        rw [ModuleCat.epi_iff_surjective]
        exact Submodule.mkQ_surjective _ }
  let Q := ProjectiveResolution.of N
  have hm := a3c_mono_of_isZero Q S hS 0 (h.of_iso (a3c_torIso _ N Q 1).symm)
  have hnat := a3c_H0Iso_naturality Q S.f
  have hw : S.f ▷ N = (a3c_H0Iso Q S.X₁).inv ≫
      HomologicalComplex.homologyMap (a3c_tensMap S.f Q.complex) 0 ≫ (a3c_H0Iso Q S.X₂).hom := by
    rw [hnat, Iso.inv_hom_id_assoc]
  have : Mono (S.f ▷ N) := by
    rw [hw]
    infer_instance
  rw [ModuleCat.mono_iff_injective] at this
  have : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N
  exact Module.free_of_maximalIdeal_rTensor_injective ‹Function.Injective _›

/-- If `Tor_n(k, N)` vanishes above `d` for a finitely generated `N`, then so does `Tor_n(M, N)`
for every `M`. -/
theorem a3e_isZero_tor_of_residue (d : ℕ) :
    ∀ (N : ModuleCat.{u} R) [Module.Finite R N],
      (∀ n, d < n → IsZero (((Tor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R (R ⧸ maximalIdeal R))).obj N)) →
      ∀ (M : ModuleCat.{u} R) (n : ℕ), d < n → IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj N) := by
  induction d with
  | zero =>
    intro N _ hk M n hn
    have : Module.Free R N := a3e_free_of_isZero_tor_one N (hk 1 one_pos)
    have : Module.Projective R N := Module.Projective.of_free
    have : Projective N := (IsProjective.iff_projective (R := R) N).1 this
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact isZero_Tor_succ_of_projective _ _ _ _
  | succ d ih =>
    intro N _ hk M n hn
    obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R N
    let S := a3e_kerSES f
    have hS : S.ShortExact := a3e_kerSES_shortExact f hf
    have : Module.Projective R (Fin m → R) := Module.Projective.of_free
    have : Projective S.X₂ := (IsProjective.iff_projective (R := R) S.X₂).1 this
    have : Module.Finite R (LinearMap.ker f) := Module.Finite.of_injective
      (LinearMap.ker f).subtype Subtype.val_injective
    have : Module.Finite R S.X₁ := this
    have hK : ∀ n, d < n → IsZero (((Tor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R (R ⧸ maximalIdeal R))).obj S.X₁) := by
      intro n hn
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      refine a3e_isZero_tor_symm _ _ _ (a3e_isZero_tor_left S hS _ (n' + 1)
        (a3e_isZero_tor_symm _ _ _ (hk _ (by omega)))
        (a3e_isZero_tor_symm _ _ _ (isZero_Tor_succ_of_projective _ _ _ _)))
    have := ih S.X₁ hK
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact a3e_isZero_tor_symm _ _ _ (a3e_isZero_tor_right S hS M n'
      (a3e_isZero_tor_symm _ _ _ (isZero_Tor_succ_of_projective _ _ _ _))
      (a3e_isZero_tor_symm _ _ _ (this M n' (by omega))))

end residue

/-- Over a regular local ring of dimension `d`, `Tor_n(M, N) = 0` for `n > d` and `N` finitely
generated.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre IV, Théorème 9; Matsumura,
*Commutative Ring Theory*, Theorem 19.2. -/
theorem a3e_isZero_tor_regular {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M N : ModuleCat.{u} R) [Module.Finite R N] (n : ℕ) (hn : ringKrullDim R < n) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj N) := by
  obtain ⟨ys, hlen, hys, -, hreg⟩ := a3c_exists_regular_sop R
  rw [← hlen] at hn
  have hn' : ys.length < n := by exact_mod_cast hn
  exact a3e_isZero_tor_of_residue ys.length N
    (fun m hm => a3c_isZero_tor_residue ys hreg hys N m hm) M n hn'

example {R : Type u} [CommRing R] [IsRegularLocalRing R] (M N : ModuleCat.{u} R)
    [Module.Finite R N] (n : ℕ) (hn : ringKrullDim R < n) :
    Module.length R (((Tor (ModuleCat.{u} R) n).obj M).obj N) = 0 := by
  rw [Module.length_eq_zero_iff, ← ModuleCat.isZero_iff_subsingleton]
  exact a3e_isZero_tor_regular M N n hn

end HodgeLean.Adapters

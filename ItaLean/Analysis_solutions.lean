import Mathlib
set_option linter.unusedVariables false

noncomputable section

namespace ItaLean



/-!
# Filters
-/



section Filter

open Filter Topology
variable {α β γ : Type*}

lemma mono (f : α → β) {F G : Filter α} (h : F ≤ G) : F.map f ≤ G.map f := /- fun _ H ↦ h H -/by
  simp [Filter.le_def] --remove after first trial
  intro U hU
  apply h --remove after first trial
  exact /- h -/ hU


/-- The function `f` tends to `G` along `F`. -/
def Tendsto (f : α → β) (F : Filter α) (G : Filter β) := F.map f ≤ G

lemma Tendsto_comp {s : α → β} {t : β → γ} {F : Filter α} {G : Filter β} {H : Filter γ}
    (hs : Tendsto s F G) (ht : Tendsto t G H) : Tendsto (t ∘ s) F H := by --remove
  rw [Tendsto] --remove
  have := mono t hs --remove
  apply le_trans this ht --remove
  -- le_trans (mono t hs) ht


example (f g : ℝ → ℝ) (hf : Tendsto f (𝓝 0) (𝓝 Real.pi))
    (hg : Tendsto g (𝓝 Real.pi) atTop) : Tendsto (g ∘ f) (𝓝 0) atTop := by
  apply Tendsto_comp hf hg

example (a : ℕ → ℝ) (φ : ℝ → ℂ) (ha : Tendsto a atTop (𝓝 (-1)))
    (hφ : Tendsto φ (𝓝 (-1)) (𝓝 (Complex.I))) : Tendsto (φ ∘ a) atTop (𝓝 (Complex.I)) := by
  apply Tendsto_comp ha hφ

/-
`filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intro a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing `filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.
-/

example [TopologicalSpace α] {x : α} {p p' q q' : α → Prop}
    (hT : {x | p x} ∈ 𝓝 x)
    (hT' : {x | p' x} ∈ 𝓝 x)
    (hS : {x | q x} ∈ 𝓝 x)
    (hS' : {x | q' x} ∈ 𝓝 x) :
    {x | p x ∧ q x ∨ p' x ∧ q' x} ∈ 𝓝 x := by
  filter_upwards [hT, hT', hS, hS'] with a ha ha' hb hb' using (by tauto)

end Filter

/-!
## Lp-spaces
-/



section Lp

open MeasureTheory ENNReal Set

/-! The Dirac (outer) meaesure at `π ∈ ℝ`. -/
def μD : OuterMeasure ℝ where
  measureOf := fun S ↦ S.indicator (fun _ ↦ (1 : ℝ≥0∞)) Real.pi
  empty := by simp
  mono {S T} hST := by
    apply Set.indicator_le_indicator_of_subset hST (by simp only [zero_le])
  iUnion_nat s _ := by
    calc
    indicator (⋃ n, s n) 1 Real.pi = ⨆ n, indicator (s n) 1 Real.pi :=
      indicator_iUnion_apply (M := ℝ≥0∞) rfl _ _ _
    _ ≤ ∑' n, indicator (s n) 1 Real.pi := iSup_le fun _ ↦ ENNReal.le_tsum _

def μL : Measure ℝ := by volume_tac

def LebesgueFilter := ae μL
def DiracFilter := ae μD

example : {x : ℝ | x < 0} =ᵐ[μD] (∅ : Set ℝ) := by
  rw [μD, ae_eq_empty, ← OuterMeasure.measureOf_eq_coe]
  simp only [Set.indicator_apply_eq_zero, Set.mem_setOf_eq, one_ne_zero,
    imp_false, not_lt]
  positivity

example (f g h : ℝ → ℝ) (h1 : f =ᵐ[μL] g) (h2 : g =ᵐ[μL] h) : f =ᵐ[μL] h := by
  have H2 := @Filter.inter_mem (f := ae μL) (s := {x | f x = g x}) (t := {x | g x = h x}) _ ?_ ?_
  simp only [Set.inter_def, Set.mem_setOf_eq] at H2
  have H1 := @Filter.mem_of_superset (f := ae μL) (x := {x | f x = g x ∧ g x = h x})
    (y := {x | f x = h x}) _ H2
  apply H1
  simp+contextual
  apply h1
  apply h2

example (f g h : ℝ → ℝ) (h1 : f =ᵐ[μL] g) (h2 : g =ᵐ[μL] h) : f =ᵐ[μL] h := by
-- We need to prove that `∀ᶠ x, f x = h x`, namely `{x | f x = h x} ∈ ae (μL)`, namely
-- `μL {x | f x ≠ h x} = 0`.
  filter_upwards [h1, h2]
  intro a ha1 ha2
  rw [ha1, ha2]


example (f g h : ℝ → ℝ) (h1 : f =ᵐ[μL] g) (h2 : g =ᵐ[μL] h) : f =ᵐ[μL] h := by
  filter_upwards [h1, h2]
  simp +contextual

end Lp

/-!
## ℓp-spaces
-/



section ℓp

open Memℓp ENNReal

variable (p : ℝ≥0∞)
variable (ι : Type*) (E : ι → Type*) [(i : ι) → NormedAddCommGroup (E i)]
variable (v : Π (i : ι), E i)

#check PreLp (α := ι) E
#check Memℓp v p
#check lp E p

def ONE : PreLp (fun n : ℕ ↦ ℝ) := (fun _ : ℕ ↦ 1)

def GEO : PreLp (fun n : ℕ ↦ ℝ) := (fun n : ℕ ↦ (1 / n))

example : Memℓp ONE ∞ := by
  apply memℓp_infty
  simp only [ONE, Set.range_const, bddAbove_singleton]

lemma GEO_mem_ℓ2 : Memℓp GEO 2 := by
  apply memℓp_gen
  simp only [GEO, one_div, norm_inv, RCLike.norm_natCast, toReal_ofNat, Real.rpow_ofNat, inv_pow,
    Real.summable_nat_pow_inv, Nat.one_lt_ofNat]

def GEO' : lp (fun _ : ℕ ↦ ℝ) 2 := ⟨GEO, GEO_mem_ℓ2⟩

example : Memℓp GEO 2025 := by
  apply of_exponent_ge GEO_mem_ℓ2
  norm_num

end ℓp

end ItaLean

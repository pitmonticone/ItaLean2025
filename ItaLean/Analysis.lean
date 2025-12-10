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

lemma mono (f : α → β) {F G : Filter α} (h : F ≤ G) : F.map f ≤ G.map f := by sorry


/-- The function `f` tends to `G` along `F`. -/
def Tendsto (f : α → β) (F : Filter α) (G : Filter β) := F.map f ≤ G

lemma Tendsto_comp {s : α → β} {t : β → γ} {F : Filter α} {G : Filter β} {H : Filter γ}
    (hs : Tendsto s F G) (ht : Tendsto t G H) : Tendsto (t ∘ s) F H := by sorry


example (f g : ℝ → ℝ) (hf : Tendsto f (𝓝 0) (𝓝 Real.pi))
    (hg : Tendsto g (𝓝 Real.pi) atTop) : Tendsto (g ∘ f) (𝓝 0) atTop := by sorry

example (a : ℕ → ℝ) (φ : ℝ → ℂ) (ha : Tendsto a atTop (𝓝 (-1)))
    (hφ : Tendsto φ (𝓝 (-1)) (𝓝 (Complex.I))) : Tendsto (φ ∘ a) atTop (𝓝 (Complex.I)) := by sorry

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
    {x | p x ∧ q x ∨ p' x ∧ q' x} ∈ 𝓝 x := by sorry


end Filter

/-!
## Lp-spaces
-/



section Lp

open MeasureTheory ENNReal Set

/-! The Dirac (outer) meaesure at `π ∈ ℝ`. -/
def μD : OuterMeasure ℝ where
  measureOf := by sorry
  empty := by sorry
  mono {S T} hST := by sorry
  iUnion_nat := by sorry

def μL : Measure ℝ := by volume_tac

def LebesgueFilter := ae μL
def DiracFilter := ae μD
#check DiracFilter

example : {x : ℝ | x < 0} =ᵐ[μD] (∅ : Set ℝ) := by sorry

example (f g h : ℝ → ℝ) (h1 : f =ᵐ[μL] g) (h2 : g =ᵐ[μL] h) : f =ᵐ[μL] h := by sorry


example (f g h : ℝ → ℝ) (h1 : f =ᵐ[μL] g) (h2 : g =ᵐ[μL] h) : f =ᵐ[μL] h := by sorry


example (f g h : ℝ → ℝ) (h1 : f =ᵐ[μL] g) (h2 : g =ᵐ[μL] h) : f =ᵐ[μL] h := by sorry

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

example : Memℓp ONE ∞ := by sorry

lemma GEO_mem_ℓ2 : Memℓp GEO 2 := by sorry

def GEO' : lp (fun _ : ℕ ↦ ℝ) 2 := ⟨GEO, GEO_mem_ℓ2⟩

example : Memℓp GEO 2025 := by sorry


end ℓp

end ItaLean

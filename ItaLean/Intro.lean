import Mathlib

open Real




















/-!
# Reading and Writing Lean in practice

A practical introduction to formalising mathematics in Lean for the working mathematician.
-/























/-!
# Reading and Writing Lean in practice

A practical introduction to formalising mathematics in Lean for the working mathematician.
This talk is *not* for the experts in the room (sorry!)

We'll go through:
* Reading statements
* Understanding proofs
* Writing definitions and statements
-/







/-!
Acknowledgements: Adapted from work of Jeremy Avigad, Kevin Buzzard, Riccardo Brasca, Patrick Massot


# Reading statements

## Expressions and terms

Lean uses types instead of sets, as its foundational way of saying a "collection of stuff".
For example, the real numbers are a type in Lean, a group `G` is a type `G` equipped with a
multiplication and satisfying some axioms, and so on.
-/













/- Every expression has a type, and `#check` can tell you the type -/
#check 2
#check 17 + 4
#check π
#check rexp 1
-- (If you get the Error Lens extension in VSCode, these show up nicely)

/-
You can read these as saying "2 has type ℕ".
Note the `:` relation is definitely not symmetric.
-/




















/- Types are expressions too! -/
#check ℕ
#check ℝ


































/- We can also make our own expressions, and give them names. -/
def myFavouriteNumber : ℕ := 7





























/- For any expression in Lean, I can use `sorry` as a placeholder to mean "I'll fill this in
later". Any definition or proof that uses `sorry` will give a warning. Let's fill this one in now
with your favourite number! -/
def yourFavouriteNumber : ℕ := 42


#check myFavouriteNumber
#check yourFavouriteNumber
























/- What about theorems? -/

-- The type `Prop` contains `Prop`ositions...
-- They could be true:
#check 2 + 2 = 4
#check rexp 1 < π
-- or false:
#check 2 + 2 = 5
-- or open.
#check Irrational (rexp 1 + π)
-- I can use any definition that was made *earlier* in the file, or imported
#check myFavouriteNumber = 7
-- This one was open, but now it's not!
#check myFavouriteNumber = yourFavouriteNumber


























/-
Here are some more propositions, this time with names.
They're a bit more involved than our earlier examples, but Lean's syntax is designed to look
very familiar compared to the usual practice of mathematics.
-/

/- The first one is easy to see is true... -/
def MyVeryEasyProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p
/- ...the second is a little trickier, but not hard to show it's false... -/
def MyEasyProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)
/- ...and the last one is hopefully recognisable as an open problem! -/
def MyDifficultProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)






















/-
*KEY!* If `p : Prop`, an expression of type `p` is a proof of `p`.

Thus, for example, an expression `hp` of type `2 + 2 = 4` (that is, `hp : 2 + 2 = 4`) corresponds to
a proof that `2 + 2 = 4`.
-/




























/-
The syntax to make these expressions is just like we saw before, except with `theorem`
rather than `def`.
-/
theorem two_plus_two_equals_four : 2 + 2 = 4 := by rfl






/-
The keyword `theorem` might feel pretentious for a basic claim like this, and so `lemma` works
too:
-/
lemma two_plus_two_equals_four_again : 2 + 2 = 4 := by rfl

/-
The `rfl` here refers to reflexivity of equality, and Lean here is checking that both sides
are actually the same, so this is true by reflexivity.
-/









/-- Here's another proof, this time slightly less trivial. We'll see the meaning of `simp` in more
detail later. -/
theorem two_plus_two_not_equals_five : 2 + 2 ≠ 5 := by simp













/-
Recall that Lean checked that `3` was indeed a natural number, and so `3 : ℕ`.
Similarly, Lean is checking (at each point, in real time) that the
proof (the stuff after the `:= by`) does indeed have its type as what it
should be (the stuff before the `:=`).
In other words, Lean is checking that the proof we provide makes sense in proving what we claimed
to be proving.

In this way, Lean is verifying that our proofs are correct!



We'll come back to proofs in the next section.
-/
























/-
We can also use `sorry` for proofs, for example for the Erdős-Straus conjecture, which
is an open problem in number theory.
Just like before, this gives me a yellow warning, because I've used `sorry` here instead of
writing the proof.
-/
theorem erdos_straus :
    ∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 4 * x * y * z = n * (x * y + x * z + y * z) :=
  sorry






















/-
Our statements so far have been fairly basic, so let's look at some more involved ones.
-/
theorem cosine_addition_rule (x y : ℝ) : cos (x + y) = cos x * cos y - sin x * sin y := by
  exact Real.cos_add x y

theorem f_riesz_theorem (𝕜 : Type) [NontriviallyNormedField 𝕜] (E : Type) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace 𝕜] (r : ℝ) (hr₀ : 0 < r) (c : E)
    (h : IsCompact (Metric.closedBall c r)) :
    FiniteDimensional 𝕜 E := by
  exact FiniteDimensional.of_isCompact_closedBall 𝕜 hr₀ h






















/-
And here's an example of an inductive definition, in which we define later cases in terms of
earlier cases.
-/
def myFactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * myFactorial n























/-!
# Understanding proofs

Now the real question is: now that we know certain expressions correspond to proofs, how can
we make these proofs?
And if we're given a proof to read, let's learn to understand what it's actually doing.
-/




/-!
## Tactic proofs

The most common way to write proofs is using *tactics*.
(This isn't the only way, though!)
Let's look at an example.
-/




/-- A sequence `u` of real numbers converges to `l` if `∀ ε > 0, ∃ N, ∀ n ≥ N, |u_n - l| ≤ ε`.
This condition will be spelled `seq_limit u l`. -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε




/- In the above definition, note that the `n`-th term of the sequence `u` is denoted
simply by `u n` not u(n). -/

/-- A function `f : ℝ → ℝ` is continuous at `x₀` if
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ ⇒ |f(x) - f(x₀)| ≤ ε`.
This condition will be spelled `continuous_at f x₀`. -/
def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε



/-- Now we claim that if `f` is continuous at `x₀` then it is sequentially continuous
at `x₀`: for any sequence `u` converging to `x₀`, the sequence `f ∘ u` converges
to `f x₀`.
Every thing on the next line describes the objects and assumptions, each with its name.
The following line is the claim we need to prove. -/
example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
    seq_limit (f ∘ u) (f x₀) := by -- This `by` keyword marks the beginning of the proof
  -- Watch the panel to the right.
  -- To the right of the blue `⊢` symbol is what we are trying to prove. Above this
  -- is our list of variables and hypotheses. As you read the proof, move your cursor from
  -- line to line (for example with the down-arrow button) and watch the panel change.

  -- Our goal is to prove that, for any positive `ε`, there exists a natural
  -- number `N` such that, for any natural number `n` at least `N`,
  --  `|f(u_n) - f(x₀)|` is at most `ε`.
  unfold seq_limit
  -- Fix a positive number `ε`.
  intros ε hε
  -- By assumption on `f` applied to this positive `ε`, we get a positive `δ`
  -- such that, for all real numbers `x`, if `|x - x₀| ≤ δ` then `|f(x) - f(x₀)| ≤ ε` (1).
  obtain ⟨δ, δ_pos, Hf⟩ : ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε := hf ε hε
  -- The assumption on `u` applied to this `δ` gives a natural number `N` such that
  -- for every natural number `n`, if `n ≥ N` then `|u_n - x₀| ≤ δ`   (2).
  obtain ⟨N, Hu⟩ : ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ := hu δ δ_pos
  -- Let's prove `N` is suitable.
  use N
  -- Fix `n` which is at least `N`. Let's prove `|f(u_n) - f(x₀)| ≤ ε`.
  intros n hn
  -- Thanks to (1) applied to `u_n`, it suffices to prove that `|u_n - x₀| ≤ δ`.
  apply Hf
  -- This follows from property (2) and our assumption on `n`.
  apply Hu n hn
  -- This finishes the proof!










/-
In this way, tactics allow us to build up proofs step by step, while keeping track of what
we've got so far and what we still need to prove.


This cheatsheet shows virtually all of the most commonly used tactics
https://leanprover-community.github.io/papers/lean-tactics.pdf
I'll go through a few examples now, but not all of them!

I'll informally group tactics into a few categories, based on their approximate complexity.
-/








/-
## Level 1 tactics

Here's a simple proof using some of the most basic tactics.
For simple logic goals like this, look at the table at the top of
https://leanprover-community.github.io/papers/lean-tactics.pdf

* intro
* specialize
* constructor
* obtain
* use
* left/right
* rfl
* trivial
* contradiction
* by_contra
* exact

These tactics allow us to work with the basic logical connectives.
-/
example {p q : Prop} : p ∧ q → p ∨ q := by
  intro h
  obtain ⟨h1, h2⟩ := h
  left
  exact h1





/-
Intermediate steps can be expressed using `have`, or `suffices`.
-/
example {p q r : Prop} (h1 : p → q) (h2 : q → r) (hp : p) : r := by
  have hq : q := by
    apply h1
    exact hp
  apply h2
  exact hq

example {p q r : Prop} (h1 : p → q) (h2 : q → r) (hp : p) : r := by
  suffices hq : q by
    apply h2
    exact hq
  apply h1
  exact hp





/-
The `rw` tactic (short for "rewrite") is also somewhat straightforward: it lets us rewrite along
equivalent propositions.
-/
example {p q r : Prop} (h1 : p ↔ q) (h2 : q ∨ r) : p ∨ r := by
  rw [h1]
  exact h2











/-
We can also use `rw` to rewrite equalities.
(In fact, this is the more common case, and the one powering the previous!)
-/
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]














/-
We can chain rewrites, although this gets tedious...
-/
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul, ← add_assoc, add_assoc (a * a), mul_comm b a, ← two_mul]









/-!
# Level 2 tactics: automation
The tactics we've seen so far have been very manual: they do tiny steps, and we have to be very
specific about what we want to do.

The tactics in this section are more powerful, and can save quite a bit of effort.
These tactics however, are limited in scope, but this means they're fast and reliable.
-/
















/-
Here's the `ring` tactic:
"Tactic for evaluating expressions in commutative (semi)rings, allowing for variables in the
exponent."

This tactic will finish the proof if the *target* is an equality of ring expressions that holds in
an arbitrary ring (the free ring).
Equivalently, it will prove the goal if and only if the target is provable from just the ring
axioms.
It can't use any hypotheses, and it can't prove inequalities.
It can't use any specific properties of the particular ring.
-/
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring














/-!
The `simp` tactic is Lean's simplifier.
A bunch of lemmas throughout mathlib are tagged `@[simp]`, meaning they're "simplification" lemmas.
When `simp` is given a goal to try to prove, it will look through all these lemmas `LHS = RHS` and
try to find instances of `LHS` in the goal, replacing them with `RHS`.
It keeps doing this until it can't simplify any more, and then checks if the goal is proved.

Here's an example:
-/
example (n : ℕ) : Fintype.card (Fin n) = n := by simp

/-
You can find out which lemmas `simp` used by changing `simp` to `simp?`, which gives a code action
telling you which lemmas `simp` actually used, and produces a call to `simp only` instead.
This is a restricted version of `simp` which simplifies in the same way, but *only* uses the
lemmas listed.
-/
example (n : ℕ) : Fintype.card (Fin n) = n := by simp?

example (n : ℕ) : 0 * Fintype.card (Fin n) = 0 := by simp?












/-!
The `fun_prop` tactic is a tactic for proving propositions about functions, like continuity.
-/
example : Differentiable ℝ (fun x ↦ x * sin x) := by fun_prop
example : Measurable (fun x ↦ x + 1) := by fun_prop




/-!
The `positivity` tactic is a tactic for proving things of the form `0 <`, `0 ≤` or `≠ 0`.
-/
example : 0 < 1 := by positivity
example (x : ℝ) (hx : 0 < x) : 0 < sinh x := by positivity
example (x y : ℝ) (hx : 0 < y) : 0 < x ^ 2 + y ^ 2 := by positivity




/-
The `linear_combination` tactic is a tactic for proving linear (in)equalities, by combining existing
hypotheses linearly.
-/
example (x y : ℝ) (h : 2 * x + 3 * y = 5) (h' : 4 * x - y = 1) : 10 * x + y = 7 := by
  linear_combination h + 2 * h'




/-!
These tactics are often useful to finish a proof once the main idea is done, but in combination
can be surprisingly powerful.
-/
example (a b : ℝ) : a * b ≤ ((a + b) / 2) ^ 2 := by
  have : 0 ≤ (a - b) ^ 2 := by positivity
  linear_combination this / 4


/-
For some of these examples, other tactics could work too! Sometimes there's a tradeoff between
speed and power, and other times using a less powerful but more precise tactic is more readable and
maintainable.
-/
example (x y : ℝ) (h : 2 * x + 3 * y = 5) (h' : 4 * x - y = 1) : 10 * x + y = 7 := by linarith
example (a b : ℝ) : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
example (x y : ℝ) (h : 2 * x + 3 * y = 5) (h' : 4 * x - y = 1) : 10 * x + y = 7 := by grobner
example (x y z : ℕ) (h : 5 * x + 48 * y + 49 * z = 92) : False := by cutsat
  -- deprecated, new version is `lia`!










/-!
## Level 3 tactics: automatic search

The `aesop` tactic will do search in "tactic space", trying to find sequences of tactics like
`intro`, `simp`, `ext` to prove the goal.
This is particularly helpful in category theory!


The `grind` tactic does search as if on a whiteboard, for example can chain sequences of equalities
together, even if they're not all in the same direction.
-/
example {f : ℝ → ℝ} {x : ℝ} (H1 : f (f (f x)) = x) (H2 : f (f (f (f (f x)))) = x) :
    f x = x := by grind
/-
But `grind` can do more than just chaining equalities, in fact `grobner` and `cutsat` above are
both "just" special cases of `grind`!
-/








/-
Both `grind` and `aesop` can struggle to *fill in* existential statements.
What should I pick as `N`? How should I construct the object I need?
-/














/-
Overall, proofs are constructed by sequences of tactics.
Tactics can very quite heavily in scope, power, readability and speed.

Make sure to keep https://leanprover-community.github.io/papers/lean-tactics.pdf open when you're
starting off!

An AI system designed to use Lean will find tactic proofs, using tactics from each of the three
categories above.
-/





























/-!
# Writing definitions and statements

Writing good definitions and statements has a very different challenge to writing proofs.
For proofs, Lean will tell you if your step is valid. The infoview helps you figure out if you've
taken a *useful* step or not.
On the other hand, for definitions and statements, Lean can't help you as much: it can only check if
your definition or statement follows its grammar rules, but not if it's a meaningful or correct
definition.
On top of this, the design decisions going into a definition vary quite heavily depending on the
area of mathematics you're working in.

So instead of trying to cover everything, I'll give a few common ways in which definitions or
statements can be mis-written.
This is essentially the problem of mis-formalisation (which every AI Lean company you've heard of
has had to deal with at some point!)

## Trust

Why are good definitions so important?
Useful and idiomatic definitions are valuable when building mathlib: writing good abstractions can
make the process of formalisation smoother.
But what's even more important is correct definitions and statements.

Lean will valiantly and patiently check that your proof is a valid proof of your statement.
But at no point will Lean attempt to check that your statement makes any sense!
In informal mathematics, to check correctness of a paper, we need to understand the definitions and
the proofs. With formal mathematics, we no longer need to check the proofs: Lean does that for us.

How much can we trust Lean? Lean has a small C++ kernel, and proofs will be checked relative to
that kernel. Lean additionally has three "usual" axioms, very roughly approximately corresponding to
the axioms of ZFC.
(This is a lie in a couple of ways, but I won't go into that: see the Masters' thesis of Mario
Carneiro for more details.)
If your proof uses only these three axioms, all that you need to trust is the definition, statement
and kernel.
In addition, independent, external checkers can also verify correctness.
-/

lemma test1 : Set.Infinite {n | Nat.Prime n} := by
  exact Nat.infinite_setOf_prime

#print axioms test1

/-
If your proof uses the `sorryAx` axiom, it contains a `sorry` somewhere: your proof isn't done!
-/

lemma test2 : 1 = 2 := by
  sorry

#print axioms test2

/-
If your proof uses `Lean.ofReduceBool` or `Lean.trustCompiler`, then the trusted code base expands
further, becomes open and unbounded, external checkers can no longer be used. But your proofs can
be easier to write, and faster to check.
-/
lemma test : 1 = 1 := by decide +native
#print axioms test

/-
## Junk values

Lean and Mathlib use so-called "junk" values to make definitions total. This is an intentional
design choice, and in practice turns out to be incredibly convenient.
For instance, `x / y` is something I can write down without needing to prove that it makes sense
(`y` is nonzero).
And `x / 0` is defined to be `0`.

Imagine expressing `N ^ 2 / (log N) ^ (1 - (1 + log log 2) / log 2 + o(1))` if I had to additionally
prove that `N` is sufficiently large that the denominator is nonzero in order to just write down
the statement!

The key drawback, however, is that it's slightly easier to write down sensible-looking but
incorrect or invalid statements.
-/

-- This is false!
example : 0 < 2 / 3 := by sorry

-- We can prove its negation
example : ¬ (0 < 2 / 3) := by simp

example : ¬ (2 - 3 < 0) := by simp

example : Real.log (-1) = 0 := by simp


/-
Real examples!

Here's an example from my own work.
-/
noncomputable def upper_density (A : Set ℕ) : ℝ := sorry



/-
This was an open problem of Erdős and Graham, and the solution of an easier version of it was a 2003
paper in the Annals of Mathematics.
Thomas Bloom proved this, then he and I formalised it.

This was the first Erdős problem solution formalised in Lean!
But I could have cheated!
-/
theorem bloom (A : Set ℕ) (hA : 0 < upper_density A) :
    ∃ B : Finset ℕ, (B : Set ℕ) ⊆ A ∧ ∑ i ∈ B, (1 / i : ℚ) = 1 := by
  sorry









/-!
Lean is a super convenient, practical language for expressing mathematics.
We write proofs using tactics: https://leanprover-community.github.io/papers/lean-tactics.pdf
But make sure your statements are correct!
-/

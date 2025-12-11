import ItaLean.Damiano.ShadyAuxLemmas

/-
I was going to give a metaprogramming talk, but then I found a proof of Fermat's Last Theorem,
so I am going to talk about that instead!

Because the proof does not fit in this file, I added a `fermat` tactic in a previous file.
-/

theorem FLT {a b c n : Nat} (abc : a * b * c ≠ 0) (n3 : 3 ≤ n) :
    a ^ n + b ^ n ≠ c ^ n := by
  fermat

#print axioms FLT

/-
*Disclaimer*.
The proof above contains a `sorry`-like axiom.
I am simply pulling a game of smoke and mirrors and deflecting
the audience attention from what is really going on.

In particular, there is no type-checking or soundness issue: `Ctrl-Click`ing on `FLTAuxLemma` immediately shows that it is an *axiom* and not a lemma!
-/
#print FLT

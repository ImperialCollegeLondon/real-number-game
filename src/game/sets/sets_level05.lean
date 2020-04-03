import tactic
variable α : Type

/-
In this level you continue working with sets, while learning some useful
proof techniques. 
This level asks you to prove that the empty set is included in any set.
To do that, we'll follow the advice of P. Halmos in "Naive Set Theory".
That is, to prove anything about the empty set, think by contradiction.

When starting this level, the goal (what you need to prove) is:
∀ (A : set α), ∅ ⊆ A
To make progress, you'll need to look at a specific set $A$. In Lean, this is
accomplished by introducing an instance of $A$ with the "intro" tactic. 
So type "intro A," after the "begin". Remember the comma, press "Enter" and see 
how the goal changes. Now you have a set $A$ to work with, if needed.

Remember now the definition of set inclusion. The goal 
∅ ⊆ A
is the same as 
∀ x ∈ ∅, x ∈ A
and because of this definitional equality you can just switch in between the two.
To experience that, type "change ∀ x ∈ ∅, x ∈ A," on the line after "intro A,". Then
again press "Enter" and notice how the goal changes. Lean will only allow you to do this if 
what you type after "change" is exactly the same, in a very precise way, with the current
goal.

Time to switch to the meat of the proof. We'll use the "by_contradiction" tactic; 
type "by_contradiction hn," to introduce the hypothesis "hn" which negates the goal and
change the goal to "false".
 
Next, it is helpful to change this into a statement that there exists a member of
the empty set which does not belong to $A$. This can be accomplished by
"push_neg at hn,". You sure can bring this home from here by using "cases".

-/
local attribute [instance] classical.prop_decidable
theorem empty_set_included : ∀ A : set α, ∅ ⊆ A :=
begin
    intro A, 
    change ∀ x ∈ ∅, x ∈ A,
    by_contradiction hn,
    push_neg at hn,
    cases hn with x h1,
    cases h1 with hf ha,
    exact hf, done
end
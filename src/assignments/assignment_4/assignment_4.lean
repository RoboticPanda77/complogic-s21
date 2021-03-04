
def list_map {α β : Type} : (α → β) → (list α) → list β 
| f list.nil := list.nil
| f (h::t) := (f h)::(list_map f t)

/-
1. Write a polymorphic function, someSatisfies, 
that takes a a predicate function, p, of type 
α → bool, and list of values of type α (a type
parameter), and and that returns true (tt) if 
and only if there is some value, v, in the list, 
for which (p v) is true (tt). Your implementation
must use list_map to convert the given list of α 
values to a list of bool values, which it must
then pass to a helper function, the job of which
is to return true (tt) if and only there is some
tt value in the list.
-/

def someSatisfiesHelper : list bool → bool
| list.nil := ff
| (h::t) := if h
            then tt
            else someSatisfiesHelper t

def someSatisfies {α : Type} : (α → bool) → list α → bool 
| p l := someSatisfiesHelper (list_map p l)

/-
2.  Write a polymorphic function, allSatisfy, 
that takes a predicate function, p, of type 
α → bool, and list of values of type α (a type
parameter), and and that returns true (tt) if 
and only if for every value, v, in the list, 
(p v) is true (tt). Your implementation must 
use list_map to convert the given list of α 
values to a list of bool values, which it must
then pass to a helper function, the job of which
is to return true (tt) if and only every value
in the list is tt. 
-/

def allSatisfyHelper : list bool → bool
| list.nil := tt
| (h::t) := if h = ff
            then ff
            else allSatisfyHelper t

def allSatisfy {α : Type} : (α → bool) → list α → bool 
| p l := allSatisfyHelper (list_map p l)

/-
3. Write a function called simple_fold_list.
It has a type parameter, α, and takes (1) a
binary function, f, of type α → α → α, (2) a 
single value, i, of type α, as a list, l, of
type list α The purpose of simple_fold_list 
is to "reduce" a list to a single value by
(1) returning i for the empty list, otherwise
(2) returning the result of applying f to the
head of the list and the reduction of the rest
of the list. 

Here are two examples:

simple_fold_list nat.add 0 [1,2,3,4,5] = 15
simple_fold_list nat.mul 1 [1,2,3,4,5] = 120
-/

def simple_fold_list {α : Type} : (α → α → α) → α → list α → α
| f i list.nil := i
| f i (h::t) := f h (simple_fold_list f i t)

/-
4. Write an application of simple_fold_list to
reduce a list of strings to a single string in
which all the individual lists are appended to
each other. You can use ++ (or string.append) to
append strings without writing your own function
to do so. 

For example, reduce ["Hello", " ", "Lean!"] to
"Hello, Lean!"
-/

#eval simple_fold_list string.append "" ["Hello", ", ", "Lean!"]

/-
5. Re-implement here your helper functions from
questions 1 and 2 using simple_fold_list.
-/

def someSatisfiesHelper' (l : list bool) : bool :=
simple_fold_list bor ff l

def allSatisfyHelper' (l : list bool) : bool :=
simple_fold_list band tt l

/-
6. This question asks you to understand how to
write inductive families in a slightly different
way than we've seen. Here's the definition of an
inductive family, ev, indexed by natural numbers.
Read the definition. We explain it further below.
-/

inductive ev : ℕ → Type
| ev_base : ev 0
| ev_ind  {n : nat} (evn : ev n) : ev (n + 2)

open ev


/-
The first line of this definition explains that
ev is a family of types indexed by values of type
nat. In other words, for every nat, n, there is
a corresponding type, ev n. In particular, there
are types, ev 0, ev 1, ev 2, ev 3, etc.

The next two lines, the constructors, explain how
values of all of these types can be constructed.

The first constructor, ev_base, is declared to 
be a term (value) of type ev 0. You can think
of this term as being our version of "evidence"
that "zero is even".

The second constructor takes two arguments. The
first implcit argument is a natural number, n.
The second, evn, must be a term of type (ev n),
*for that particular n* (dependent typing here).
Finally, focus on this, a term (ev_ind n evn) is
of type (ev (n+2)). You can think of such a term
as being our form of evidence that n+2 is even. 
-/

/-
6A. Complete the following definitions by filling
in the placeholders with terms of the indicated
dependent types. Use the available constructors
to create these values. (Remember that the first
argument to ev_ind is impliict, and not that it
can be inferred from the second argument.)
-/

def ev0 : ev 0 := ev_base
def ev2 : ev 2 := ev_ind ev_base
def ev4 : ev 4 := ev_ind (ev_ind ev_base)
def ev6 : ev 6 := ev_ind (ev_ind (ev_ind ev_base))
def ev8 : ev 8 := ev_ind (ev_ind (ev_ind (ev_ind ev_base)))
def ev10 : ev 10 := ev_ind (ev_ind (ev_ind (ev_ind (ev_ind ev_base)))))

/-
6B. You should have been able to give values for 
each of the preceding six types ev 0, ..., ev 10.
What single word can you use to indate that each
of these types has at least one value?
-/

-- inhabited

/-
6C. Try to give values for each of the types in
the following definitions. Explain as clearly and
in as few words as you can why you won't be able
to do this, and state the word that best describes
each of these types, in relation to the fact that
these types have no values.
-/

-- None of these ev functions' corresponding natural
-- is even, so the definitions cannot be completed.

def ev1 : ev 1 := _
def ev3 : ev 3 := _
def ev5 : ev 5 := _

-- uninhabited


/-
6D. Define an inductive family, odd n, indexed by
natural numbers, such that the type for every odd
number has at least one value, and the types for
even numbers have no values. Then show that you 
can complete the preceding three definitions if you
replace ev by odd.
-/

<<<<<<< HEAD:assignments/assignment_4/assignment_4.lean
inductive od : ℕ → Type
| od_base : od 1
| od_ind  {n : nat} (odn : od n) : od (n + 2)

open od

def od1 : od 1 := od_base
def od3 : od 3 := od_ind od_base
def od5 : od 5 := od_ind (od_ind od_base)
=======
inductive empty' : Type
>>>>>>> c1ebd746ee79e34b00a42e053b163c0a805ef5e2:src/assignments/assignment_4/assignment_4.lean

/-
7. As you know, the type, empty, is uninhabited.
That is, it has no values. So what does it tell
us if we can define a function of a type that
"returns a value of type empty?"
  
Show that there is a function, let's call it 
foo, of type ev 1 → empty. Then show there's a 
function, let's call it bar, of type ev 3 → empty. 
Finally, show that there's a function, baz, of 
type ev 5 → empty. (NB: To show that there is a
function of a given type, you must write some
(any) function of that type. What it actually 
does doesn't matter.)

Once you've done the preceding exercises,
write a short answer (in English) to the
question at the beginning of this problem.
-/

<<<<<<< HEAD:assignments/assignment_4/assignment_4.lean
def foo {m : empty} : ev 1 → empty :=
λ (e : ev 1),
  m

def bar {m : empty} : ev 3 → empty :=
λ (e : ev 3),
  m

def baz {m : empty} : ev 5 → empty :=
λ (e : ev 5),
  m

-- This tells us that in functional programming
-- we can even define functions that cannot
-- possibly be called, expanding our toolkit 
-- in case one day false suddenly decides to
-- be true.
=======
def foo : ev 1 → empty :=
λ (e : ev 1), _ -- match ... with ... end
  -- for every possible form of e, return a value of type empty
>>>>>>> c1ebd746ee79e34b00a42e053b163c0a805ef5e2:src/assignments/assignment_4/assignment_4.lean

/- 8. Define evdp to be a sigma (dependent 
pair) type, a value of which has a natural
number, n,  as its first component, and a 
value of type, ev n, as its second. Then 
define evp0, evp2, and evp4 to be values
of this type, whose first elements are,
respectively, 0, 2, and 4.
-/

<<<<<<< HEAD:assignments/assignment_4/assignment_4.lean
def evdp := Σ (n : ℕ), ev n

def evp0 : evdp := ⟨ 0, ev0 ⟩
def evp2 : evdp := ⟨ 2, ev2 ⟩ 
def evp4 : evdp := ⟨ 4, ev4 ⟩ 
=======
-- hint
#check Σ (n : nat), ev n

-- Your answers here
>>>>>>> c1ebd746ee79e34b00a42e053b163c0a805ef5e2:src/assignments/assignment_4/assignment_4.lean

/- 9. Write a function, mkEvp, that takes 
a argument, mn, of type nat, iplicitly, and 
an argument, nEv ot type, ev n, and that 
returns a value of type evdp (from the last
problem). Then briefly answer the question, 
in what sense does mkEvp have a dependent
function type? 
-/

<<<<<<< HEAD:assignments/assignment_4/assignment_4.lean
def mkEvp {n : ℕ} : ev n → evdp
| nEv := ⟨ n, nEv⟩

-- It has a dependent function type in that 
-- any "ev n" type depends on the value of
-- "n" to determine its type, and mkEvp 
-- similarly incorporates "ev n" types
-- into its construction.
=======
-- Your answers here

>>>>>>> c1ebd746ee79e34b00a42e053b163c0a805ef5e2:src/assignments/assignment_4/assignment_4.lean

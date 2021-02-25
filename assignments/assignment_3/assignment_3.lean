/-
HIGHER-ORDER FUNCTION WARMUP
ncm5jv
-/

/-
1. Write a function, double, that takes
a natural number and returns its double.
Write it using the following recursive
definition:
- double 0 = 0
- double (n' + 1) = double n' + 2
-/


def double : ℕ → ℕ
| 0 := 0
| (n' + 1) := (double n') + 2

/-
2. Write a function, map_list_nat, that 
takes as its arguments (1) a list, l, of 
natural numbers, and (2) a function, f, 
from nat to nat, and that returns a new 
list of natural numbers constructed by 
applying f to each element of l. Make f
the first argument and l the second. The
function will work by case analysis and
recursion on l.
-/

def map_list_nat : (ℕ → ℕ) → (list ℕ) → (list ℕ)
| f list.nil := list.nil
| f (h::t) := list.cons (f h) (map_list_nat f t)  

/-
3. Test your map_list_nat function by
applying it to several lists, both empty
and not, passing double as the function
value. Include [], [2], and [1,2,3] in
your set of test inputs and use comments
to document the expected return values.
-/

#eval map_list_nat nat.succ []
#eval map_list_nat nat.succ [2]
#eval map_list_nat nat.succ [1,2,3]
#eval map_list_nat nat.succ [1,1,1]
#eval map_list_nat nat.succ [0]

/-
4. In Lean, repr is an "overloaded"
function. When applied to a value of a
type for which it's defined (we'll see 
later  how that happens) it returns a
string representation of the value. It
is defined for the nat type, and so 
when applied to a nat value it returns
a corresponding string. It's "toString"
for Lean. Here's an example.
-/

#eval repr 5

/-
Write a function map_list_nat_string
that takes a list of nat values and
returns a list of strings in which
each nat in the given list has been
converted to a string using repr.
-/

def map_list_nat_string : list ℕ → list string 
| list.nil := list.nil
| (h::t) := list.cons (repr h) (map_list_nat_string t)
  

/-
5. Write a function, filterZeros,
that takes a list of natural numbers
and returns the same list but with any
and all zero values removed. Given
[0], for example, it should return
[]; given [1,2,0,3,4,0, 0, 5] it 
should return [1,2,3,4,5].
-/

def filterZeros : list ℕ → list ℕ
| list.nil := list.nil
| (h::t) := 
  if h = 0
  then t
  else list.cons h (filterZeros t)


/-
6. Write a function, isEqN, that
takes a natural number, n, and returns
a function that takes a natural number,
m, and returns true (tt) if m = n and
that returns false (ff) otherwise. Be
sure to test your function.
-/

def isEqN : ℕ → (ℕ → bool) :=
λ n,
  λ m,
    n = m

#eval isEqN 5
#eval isEqN 5 6
#eval isEqN 5 5
#check isEqN 5
#check isEqN 5
#check isEqN 5 6
#check isEqN 5 5

/-
7. Write a function filterNs that takes
a function, pred, from nat to bool 
and a list, l, of natural numbers, and
that returns a list like l but with all
the numbers that satisfy the predicate
function removed. Test your function
using isEqN to produce a few predicate
functions (functions that for a given
argument return true or false).
-/

def filterNs : (ℕ → bool) →  list ℕ → list ℕ
| pred list.nil := list.nil
| pred (h::t) := 
  if pred h
  then filterNs pred t
  else list.cons h (filterNs pred t)


/-
8. Write a function, iterate, that 
takes as its arguments (1) a function, 
f, of type nat → nat, and (2) a natural
number, n, and that returns a function 
that takes an argument, (m : nat), and
that returns the result of applying f 
to m n times. For example, if n = 3, it
should return f (f (f m)). The result
of applying f zero times is just m.
Hint: use case analysis on n, and 
recursion. Test your function using 
nat.succ, your double function, and
(nat.add 4) as function arguments. 
-/

def iterate : (ℕ → ℕ) → ℕ → (ℕ → ℕ)
| f 0 := λ m, m
| f (n' + 1) := λ m, f (iterate f (n') m) 

#eval iterate nat.succ 3 5
#eval iterate double 3 5
#eval iterate (nat.add 4) 3 5

/-
9. Write a function, list_add, that takes
a list of natural numbers and returns the
sum of all the numbers in the list.
-/

def list_add : list ℕ → ℕ 
| list.nil := 0
| (h::t) := h + list_add t


/-
10. Write a function, list_mul, that takes
a list of natural numbers and returns the
product of all the numbers in the list.
-/

def list_mul : list ℕ → ℕ 
| list.nil := 1
| (h::t) := h * list_mul t


/-
11. Write a function, list_has_zero, that
takes a list of natural numbers and returns
tt if the list contains any zero values and
that returns false otherwise. Use isEqN in
your solution. Test your solution on both
empty and non-empty lists including lists
that both have and don't have zero values.
-/

def list_has_zero : list ℕ → bool 
| list.nil := ff
| (h::t) := if h = 0
            then tt
            else list_has_zero t

#eval list_has_zero []
#eval list_has_zero [1,0,1]
#eval list_has_zero [0]
#eval list_has_zero [1,1,1]

/-
12. Write a function, compose_nat_nat,
that takes two functions, f : ℕ → ℕ,
and g : ℕ → ℕ, and that returns a
function that takes a nat, n, and that
returns g (f n). Test your function 
using at least nat.succ and double as
argument values.
-/

def compose_nat_nat : (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ) :=
λ f,
  λ g,
    λ n,
      g (f n)
      
#eval compose_nat_nat nat.succ double 4
#eval compose_nat_nat double nat.succ 4
#check compose_nat_nat nat.succ double 4
#check compose_nat_nat nat.succ double 


/-
13. Write a polymorphic map_box function
of type 

Π (α β : Type u), 
  (α → β) → box α → box β  
  
that takes a function, f, of type 
(α → β), and a box, b, containing a 
value of type α and that returns a 
box containing that value transformed
by the application of f.  
-/
universe u

structure box (α : Type u) : Type u :=
(val : α)

def map_box {α β : Type u}
  (f : α → β) : (box α → box β) :=
  λ b, 
    box.mk (f b.val)

/-
14. 
Write a function, map_option, that
takes a function, f, of type α → β
and an option α and that transforms
it into an option β, where none goes
to none, and some (a : α) goes to
some b, where b is a transformed by 
f.
-/

def map_option {α β : Type u} (f : α → β) : (option α) → (option β) :=
λ opa,
  match opa with
  | option.none := option.none
  | option.some (a : α) := option.some (f a)
  end


/-
15. Write three functions, default_nat,
default_bool, and default_list α, each
taking no arguments (other than a type,
argument, α, in the third case), and 
each returning a default value of the
given type: a nat, a bool, and a list.
Don't overthink this: Yes, a function
that takes no arguments is basically 
a constant. You'll need to declare a
universe variable for the list problem.
-/

<<<<<<< HEAD
def default_nat : ℕ := 0
def default_bool : bool := ff
def default_list {α : Type u} : list α := list.nil
=======
-- ANSWER HERE

-- C style
def comp (g f : nat → nat) : nat → nat :=
λ n, g (f n)

-- lambda expressions
def comp' : (nat → nat) → (nat → nat) → (nat → nat) :=
λ g f, 
  λ n, g (f n)

-- by cases
def comp'' : (nat → nat) → (nat → nat) → (nat → nat)
| g f := λ (n : ℕ), g (f n)

def square (n : nat) := n * n
def double (n : nat) := 2 * n

def myFavFunc := comp' square double
#check myFavFunc
#eval myFavFunc 5
-- square (double 5)
-- square 10
-- 100

def comp_nat_string : (nat → bool) → (string → nat) → (string → bool) := 
λ (nb : ℕ → bool),
  λ (sn : string → nat),
    λ (s : string), 
     nb (sn s)

def isStringEmpty := comp_nat_string (λ (n : nat), n=0) string.length
 
#eval isStringEmpty "Hello"
#eval isStringEmpty ""
      
def yeah {α β γ : Type} (g : β → γ) (f : α → β) : (α → γ) :=
λ (a : α), g (f a) 

#reduce (yeah (λ (n : nat), (n=0 : bool)) string.length) ""
#reduce (yeah square double) 5
#reduce (yeah (λ (n : nat), (n=0 : bool)) string.length) ""


/-
Write a function, iterate, that 
takes as its arguments (1) a function, 
f, of type nat → nat, and (2) a natural
number, n, and that returns a function 
that takes an argument, (m : nat), and
that returns the result of applying f 
to m n times.
-/

def iterate : (nat → nat) → nat → (nat → nat) 
| f 0 := λ (m : nat), m
| f (n' + 1) := λ m, _


#eval (iterate double 10) 1

/-
Write a polymorphic map_box function
of type 

Π (α β : Type u), 
  (α → β) → box α → box β  
  
that takes a function, f, of type 
(α → β), and a box, b, containing a 
value of type α and that returns a 
box containing that value transformed
by the application of f.  

-/
universe u
structure box (α : Type u) : Type u :=
mk :: (val : α)

def map_box : Π {α β : Type u}, 
  (α → β) → (box α → box β) 
| _ _ f b := box.mk (f b.val)

def b0 := box.mk 0

def f := nat.succ

def q := map_box f

#reduce q b0
>>>>>>> 936456d6bdecb0cbc9fd1c54ac8980312b282377

namespace hw2

/-
In this assignment, use Lean's version
of basic data types, e.g., nat, prod α 
β, etc. You don't need to import from 
our type library.
-/

/-
1.[25 points] Syntax and semantics 

Formalize the syntax of the following
language, SalmonTrout, as an inductive
data type definition.

The SalmonTrout language (ST for short)
is spoken by workers on a fish factory 
production line. On a conveyor belt in
front of a worker, fish pass by, one by
one. If a fish passing by is a salmon,
the worker shouts "salmon", and if it's
a trout, the worker shouts, "trout". A
machine records the string of shouts,
resulting in an ST expression/sentence.

Such an expression can be empty (and it
will be if no fish have gone by yet), OR
it can be "salmon" followed by a smaller
ST expression (for the fish that've gone
by already), OR it can be trout followed
by a smaller ST expression (similarly).
-/

inductive SalmonTrout : Type
| nofish
| salmon (restoffish : SalmonTrout)
| trout (restoffish : SalmonTrout)

open SalmonTrout

/-
Now assume that the *meaning* of a 
given ST expression, e, is a  pair,
p = prod.mk s t (which in Lean can 
also be written as (s, t)), of type 
prod nat nat (which also can be written 
as nat × nat), where s is the number
of occurrences of "salmon" in e, and 
t is the number of occurrences of 
"trout." 

Implement the semantics of ST as a 
function, fishEval, that takes an
expression e : ST and returns its
meaning as the correct pair. Hint: 
Have your fishEval function call a
recursive fishEvalHelper function 
that takes an ST expression as an 
argument along with an initial (s,t)
pair, with fishEval passing it (0,0)
as an initial value. Remember to 
use the "by cases" syntax, as you 
will want your helper function to 
be recursive.
-/

def fishEvalHelper : SalmonTrout → prod nat nat → prod nat nat 
| SalmonTrout.nofish (prod.mk s t) := (prod.mk s t)
| (SalmonTrout.salmon e) (prod.mk s t) := fishEvalHelper e (s+1,t)
| (SalmonTrout.trout e) (prod.mk s t) := fishEvalHelper e (s,t+1)

def fishEval : SalmonTrout → prod nat nat 
| e := fishEvalHelper e (0,0)

/-
 WRITE SOME TEST CASES

(1) Check that fishEval returns (0,0)
    for the empty expression, 
(2) Check that it returns (3,2) for 
    an expression with three salmon
    and two trout.
-/

def case1 := nofish
def case2 := salmon (salmon nofish)
def case3 := salmon (trout (trout (nofish)))

#eval fishEval case1
#eval fishEval case2
#eval fishEval case3

/-
2. [25 points] polymorphic functions 

Define a polymorpic function, id',
implementing the identity function
for values of *any* type: not only 
for values of any type in Type, but 
for values of any type in any type
universe. Make the type argument to 
your function implicit. You will
need to introduce a universe
variable (by convention, u). Note 
that Lean defines this function
with the name, id. 
-/

universe u

def id' : Π { α : Type u}, α → α :=
λ α, 
    fun a, 
        a 


/-
When you've succeded, the following
tests should succed in returning the
values passed as the arguments: .
-/
#reduce id' 3
#reduce id' nat
#reduce id' Type
#reduce id' (Type 1)


/- 3. [25 points] Partial functions 

This question requires you to read 
about a type we haven't covered yet
and to use it correctly. Before going
forward, please read about the option
type, as described in our type library.
Then continue.

A total function is one that is defined
(has a "return value") for each value
in its "domain of definition" (in type
theory, the domain of definition of a
total function is given by the *type* 
of its argument; a function has to be
defined for *every* value of its argument
type). 

Example: the successor function on 
natural numbers is total: given *any* 
natural number, n, the successor of n
(i.e., the number that is one more 
than n, expressed as (nat.succ n) in 
Lean) is well defined.

By contrast, a strictly partial function
is one that is undefined (has no "return 
value") for at least one element of its
"domain of definition."" 

Here's an example: Consider the partial
function from bool to bool given by the
following set of pairs: { (tt, tt) }. If
the argument is tt, the result is tt, but
the function is undefined in the case 
where the argument value is ff, because
there is no pair with first element ff. 

The function we've described is a partial
version of the usual identity function on
Boolean values. Define a total function in
Lean, pId_bool, using the option type, to
represent this partial function. 
-/

def pId_bool : option bool → bool
| none := ff
| (some v) :=  tt
/-
TEST YOUR FUNCTION
Use #eval or #reduce to show that your
function works as expected for both 
argument values. 
-/

def nothing : option bool := option.none
def something : option bool := option.some tt
#eval pId_bool nothing
#eval pId_bool something

/- 
4. [25 points] Higher-order functions 

Write a function, liftF2Box, polymorphic 
in two types, α and β, that take as its
argument a function, f, of any type 
α to β, and that returns a function of 
type box α → box β, where the returned 
function works by (1) getting the value 
of type α from its box argument, (2) then 
applying f to it, and finally (3) returning 
the result in a new box. Make your function
work in all type universes. We include 
the box definition here so you don't have
to rewrite it.
-/

-- universe u 
structure box (α : Type u) : Type u :=
(val : α)
/- 
def liftF2Box (f : (Type → Type)) : Π (α β : Type), (α → β) → (box α → box β) :=
    
        box.mk (f a.val) -/
        
def liftF2Box (f : Type → Type): Π (α β : Type), (α → β) → ((box α) → (box β)) :=

    λ a,
        box.mk (f a.val)

-- WHEN YOU'VE GOT IT, THIS TEST SHOULD PASS

#reduce (liftF2Box nat.succ) (box.mk 3) 
/- 
Expect {val:=4}. This is Lean notation for a 
structure (here a box) with one field, val, 
with the value, 4.
-/

end hw2
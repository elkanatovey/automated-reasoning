# Automated Reasoning about Software #

This project contains an implementation of a SAT solver, SMT solver for `T_UF`, and an LP Theory Solver. Run 
`solver.py` to use any of the solvers and follow the prompts.

***
#Valid input for the SAT solver:

A  **Propositional Formula** is recursively defined as the following:<br/>
• An **atomic proposition**: a letter in ‘p’. . . ‘z’, optionally followed by a sequence of
digits.<br/>
Examples: ‘p’, ‘y12’, ‘z035’.<br/>
• ‘T’.<br/>
• ‘F’.<br/>
• ‘~φ’, where φ is a valid propositional formula.<br/>
• ‘(φ&ψ)’ where each of φ and ψ is a valid propositional formula.<br/>
• ‘(φ|ψ)’ where each of φ and ψ is a valid propositional formula.<br/>

The SAT solver will accept any formula with the above construction 
(along with a specification as to whether the formula is already in CNF) and return UNSAT, or SAT with a satisfying assignment.<br/>

#Valid input for the SMT solver:

A  **Predicate Formula** in `T_uf` made up of CNF combinations of equalities of terms as follows;

 The following strings are valid **terms** for the SMT solver:<br/>
• A **variable name**: a sequence of alphanumeric characters that begins with a letter
in ‘u’. . . ‘z’.<br/>
Examples: ‘x’, ‘y12’, ‘zLast’.<br/>
• A **constant name**: a sequence of alphanumeric characters that begins with a digit
or with a letter in ‘a’. . . ‘d’; or an underscore (with nothing before or after it).<br/>
Examples: ‘0’, ‘c1’, ‘7x’, ‘ ’.<br/>
• An n-ary **function invocation** of the form ‘f(t1,. . . ,tn)’, where f is a **function
name** denoted by a sequence of alphanumeric characters that begins with a letter
in ‘f’. . . ‘t’, where 1 n ≥ 1, and where each ti
is itself a valid term.<br/>
Examples: ‘plus(x,y)’, ‘s(s(0))’, ‘f(g(x),h(7,y),c)’.<br/>

The following strings are valid **formulas** in our SMT solver:
• An equality of the form ‘t1=t2’, where each of t1 and t2 is a valid terms.<br/>
Examples: ‘0=0’, ‘s(0)=1’, ‘plus(x,y)=plus(y,x)’.<br/>
• A unary negation of the form ‘~φ’, where φ is a valid formula.<br/>
• A binary operation of the form ‘(φ*ψ)’, where * is one of the binary operators
‘|’, ‘&’, or ‘→’,2 and each of φ and ψ is a valid formula.<br/>

#Valid input for the LP solver:

A  **Predicate Formula** in `T_q` (Theory of Rationals) that is made up of combination of equalities.
 The following strings are valid **terms** for the SMT solver:<br/>
• A **variable name**: a sequence of alphanumeric characters that begins with a letter
in ‘u’. . . ‘z’. **DO NOT USE SAVED NAMES** `x0` **OR** `y`<br/>
Examples: ‘x’, ‘y12’, ‘zLast’.<br/>
• A binary **function** of the form ‘f(a,b)’, where f is one of the following - 
 **plus, minus, mult**.<br/>
**mult** - Multiplication of a term by a constant, the constant is always the first argument. <br/> 
**minus** - Deduction of the second argument from the first one. <br/>
Example: the formula  `x - 6` is **minus(x,6)** and the formula `-x + 6` will be written as **plus(minus(0,x),6)**<br/>
**plus** - Addition of 2 terms
Examples: ‘plus(x,z)’, ‘plus(mult(8,x),minus(0,z))’ .<br/>

The following strings are valid **formulas** for the LP solver: <br/>
• An equality of the form ‘t1=t2’, where each of t1 and t2 is a valid terms, will be written as 'S(t1, t2)'.<br/>
Examples: 'S(x, z)' means `x = z`, ‘S(plus(x1, z), minus(x2, 5))’ means `x1 + z = x2 - 5`.<br/>
• Same for the relation '>=' - will be written as 'GS(t1, t2)' .<br/>
• A unary negation of the form ‘~φ’, where φ is a valid formula.<br/>
• A binary operation of the form ‘(φ*ψ)’, where * is one of the binary operators
‘|’, ‘&’, or ‘→’,2 and each of φ and ψ is a valid formula.<br/>

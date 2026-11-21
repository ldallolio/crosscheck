/* http://kti.ms.mff.cuni.cz/~bartak/prolog/booleans.html
 a program to evaluate boolean expression which is similar 
 to evaluation of arithmetic expressions. 
 In the second part, we will work with expression in a symbolic manner 
 and we write a program for transformation of a boolean expression into a conjunctive normal form.
*/

/*  Operator definitions */
:-op(720,fy,non).
:-op(730,yfx,and).
:-op(740,yfx,or).

/* We can also define meta-operations which can be fully transformed into classic operations and, or, non. */
:-op(710,yfx,implies).
:-op(710,yfx,equiv).
:-op(740,yfx,xor).

/* Evaluating
 We have to define procedures for evaluating and, or, not operations in Prolog.
*/

non_d(true,false).
non_d(false,true).

/* Idempotency laws */
and_d(X,X,X).
or_d(X,X,X).

/* The Identity Laws */
and_d(X,false,false).
and_d(X,true,X).
or_d(X,false,X).
or_d(X,true,true).

/* The Commutative Laws */
and_d(X,Y,Z):-and_d(Y,X,Z).
or_d(X,Y,Z):-or_d(Y,X,Z).

/* We should also indicate which values can be used in expressions. */
logic_const(true).
logic_const(false).

/* Now, it is easy to write an evaluator for boolean expressions. */
eval_b(X,X):-logic_const(X).

/* The Involution Law */
eval_b(non non X,R):-eval_b(X,R).

eval_b(X and Y,R):-eval_b(X,XV),eval_b(Y,YV),and_d(XV,YV,R).
eval_b(X or Y,R):-eval_b(X,XV),eval_b(Y,YV),or_d(XV,YV,R).
eval_b(non X,R):-eval_b(X,XV),non_d(XV,R).

/* Evaluation of meta-operations is transformed into evaluation of classic operations in an obvious way. */
eval_b(X implies Y,R):-eval_b(Y or non X, R).
eval_b(X equiv Y,R):-eval_b(X implies Y and Y implies X, R).
eval_b(X xor Y,R):-eval_b((X and non Y) or (Y and non X), R).

/* Normalizing */
/* In this section, we will write a Prolog program for transformation of boolean expressions 
 into conjunctive normal form. Conjunctive normal form is an expression in the following form:
 (a or non b) and c and (b or d or non c).

 Note, that we work with arbitrary atoms in boolean expressions now and these atoms are not interpreted, i.e., we do not know their value (true or false).

 First, we remove meta-expressions, i.e., implies, equiv & xor which are substituted by or, and & non.
*/
ex2basic(X implies Y, R):-ex2basic(Y or non X,R).
ex2basic(X equiv Y,R):-ex2basic(X implies Y and Y implies X, R).
ex2basic(X xor Y,R):-ex2basic((X and non Y) or (Y and non X), R).
ex2basic(X or Y, XB or YB):-ex2basic(X,XB),ex2basic(Y,YB).
ex2basic(X and Y, XB and YB):-ex2basic(X,XB),ex2basic(Y,YB).
ex2basic(non X, non XB):-ex2basic(X,XB).
ex2basic(X,X):-atom(X).

/* Second, we move negation non to atomic formulas. */
non2basic(non (X and Y),XN or YN):-non2basic(non X,XN),non2basic(non Y,YN).
non2basic(non (X or Y),XN and YN):-non2basic(non X,XN),non2basic(non Y,YN).
non2basic(non non X, XB):-non2basic(X,XB).
non2basic(non X,non X):-atom(X).
non2basic(X and Y,XB and YB):-non2basic(X,XB),non2basic(Y,YB).
non2basic(X or Y,XB or YB):-non2basic(X,XB),non2basic(Y,YB).
non2basic(X,X):-atom(X).

/* Finally, we can construct a conjunctive normal form. */
ex2conj(X and Y,XC and YC):-ex2conj(X,XC),ex2conj(Y,YC).
ex2conj(X or Y, R):-ex2conj(X,XC),ex2conj(Y,YC),join_disj(XC,YC,R).
ex2conj(non X,non X).
ex2conj(X,X):-atom(X).
   
join_disj(X and Y,Z,XZ and YZ):-join_disj(X,Z,XZ),join_disj(Y,Z,YZ).
join_disj(X,Y and Z,XY and XZ):-X\=(_ and _),join_disj(X,Y,XY),join_disj(X,Z,XZ).
join_disj(X,Y,X or Y):-X\=(_ and _),Y\=(_ and _).

/* Now, we join above three procedures into compact form 
 which transforms arbitrary expression into its conjuctive normal form. 
 We call this process normalization.
*/
normalize(Ex,Norm):-
   ex2basic(Ex,Bas),
   non2basic(Bas,NonBas),
   ex2conj(NonBas,Norm).
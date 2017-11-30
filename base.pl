/* Prédicats utiles */

:- op(20,xfy,?=).

fonc(X)
:- nonvar(X), functor(X, _, A), A > 0 .

const(X)
:- nonvar(X), functor(X, _, 0).



/* Vérifie si X apparait dans T */

occur_check(X, T)
:- var(X), term_variables(T, Arguments), member(X, Arguments).




/* Définition quelle regle appliquer en fonction de l'équation */

regle(rename_r, X ?= T) 
:- var(X), var(T).

regle(simplify_r, X ?= T) 
:- var(X), const(T).

regle(expand_r, X ?= T) 
:- var(X), fonc(T), \+occur_check(X, T).

regle(check_r, X ?= T) 
:- var(X), X \= T, occur_check(X, T).

regle(orient_r, T ?= X) 
:- var(X), \+var(T).

regle(decompose_r, X ?= T)
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), A1 = A2, N1 = N2.

regle(clash_r, X ?= T) 
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), A1 \= A2, N1 \= N2.

regle(clash_r, X ?= T) 
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), N1 \= N2.

regle(clash_r, X ?= T) 
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), A1 \= A2.



/* règles de transformation */

/* X: variable à renommer, Y: terme qui remplace X, L: liste où remplacer */
rename_p(X, Y, [], Lout).

rename_p(X, Y, Lin, [Z ?= T | Lout])
:- rename_p(X, Y, [Z ?= T | Lin], Lout).


/* Transforme P (couples) en Q (couples) en appliquant R (règle) sur E (équation tête de P) */






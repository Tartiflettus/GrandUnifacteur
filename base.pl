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

regle(X ?= T, rename_r) 
:- var(X), var(T).

regle(X ?= T, simplify_r) 
:- var(X), const(T).

regle(X ?= T, expand_r) 
:- var(X), fonc(T), \+occur_check(X, T).

regle(X ?= T, check_r) 
:- var(X), X \= T, occur_check(X, T).

regle(T ?= X, orient_r) 
:- var(X), \+var(T).

regle(X ?= T, decompose_r)
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), A1 = A2, N1 = N2.

regle(X ?= T, clash_r) 
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), (A1 \= A2 ; N1 \= N2).



/* règles de transformation */

/* X: variable à renommer, Y: terme qui remplace X, L: liste où remplacer */
rename_p(X, Y, [], Lout).

rename_p(X, Y, Lin, [Z ?= T | Lout])
:- rename_p(X, Y, [Z ?= T | Lin], Lout).



/* Transforme P (couples) en Q (couples) en appliquant R (règle) sur E (équation tête de P) */






/* check */


fail
:- check_p(P,S).



/* orient */

orient ([X ?= T | P], S)
:- orient ([T ?= X | P], S).


/* decompose */



/* clash */

fail
:- clash_p(P,S).



/* Essais 03/12/2017 */

/*check */
reduit(check_r, X ?= T, P, [fail | Q])
:- reduit(check_r, E, [X ?= T | P], Q]).


reduit(orient_r, T ?= X, [X ?= T | P], Q)
:- reduit(orient_r, E, [T ?= X | P], Q).



/* unifie*/

unifie([]).

unifie(P)
:- unifie([X ?= T, P]), regle(X ?= T, R), reduit(R, X ?= T, P, Q).
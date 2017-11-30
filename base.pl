/* Prédicats utiles */

fonc(X)
:- functor(X, _, A), A > 0 .

const(X)
:- nonvar(X), functor(X, _, 0).


/* Définition quelle regle appliquer en fonction de l'équation */

regle(rename_r, X ?= T) 
:- var(X), var(T).

regle(simplify_r, X ?= T) 
:- var(X), const(T).

regle(expand_r, X ?= T) 
:- var(X), \+occur_check(X, T).

regle(check_r, X ?= T) 
:- var(X), X \= T, occur_check(X, T).

regle(orient_r, T ?= X) 
:- var(X), \+var(T).

regle(decompose_r, X ?= T)
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), A1 = A2, N1 = N2.

regle(clash_r, X ?= T) 
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), A1 \= A2, N1 \= N2.



/* Vérifie si X apparait dans T */

occur_check(X, T)
:- var(X), term_variables(T, Arguments), member(X, Arguments).


/* Transforme P (couples) en Q (couples) en appliquant R (règle) sur E (équation tête de P) */

reduit(rename_r, X ?= a, [X ?= a, Y ?= f(X)], L).


/* reduit(R, E, P, [E | Q])
<- reduit([ E | P], regle(E, R).*/

reduit(R, E, [], Q). % Condition d'arrêt

reduit(R, E, P, [E | Q])
:- reduit(R, E, [E | P], Q), regle(R, E).






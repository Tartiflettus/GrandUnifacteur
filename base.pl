/* Prédicats utiles */

:- op(20,xfy,?=).

fonc(X)
:- nonvar(X), functor(X, _, A), A > 0 .

const(X)
:- nonvar(X), functor(X, _, 0).



/* Vérifie si X apparait dans T */

occur_check(X, T)
:- var(X), term_variables(T, Arguments), occur_check_list(X, Arguments), !.

occur_check_list(X, [E | List])
:- var(X), same_term(X, E) ; occur_check(X, List).




/* Définition quelle regle appliquer en fonction de l'équation */

regle(X ?= T, rename_r) 
:- var(X), var(T), !.

regle(X ?= T, simplify_r) 
:- var(X), const(T), !.

regle(X ?= T, expand_r) 
:- var(X), fonc(T), \+occur_check(X, T), !.

regle(X ?= T, check_r) 
:- var(X), fonc(T), occur_check(X, T), !.

regle(T ?= X, orient_r) 
:- var(X), \+var(T), !.

regle(X ?= T, decompose_r)
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), A1 = A2, N1 = N2, !.

regle(X ?= T, clash_r) 
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), (A1 \= A2 ; N1 \= N2), !.



/* règles de transformation */

/* X: variable à renommer, Y: terme qui remplace X, L: liste où remplacer */
/*rename_p(X, Y, [], Lout).

rename_p(X, Y, Lin, [Z ?= T | Lout])
:- rename_p(X, Y, [Z ?= T | Lin], Lout).*/



/* Essais 03/12/2017 */

/*check */
reduit(check_r, E, _, bottom)
:- regle(E, check_r).

/*clash*/
reduit(clash_r, E, _, bottom)
:- regle(E, clash_r).


%comment interroger
%reduit(orient_r, t ?= X, P, Q).


/*orient*/
reduit(orient_r, T ?= X, [X ?= T | _], _)
:- regle(T ?= X, orient_r).



/*rename*/
%reduit(rename_r, X ?= T, [X ?= T | P], Q)



/* unifie*/

%unifie([X ?= t, X ?= f(X)]). %question

unifie([]).

unifie([E | P])
:- unifie(P), reduit(_, E, P, Q), Q \= bottom.










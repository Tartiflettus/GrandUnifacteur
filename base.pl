/* Prédicats utiles */

:- op(20,xfy,?=).

fonc(X)
:- nonvar(X), functor(X, _, A), A > 0 .

const(X)
:- nonvar(X), functor(X, _, 0).


% Prédicats d'affichage fournis

% set_echo: ce prédicat active l'affichage par le prédicat echo
set_echo :- assert(echo_on).

% clr_echo: ce prédicat inhibe l'affichage par le prédicat echo
clr_echo :- retractall(echo_on).

% echo(T): si le flag echo_on est positionné, echo(T) affiche le terme T
%          sinon, echo(T) réussit simplement en ne faisant rien.

echo(T) :- echo_on, !, write(T).
echo(_).



/* Vérifie si X apparait dans T */

occur_check(X, T)
:- var(X), term_variables(T, Arguments), occur_check_list(X, Arguments), !.

occur_check_list(X, [E | List])
:- var(X), same_term(X, E) ; occur_check(X, List).




/* Définition quelle regle appliquer en fonction de l'équation */

regle(X ?= T, rename_r) 
:- var(X), var(T), !.

regle(X ?= T, simplify_r) 
:- ((var(X), const(T)) ; (X==T, const(T))), !.

regle(X ?= T, expand_r) 
:- var(X), fonc(T), \+occur_check(X, T), !.

regle(X ?= T, check_r) 
:- var(X), fonc(T), occur_check(X, T), !.

regle(T ?= X, orient_r) 
:- var(X), \+var(T), !.

regle(X ?= T, decompose_r)
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), A1 == A2, N1 =\= N2, !.

regle(X ?= T, clash_r) 
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), (A1 \== A2 ; N1 =\= N2), !.



/* règles de tran/formation */

/* rename_r */
reduit(rename_r, X ?= T, P, Q)
:- append(P, [], Q), X = T.

/*simplify*/
reduit(simplify_r, X ?= T, P, Q)
:- append(P, [], Q), X = T.

/*expand*/
reduit(expand_r, X ?= T, P, Q)
:- append(P, [], Q), X = T.

/*check */
%fonctionne
reduit(check_r, _, _, bottom).

/*orient*/
%fonctionne
reduit(orient_r, T ?= X, [T ?= X | P], [X ?= T | P]).

/*decompose*/
reduit(decompose_r, X ?= T, [X ?= T | P], Pout)
:- X =.. [_ |F], T =.. [_ |G], decompose_aux(F, G, Q), append(P, Q, Pout).

	/*Lout reçoit des équations entre les éléments de L1 et L2*/
	decompose_aux([], [], _).

	decompose_aux([X1 | L1], [X2 | L2], Lout)
	:- decompose_aux(L1, L2, Lout), memberchk(X1 ?= X2, Lout).

/*clash*/
%fonctionne
reduit(clash_r, _, _, bottom).




/* Unifie */


unifie([]).

unifie([E | P])
:- regle(E, R), reduit(R, E, P, Q), unifie(Q). 


/* 
unifie([X ?= b]) réponse X = b
unifie([X ?= X]) réponse true
unifie([X ?= f(X)]) réponse false
unifie([X ?= f(a)]) X=f(a)

unifie([a ?= a]) réponse true
unifie([a ?= b]) réponse false
unifie([a ?= f(a)]) réponse false

unifie([f(X) ?= X]) reponse false
unifie([f(X) ?= a]) reponse false
unifie([f(X) ?= f(a)]) erreur --------------
unifie([f(X) ?= f(X)]) erreur --------------
unifie([f(X, k) ?= f(X,n)]) erreur --------------

*/


/*rename*/
/*reduit(rename_r, X ?= T, [X ?= T | P], Q)
:- rename_aux(X, T, P, Q).*/

/*rename_aux(_, _, [], _).*/ /*on s arrete quand c est vide*/

/* cas où X = X1 et T = T1 */
/*rename_aux(X, T, [X1 ?= T1| Pin], [T ?= T |Pout])
:- same_term(X, X1), same_term(X, T1).*/

/* cas où X = X1 */
/*rename_aux(X, T, [X1 ?= T1| Pin], [T ?= T |Pout])
:- same_term(X, X1), \+same_term(X, T1).*/

/* cas où T = T1 */
/*rename_aux(X, T, [X1 ?= T1| Pin], [X1 ?= T |Pout])
:- \+same_term(X, X1), same_term(X, T1).*/

/* cas où il n'y a rien à rename */
/*rename_aux(X, T, [X1 ?= T1| Pin], [X1 ?= T1 |Pout])
:- \+same_term(X, X1), \+same_term(X, T1).*/


rename_terme(X, T, Terme, T)
:- X == Terme.

rename_terme(X, _, Terme, Terme)
:- X \== Terme, \+fonc(Terme).

rename_terme(X, T, Terme, Sortie)
:- X \== Terme, fonc(Terme), Terme=..Liste, rename_list(X, T, Liste, ListeSortie), Sortie=..ListeSortie.


rename_list(_, _, [], _).

rename_list(X, T, [E | Lin], [Eout | Lout])
:- rename_terme(X, T, E, Eout), rename_list(X, T, Lin, [Eout | Lout]).


/*
rename_terme(X, T, Terme, T)
:- var(X), var(Terme), same_term(X, Terme), !.

rename_terme(X, _, Terme, Terme)
:- var(X), var(Terme), \+same_term(X, Terme), !.

rename_terme(X, _, Terme, Terme)
:- var(X), nonvar(Terme), \+same_term(X, Terme), \+fonc(Terme), !.

rename_terme(X, T, Terme, Sortie)
:- var(X), nonvar(Terme), \+same_term(X, Terme), fonc(Terme), 
Terme=..Liste, rename_list(X, T, Liste, ListeSortie), Sortie=..ListeSortie, !.
*/




/* unifie*/

%unifie([X ?= t, X ?= f(X)]). %question
%unifie([X ?= t, Y = X]). %question

%unifie([]).

%unifie([E | P])
%:- unifie(P), reduit(_, E, P, Q), Q \= bottom.



% select/4 éventuellement pour rename






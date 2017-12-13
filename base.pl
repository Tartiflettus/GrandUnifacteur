/* Prédicats utiles */


:- op(20,xfy,?=).


fonc(X)
:- nonvar(X), functor(X, _, A), A > 0 .


const(X)
:- nonvar(X), functor(X, _, 0).


delete_p(_, [], []).

delete_p(X, [E | P], Qout) 
:- X \== E, append([E], Q, Qout), delete_p(X, P, Q), !.

delete_p(X, [E | P], Q) 
:- X == E, delete_p(X, P, Q).



:- dynamic echo_on/0.
% Prédicats d affichage fournis

% set_echo: ce prédicat active l affichage par le prédicat echo
set_echo :- assert(echo_on).

% clr_echo: ce prédicat inhibe l affichage par le prédicat echo
clr_echo :- retractall(echo_on).

% echo(T): si le flag echo_on est positionné, echo(T) affiche le terme T
%          sinon, echo(T) réussit simplement en ne faisant rien.

echo(T) :- echo_on, !, writeln(T).
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
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), A1 =:= A2, N1 == N2, !.

regle(X ?= T, clash_r) 
:- fonc(X), fonc(T), functor(X, N1, A1), functor(T, N2, A2), (A1 =\= A2 ; N1 \== N2), !.



/* règles de tran/formation */

/* rename_r */
reduit(rename_r, X ?= T, P, Q)
:- append(P, [], Q), X = T, !.

/*simplify*/
reduit(simplify_r, X ?= T, P, Q)
:- append(P, [], Q), X = T, !.

/*expand*/
reduit(expand_r, X ?= T, P, Q)
:- append(P, [], Q), X = T, !.

/*check */
reduit(check_r, _, _, bottom).

/*orient*/
reduit(orient_r, T ?= X, P, [X ?= T | P]).

/*clash*/
reduit(clash_r, _, _, bottom).

/*decompose*/
reduit(decompose_r, X ?= T, P, Pout)
:- X =.. [_ |F], T =.. [_ |G], decompose_aux(F, G, Q), append(P, Q, Pout).

	/*Lout reçoit des équations entre les éléments de L1 et L2*/
	decompose_aux([], [], []).

	decompose_aux([X1 | L1], [X2 | L2], Lout)
	:- decompose_aux(L1, L2, Q), append([X1 ?= X2], Q, Lout).





/* Unifie(P) */
unifie([]).

unifie([E | P])
:- regle(E, R), reduit(R, E, P, Q), unifie(Q), !. 


/* Unifie(P,S) */
unifie([], _).

unifie(P, choix_premier)
:- choix_premier(P, Q, E, R), reduit(R, E, Q, Q1), echo(system: P), echo(R: E),
unifie(Q1, choix_premier), !.


unifie(P, choix_pondere)
:- choix_pondere(P, Q, E, R), reduit(R, E, Q, Q1), echo(system: P), echo(R: E),
unifie(Q1, choix_pondere), !.


unifie(P, choix_aleatoire)
:- choix_aleatoire(P, Q, E, R), reduit(R, E, Q, Q1), echo(system: P), echo(R: E),
unifie(Q1, choix_aleatoire), !.



/* affichages exécution */
trace_unif(P, S)
:- set_echo, unifie(P, S), clr_echo.

unif(P, S)
:- clr_echo, unifie(P, S).



/* choix_premier */
choix_premier([E | P], P, E, R)
:- regle(E, R), !. 



/* choix_pondere */
choix_pondere(P, Q, E, R)
:- ( extrait_clash_check(P, E, R); extrait_rename_simplify(P, E, R); extrait_orient(P, E, R); extrait_decompose(P, E, R); extrait_expand(P, E, R) ),
delete_p(E, P, Q), !.


    /*clash et check */
    extrait_clash_check([E | _], E, R)
    :- ( regle(E, clash_r) ; regle(E, check_r) ), regle(E, R).

    extrait_clash_check([E | P], ESortie, RSortie)
    :- \+regle(E, clash_r), \+regle(E, check_r), 
    extrait_clash_check(P, ESortie, RSortie).

    /* rename et simplify */
    extrait_rename_simplify([E | _], E, R)
    :- ( regle(E, rename_r) ; regle(E, simplify_r) ), regle(E, R).

    extrait_rename_simplify([E | P], ESortie, RSortie)
    :- \+regle(E, rename_r), \+regle(E, simplify_r), 
    extrait_rename_simplify(P, ESortie, RSortie).

    /* orient */
    extrait_orient([E | _], E, orient_r)
    :- regle(E, orient_r).

    extrait_orient([E | P], ESortie, RSortie)
    :- \+regle(E, orient_r), 
    extrait_orient(P, ESortie, RSortie).

    /* decompose */
    extrait_decompose([E | _], E, decompose_r)
    :- regle(E, decompose_r).

    extrait_decompose([E | P], ESortie, RSortie)
    :- \+regle(E, decompose_r), 
    extrait_decompose(P, ESortie, RSortie).

    /* expand */
    extrait_expand([E | _], E, expand_r)
    :- regle(E, expand_r).

    extrait_expand([E | P], ESortie, RSortie)
    :- \+regle(E, expand_r), 
    extrait_expand(P, ESortie, RSortie).
    

/* choix_aleatoire */

choix_aleatoire(P, Q, E, R)
:- random_member(E, P), regle(E, R), delete_p(E, P, Q), !.




/* tests 
unifie([X ?= b]) réponse X = b
unifie([X ?= X]) réponse true
unifie([X ?= Y]) réponse X = Y
unifie([X ?= f(X)]) réponse false
unifie([X ?= f(a)]) X=f(a)

unifie([a ?= a]) réponse true
unifie([a ?= b]) réponse false
unifie([a ?= f(a)]) réponse false

unifie([f(X) ?= X]) reponse false
unifie([f(X) ?= a]) reponse false
unifie([f(X) ?= f(a)]) X = a
unifie([f(X) ?= f(X)]) true
unifie([f(a) ?= f(a)]) true
unifie([f(X, k) ?= f(X,n)]) false
unifie([f(a) ?= f(X)]) X = a

unifie([f(a, b) ?= f(X, Y)]) X = a    Y = b


unifie([f(a, X) ?= f(a, b)]) X =b
unifie([f(X) ?= f(Y)]) X = Y
unifie([f(X) ?= f(g(Y))]) X = g(Y)
unifie([f(X) ?= f(X,Y)]) false

*/


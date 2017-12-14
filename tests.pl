/* tests de fonc(X) */
?- fonc(f(a)).
true.

?- fonc(f(X)).
true.

?- fonc(c).
false.

?- fonc(X).
false.


/* tests de const(X) */
?- const(a).
true.

?- const(X).
false.

?- const(f(a)).
false.

?- const(f(X)).
false.


/* tests de delete_p(Elem, Lin, Lout) */
?- delete_p(a, [a, b, c], Lout).
Lout = [b, c].

?- delete_p(a, [a, b, c, d, a], Lout).
Lout = [b, c, d].

?- delete_p(a, [b, c, d], Lout).
Lout = [b, c, d].

?- delete_p(a, [], Lout).
Lout = [].

?- delete_p(a, [X, Y, Z], Lout).
Lout = [X, Y, Z].

?- delete_p(X, [a, b, X], Lout).
Lout = [a, b].

?- delete_p(f(X), [a, b, f(X)], Lout).
Lout = [a, b].


/* tests de occur_check(X, T) */
?- occur_check(X, f(X)).
true.

?- occur_check(X, f(a, b, c)).
false.

?- occur_check(X, f(Y, X, Z)).
true.

?- occur_check(X, f(Y)).
false.


/*tests des règles */
/* rename */
?- regle(X ?=T, R).
R = rename_r.

?- regle(X ?= a, rename_r).
false.

?- regle(X ?= f(a), rename_r).
false.

?- regle(X ?= f(X), rename_r).
false.


/* simplify */
?- regle(X ?=t, R).
R = simplify_r.

?- regle(X ?= a, simplify_r).
true.

?- regle(X ?= f(a), simplify_r).
false.

?- regle(X ?= f(X), simplify_r).
false.


/* expand */
?- regle(X ?=f(t), R).
R = expand_r.

?- regle(X ?= a, expand_r).
false.

?- regle(X ?= f(a), expand_r).
true.

?- regle(X ?= f(X), expand_r).
false.


/* check */
?- regle(X ?= f(X), R).
R = check_r.

?- regle(X ?= a, check_r).
false.

?- regle(X ?= f(a), check_r).
false.

?- regle(X ?= f(X), check_r).
true.


/* orient */
?- regle(t ?= X, R).
R = orient_r.

?- regle(t ?= X, orient_r).
true.

?- regle(X ?= f(a), orient_r).
false.

?- regle(X ?= a, orient_r).
false.


/* decompose */
?- regle(f(t) ?= f(X), R).
R = decompose_r.

?- regle(f(X) ?= X, decompose_r).
false.

?- regle(f(X) ?= f(X, Y), decompose_r).
false.

?- regle(f(X) ?= f(a), decompose_r).
true.

?- regle(f(X) ?= g(Y), decompose_r).
false.


/* clash */
?- regle(f(t) ?= g(X, a), R).
R = clash_r.

?- regle(f(X) ?= X, clash_r).
false.

?- regle(f(X) ?= f(X, Y), clash_r).
true.

?- regle(f(X) ?= f(a), clash_r).
false.

?- regle(f(X) ?= g(Y), clash_r).
true.


/* tests reduit */
/* rename */
?- reduit(rename_r, X ?= T, [], Q).
X = T,
Q = [].

?- reduit(rename_r, X ?= T, [f(X) ?= X], Q).
X = T,
Q = [f(T)?=T].


/* simplify */
?- reduit(simplify_r, X ?= t, [], Q).
X = t,
Q = [].

?- reduit(simplify_r, X ?= t, [f(X) ?= X], Q).
X = t,
Q = [f(t)?=t].


/* expand */
?- reduit(expand_r, X ?= f(t), [], Q).
X = f(t),
Q = [].

?- reduit(expand_r, X ?= f(t), [f(X) ?= X], Q).
X = f(t),
Q = [f(f(t))?=f(t)].


/* check */
?- reduit(check_r, X ?= f(t, Y, X, k), [], Q).
Q = bottom.

?- reduit(check_r, X ?= f(t, Y, X, k), [f(X) ?= X], Q).
Q = bottom.


/* orient */
?- reduit(orient_r, t ?= X, [], Q).
Q = [X?=t].

?- reduit(orient_r, t ?= X, [f(X) ?= X], Q).
Q = [X?=t, f(X)?=X].


/* clash */
?- reduit(clash_r, f(t) ?= g(X), [], Q).
Q = bottom.

?- reduit(clash_r, f(t) ?= f(X, m), [], Q).
Q = bottom.

?- reduit(clash_r, f(t) ?= g(X), [f(X) ?= X], Q).
Q = bottom.


/* decompose */
?- reduit(decompose_r, f(t, C, X) ?= f(X, k, Y), [], Q).
Q = [t?=X, C?=k, X?=Y].

?- reduit(decompose_r, f(t) ?= f(X), [f(X) ?= X], Q).
Q = [f(X)?=X, t?=X].


/* unifie(P) */
?- unifie([X ?= b]).
X = b.

?- unifie([X ?= X]).
true.

?- unifie([X ?= Y]).
X = Y.

?- unifie([X ?= f(X)]).
false.

?- unifie([X ?= f(a)]).
X = f(a).

?- unifie([a ?= a]).
true.

?- unifie([a ?= b]).
false.

?- unifie([a ?= f(a)]).
false.

?- unifie([f(X) ?= X]).
false.

?- unifie([f(X) ?= a]).
false.

?- unifie([f(X) ?= f(a)]).
X = a.

?- unifie([f(X) ?= f(X)]).
true.

?- unifie([f(a) ?= f(a)]).
true.

?- unifie([f(X, k) ?= f(X,n)]).
false.

?- unifie([f(a) ?= f(X)]).
X = a.

?- unifie([f(a, b) ?= f(X, Y)]).
X = a,
Y = b.

?- unifie([f(a, X) ?= f(a, b)]).
X = b.

?- unifie([f(X) ?= f(Y)]).
X = Y.

?- unifie([f(X) ?= f(g(Y))]).
X = g(Y).

?- unifie([f(X) ?= f(X,Y)]).
false.

?- unifie([f(X, Y) ?= f(g(Z), h(a)), Z ?= f(Y)]).
X = g(f(h(a))),
Y = h(a),
Z = f(h(a)).

?- unifie([f(X, Y) ?= f(g(Z), h(a)), Z ?= f(X)]).
false.


/* tests trace_unif(P, S) */
/* choix premier */
?- trace_unif([Z ?= f(Y), f(X, Y) ?= f(g(Z), h(a))], choix_premier).
system:[f(_G4306)?=f(_G4306),f(_G4314,_G4306)?=f(g(f(_G4306)),h(a))]
expand_r:f(_G4306)?=f(_G4306)
system:[f(_G4314,_G4306)?=f(g(f(_G4306)),h(a))]
decompose_r:f(_G4314,_G4306)?=f(g(f(_G4306)),h(a))
system:[g(f(_G4306))?=g(f(_G4306)),_G4306?=h(a)]
expand_r:g(f(_G4306))?=g(f(_G4306))
system:[h(a)?=h(a)]
expand_r:h(a)?=h(a)
Z = f(h(a)),
Y = h(a),
X = g(f(h(a))).

/* choix pondere */
?- trace_unif([Z ?= f(Y), f(X, Y) ?= f(g(Z), h(a))], choix_pondere).
system:[_G4308?=f(_G4306),f(_G4314,_G4306)?=f(g(_G4308),h(a))]
decompose_r:f(_G4314,_G4306)?=f(g(_G4308),h(a))
system:[f(_G4306)?=f(_G4306),_G4314?=g(f(_G4306)),_G4306?=h(a)]
expand_r:f(_G4306)?=f(_G4306)
system:[g(f(_G4306))?=g(f(_G4306)),_G4306?=h(a)]
expand_r:g(f(_G4306))?=g(f(_G4306))
system:[h(a)?=h(a)]
expand_r:h(a)?=h(a)
Z = f(h(a)),
Y = h(a),
X = g(f(h(a))).

/* choix aleatoire */
?- trace_unif([Z ?= f(Y), f(X, Y) ?= f(g(Z), h(a))], choix_aleatoire).
system:[f(_G4306)?=f(_G4306),f(_G4314,_G4306)?=f(g(f(_G4306)),h(a))]
expand_r:f(_G4306)?=f(_G4306)
system:[f(_G4314,_G4306)?=f(g(f(_G4306)),h(a))]
decompose_r:f(_G4314,_G4306)?=f(g(f(_G4306)),h(a))
system:[g(f(_G4306))?=g(f(_G4306)),_G4306?=h(a)]
expand_r:g(f(_G4306))?=g(f(_G4306))
system:[h(a)?=h(a)]
expand_r:h(a)?=h(a)
Z = f(h(a)),
Y = h(a),
X = g(f(h(a))).

?- trace_unif([Z ?= f(Y), f(X, Y) ?= f(g(Z), h(a))], choix_aleatoire).
system:[_G4308?=f(_G4306),f(_G4314,_G4306)?=f(g(_G4308),h(a))]
decompose_r:f(_G4314,_G4306)?=f(g(_G4308),h(a))
system:[f(_G4306)?=f(_G4306),_G4314?=g(f(_G4306)),_G4306?=h(a)]
expand_r:f(_G4306)?=f(_G4306)
system:[g(f(_G4306))?=g(f(_G4306)),_G4306?=h(a)]
expand_r:g(f(_G4306))?=g(f(_G4306))
system:[h(a)?=h(a)]
expand_r:h(a)?=h(a)
Z = f(h(a)),
Y = h(a),
X = g(f(h(a))).
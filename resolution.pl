/*
1. YES
2. YES
3. YES
4. NO
5. YES
6. YES
7. YES
8. NO
9. NO
10. YES
*/


%These lines define the operator precedence for the operators used in the program.
?-op(140, fy, neg).
?-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, notimp, notrevimp, equiv, notequiv]).

%These lines define a predicate member that checks if an element is a member of a list.
member(X, [X|_]).
member(X, [_|Tail]) :- member(X, Tail).

%These lines define a predicate remove that removes one occurrence of an element from a list.
remove(_, [], []) :- !.
remove(Item, [Item | Rest], Newlist) :- 
    remove(Item, Rest, Newlist).
remove(Item, [Head | Rest], [Head | Newlist]) :-
    dif(Head, Item),
    remove(Item, Rest, Newlist).

%These lines define a predicate remove that removes all occurrences of an element from a list.
removeall(_, [], []) :- !.
removeall(Item, [Item | Rest], Newlist) :-
    removeall(Item, Rest, Newlist).
removeall(Item, [Head | Rest], [Head | Newlist]) :-
    dif(Head, Item),
    removeall(Item, Rest, Newlist).

%These lines remove duplicates from all members of all lists
sortall(List, Newlist) :-
    maplist(sort, List, SortedList),
    sort(SortedList, Newlist).

%These lines 
find(X, [List | _], List) :-
    member(X, List).
find(X, [_ | Tail], Y) :-
    find(X, Tail, Y).

%Merges the contents of lists together
merge(List1, List2, Result) :-
    merge_helper(List1, List2, Result).

merge_helper([Head | Tail], List2, [Head | NewTail]) :-
    merge_helper(Tail, List2, NewTail).
merge_helper([], Newlist, Newlist).

%These lines define the conjunctive formulas for the CNF conversion.
conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).

%These lines define the disjunctive formulas for the CNF conversion
disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).

%Equivalence definitions
eq(_ equiv _).
eq(_ notequiv _).
eq(neg(_ equiv _)).
eq(neg(_ notequiv _)).

%These lines define the unary formulas for the CNF conversion. 
unary(neg neg _).
unary(neg true).
unary(neg false).

%These lines define the component formulas for the CNF conversion.
components(X and Y, X, Y).
components(neg(X and Y), neg X, neg Y).
components(X or Y, X, Y).
components(neg(X or Y), neg X, neg Y).
components(X imp Y, neg X, Y).
components(neg(X imp Y), X, neg Y).
components(X revimp Y, X, neg Y).
components(neg(X revimp Y), neg X, Y).
components(X uparrow Y, neg X, neg Y).
components(neg(X uparrow Y), X, Y).
components(X downarrow Y, neg X, neg Y).
components(neg(X downarrow Y), X, Y).
components(X notimp Y, X, neg Y).
components(neg(X notimp Y), neg X, Y).
components(X notrevimp Y, neg X, Y).
components(neg(X notrevimp Y), X, neg Y).
component(X equiv Y, (neg X or Y) and (X or neg Y)).
component(neg(X equiv Y), (neg X or neg Y) and (X or Y)).
component(X notequiv Y, (neg X or neg Y) and (X or Y)).
component(neg(X notequiv Y), (neg X or Y) and (X or neg Y)).
component(neg neg X, X).
component(neg true, false).
component(neg false, true).
%negation checker
ifneg(neg _).

/*
The check predicate checks whether 
a given list is satisfiable by verifying 
that no variable and its negation both 
appear in the list, and by recursively 
checking the satisfiability of the 
remaining variables.
*/
check([]).
check([X | Tail]) :-
    not(ifneg(X)),
    not(member(neg X, Tail)),
    remove(neg X, Tail, NewTail),
    check(NewTail).
check([X | Tail]) :-
    ifneg(X),
    component(neg X, New),
    not(member(New, Tail)),
    remove(New, Tail, NewTail),
    check(NewTail).


/*
The singlestep predicate is used to perform one step of the 
conversion process of a formula in propositional logic to conjunctive
normal form (CNF). The predicate takes as input a conjunction of 
disjunctions Conjunction and produces a new conjunction of
disjunctions New. The predicate tries three different patterns, each
corresponding to a different type of formula: unary, conjunctive, or 
disjunctive. The last pattern is recursive and applies 'singlestep'
on the rest of the conjunction.
*/

singlestep([Conjunction | Rest], New) :-
    member(Formula, Conjunction),
    unary(Formula),
    component(Formula, Newformula),
    removeall(Formula, Conjunction, Temporary),
    Newconjunction = [Newformula | Temporary],
    New = [Newconjunction | Rest].

singlestep([Conjunction|Rest], New) :-
    member(Equiv, Conjunction),
    eq(Equiv),
    component(Equiv, Newequiv),
    removeall(Equiv, Conjunction, Temporary),
    Newconjunction = [Newequiv | Temporary],
    New = [Newconjunction | Rest].

singlestep([Conjunction|Rest], New) :-
    member(Alpha, Conjunction),
    conjunctive(Alpha),
    components(Alpha, Alphaone, Alphatwo),
    removeall(Alpha, Conjunction, Temporary),
    Newconone = [Alphaone | Temporary],
    Newcontwo = [Alphatwo | Temporary],
    New = [Newconone, Newcontwo | Rest].

singlestep([Conjunction|Rest], New) :-
    member(Beta, Conjunction),
    disjunctive(Beta),
    components(Beta, Betaone, Betatwo),
    removeall(Beta, Conjunction, Temporary),
    Newcon = [Betaone, Betatwo | Temporary],
    New = [Newcon | Rest].

singlestep([Conjunction | Rest], [Conjunction | Newrest]) :-
    singlestep(Rest, Newrest).

/*
The resolutionstep predicate performs a single resolution step on a
given list of clauses, by selecting two clauses with a complementary 
literal, then merging them into a new clause while removing the 
complementary literals, or if the list contains the empty clause then 
return it as the result.
*/
resolutionstep([Conjunction|Tail], New) :-
    member(neg X, Conjunction),
    member(X, Tail),
    remove(X, Conjunction, Conjunction1),
    remove(neg X, Tail, Tail1),
    Temp = [Conjunction1 | Tail1],
    sort(Temp, New).

resolutionstep([Conjunction|Tail], New) :-
    member(X, Conjunction),
    check(Conjunction),
    find(neg X, Tail, Conjunction1),
    check(Conjunction1),
    removeall(X, Conjunction, Temp1),
    removeall(neg X, Conjunction1, Temp2),
    merge(Temp1, Temp2, Temp3),
    sort(Temp3, SortedTemp),
    check(SortedTemp),
    remove(Conjunction1, Tail, NewTail),
    \+ Tail = NewTail,
    merge([SortedTemp], NewTail, New).

resolutionstep([Conjunction|Tail], New) :-
    member(neg X, Conjunction),
    check(Conjunction),
    find(X, Tail, Conjunction1),
    check(Conjunction1),
    removeall(neg X, Conjunction, Temp1),
    removeall(X, Conjunction1, Temp2),
    merge(Temp1, Temp2, Temp3),
    sort(Temp3, NewConjunction),
    check(NewConjunction),
    remove(Conjunction1, Tail, NewTail),
    NewTail = Tail,
    merge([NewConjunction], NewTail, New).

resolutionstep([Conjunction|Tail], Result) :-
    resolutionstep(Tail, NewTail),
    merge([Conjunction], NewTail, Result).

/*
A recursive predicate that resolves clauses until 
it reaches the empty clause or no new clause is generated.
*/
resolution(Con, Con) :-
    member([], Con).
resolution(Con, Newcon) :-
    resolutionstep(Con, Temp),
    resolution(Temp, Newcon).

%Basic if checking
if_then_else(P, Q, R) :- P, !, Q.
if_then_else(P, Q, R) :- R.

%Choosing for result
yes :- write('YES'), nl.
no  :- write('NO'),  nl.

/*
The expand predicate applies a single step of the expansion 
process to a conjunction of disjunctions until no more expansions can 
be made, resulting in the CNF form of a formula.
*/
expand(X, Y) :-
    singlestep(X, Temp),
    !, expand(Temp, Y).
expand(X, Y) :-
    sortall(X, Temp),
    resolution(Temp, Y).


/*
The clauseform predicate returns the clause form of a given 
logical expression by first expanding it and then sorting the result.
*/
clauseform(X, CNF) :-
    cnf([[X]], CNF).
    
cnf(X, Y) :-
    singlestep(X, Temp),
    !, cnf(Temp, Y).
cnf(X, X).

/*
Calling the testing
*/
test(X) :-
    if_then_else(expand([[neg X]], Y), yes,no).
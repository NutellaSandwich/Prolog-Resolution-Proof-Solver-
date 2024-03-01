% CNF conversion rules
cnf(neg neg F, CNF) :- cnf(F, CNF).
cnf(neg(F and G), CNF) :- cnf(neg F or neg G, CNF).
cnf(neg(F or G), CNF) :- cnf(neg F and neg G, CNF).
cnf(F and G, CNF) :- cnf(F, CNF1), cnf(G, CNF2), append(CNF1, CNF2, CNF).
cnf(F or G, CNF) :- cnf(F, CNF1), cnf(G, CNF2), distribute_or(CNF1, CNF2, CNF).
cnf(F imp G, CNF) :- cnf(neg F or G, CNF).
cnf(F revimp G, CNF) :- cnf(F or neg G, CNF).
cnf(F uparrow G, CNF) :- cnf(neg(F and G), CNF).
cnf(F downarrow G, CNF) :- cnf(neg(F or G), CNF).
cnf(F notimp G, CNF) :- cnf(F and neg G, CNF).
cnf(F notrevimp G, CNF) :- cnf(neg F and G, CNF).
cnf(F equiv G, CNF) :- cnf((F imp G) and (G imp F), CNF).
cnf(F notequiv G, CNF) :- cnf((F imp neg G) and (neg F imp G), CNF).

% Helper predicate to distribute OR over AND
distribute_or([], _, []).
distribute_or([H1|T1], L2, CNF) :-
    distribute_or(T1, L2, CNF1),
    distribute_or_helper(H1, L2, CNF2),
    append(CNF1, CNF2, CNF).

distribute_or_helper(_, [], []).
distribute_or_helper(H1, [H2|T2], [[H1,H2]|CNF]) :-
    distribute_or_helper(H1, T2, CNF).

% Example usage
% cnf((p or q) and (neg p or q), CNF).
% CNF = [[p, q], [neg p, q]]

% Main predicate for CNF conversion
cnf(F, CNF) :- nnf(F, NNF), flatten(NNF, FlatNNF), convert_to_cnf(FlatNNF, CNF).

% Convert formula to negation normal form
nnf(neg neg F, NNF) :- nnf(F, NNF).
nnf(neg(F and G), NNF) :- nnf(neg F or neg G, NNF).
nnf(neg(F or G), NNF) :- nnf(neg F and neg G, NNF).
nnf(F and G, [NNF1, NNF2]) :- nnf(F, NNF1), nnf(G, NNF2).
nnf(F or G, NNF) :- nnf(neg F and neg G, NNF).
nnf(F imp G, NNF) :- nnf(neg F or G, NNF).
nnf(F revimp G, NNF) :- nnf(F imp G, NNF).
nnf(F uparrow G, NNF) :- nnf(neg(F and G), NNF).
nnf(F downarrow G, NNF) :- nnf(neg(F or G), NNF).
nnf(F notimp G, NNF) :- nnf(F and neg G, NNF).
nnf(F notrevimp G, NNF) :- nnf(neg F or G, NNF).
nnf(F equiv G, NNF) :- nnf((F imp G) and (G imp F), NNF).
nnf(F notequiv G, NNF) :- nnf((F imp neg G) and (neg F imp G), NNF).
nnf(F, F) :- atomic(F).

% Convert formula to CNF
convert_to_cnf([], []).
convert_to_cnf([H|T], CNF) :-
convert_clause_to_cnf(H, ClauseCNF),
convert_to_cnf(T, RestCNF),
append(ClauseCNF, RestCNF, CNF).

convert_clause_to_cnf([], []).
convert_clause_to_cnf([H|T], [NewH|NewT]) :-
convert_literal_to_cnf(H, NewH),
convert_clause_to_cnf(T, NewT).

convert_literal_to_cnf(neg F, [neg F]) :- atomic(F).
convert_literal_to_cnf(F, [F]) :- atomic(F).
convert_literal_to_cnf(F or G, CNF) :- cnf(F or G, CNF1), convert_to_cnf(CNF1, CNF).
convert_literal_to_cnf(F and G, CNF) :- convert_clause_to_cnf([F, G], CNF).

% Example usage:
% cnf((p or q) and (neg p or q), CNF).
% CNF = [[p, q], [neg p, q]]


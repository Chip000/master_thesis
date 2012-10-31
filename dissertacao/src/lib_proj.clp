:- lib(ic).
:- lib(branch_and_bound).

% ordered/1: Verifica se a lista dada está ordenada
ordered([]).
ordered([H | T]) :- 
	ordered(H, T).
ordered(_,[]).
ordered(E, [H | T]) :- 
	E #=< H,
	ordered(H, T).

% element_is_different/2: Verifica se o elemento X é diferente de todos os elementos da lista L=[H|T]
element_is_different(_, []).
element_is_different(X, [H|T]) :-
	X \= H,
	element_is_different(X, T).

% all_different/1: Verifica se a lista L=[H|T] possui elementos repetidos 
all_different([]).
all_different([H|T]) :- 
	element_is_different(H, T),
	all_different(T).

% is_identity/1: Verifica se a lista é a permutação identidade
is_identity(H) :-
	ordered(H),
	all_different(H).

% in_range/2: Verifica se todos elementos da lista L=[H|T] está dentro do intervalo M .. N
in_range(_, _, []).
in_range(M, N, [H|T]) :- 
	H :: M .. N,
	in_range(M, N, T).

% split3/6: Divide a lista L=[H|T] em 3 sublistas
split3([H|T], I, J, [H|C1], C2, C3) :-
	length([H|T], N),
	I :: 0 .. N,
	indomain(I), 
	J :: 0 .. N,
	indomain(J), 
	I1 is I - 1,
	J1 is J - 1,
	split3(T, I1, J1, C1, C2, C3).
split3([H|T], 0, J, [], [H|C2], C3) :-
	length([H|T], N),
	J :: 0 .. N,
	indomain(J),
	J1 is J - 1,
	split3(T, 0, J1, [], C2, C3).
split3(L, 0, 0, [], [], L).

% split4/8: Divide a lista L=[H|T] em 4 sublistas
split4([H|T], I, J, K, [H|C1], C2, C3, C4) :-
	length([H|T], N),
	I :: 0 .. N,
	indomain(I), 
	J :: 0 .. N,
	indomain(J), 
	K :: 0 .. N,
	indomain(K), 
	I1 is I - 1,
	J1 is J - 1,
	K1 is K - 1,
	split4(T, I1, J1, K1, C1, C2, C3, C4).
split4([H|T], 0, J, K, [], [H|C2], C3, C4) :-
	length([H|T], N),
	J :: 0 .. N,
	indomain(J),
	K :: 0 .. N,
	indomain(K), 
	J1 is J - 1,
	K1 is K - 1,
	split4(T, 0, J1, K1, [], C2, C3, C4).
split4([H|T], 0, 0, K, [], [], [H|C3], C4) :-
	length([H|T], N),
	K :: 0 .. N,
	indomain(K), 
	K1 is K - 1,
	split4(T, 0, 0, K1, [], [], C3, C4).
split4(L, 0, 0, 0, [], [], [], L).

%
% Breakpoints
%

% calc_breakpoint/3: Encontra o número de breakpoints dada uma permutação Pi, de acordo com o modelo escolhido
calc_breakpoint([],0, _) :- !.
calc_breakpoint(Pi, N, rev) :-
	length(Pi, M),
	calc_breakpoint_rev(0, Pi, N, M), !.
calc_breakpoint(Pi, N, trans) :-
	length(Pi, M),
	calc_breakpoint_trans(0, Pi, N, M), !.

% breakpoints para reversões
calc_breakpoint_rev(E, [], 0, L) :-
	E >= L - 1,
	E =< L + 1, !.
calc_breakpoint_rev(E, [], 1, L) :-
	E =\= L - 1,
	E =\= L + 1, !.
calc_breakpoint_rev(E, [H | T], N, L) :-
	E >= H - 1,
	E =< H + 1,
	calc_breakpoint_rev(H, T, N, L), !.
calc_breakpoint_rev(E, [H | T], N, L) :-
	E =\= H - 1,
	E =\= H + 1,
	calc_breakpoint_rev(H, T, N1, L),
	N is N1 + 1, !.

% breakpoints para transposições
calc_breakpoint_trans(E, [], 0, L) :-
	E =:= L - 1, !.
calc_breakpoint_trans(E, [], 1, L) :-
	E =\= L - 1, !.
calc_breakpoint_trans(E, [H | T], N, L) :-
	E =:= H - 1,
	calc_breakpoint_trans(H, T, N, L), !.
calc_breakpoint_trans(E, [H | T], N, L) :-
	E =\= H - 1,
	calc_breakpoint_trans(H, T, N1, L),
	N is N1 + 1, !.

%
% Grafo de ciclos para transposições
%

%black_edges_cg_trans/2: Cria o conjunto de arestas pretas
black_edges_cg_trans([A, B], [[B, A]]) :- !.
black_edges_cg_trans([A, B | T], [[B, A] | R]) :-
	black_edges_cg_trans([B|T], R).

%gray_edges_cg_trans/2| Cria o conjunto de arestas cinzas
gray_edges_cg_trans([], N, I) :-
	I > N, !.
gray_edges_cg_trans([[I, J]| T], N, I) :- 
	I =< N,
	J is I + 1,
	gray_edges_cg_trans(T, N, J).

%look_for_next/3: Procura a aresta vizinha a [U,V] no conjunto de arestas dados
look_for_next([_, V], [[V, J] | _], [I, J]) :-
	I is V, !.
look_for_next([U, V], [[I, _] | T], E) :-
	I =\= V, 
	look_for_next([U, V], T, E).
look_for_next(_, [], []).

%remove_edge/3: Remove a aresta do conjunto.
remove_edge(E, [E | T], T) :- !.
remove_edge(E, [H | T], [H | Ts]) :-
	remove_edge(E, T, Ts), !.
remove_edge(_, [], []).

%create_cycle_trans/4: Encontra um ciclo começando por arestas cinzas. Usa os predicados create_cycle_gray/5 e create_cycle_black/5 para alternar as cores no ciclo
create_cycle_trans([H | TBlack], Gray, [H | T], N) :-
	create_cycle_gray(H, TBlack, Gray, T, R),
	N is R + 1, !.

%create_cycle_gray/5: Encontra a aresta cinza e segue para uma aresta preta
create_cycle_gray(H, Black, Gray, [E | T], N) :-
	look_for_next(H, Gray, E),
	length(E, NE),
	NE > 0,
	remove_edge(E, Gray, NGray),
	create_cycle_black(E, Black, NGray, T, N), !.
create_cycle_gray(H, _, Gray, [], 0) :-
	look_for_next(H, Gray, E),
	length(E, NE),
	NE =< 0, !.

%create_cycle_black/5: Encontra a aresta preta e segue para uma aresta cinza
create_cycle_black(H, Black, Gray, [E | T], N) :-
	look_for_next(H, Black, E),
	length(E, NE),
	NE > 0,
	remove_edge(E, Black, NBlack),
	create_cycle_gray(E, NBlack, Gray, T, R), 
	N is R + 1, !.
create_cycle_black(H, Black, _, [], 0) :-
	look_for_next(H, Black, E),
	length(E, NE),
	NE =< 0, !.

%remove_cycle/5: Efetua a remoção das arestas que pertencem ao ciclo. OBS: Dois ciclos não possuem arestas em comum
remove_cycle([H | TC], B, G, NBlack, NGray):-
	remove_edge(H,B,NB),
	remove_cycle_G(TC, NB, G, NBlack, NGray), !.
remove_cycle([], B, G, B, G).

remove_cycle_G([H | TC], B, G, NBlack, NGray) :- 
	remove_edge(H, G, NG),
	remove_cycle(TC, B, NG, NBlack, NGray), !.
remove_cycle_G([], B, G, B, G).

%count_odd_cg_trans/3: Retorna o número de ciclos ímpares usando o conjunto de arestas pretas e cinzas
count_odd_cg_trans([], _, 0) :- !.
count_odd_cg_trans(_, [], 0) :- !.
count_odd_cg_trans(Black, Gray, C) :-
	create_cycle_trans(Black, Gray, Cycle, N),
	1 is N mod 2,
	remove_cycle(Cycle, Black, Gray, NewBlack, NewGray),
	count_odd_cg_trans(NewBlack, NewGray, R),
	C is R + 1, !.
count_odd_cg_trans(Black, Gray, C) :-
	create_cycle_trans(Black, Gray, Cycle, N),
	0 is N mod 2,
	remove_cycle(Cycle, Black, Gray, NewBlack, NewGray),
	count_odd_cg_trans(NewBlack, NewGray, C), !.

%calc_odd_cycles_transposition/3: Cria a representação do grafo de ciclos para a permutação Pi e encontra a quantidade de ciclos ímpares
calc_odd_cycles_transposition(Pi, N, C) :- 
        extend_pi(Pi, EPi),
	black_edges_cg_trans(EPi, Black),
	gray_edges_cg_trans(Gray, N, 0),
	count_odd_cg_trans(Black, Gray, C). 

%
% Grafo de ciclos para reversões
%

%create_black_edges_cg_rev/2: Cria a lista de arestas pretas para o grafo de ciclos para reversões
create_black_edges_cg_rev([_], []).
create_black_edges_cg_rev([U, V| T], [[U, V] | RT]) :-
	V =\= U + 1,
	V =\= U - 1,
	create_black_edges_cg_rev([V | T], RT), !.
create_black_edges_cg_rev([U, V| T], RT) :-
	V =< U + 1,
	V >= U - 1,
	create_black_edges_cg_rev([V | T], RT), !.

%neighbors/4: Verifica se dois elementos são vizinhos em Pi
neighbors(_, _, [], 0) :- !.
neighbors(A, B, [A, B | _], 1) :- !.
neighbors(A, B, [B, A | _], 1) :- !.
neighbors(A, B, [_ | T], R) :- 
	neighbors(A, B, T, R), !.

%create_gray_edges_cg_rev_aux/3 e create_gray_edges_cg_rev/2: Cria a lista de arestas cinzas para o grafo de ciclos para reversões
%create_gray_edges_cg_rev_aux/3
create_gray_edges_cg_rev_aux(_, [_],[]).
create_gray_edges_cg_rev_aux(P, [U | T], [[U , N] | RT]) :-
	N is U + 1,
	neighbors(U, N, P, R),
	R =:= 0,
	create_gray_edges_cg_rev_aux(P, T, RT), !.
create_gray_edges_cg_rev_aux(P, [U | T], RT) :-
	N is U + 1,
	neighbors(U, N, P, R),
	R =\= 0,
	create_gray_edges_cg_rev_aux(P, T, RT), !.

%create_gray_edges_cg_rev/2
create_gray_edges_cg_rev([], []).
create_gray_edges_cg_rev(P, G) :-
	create_gray_edges_cg_rev_aux(P, P, G).

%connect_edges/4: Verifica se uma aresta [E,F] conecta as arestas [A,B] e [C,D]
connect_edges([],_,_,0) :- !.
connect_edges(_,[],_,0) :- !.
connect_edges(_,_,[],0) :- !.
connect_edges([A, _], [C, _], [E, F], 1) :-
	E =:= A,
	F =:= C, !.
connect_edges([A, _], [C, _], [E, F], 1) :-
	F =:= A,
	E =:= C, !.
connect_edges([A, _], [_, D], [E, F], 1) :-
	E =:= A,
	F =:= D, !.
connect_edges([A, _], [_, D], [E, F], 1) :-
	F =:= A,
	E =:= D, !.
connect_edges([_, B], [C, _], [E, F], 1) :-
	E =:= B,
	F =:= C, !.
connect_edges([_, B], [C, _], [E, F], 1) :-
	F =:= B,
	E =:= C, !.
connect_edges([_, B], [_, D], [E, F], 1) :-
	E =:= B,
	F =:= D, !.
connect_edges([_, B], [_, D], [E, F], 1) :-
	F =:= B,
	E =:= D, !.
connect_edges(_, _, _, 0) :- !.

%neighbour_edges/3: Verifica se duas arestas são vizinhas
neighbour_edges(_, [], 0) :- !.
neighbour_edges([], _, 0) :- !.
neighbour_edges([A,_], [A,_], 1) :- !.
neighbour_edges([A,_], [_,A], 1) :- !.
neighbour_edges([_,A], [A,_], 1) :- !.
neighbour_edges([_,A], [_,A], 1) :- !.
neighbour_edges(_, _, 0) :- !.

%remove_neighbour_edges/3: Remove as arestas vizinhas
remove_neighbour_edges([], _, _) :- !.
remove_neighbour_edges(_, [], []) :- !.
remove_neighbour_edges(A, [B | GT], NG) :-
	neighbour_edges(A, B, R),
	R =:= 1,
	remove_neighbour_edges(A, GT, NG), !.
remove_neighbour_edges(A, [B | GT], [B |NG]) :-
	neighbour_edges(A, B, R),
	R =:= 0,
	remove_neighbour_edges(A, GT, NG), !.

%find_gray_edges/4: Encontra as arestas cinzas que ligam as arestas A e B
find_gray_edges([], [], _, []) :- !.
find_gray_edges(_, _, [], []) :- !.
find_gray_edges(A, B, [E | GT], [E | ET]) :-
	connect_edges(A, B, E, R),
	R =:= 1,
	remove_neighbour_edges(E, GT, NGT),
	find_gray_edges(A, B, NGT, ET), !.
find_gray_edges(A, B, [E | GT], ET) :-
	connect_edges(A, B, E, R),
	R =:= 0,
	find_gray_edges(A, B, GT, ET), !.

%create_matching_graph_aux/6 e create_matching_graph/4: Criam um emparelhamento para encontrar a decomposição de ciclos do grafo de ciclos para reversões
%create_matching_graph_aux/6
create_matching_graph_aux(_ , _, [] , _  , [], []) :- !.
create_matching_graph_aux(_ , _, _  , [] , [], []) :- !.
create_matching_graph_aux([], _, _  , _  , [], []) :- !.
create_matching_graph_aux(U, [V | BT], B, G, [[U, V] | FT], 
			  [Edges | FGT]) :-
	find_gray_edges(U, V, G, Edges),
	length(Edges, N),
	N =:= 2,
	create_matching_graph_aux(U, BT, B, G, FT, FGT), !.
create_matching_graph_aux(U, [V | BT1], B, G, FT, FGT) :-
	find_gray_edges(U, V, G, Edges),
	length(Edges, N),
	N =\= 2,
	create_matching_graph_aux(U, BT1, B, G, FT, FGT), !.
create_matching_graph_aux(_, [], [H | BT], G, FT, FGT) :-
	create_matching_graph_aux(H, BT, BT, G, FT, FGT), !.

%create_matching_graph/4
create_matching_graph(_, [], [], []).
create_matching_graph([], _, [], []).
create_matching_graph([H | BT], G, F, FG) :-
	create_matching_graph_aux(H, BT, BT, G, F, FG), !.

%check_adjacency/3: Verifica se A possui adjacência com algum elemento da lista L=[B|T]
check_adjacency([], _, 0) :- !.
check_adjacency(_, [], 0) :- !.
check_adjacency(A, [B|_], 1) :-
	neighbour_edges(A,B,R),
	R =:= 1, !.
check_adjacency(A, [B|T], RES) :-
	neighbour_edges(A,B,R),
	R =:= 0, 
	check_adjacency(A, T, RES), !.

%maximum_cardinality_matching/3: Escolhe qual aresta faz parte parte do emparelhamento máximo
maximum_cardinality_matching([], [], _) :- !.
maximum_cardinality_matching([FH | FT], [-1| XT], []) :-
	maximum_cardinality_matching(FT, XT, [FH]).
maximum_cardinality_matching([FH | FT], [-1| XT], M) :-
	check_adjacency(FH, M, R),
	R =:= 0,
	maximum_cardinality_matching(FT, XT, [FH | M]).
maximum_cardinality_matching([FH | FT], [0| XT], M) :-
	check_adjacency(FH, M, R),
	R =:= 1,
	maximum_cardinality_matching(FT, XT, M).

%mcm_res/3: Retorna a lista com as arestas que fazem parte da solução
mcm_res([], _, []) :- !.
mcm_res(_, [], []) :- !.
mcm_res([-1 | T], [H | FT], [H | MT]) :-
	mcm_res(T, FT, MT), !.
mcm_res([0 | T], [_ | FT], M) :-
	mcm_res(T, FT, M), !.

%find_maximum_cardinality_matching/4: Encontra o emparelhamento máximo. OBS: Usa a teoria COP para encontrar o emparelhamento máximo
find_maximum_cardinality_matching(F, FG, M, MG) :-
	length(F, N),
	length(X, N),
	minimize((maximum_cardinality_matching(F, X, []),
	         sum(X, Cost)), Cost),
	mcm_res(X, F, M),
	mcm_res(X, FG, MG).

%create_lg_aux/4: Cria a lista de ladder cycles (2-ciclos que compartilha arestas cinzas)
create_lg_aux(_, _, [], []) :- !.
create_lg_aux(U, [V | MGT], MG, [[U, V] | LE]) :- 
	neighbour_edges(U, V, R),
	R =:= 1,
	create_lg_aux(U, MGT, MG, LE), !.
create_lg_aux(U, [V | MGT], MG, LE) :- 
	neighbour_edges(U, V, R),
	R =:= 0,
	create_lg_aux(U, MGT, MG, LE), !.
create_lg_aux(_, [], [H | MGT], LE) :- 
	create_lg_aux(H, MGT, MGT, LE), !.

%join_ladder_aux/3 e join_ladder/2: Cria a lista dos vértices do conjunto de ladder cycles
%join_ladder_aux/3
join_ladder_aux(E, [], E) :- !.
join_ladder_aux(E, [H | T], R) :-
	append(E, H, TEMP),
	join_ladder_aux(TEMP, T, R), !.

%join_ladder/2
join_ladder([], []) :- !.
join_ladder([H | T], R) :-
	join_ladder_aux(H, T, R), !.

%in_list/3: Verifica se um elemento já está na lista
in_list(_, [], 0) :- !.
in_list(H, [H | _], 1) :- !.
in_list(H, [_ | T], R) :- 
	in_list(H, T, R), !.

%remove_equals_aux/3 e remove_equals/2: Retira os elementos repetidos da lista
%remove_equals_aux/3
remove_equals_aux(E, [], [E]) :- !.
remove_equals_aux(E, [H | T], [E | R]) :-
	in_list(E, [H | T], B),
	B =:= 0,
	remove_equals_aux(H, T, R), !.
remove_equals_aux(E, [H | T], R) :-
	in_list(E, [H | T], B),
	B =:= 1,
	remove_equals_aux(H, T, R), !.

%remove_equals/2
remove_equals([], []) :- !.
remove_equals([H | T], R) :-
	remove_equals_aux(H, T, R), !.

%vertex_in_ladder/2: Cria a lista com os vértices pertencentes aos ladder cycles (ladder vertices)
vertex_in_ladder([],[]).
vertex_in_ladder(Ladder, Vertex) :-
	join_ladder(Ladder, List),
	remove_equals(List, Vertex), !.

%find_independent_vertex_aux/3 e find_independent_vertex/2: Encontra os 2-ciclos independentes (Não possuem nenhuma aresta em comum com os outros ciclos) e os ladder vertices 
%find_independent_vertex_aux/3
find_independent_vertex_aux([], _, []) :- !.
find_independent_vertex_aux([H | MGT], LE, [H | LI]) :- 
	in_list(H, LE, R),
	R =:= 0,
	find_independent_vertex_aux(MGT, LE, LI), !.
find_independent_vertex_aux([H | MGT], LE, LI) :- 
	in_list(H, LE, R),
	R =:= 1,
	find_independent_vertex_aux(MGT, LE, LI), !.

%find_independent_vertex/3
find_independent_vertex(A, [], A) :- !.
find_independent_vertex(MG, Ladder, LI) :-
	vertex_in_ladder(Ladder, LVertex),
	find_independent_vertex_aux(MG, LVertex, LI), !.

%create_ladder_graph/3: Cria o ladder graph usando o emparelhamento criado a partir do grafo de ciclos 
create_ladder_graph([],[],[]) :- !.
create_ladder_graph([H | MGT], LEdges, LInd) :-
	create_lg_aux(H, MGT, MGT, LEdges),
	find_independent_vertex([H | MGT], LEdges, LInd), !.

%calc_2_cycle/3: Calcula o número de 2-ciclos no grafo de ciclos para reversões
calc_2_cycle([], [], 0).
calc_2_cycle(LE, LI, C) :-
	length(LI, Z),
	length(LE, Y),
	C is Z + Y.

%find_2_cycle/2: Retorna o número de 2-ciclos no grafo de ciclos para reversões
find_2_cycle([], 0) :- !.
find_2_cycle(Vertex, C) :-
	create_black_edges_cg_rev(Vertex, BEdges),
	create_gray_edges_cg_rev(Vertex, GEdges),
	create_matching_graph(BEdges, GEdges, FEdges, FGEdges),
	find_maximum_cardinality_matching(FEdges, FGEdges, _MEdges, MGEdges),
	create_ladder_graph(MGEdges, LEdges, LIndependent),
	calc_2_cycle(LEdges, LIndependent, C), !.

%
% Permutação
%

% permutation/2: Verifica se Pi é uma permutação
permutation(Pi, N) :- 
	length(Pi, N), 
	in_range(1, N, Pi), % Pi :: [1 .. N],
	all_different(Pi).

%extend_pi/2: Adiciona 0 no início e N+1 no fim da permutação Pi
extend_pi([],[]).
extend_pi(Pi, EPi) :-
	length(Pi, N),
	N1 is N + 1,
	append([0|Pi], [N1], EPi). 

%
% Bounds
%

% bound/4: Dado um modelo retorna os limitantes inferior e superior para a permutação Pi
bound(Pi, def, LB, UB) :-
	length(Pi, N),
	LB is 0,
	UB is N.

% Limitantes para reversões
bound(Pi, rev_br, LB, UB) :-
	calc_breakpoint(Pi, B, rev),
	LB is B // 2,
	UB is B.
bound(Pi, rev_cg, LB, UB) :-
	extend_pi(Pi, EPi),
	calc_breakpoint(EPi, B, rev),
	find_2_cycle(EPi, C),
	LB is ((2*B - C) // 3),
	UB is (B - (C // 2)).

% Limitantes para transposições
bound(Pi, tra_br, LB, UB) :-
	calc_breakpoint(Pi, B, trans),
	LB is B // 3,
	UB is B.
bound(Pi, tra_cg, LB, UB) :-
	length(Pi, N),
	calc_odd_cycles_transposition(Pi, N, C),
	LB is (N + 1 - C) // 2,
	UB is (3 * (N + 1 - C)) // 4.

% Limitantes para reversões + transposições
bound(Pi, t_r_br, 0, UB) :-
	bound(Pi, tra_br, _TLB, TUB),
	bound(Pi, rev_br, _RLB, RUB),
	min(RUB, TUB, UB).
bound(Pi, t_r_cb, 0, UB) :-
	bound(Pi, tra_cg, _TLB, TUB),
	bound(Pi, rev_br, _RLB, RUB),
	min(RUB, TUB, UB).
bound(Pi, t_r_cc, 0, UB) :-
	bound(Pi, tra_cg, _TLB, TUB),
	bound(Pi, rev_cg, _RLB, RUB),
	min(RUB, TUB, UB).

%
% CSP models
%

% reversal/4: Efetua a reversão no bloco definido por (I,J)
reversal(Pi, Sigma, I, J) :-
	permutation(Pi, N),
	[I, J] #:: 0 .. N, I #< J,
	indomain(I),
	indomain(J),
	split3(Pi, I, J, C1, C2, C3),
	reverse(C2, R2),
	append(C1, R2, C12),
	append(C12, C3, C123),
	Sigma = C123,
	permutation(Sigma, N).

% transposition/5: Efetua a transposições dos blocos definidos por (I,J,K)
transposition(Pi, Sigma, I, J, K) :-
	permutation(Pi, N),
	[I, J, K] #:: 0 .. N, I #< J, J #< K,
	indomain(I),
	indomain(J),
	indomain(K),
	split4(Pi, I, J, K, C1, C2, C3, C4),
	append(C1, C3, C13),
	append(C13, C2, C132),
	append(C132, C4, C1324),
	Sigma = C1324,
	permutation(Sigma, N).

% event/2: Escolhe o melhor evento entre reversão e transposição
event(Pi, Sigma,tra) :- 
	transposition(Pi, Sigma, _I, _J, _K).	
event(Pi, Sigma,rev) :- 
	reversal(Pi, Sigma, _I, _J).	
event(Pi, Sigma) :- 
	bound(Pi, tra_br, _TLB, TUB),
	bound(Pi, rev_br, _RLB, RUB),
	TUB =< RUB,
	event(Pi, Sigma, tra).
event(Pi, Sigma) :- 
	bound(Pi, tra_br, _TLB, TUB),
	bound(Pi, rev_br, _RLB, RUB),
	TUB > RUB,
	event(Pi, Sigma, rev).

% reversal_dist/3: CSP: Retorna a distância de reversão usando o modelo M
reversal_dist(Pi, 0, _M) :-
	is_identity(Pi).
reversal_dist(Pi, T, M) :-
	bound(Pi, M, LB, UB),
	T :: LB .. UB,
	indomain(T),
	reversal(Pi, Sigma, _I, _J),
	TAUX is T - 1,
	reversal_dist(Sigma, TAUX, M), !.

% transposition_dist/3: CSP: Retorna a distância de transposição usando o modelo M
transposition_dist(Pi, 0, _M) :-
	is_identity(Pi).
transposition_dist(Pi, T, M) :-
	bound(Pi, M, LB, UB),
	T :: LB .. UB,
	indomain(T),
	transposition(Pi, Sigma, _I, _J, _K),
	TAUX is T - 1,
	transposition_dist(Sigma, TAUX, M), !.

% rev_trans_dist/3: CSP: Retorna a distância de reversão+transposição usando o modelo M
rev_trans_dist(Pi, 0, _M) :-
	is_identity(Pi).
rev_trans_dist(Pi, D, M) :-
	bound(Pi, M, LB, UB),
	D :: LB .. UB,
	indomain(D),
	event(Pi, Sigma),
	DAUX is D - 1,
	rev_trans_dist(Sigma, DAUX, M), !.

%
% COP models
%

% reversal_cop/5: Modificação do predicado reversal/4 do modelo CSP para incluir a variável B
reversal_cop(Pi, Sigma, 0, 0, 0) :-
	is_identity(Pi),
	is_identity(Sigma), !.
reversal_cop(Pi, Sigma, I, J, 1) :-
	reversal(Pi, Sigma, I, J).

% transposition/6: Modificação do predicado transposition/5 do CSP para incluir a variável B
transposition_cop(Pi, Sigma, 0, 0, 0, 0) :-
	is_identity(Pi),
	is_identity(Sigma), !.
transposition_cop(Pi, Sigma, I, J, K, 1) :-
	transposition(Pi, Sigma, I, J, K).

% ub_constraint_rev/3: Aplica os efeitos da reversão. Retorna os valores corretos na lista B
ub_constraint_rev(Pi, [], _M, _UB) :-
	is_identity(Pi).
ub_constraint_rev(Pi, [B|Bt], M, UB) :-
	reversal_cop(Pi, Sigma, _I, _J, B),
	bound(Pi, M, LB, _UB),
	UB >= LB,
	UBAUX is UB - 1,
	ub_constraint_rev(Sigma, Bt, M, UBAUX).

% ub_constraint_trans/3: Aplica os efeitos da reversão. Retorna os valores corretos na lista B
ub_constraint_trans(Pi, [], _M, _UB) :-
	is_identity(Pi).
ub_constraint_trans(Pi, [B|Bt], M, UB) :- 
	transposition_cop(Pi, Sigma, _I, _J, _K, B), 
	bound(Pi, M, LB, _UB),
	UB >= LB,
	UBAUX is UB - 1,
	ub_constraint_trans(Sigma, Bt, M, UBAUX).

% ub_constraint_event/3: Escolhe qual evento será usado. Retorna os valores corretos na lista B
ub_constraint_event(Pi, [], _M, _UB) :-
	is_identity(Pi).
ub_constraint_event(Pi, [B|Bt], M, UB) :- 
	transposition_cop(Pi, Sigma, _I, _J, _K, B), 
	bound(Pi, M, LB, _UB),
	UB >= LB,
	UBAUX is UB - 1,
	ub_constraint_event(Sigma, Bt, M, UBAUX).
ub_constraint_event(Pi, [B|Bt], M, UB) :- 
	reversal_cop(Pi, Sigma, _I, _J, B), 
	bound(Pi, M, LB, _UB),
	UB >= LB,
	UBAUX is UB - 1,
	ub_constraint_event(Sigma, Bt, M, UBAUX).

% reversal_dist_cop/3: COP: Retorna a distância de reversão usando o modelo M
reversal_dist_cop(Pi, 0, _M) :-
	is_identity(Pi), !.
reversal_dist_cop(Pi, T, M) :-
	bound(Pi, M, LB, UB),
	length(B, UB),
	minimize((ub_constraint_rev(Pi, B, M, UB),
	          sum(B, Cost), 
		  Cost >= LB), Cost), T is Cost.

% transposition_dist_cop/3: COP: Retorna a distância de transposição usando o modelo M
transposition_dist_cop(Pi, 0, _M) :-
	is_identity(Pi), !.
transposition_dist_cop(Pi, T, M) :-
	bound(Pi, M, LB, UB),
	length(B, UB), 
	minimize((ub_constraint_trans(Pi, B, M, UB),
	          sum(B, Cost), 
		  Cost >= LB), Cost), T is Cost.

% rev_trans_dist_cop/3: COP: Retorna a distância de reversão+transposição usando o modelo M
rev_trans_dist_cop(Pi, 0, _M) :-
	is_identity(Pi), !.
rev_trans_dist_cop(Pi, T, M) :-
	bound(Pi, M, LB, UB),
	length(B, UB), 
	minimize((ub_constraint_event(Pi, B, M, UB),
	          sum(B, Cost), 
		  Cost >= LB), Cost), T is Cost.


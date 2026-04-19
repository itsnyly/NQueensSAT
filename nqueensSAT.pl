%%%%%%%%%%%%
% sat(F,I,M)
% si F es satisfactible, M sera el model de F afegit a la interpretació I (a la primera crida I sera buida).
sat([],I,I):-     write('SAT!!'),nl,!.
sat(CNF,I,M):-
    decideix(CNF,Lit),
    simplif(Lit,CNF,CNFS),
    sat(CNFS, [Lit|I], M).

%%%%%%%%%%%%%%%%%%
% decideix(F, Lit)
decideix(CNF,Lit):-
    member([Lit], CNF), !. % si hi ha una clausula unitaria, tria el seu literal

decideix([[L|_]|_], Lit):- % si no hi ha clausula unitaria, agafa el primer literal
    tria_positiu_o_negatiu(L, Lit).

tria_positiu_o_negatiu(L, L).
tria_positiu_o_negatiu(L, Lit):-
    Lit is -L.

%%%%%%%%%%%%%%%%%%%%%
% simplif(Lit, F, FS)
simplif(_,[],[]).
simplif(Lit, [Cl|RestaCNF], CNFS):-
    member(Lit, Cl), !, % Mirem si Lit hi és. Si hi és, tallem perquè no miri els altres casos.
    simplif(Lit, RestaCNF, CNFS). 

simplif(Lit, [Cl|RestaCNF], [ClN|RestaCNFS]):-
    LitNegat is -Lit,
    member(LitNegat, Cl), !, % Mirem si el negat hi és.
    treu(LitNegat, Cl, ClN), 
    ClN \= [], % Si després de treure el literal negatiu la clàusula queda buida, fallarà.
    simplif(Lit, RestaCNF, RestaCNFS). 

simplif(Lit, [Cl|RestaCNF], [Cl|RestaCNFS]):-
    simplif(Lit, RestaCNF, RestaCNFS). 

% AUX: treu(Element, LlistaOriginal, LlistaSenseElement)
treu(_, [], []).
treu(E, [E|Cua], Cua) :- !.  
treu(E, [Cap|Cua], [Cap|CuaNeta]) :- 
    treu(E, Cua, CuaNeta).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%
% comaminimUn(L,CNF)
comaminimUn(L, [L]). 

%%%%%%%%%%%%%%%%%%%
% comamoltUn(L,CNF)
comamoltUn([],[]). 
comamoltUn([X|Cua], CNF):-
    combina(X, Cua, ParellesNegades), 
    comamoltUn(Cua, CNFResta), 
    append(ParellesNegades, CNFResta, CNF). 

% AUX: combina(Element, Llista, ParellesNegades)
combina(_, [], []). 
combina(X, [Y|Cua], [[NX, NY] | RestaParelles]) :-
    NX is -X, 
    NY is -Y, 
    combina(X, Cua, RestaParelles). 

%%%%%%%%%%%%%%%%%%%
% exactamentUn(L,CNF)
exactamentUn(L, CNF):-
    comaminimUn(L, CNF1),
    comamoltUn(L, CNF2),
    append(CNF1, CNF2, CNF). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fesTauler(+N,+PI,+PP,V,I)
fesTauler(N, PI, PP, V, I) :-
    TotalCaselles is N * N,
    llista(1, TotalCaselles, LlistaN), 
    trosseja(LlistaN, N, V),           
    fixa(PI, N, ClausulesPI),          
    prohibeix(PP, N, ClausulesPP),     
    append(ClausulesPI, ClausulesPP, I). 

% AUX: llista(I,F,L)
llista(I, F, []):- I > F, !. 
llista(I, F, [I|Resta]):-
    I =< F, ISeguent is I + 1, llista(ISeguent, F, Resta). 

% AUX: trosseja(L,N,LL)
trosseja([],_,[]). 
trosseja(L, N, [Tros|RestaTrossos]):-
    length(Tros, N), 
    append(Tros, RestaLlista, L), 
    trosseja(RestaLlista, N, RestaTrossos). 

% AUX: fixa(PI,N,F)
fixa(PI, N, F) :-
    coordenadesAVars(PI, N, Vars),
    creaPositives(Vars, F).

creaPositives([], []).
creaPositives([V | Resta], [[V] | RestaClausules]) :-
    creaPositives(Resta, RestaClausules).

% AUX: prohibeix(PP,N,P)
prohibeix(PP, N, P) :-
    coordenadesAVars(PP, N, Vars),
    creaNegatives(Vars, P).

creaNegatives([], []).
creaNegatives([V | Resta], [[NegV] | RestaClausules]) :-
    NegV is -V,
    creaNegatives(Resta, RestaClausules).

%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesFiles(+V,F)
noAmenacesFiles([],[]). 
noAmenacesFiles([Fila|RestaFiles], CNFTotal):- 
    exactamentUn(Fila, CNFFila), 
    noAmenacesFiles(RestaFiles, CNFResta), 
    append(CNFFila, CNFResta, CNFTotal). 

%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesColumnes(+V,C)
noAmenacesColumnes(V, C):-
    transposa(V, VCol),
    recorreColumnes(VCol, C).

transposa([[]|_], []) :- !.
transposa(M, [Columna|RestaCols]):-
    extreu_columna(M, Columna, RestaMatriu), 
    transposa(RestaMatriu, RestaCols). 

extreu_columna([], [], []).
extreu_columna([[Cap|Cua] | RestaFiles], [Cap|RestaCaps], [Cua|RestaCues]) :-
    extreu_columna(RestaFiles, RestaCaps, RestaCues).

recorreColumnes([], []).
recorreColumnes([Col|RestaCols], CNFTotal):-
    exactamentUn(Col, CNFCol), 
    recorreColumnes(RestaCols, CNFResta), 
    append(CNFCol, CNFResta, CNFTotal). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesDiagonals(+N,C)
noAmenacesDiagonals(N,D):-
    diagonals(N,L), 
    llistesDiagonalsAVars(L,N,VARS), 
    recorreDiagonals(VARS,D).

recorreDiagonals([], []).
recorreDiagonals([Diag|Resta], CNFTotal) :-
    comamoltUn(Diag, CNFDiag),
    recorreDiagonals(Resta, CNFResta),
    append(CNFDiag, CNFResta, CNFTotal).

diagonals(N,L):- diagonalsIn(1,N,L1), diagonals2In(1,N,L2), append(L1,L2,L).

diagonalsIn(D,N,[]):-D is 2*N,!.
diagonalsIn(D,N,[L1|L]):- D=<N,fesDiagonal(1,D,L1), D1 is D+1, diagonalsIn(D1,N,L).
diagonalsIn(D,N,[L1|L]):- D>N, F is D-N+1,fesDiagonalReves(F,N,N,L1), D1 is D+1, diagonalsIn(D1,N,L).

fesDiagonal(F,1,[(F,1)]):- !.
fesDiagonal(F,C,[(F,C)|R]):- F1 is F+1, C1 is C-1, fesDiagonal(F1,C1,R).

fesDiagonalReves(N,C,N,[(N,C)]):-!.
fesDiagonalReves(F,C,N,[(F,C)|R]):-F1 is F+1, C1 is C-1, fesDiagonalReves(F1,C1,N,R).

diagonals2In(D, N, []) :- D is 2*N, !.
diagonals2In(D, N, [L1|L]) :- 
    D =< N, fesDiagonal2(N, D, L1), D1 is D+1, diagonals2In(D1, N, L).
diagonals2In(D, N, [L1|L]) :- 
    D > N, F is 2*N - D, fesDiagonal2Reves(F, N, L1), D1 is D+1, diagonals2In(D1, N, L).

fesDiagonal2(F, 1, [(F, 1)]) :- !.
fesDiagonal2(F, C, [(F, C)|R]) :- F1 is F-1, C1 is C-1, fesDiagonal2(F1, C1, R).

fesDiagonal2Reves(1, C, [(1, C)]) :- !.
fesDiagonal2Reves(F, C, [(F, C)|R]) :- F1 is F-1, C1 is C-1, fesDiagonal2Reves(F1, C1, R).

coordenadesAVars([],_,[]).
coordenadesAVars([(F,C)|R],N,[V|RV]):-V is (F-1)*N+C, coordenadesAVars(R,N,RV).

llistesDiagonalsAVars([], _, []).
llistesDiagonalsAVars([DiagCoord | RestaDiags], N, [DiagVars | RestaVars]) :-
    coordenadesAVars(DiagCoord, N, DiagVars),
    llistesDiagonalsAVars(RestaDiags, N, RestaVars).

%%%%%%%%%%%%%%%%%%%%%
% minimNReines(+V,FN)
% Garantim que a cada fila hi ha com a mínim una reina. Això, sumat
% al "com a molt una" de la resta, ens dóna exactament N reines.
minimNReines([], []).
minimNReines([Fila|Resta], CNFTotal) :-
    comaminimUn(Fila, CNFFila),
    minimNReines(Resta, CNFResta),
    append(CNFFila, CNFResta, CNFTotal).

%%%%%%%%%
% resol()
resol :-
    write('Mida del tauler (N)? '), read(N),
    write('Posicions inicials (llista de tuples [(F,C),...], o [])? '), read(PI),
    write('Posicions prohibides (llista de tuples [(F,C),...], o [])? '), read(PP),
    fesTauler(N, PI, PP, V, Ini),
    minimNReines(V, FN),
    noAmenacesFiles(V, CNFfiles),
    noAmenacesColumnes(V, CNFcolumnes),
    noAmenacesDiagonals(N, CNFdiagonals),
    append(Ini, FN, C0),
    append(C0, CNFfiles, C1),
    append(C1, CNFcolumnes, C2),
    append(C2, CNFdiagonals, CNFTotal),
    crida_sat(CNFTotal, N, PP).

% Predicat auxiliar per simular l'if-else sense fer servir el prohibit operador ;
crida_sat(CNF, N, PP) :-
    sat(CNF, [], Model),
    !, % Si sat troba solució, tallem aquí per no executar l'avís de UNSAT.
    nl, write('Tauler Solucio:'), nl,
    mostraTauler(N, PP, Model).
crida_sat(_, _, _) :-
    nl, write('Inabastable (UNSAT)'), nl.

%%%%%%%%%%%%%%%%%%%
% mostraTauler(N,PP,M)
% Hem afegit PP com a paràmetre per saber quines caselles pintar amb 'X'.
% Si només mirem el model negatiu, no podem distingir una casella buida normal d'una prohibida.
mostraTauler(N, PP, M) :-
    Total is N * N,
    coordenadesAVars(PP, N, VarsPP),
    escriu_ratlles(N), nl,
    mostra_caselles(1, Total, N, VarsPP, M).

escriu_ratlles(0) :- !, write('-').
escriu_ratlles(N) :- write('--'), N1 is N - 1, escriu_ratlles(N1).

mostra_caselles(I, Total, _, _, _) :- I > Total, !.
mostra_caselles(I, Total, N, VarsPP, M) :-
    inici_fila(I, N),
    escriu_casella(I, VarsPP, M),
    fi_fila(I, N),
    ISeguent is I + 1,
    mostra_caselles(ISeguent, Total, N, VarsPP, M).

% Auxiliars per estructurar el print de cada cel·la sense usar la disjunció (;)
inici_fila(I, N) :- (I - 1) mod N =:= 0, !, write('|').
inici_fila(_, _).

fi_fila(I, N) :- I mod N =:= 0, !, nl, escriu_ratlles(N), nl.
fi_fila(_, _).

escriu_casella(I, _, M) :- member(I, M), !, write('Q|').
escriu_casella(I, VarsPP, _) :- member(I, VarsPP), !, write('X|').
escriu_casella(_, _, _) :- write(' |').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% BATERIA DE PROVES AUTOMATITZADA
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Aquest predicat fa exactament el mateix que resol/0, 
% però en comptes de preguntar, rep les dades com a arguments.
resol_test(N, PI, PP) :-
    write('--------------------------------------------------'), nl,
    write('TEST: Tauler '), write(N), write('x'), write(N), nl,
    write('Posicions Inicials: '), write(PI), nl,
    write('Posicions Prohibides: '), write(PP), nl,
    write('Resultat: '), nl,
    fesTauler(N, PI, PP, V, Ini),
    minimNReines(V, FN),
    noAmenacesFiles(V, CNFfiles),
    noAmenacesColumnes(V, CNFcolumnes),
    noAmenacesDiagonals(N, CNFdiagonals),
    append(Ini, FN, C0),
    append(C0, CNFfiles, C1),
    append(C1, CNFcolumnes, C2),
    append(C2, CNFdiagonals, CNFTotal),
    crida_sat(CNFTotal, N, PP),
    nl.

% --------------------------------------------------------
% JOC DE PROVES (Llestos per executar des de la consola)
% --------------------------------------------------------

% Prova 1: N=3 (Sense solució matemàtica)
prova1 :- resol_test(3, [], []).

% Prova 2: N=4 Bàsic (El primer amb solució)
prova2 :- resol_test(4, [], []).

% Prova 3: N=4 amb conflicte directe (Dues reines a la mateixa diagonal)
prova3 :- resol_test(4, [(1,1), (2,2)], []).

% Prova 4: N=4 amb bloqueig estratègic (Ofega les úniques solucions)
prova4 :- resol_test(4, [], [(1,2), (1,3)]).

% Prova 5: N=5 Forçant una reina al centre i prohibint cantonades
prova5 :- resol_test(5, [(3,3)], [(1,1), (5,5)]).

% Prova 6: N=8 El problema clàssic (Prova de rendiment)
prova6 :- resol_test(8, [], []).

% Predicat mestre: Executa tota la bateria de cop
totes_les_proves :-
    prova1,
    prova2,
    prova3,
    prova4,
    prova5,
    prova6,
    write('Bateria de proves finalitzada.'), nl.
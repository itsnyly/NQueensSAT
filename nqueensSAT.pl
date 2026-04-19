%%%%%%%%%%%%
% sat(F,I,M)
% si F es satisfactible, M sera el model de F afegit a la interpretació I (a la primera crida I sera buida).
% Assumim invariant que no hi ha literals repetits a les clausules ni la clausula buida inicialment.

sat([],I,I):-     write('SAT!!'),nl,!.
sat(CNF,I,M):-
% Ha de triar un literal d’una clausula unitaria, si no n’hi ha cap, llavors un literal pendent qualsevol.
decideix(CNF,Lit),

% Simplifica la CNF amb el Lit triat (compte pq pot fallar, es a dir si troba la clausula buida fallara i fara backtraking).
simplif(Lit,CNF,CNFS),

% crida recursiva amb la CNF i la interpretacio actualitzada
sat(CNFS, [Lit|I], M).


%%%%%%%%%%%%%%%%%%
% decideix(F, Lit)
% Donat una CNF,
% -> el segon parametre sera un literal de CNF
    decideix(CNF,Lit):-
        member([Lit], CNF), !. % si hi ha una clausula unitaria, tria el seu literal

    decideix([[L|_]|_], Lit):- % si no hi ha clausula unitaria, agafa el primer literal de la primera clàusula que trobis
        tria_positiu_o_negatiu(L, Lit).

    tria_positiu_o_negatiu(L, L).

    tria_positiu_o_negatiu(L, Lit):-
        Lit is -L.

%%%%%%%%%%%%%%%%%%%%%
% simlipf(Lit, F, FS)
% Donat un literal Lit i una CNF,
% -> el tercer parametre sera la CNF que ens han donat simplificada:
    %  - sense les clausules que tenen lit
%  - treient -Lit de les clausules on hi es, si apareix la clausula buida fallara.
% ...
    simplif(Lit,[],[]).
    simplif(Lit, [Cl|RestaCNF], CNFS):-
        member(Lit, Cl), !, % Mirem si Lit hi és. Si hi és, tallem perquè no miri els altres casos.
        simplif(Lit, RestaCNF, CNFS). % No incloem la clàusula a CNFS perquè ja està satisfeta.
    
    simplif(Lit, [Cl|RestaCNF], [ClN|RestaCNFS]):-
        LitNegat is -Lit,
        member(LitNegat, Cl), !, % Mirem si el negat hi és.
        treu(LitNegat, Cl, ClN), % Fem servir un predicat auxiliar per esborrar-lo.
        ClN \= [], % Si després de treure el literal negatiu la clàusula queda buida, fallarà.
        simplif(Lit, RestaCNF, RestaCNFS). % Si no és buida, afegim al resultat i continuem.
    
    simplif(Lit, [Cl|RestaCNF], [Cl|RestaCNFS]):-
        simplif(Lit, RestaCNF, RestaCNFS). % Si el literal no hi és, ni el seu negat, mantenim la clàusula i continuem

% AUX: treu(Element, LlistaOriginal, LlistaSenseElement)
treu(_, [], []).
treu(E, [E|Cua], Cua) :- !.  % Quan troba element, el salta.
treu(E, [Cap|Cua], [Cap|CuaNeta]) :- 
    treu(E, Cua, CuaNeta). % Si no és element, el manté i segueix mirant.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%
% comaminimUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a minim una sigui certa.
% ...
    comaminimUn(L, [L]). % Per assegurar que al menys una sigui certa, només cal una clàusula que contingui totes les variables com a literals positius.

%%%%%%%%%%%%%%%%%%%
% comamoltUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a molt una sigui certa.
% ...
    comamoltUn([],[]). % Si la llista està buida, no hi ha variables, per tant no hi ha cap que sigui certa.
    comamoltUn([X|Cua], CNF):-
        combina(X, Cua, ParellesNegades), % Combinem X amb tota la Cua.
        comamoltUn(Cua, CNFResta), % Crida recursiva per a la resta de la llista.
        append(ParellesNegades, CNFResta, CNF). % Ajuntem totes les clàusules generades.
    
% AUX: combina(Element, Llista, ParellesNegades)
combina(_, [], []). % Cas base: si no queden elements per combinar, no hi ha parelles.
combina(X, [Y|Cua], [[NX, NY] | RestaParelles]) :-
    NX is -X, % Neguem el primer element
    NY is -Y, % Neguem el segon element
    combina(X, Cua, RestaParelles). % Crida recursiva amb la resta de la llista

%%%%%%%%%%%%%%%%%%%
% exactamentUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que exactament una sigui certa.
% ...
    exactamentUn(L, CNF):-
        comaminimUn(L, CNF1),
        comamoltUn(L, CNF2),
        append(CNF1, CNF2, CNF). % La CNF que codifica que exactament una sigui certa és la combinació de les dues condicions anteriors.

%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fesTauler(+N,+PI,+PP,V,I)
% Donat una dimensio de tauler N, unes posicions inicials PI i
% unes prohibides PP
% -> V sera el la llista de llistes variables necessaries per codificar el tauler
% -> I sera la CNF codificant posicions inicials i prohibides

    fesTauler(N, PI, PP, V, I) :-
    TotalCaselles is N * N,
    llista(1, TotalCaselles, LlistaN), % Creem tots els números de caselles
    trosseja(LlistaN, N, V),           % Ho transformem en la matriu V
    fixa(PI, N, ClausulesPI),          % Generem clàusules posicions inicials
    prohibeix(PP, N, ClausulesPP),     % Generem clàusules posicions prohibides
    append(ClausulesPI, ClausulesPP, I). % Ho ajuntem tot a la llista d'interpretació I

% AUX
% llista(I,F,L)
% Donat un inici i un fi
% -> el tercer parametre sera una llista de numeros d'inici a fi
% ...
    llista(I, F, []):-
        I > F, !. % Cas base: si l'inici supera el final, retornem llista buida i tallem
    
    % Cas recursiu: posem I a la llista, sumem 1, i cridem recursivament.
    llista(I, F, [I|Resta]):-
        I =< F,
        ISeguent is I + 1,
        llista(ISeguent, F, Resta). 

% AUX   
% trosseja(L,N,LL)
% Donada una llista (L) i el numero de trossos que en volem (N)
% -> LL sera la llista de N llistes de L amb la mateixa mida
% (S'assumeix que la llargada de L i N ho fan possible)
% ...
    trosseja([],_,[]). %Si la llista original està buida, no hi ha trossos a fer.

    trosseja(L, N, [Tros|RestaTrossos]):-
        length(Tros, N), % Creem un tros de mida N.
        append(Tros, RestaLlista, L), % Separem el tros de la llista original.
        trosseja(RestaLlista, N, RestaTrossos). % Cridem recursivament amb la llista sobrant.

% AUX
% fixa(PI,N,F)
% donada una llista de tuples de posicions PI i una mida de tauler N
% -> F es la CNF fixant les corresponents variables de posicions a certa
    fixa(PI, N, F) :-
        coordenadesAVars(PI, N, Vars),
        creaPositives(Vars, F).

% AUX: Converteix una llista de variables [1, 2] en clàusules [[1], [2]]
    creaPositives([], []).
    creaPositives([V | Resta], [[V] | RestaClausules]) :-
        creaPositives(Resta, RestaClausules).

% AUX
% prohibeix(PP,N,P)
% donada una llista de tuples de posicions prohibides PP i una mida  tauler N
% -> P es la CNF posant les corresponents variables de posicions a fals

    prohibeix(PP, N, P) :-
        coordenadesAVars(PP, N, Vars),
        creaNegatives(Vars, P).

% AUX: Converteix una llista de variables [1, 2] en clàusules [[-1], [-2]]
    creaNegatives([], []).
    creaNegatives([V | Resta], [[NegV] | RestaClausules]) :-
        NegV is -V,
        creaNegatives(Resta, RestaClausules).

%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesFiles(+V,F)
% donada la matriu de variables,
% -> F sera la CNF que codifiqui que no s'amenecen les reines de les mateixes files
% ...
    noAmenacesFiles([],[]). % Si no hi ha files, no hi ha amenaces.

    % separem la primera fila de la resta.
    noAmenacesFiles([Fila|RestaFiles], CNFTotal):- 
        exactamentUn(Fila, CNFFila), %Generem la CNF per a la fila actual.
        noAmenacesFiles(RestaFiles, CNFResta), %Processem la resta de files
        append(CNFFila, CNFResta, CNFTotal). %Ajuntem les clàusules generades.

%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesColumnes(+V,C)
% donada la matriu de variables,
% -> C sera la CNF que codifiqui que no s'amenecen les reines de les mateixes columnes
% ...
    noAmenacesColumnes(V, C):-
        transposa(V, VCol),
        recorreColumnes(VCol, C).

% AUX
% transposa(+Matriu, -MatriuTransposada)
% Cas base: si la matriu està buida, la transposada és buida.
    transposa([[]|_], []) :- !.
    transposa(M, [Columna|RestaCols]):-
        extreu_columna(M, Columna, RestaMatriu), %Traiem la primera columna de totes les files
        transposa(RestaMatriu, RestaCols). % Fem el mateix per a la resta

% AUX
% extreu_columna(+Matriu, -Columna, -RestaMatriu)
    extreu_columna([], [], []).
    extreu_columna([[Cap|Cua] | RestaFiles], [Cap|RestaCaps], [Cua|RestaCues]) :-
        extreu_columna(RestaFiles, RestaCaps, RestaCues).

% AUX
% recorreColumnes(+MatriuTransposada, -CNF)
    recorreColumnes([], []).
    recorreColumnes([Col|RestaCols], CNFTotal):-
        exactamentUn(Col, CNFCol), % Generem la CNF per a la columna actual.
        recorreColumnes(RestaCols, CNFResta), % Processem la resta de columnes
        append(CNFCol, CNFResta, CNFTotal). % Ajuntem les clàusules generades.

% AQUEST PREDICAT ESTA PARCIALMENT FET. CAL QUE CALCULEU LES "ALTRES"
% DIAGONALS
%%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesDiagonals(+N,C)
% donada la mida del tauler,
% -> D sera la CNF que codifiqui que no s'amenecen les reines de les mateixes diagonals
noAmenacesDiagonals(N,D):-
    diagonals(N,L), 
    llistesDiagonalsAVars(L,N,VARS), 
    recorreDiagonals(VARS,D).

% AUX: Recorrem les diagonals ja convertides a variables i hi apliquem comamoltUn
recorreDiagonals([], []).
recorreDiagonals([Diag|Resta], CNFTotal) :-
    comamoltUn(Diag, CNFDiag),
    recorreDiagonals(Resta, CNFResta),
    append(CNFDiag, CNFResta, CNFTotal).

% Genera les llistes de diagonals d'una matriu NxN. Cada diagonal es una llista de coordenades.
diagonals(N,L):- diagonalsIn(1,N,L1), diagonals2In(1,N,L2), append(L1,L2,L).

% diagonalsIn(D,N,L)
% Generem les diagonals dalt-dreta a baix-esquerra, D es el numero de
% diagonals, N la mida del tauler i L seran les diagonals generades
% Exemple:
% ?- diagonalsIn(1,3,L).
% L = [[(1,1)],[(1,2),(2,1)],[(1,3),(2,2),(3,1)],[(2,3),(3,2)],[(3,3)]]
% Evidentment les diagonals amb una sola coordenada les ignorarem...

diagonalsIn(D,N,[]):-D is 2*N,!.
diagonalsIn(D,N,[L1|L]):- D=<N,fesDiagonal(1,D,L1), D1 is D+1, diagonalsIn(D1,N,L).
diagonalsIn(D,N,[L1|L]):- D>N, F is D-N+1,fesDiagonalReves(F,N,N,L1), D1 is D+1, diagonalsIn(D1,N,L).

fesDiagonal(F,1,[(F,1)]):- !.
fesDiagonal(F,C,[(F,C)|R]):- F1 is F+1, C1 is C-1, fesDiagonal(F1,C1,R).

% quan la fila es N parem
fesDiagonalReves(N,C,N,[(N,C)]):-!.
fesDiagonalReves(F,C,N,[(F,C)|R]):-F1 is F+1, C1 is C-1, fesDiagonalReves(F1,C1,N,R).

% diagonals2In(D,N,L)
% Generem les diagonals baix-dreta a dalt-esquerra
% Exemple
% ?- diagonals2In(1,3,L).
% L = [[(3,1)],[(3,2),(2,1)],[(3,3),(2,2),(1,1)],[(2,3),(1,2)],[(1,3)]]
% ...

% Cas base: parem quan hem fet totes les diagonals (2*N - 1)
    diagonals2In(D, N, []) :- D is 2*N, !.

    % Primera meitat de diagonals amb la principal inclosa: D =< N
    diagonals2In(D, N, [L1|L]) :- 
        D =< N, 
        fesDiagonal2(N, D, L1), 
        D1 is D+1, 
        diagonals2In(D1, N, L).
    
    % Segona meitat de diagonals per sobre de la principal: D > N
    diagonals2In(D, N, [L1|L]) :- 
        D > N, 
        F is 2*N - D, % Càlcul per saber a quina fila comencem
        fesDiagonal2Reves(F, N, L1), 
        D1 is D+1, 
        diagonals2In(D1, N, L).

% AUX
% fesDiagonal2: Parem quan toquem la vora esquerra (C = 1)
    fesDiagonal2(F, 1, [(F, 1)]) :- !.
    fesDiagonal2(F, C, [(F, C)|R]) :- 
        F1 is F-1, 
        C1 is C-1, 
        fesDiagonal2(F1, C1, R).

% AUX
% fesDiagonal2Reves: Parem quan toquem la vora superior (F = 1)
    fesDiagonal2Reves(1, C, [(1, C)]) :- !.
    fesDiagonal2Reves(F, C, [(F, C)|R]) :- 
        F1 is F-1, 
        C1 is C-1, 
        fesDiagonal2Reves(F1, C1, R).

% Passa una llista de coordenades  de tauler NxN a variables corresponents.
    coordenadesAVars([],_,[]).
    coordenadesAVars([(F,C)|R],N,[V|RV]):-V is (F-1)*N+C, coordenadesAVars(R,N,RV).

% Passa una llista de diagonals a llistes de llistes de variables
%llistesDiagonalsAVars(Lparells,N,Lvars).

    llistesDiagonalsAVars([], _, []).

    llistesDiagonalsAVars([DiagCoord | RestaDiags], N, [DiagVars | RestaVars]) :-
        coordenadesAVars(DiagCoord, N, DiagVars),
        llistesDiagonalsAVars(RestaDiags, N, RestaVars).

%%%%%%%%%%%%%%%%%%%%%
% minimNReines(+V,FN)
% donada la matriu de variables (inicialment d'un tauler NxN),
% -> FN sera la CNF que codifiqui que hi ha d'haver com a minim N reines al tauler
% ...


%%%%%%%%%
% resol()
% Ens demana els parametres del tauler i l'estat inicial,
% codifica les restriccions del problema i en fa una formula
% que la enviem a resoldre amb el SAT solver
% i si te solucio en mostrem el tauler
% resol():-
    %...
    %fesTauler(N,I,P,V,Ini),
    %minimNReines(V,FN),
    %...
    %noAmenacesFiles(V,CNFfiles),
    %...
    %noAmenacesColumnes(V,CNFcolumnes),
    %...
    %noAmenacesDiagonals(N,CNFdiagonals),
    %...
    %sat(...,[],...),
    %...
    %mostraTauler(N,...).


%%%%%%%%%%%%%%%%%%%
% mostraTauler(N,M)
% donat una mida de tauler N i una llista de numeros d'1 a N*N,
% mostra el tauler posant una Q a cada posicio recorrent per files
% d'equerra a dreta.
% Per exemple:
% | ?- mostraTauler(3,[1,5,8,9...]).
% -------
% |Q| | |
% -------
% | |Q| |
% -------
% | |Q|Q|
% -------
% Fixeu-vos que li passarem els literals positius del model de la nostra
% formula.
% ...

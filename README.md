\section{Renombres de TADs}

\tadNombre{TAD Pokemon} es \tadNombre{Sting}

\tadNombre{TAD Posicion} es \tadNombre{Tupla(Nat,Nat)}

\tadNombre{TAD Jugador} es \tadNombre{Nat}

%\tadNombre{TAD TipoPromesa} es \tadNombre{Enum \{compra, venta\}} 

%\tadNombre{TAD ParPC} es \tadNombre{Tupla(Promesa,Cliente)}

\newpage

\section{ \tadNombre{Extension de TAD Nat}}

\begin{tad}{\tadNombre{Extension de TAD Nat}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadOtrasOperaciones
\tadOperacion{restaEntera}{nat/n, nat/m}{nat}{}
\tadOperacion{ $\bullet$**2}{nat}{nat}{}
\tadOperacion{ div}{nat, nat/m, nat }{nat}{ m  \neq 0}
\tadOperacion{raiz}{nat/n}{nat}{}
\tadOperacion{raizAux}{nat/n, nat/m}{nat}{}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxiomas[\paratodo{nat}{n, m, p}]
\tadAlinearAxiomas{restaEntera(n,m)}

\tadAxioma{restaEntera(n,m)}{\IF (n == 0) THEN m ELSE {\IF (m == 0) THEN n ELSE restaEntera(prev(n), prev(m)) FI} FI} 

\vskip12pt

\tadAxioma{n**2}{n x n}

\vskip12pt

\tadAxioma{div(n,m,p) }{\IF n $<$  m THEN p ELSE div(n-m,m, suc(p)) FI}

\vskip12pt

\tadAxioma{raiz(n)}{raizAux(0,n)}

\vskip12pt

\tadAxioma{raizAux(n, m)}{\IF ( a**2 $\leq$ b $\land$ (suc(a)**2) $>$ b) THEN a ELSE raizAux(suc(a), b) FI}
\vskip12pt
  
\vskip12pt

\end{tad}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{ \tadNombre{Extension de TAD Posicion}}

\begin{tad}{\tadNombre{Extension de TAD Posicion}}

\tadOtrasOperaciones
\tadAlinearFunciones{distancia}{posicion/a, posicion/b}{nat}{}
\tadOperacion{distancia}{posicion/a, posicion/b}{nat}{}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxiomas[\paratodo{nat}{n, m, p, q}, \paratodo{posicion}{a, b}]
\tadAlinearAxiomas{restaEntera(n,m)}
\tadAxioma{distancia(a,b)}{raiz(((restaEntera($\Pi_1$(a), $\Pi_1$(b)))**2) + ((restaEntera($\Pi_2$(a), $\Pi_2$(b)))**2))}

\end{tad}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newpage

\section{TAD \tadNombre{Mapa}}

\begin{tad}{\tadNombre{Mapa}}
\tadIgualdadObservacional{m}{m'}{mapa}{($\forall$ p:posicion)((p $\in$ posiciones(m)) == (p $\in$ posiciones(m'))) $\land$ ($\forall$ p:posicion)((p $\in$ posiciones(m)) $\impluego$ conectadas(m,p) == conectadas(m',p))}

\tadGeneros{mapa}
\tadExporta{mapa, generadores, observadores, otras operaciones}
\tadUsa{\tadNombre{Posicion}, \tadNombre{Bool}, \tadNombre{Nat}, \tadNombre{conj}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadObservadores
\tadAlinearFunciones{conectadas~}

\tadOperacion{posiciones}{mapa}{conj(posicion)}{}
\tadOperacion{conectadas}{mapa/m, posicion/p}{conj(posicion)}{p $\in$ posiciones(m)}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadGeneradores
\tadAlinearFunciones{agConexion~}

\tadOperacion{nvoMapa}{}{mapa}{}

\tadOperacion{agPosicion}{mapa/m, posicion/p}{mapa}{p $\notin$ posiciones(m)}

\tadOperacion{agConexion}{mapa/m, posicion/p, posicion/q}{mapa}{\{p,q\} \subseteq posiciones(m) \ \Lambda \  q $\notin$ conectadas(m,p) \Lambda \ p \neq q}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadOtrasOperaciones
\tadAlinearFunciones{caminosRecursivos}

\tadOperacion{Caminos}{mapa/m,posicion/p}{conj(posicion)}{p $\in$ posiciones(m)}
\tadOperacion{CaminosAux}{mapa/m,posicion/p, conj(posicion)/res}{conj(posicion)}{p $\in$ posiciones(m)}
\tadOperacion{caminosRecursivos}{mapa/m,conj(posicion)cp, conj(posicion)/res}{conj(posicion)}{ cp $\subset$ posiciones(m)}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxiomas[\paratodo{mapa}{m}, \paratodo{nat}{n, m}, \paratodo{posicion}{p,q,p'}, \paratodo{conj(posicion)}{cp, cm, cq}]

\tadAlinearAxiomas{conectadas(agConexion(m,p,q), p')}

% OB posiciones
\tadAxioma{posiciones(nvoMapa)}{ \textbf{vacio}}
\tadAxioma{posiciones(agPosicion(m, p))}{ Ag(p, posiciones(m))}
\tadAxioma{posiciones(agConexion(m, p, q))}{ posiciones(m)}

\vskip12pt

% OB conectadas
\tadAxioma{conectadas(agPosicion(m, p), p')}{ \IF (p== p') THEN \textbf{vacio} ELSE conectadas(m,p') FI}
\tadAxioma{conectadas(agConexion(m, p, q), p')}{ \IF (p== p') THEN Ag(q,conectadas(m,p')) ELSE {\IF (q == p') THEN Ag(p, conectadas(m,p')) ELSE conectadas(m,p') FI} FI }
\vskip12pt



% OO caminos
\tadAlinearAxiomas{caminos(m,p)}
\tadAxioma{Caminos(m,p)}
{CaminosAux(m, p, \textbf{vacio}) - \{p\}}
\vskip12pt

% OO caminosAux
\tadAxioma{CaminosAux(m,p, res)}{ \IF vacio?(conectadas(m,p) - res) THEN res ELSE CaminosAux(m, dameUno(conectadas(m,p)- res ), (res $\cup$ conectadas(m,p)) $\cup$ p ) $\cup$ caminosRecursivos(m, sinUno(conectadas(m,p) - res  ),  res $\cup$ conectadas(m,p) $\cup$ p)) FI}
\vskip12pt

% OO caminosRecursivos
\tadAxioma{caminosRecursivos(m, cp, res  )}{\IF vacio? (cp) THEN res ELSE CaminosAux(m, dameUno(cp), res ) $\cup$ caminosRecursivos(m, sinUno(cp), res) FI} 



\vskip12pt


\end{tad}

\newpage

\section{TAD \tadNombre{PokemonGo}}




\begin{tad}{\tadNombre{PokemonGo}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadIgualdadObservacional{pg}{pg'}{PokemonGo}{mapa(pg)==mapa(pg') $\yluego$
($\forall$ p $\in$ posiciones(mapa(pg)))(contadorPos(pg, p)==contadorPos(pg',p)) $\yluego$ pokesalvajes(pg)==pokesalvajes(pg') $\land$ ($\forall$ j $\in$ jugConectados(pg))(j $\in$ jugConectados(pg')) $\land$  ($\forall$ j $\in$ jugDesconectados(pg))(j $\in$ jugDesconectados(pg')) $\land$ ($\forall$ j $\in$ ex-Jugadores(pg))(j $\in$ ex-Jugadores(pg')) $\land$($\forall$ j $\in$ jugConectados(pg))( posicion actual(pg,j) == posicion actual(pg, j') $\land$ ($\forall$ j $\in$ jugConectados(pg) $\cup$ jugDesconectados(pg))(sanciones(pg,j)==sanciones(pg',j)  $\land$  capturados(pg,j)==capturados(pg',j))}

\tadGeneros{pokemonGO}
\tadExporta{pokemoGO, generadores, observadores, otras operaciones}
\tadUsa{\tadNombre{Posicion}, \tadNombre{Bool}, \tadNombre{Nat}, \tadNombre{conj},\tadNombre{Multiconj}, \tadNombre{dicc} \tadNombre{Mapa}}


%Observadores
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadObservadores
\tadAlinearFunciones{pokesalvaje}

\tadOperacion{jugConectados}{pokemonGO/pg}{conj(jugador)}{}
\tadOperacion{jugDesconectados}{pokemonGO/pg}{conj(jugador)}{}
\tadOperacion{ex-Jugadores}{pokemonGO/pg}{conj(jugador)}{}
\tadOperacion{mapa}{pokemonGO}{mapa}{}
\tadOperacion{pokesalvajes}{pokemonGO/pg}{dicc(pokemon, conj(posicion))}{}
\tadOperacion{capturados}{pokemonGO/pg, jugador/j}{multiconj(pokemon)}{j $\in$ jugadores(pg)}
\tadOperacion{posicion actual}{pokemonGO/pg, jugador/j}{posicion}{j $\in$ jugadores(pg)}
\tadOperacion{sanciones}{pokemonGO/pg, jugador/j}{nat}{j $\in$ jugadores(pg)}
\tadOperacion{contadorpos}{pokemonGO/pg, posicion/p}{nat}{p $\in$ posiciones(mapa(pg))} %aqui puede ser que me falte reestriccion

%Generadores
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadGeneradores

\tadAlinearFunciones{agPokemon~}

\tadOperacion{nvoJuego}{mapa}{pokemonGO}{}

\tadOperacion{agJugador}{pokemonGO/pg, jugador/j, posicion/p }{pokemonGO}{p $\in$ posiciones(mapa(pg)) $\land$ j $\notin$ jugadores(pg) $\cup$ ex-Jugadores(pg) }


\tadOperacion{agPokemon}{pokemonGO/pg, pokemon/p, posicion/a}{pokemonGO}{ a $\in$ posiciones(mapa(pg)) $\land$ ($\forall$ b: posicion)((b $\in$ significados(pokesalvajes(pg))) distancia(a,b) $\geq$ 5 )}


%\tadOperacion{agPokemon}{pokemonGO/pg, pokemon/p, posicion/a}{pokemonGO}{ a $\in$ posiciones(mapa(pg)) $\land$(($\forall$ poke: claves(pokesalvajes(pg)))($\forall$ p: posicion $\in$ obtener(poke,pokesalvajes(pg)) distancia(a,pos) $\geq$ 5 )))}

\tadOperacion{Conectarse}{pokemonGO/pg, jugador/j, posicion/p}{pokemonGO}{ j $\in$ jugDesconectados(pg) $\land$ p $\in$ posiciones(mapa(pg))}


\tadOperacion{Desconectarse}{pokemonGO/pg, jugador/j}{pokemonGO}{ j $\in$ jugConectados(pg)} %%deberia ir??

\tadOperacion{Moverse}{pokemonGO/pg, jugador/j, posicion/p}{pokemonGO}{ j $\in$ jugConectados(pg) $\land$ p $\in$ posiciones(mapa(pg))}


%OtrasOperaciones
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadOtrasOperaciones
\tadAlinearFunciones{conjuntoPokemonEnPos}

\tadOperacion{IndiceDeRareza}{pokemonGO/pg,pokemon/p}{nat}{p $\in$ pokesalvajes(pg) $\lor$ (\exists j : jugador)j $\in$ jugadores(pg) $\land_{L}$ p $\in$ capturados(pg,j) }
\tadOperacion{PokemonDelTipo}{pokemonGO/pg,poke/p}{nat}{p $\in$ pokesalvajes(pg) $\lor$ (\exists j : jugador)j $\in$ jugadores(pg) $\land_{L}$ p $\in$ capturados(pg,j) }
\tadOperacion{PokemonDelTipoAux}{pokemonGO/pg,conj/cj,pokemon/poke}{nat}{p $\in$ pokesalvajes(pg) $\lor$ (\exists j : jugador)j $\in$ jugadores(pg) $\land_{L}$ p $\in$ capturados(pg,j) }
\tadOperacion{PokemonsJug}{multiconj(pokemon)/mcp,pokemon/poke}{nat}{}
\tadOperacion{CantPokeSalvajes}{pokemonGo/pg,conj(pokemon)/cpok}{nat}{}
\tadOperacion{CantCapturados}{pokemonGo/pg,conj(jugador)/cpok}{nat}{}




\tadOperacion{jugadores}{pokemonGO/pg}{conj(jugador)}{}
\tadOperacion{haypokemon}{pokemonGO/pg, posicion/p}{bool}{}
\tadOperacion{existeUnPoke}{dicc(pokemon, conj(posicion)), conj(posicion), posicion/p}{bool}{}
\tadOperacion{pokemonenpos}{pokemonGO/pg, posicion/p}{pokemon}{ p $\in$ posiciones(mapa(pg)) $\land$ haypokemon(pg,p)}
\tadOperacion{pokeenposaux}{pokemonGO/pg, conj(pokemon)/cp, posicion/p}{pokemon}{ vacio?(claves)== false}
\tadOperacion{conjuntoPokemonEnPos}{conj(posicion)/cpos, pokemonGO/pg}{multiconj(pokemon)}{}
\tadOperacion{algunoLlegaADiez}{conj(posicion)/cp, pokemonGO/pg,  posicion/p}{bool}{ cpos $\cup$ posiciones(mapa(pg)) $\land$ p $\in$ posiciones(mapa(pg))}
\tadOperacion{LlegaADiez}{conj(posicion)/cpos , conj(pokemon)/cp, posicion/p}{conj(posicion)}{cpos $\subseteq$ posiciones(mapa(pg)) $\land$ p $\in$ posiciones(mapa(pg))}
\tadOperacion{jugEnRango}{pokemonGO/pg, conj(posicion)/cpos, conj(jugador)/cjug, posicion/p}{conj(jugador)}{cpos $\subseteq$ posiciones(mapa(pg)) $\land$ p $\in$ posiciones(mapa(pg)) $\land$ cjug $\subseteq$ jugadoresConectados(cp)}
\tadOperacion{DistanciaDeCaptura}{posicion/p, conj(posicion)/cpos}{conj(posicion)}{}
\tadOperacion{jugCapturadores}{pokemonGO/pg, conj(jugador)/cjug, posicion/p}{conj(jugador)}{cjug $\subseteq$ jugadoresConectados(pg) $\land$ p $\in$ posiciones(mapa(pg))}
\tadOperacion{PokemonEnRango}{posicion/p, conj(posicion)/cpos, pokemonGO/pg}{pokemon}{ p $\cup$ cpos $\in$ posiciones(mapa(pg)) $\land$ ($\exists$ p':pos)(p $\in$ cpos) distancia(p',p)$\leq$2}
\tadOperacion{buscarPoke}{conj(pokemon)/cpok, dicc(pokemon, conj(posicion))/dicc, posicion/p}{pokemon}{ p $\in$ posiciones(mapa(pg)) $\land$  p $\in$ significados(dicc)}
\tadOperacion{significados}{dicc($\alpha$, $\beta$)/dicc}{multiconj($\betha$)}{}
\tadOperacion{significadosaux}{dicc($\alpha$, $\beta$)/dicc, conj($\alpha$)/cla}{multiconj($\betha$)}{}
% no se si deberia ser multiconjunto.
\tadOperacion{SacarDeDic}{dicc(pokemon, conj(posicion))/dicc, conjunto(posicion)cpos}{dicc(pokemon,conjunto(posicion))}{cpos $\subseteq$ significados(dicc)}
\tadOperacion{Redefinir}{dicc(pokemon, conj(posicion))/dicc, conjunto(pokemon)cpoke, conjunto(posicion)/cpos}{dicc(pokemon,cojunto(posicion))}{}
\tadOperacion{PokemonsDelTipo}{pokemonGO/pg, pokemon/poke}{nat}{}
\tadOperacion{PokeDelTipoAux}{pokemonGO/pg, conj(jugador)/cj, pokemon/poke}{nat}{}
\tadOperacion{PokemonsJug}{multiconj(pokemon)/mcp, pokemon/poke}{nat}{}
\tadOperacion{PokeTotal}{pokemonGO/pg}{nat}{}
\tadOperacion{CantPokeSalvajes}{pokemonGO/pg, conj(pokemon)/cpok}{nat}{}
\tadOperacion{CantCapturados}{pokemonGO/pg, conj(jugador)/cj}{nat}{}

%Axiomas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



\tadAxiomas[\paratodo{pokemonGO}{pg}, \paratodo{posicion}{p,a}, \paratodo{jugador}{j,j'}, \paratodo{pokemon}{poke}]
\tadAlinearAxiomas{jugDesconectados(agPokemon(pg, poke, a))}



%OB jugConectados
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxioma{jugConectados(NvoJuego(m))}{\textbf{vacio}}
\tadAxioma{jugConectados(agJugador(pg,j,p))}{ Ag(j, jugConectados(pg)) }
\tadAxioma{jugConectados(agPokemon(pg, poke, a ))}{jugConectados(pg)}
\tadAxioma{jugConectados(Conectarse(pg,j, p))}{Ag(j, jugConectados(pg))}
\tadAxioma{jugConectados(Desconectarse(pg, j))}{jugConectados(pg) - \{j\} }
\tadAxioma{jugConectados(Moverse(pg, j, p))}{\IF (sanciones(pg, j) == 4 $\land$ ((distancia(posicionActual(pg,j), p) $\geq$ 10) $\lor$  ( p $\notin$ caminos(mapa(pg), posicionActual(pg,j))))) THEN jugConectados(pg) -\{ j\} ELSE jugConectados(pg) FI }

\vskip12pt

%OB jugDesconectados
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxioma{jugDesconectados(NvoJuego(m))}{\textbf{vacio}}
\tadAxioma{jugDesconectados(agJugador(pg,j,p))}{jugDesconectados(pg)}
\tadAxioma{jugDesconectados(agPokemon(pg,poke,a))}{ jugDesconectados(pg) }
\tadAxioma{jugDesconectados(Conectarse(pg,j, p))}{ jugDesconectados(pg) - \{j\}}
\tadAxioma{jugDesconectados(Desconectarse(pg, j))}{Ag(j, jugDesconectados(pg)) }
\tadAxioma{jugDesconectados(Moverse(pg, j, p))}{jugDesconectados(pg)}

\vskip12pt


%OB ex-Jugadores
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxioma{ex-Jugadores(NvoJuego(m))}{\textbf{vacio}}
\tadAxioma{ex-Jugadores(agJugador(pg,j,p))}{ex-Jugadores(pg)}
\tadAxioma{ex-Jugadores(agPokemon(pg,poke,a))}{ex-Jugadores(pg) }
\tadAxioma{ex-Jugadores(Conectarse(pg,j, p))}{ex-Jugadores(pg)}
\tadAxioma{ex-Jugadores(Desconectarse(pg, j))}{ex-Jugadores(pg)}
\tadAxioma{ex-Jugadores(Moverse(pg, j, p))}{{\IF (sanciones(pg, j) == 4 $\land$ ((distancia(posicionActual(pg,j), p) $\geq$ 10) $\lor$  ( p $\notin$ caminos(mapa(pg), posicionActual(pg,j))))) THEN Ag(j, ex-Jugadores(pg)) ELSE ex-Jugadores(pg) FI }}

\vskip12pt



%OB mapa
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{mapa(NvoJuego(m))}{m}
\tadAxioma{mapa(agJugador(pg,j,p))}{  mapa(pg) }
\tadAxioma{mapa(agPokemon(pg, poke, a ))}{mapa(pg)}
\tadAxioma{mapa(Conectarse(pg,j, p))}{ mapa(pg)}
\tadAxioma{mapa(Desconectarse(pg, j))}{mapa(pg)}
\tadAxioma{mapa(Moverse(pg, j, p))}{mapa(pg)}

\vskip12pt


%OB pokesalvaje
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{pokesalvajes(NvoJuego(m))}{\textbf{vacio}}
\tadAxioma{pokesalvajes(agJugador(pg,j,p))}{  pokesalvejes(pg) }%%puede crear opciones de captura
\tadAxioma{pokesalvajes(agPokemon(pg, poke, a ))}{\IF $\neg$ \ def?(poke,pokesalvajes(pg)) THEN definir(poke, a, pokesalvajes(pg)) ELSE definir(p, Ag(a,obtener(p, pokesalvages(pg))), pokesalvajes(pg)) FI}
\tadAxioma{pokesalvajes(Conectarse(pg,j, p))}{ pokesalvejes(pg)}%puede crear opciones de captura
\tadAxioma{pokesalvajes(Desconectarse(pg, j))}{pokesalvejes(pg)}%puede crear opciones de captura
\tadAxioma{pokesalvajes(Moverse(pg, j, p))}{\IF AlgunollegaADiez(significados(pokesalvaje(pg)), pg, p) THEN SacarDeDic(pokesalvaje(pg), lleganADiez(significados(pokesalvajes(pg)),pg, p))   ELSE pokesalvajes(pg)  FI}% crea opciones de captura

\vskip12pt

%OB posicionactual
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxioma{posicionActual(agJugador(pg,j,p), j')}{ \IF j' == j THEN p ELSE posicionActual(pg, j') FI }
\tadAxioma{posicionActual(agPokemon(pg, poke, a ),j)}{posicionActual(pg,j)}
\tadAxioma{posicionActual(Conectarse(pg,j, p), j')}{\IF j' == j THEN p ELSE posicionActual(pg, j') FI}
\tadAxioma{posicionActual(Desconectarse(pg, j), j')}{posicionActual(p,j') }%%Verr
\tadAxioma{posicionActual(Moverse(pg, j, p).j')}{ \IF j' == j THEN p ELSE posicionActual(pg, j') FI}  %%Aca tengo dudas....porque al moverse puedfe ser que se expulse, me parece que no hay lio, pero no se....

\vskip12pt



%OB capturados
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxioma{capturados(agJugador(pg,j,p), j')}{ \IF j' == j THEN \textbf{vacio} ELSE capturados(pg, j') FI }
\tadAxioma{capturados(agPokemon(pg, poke, a ),j')}{ capturados(pg, j')}
\tadAxioma{capturados(Conectarse(pg,j, p), j')}{\IF (j' == j) THEN capturados(pg, j') ELSE {\IF AlgunollegaADiez(significados(pokesalvaje(pg)), pg, p) $\land$ j' $==$ dameUno(jugEnRango(pg, lleganADiez(significados(pokesalvajes(pg)), pg, p), jugadoresConectados(pg), p)) THEN Ag(PokemonEnRango(p, lleganADiez(significados(pokesalvajes(pg)), pg, p), capturados(pg, j')))  ELSE capturados(pg, j')  FI} FI}
\tadAxioma{capturados(Desconectarse(pg, j), j')}{ capturados(pg, j') }%%Verr
\tadAxioma{capturados(Moverse(pg, j, p).j')}{ \IF j' == j THEN capturados(pg, j') ELSE {\IF AlgunollegaADiez(significados(pokesalvaje(pg)), pg, p) $\land$ j' $==$ dameUno(jugEnRango(pg, lleganADiez(significados(pokesalvajes(pg)), pg, p), jugadoresConectados(pg), p)) THEN Ag(PokemonEnRango(p, lleganADiez(significados(pokesalvajes(pg)), pg, p), capturados(pg, j')))  ELSE capturados(pg, j')  FI} FI} 


\vskip12pt




%OB sanciones
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxioma{sanciones(agJugador(pg,j,p), j')}{  \IF j' == j THEN 0 ELSE sanciones(pg, j') FI}
\tadAxioma{sanciones(agPokemon(pg, poke, a ),j )}{sanciones(pg, j)}
\tadAxioma{sanciones(Conectarse(pg,j, p), j')}{sanciones(pg, j')}
\tadAxioma{sanciones(Desconectarse(pg, j), j')}{sanciones(pg, j')}
\tadAxioma{sanciones(Moverse(pg, j, p),j')}{\IF ((j' == j) $\land$ ((distancia(posicionActual(pg,j), p) $\geq$ 10) $\lor$  ( p $\notin$ caminos(mapa(pg), posicionActual(pg,j))))) THEN 1 + sanciones(pg,j')  ELSE sanciones(pg, j') FI}

\vskip12pt


%OB contadorPos
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxioma{contadorPos(NvoJuego(m),p')}{0}
\tadAxioma{contadorPos(agJugador(pg,j,p), p')}{contadorPos(pg,p')}
\tadAxioma{contadorPos(agPokemon(pg, p, a ), p')}{\IF (p==p') THEN 0 ELSE contadorPos(pg,p') FI}
\tadAxioma{contadorPos(Conectarse(pg,j, p), p' )}{\IF distancia(p,p')$\>$2 THEN{\IF contadorPos(pg,p')$\<$ 9 THEN contadorPos(pg, p') + 1 ELSE 0 FI} ELSE contadorPos(pg,p') FI}
\tadAxioma{contadorPos(Desconectarse(pg, j), p' )}{ contadorPos(pg,p')}
\tadAxioma{contadorPos(Moverse(pg, j, p), p')}{\IF distancia(p,p') > 2 THEN{\IF contadorPos(pg,p') < 9 THEN contadorPos(pg, p') + 1 ELSE 0 FI} ELSE{\IF distancia(posicionActual(pg,j), p') > 2 THEN 0  ELSE contadorPos(pg,p') FI} FI}

\vskip12pt



%oo otras op
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%oo jugadores
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{jugadores(pg)}{jugConectados(pg) \ $\cup$ \ jugDesconectados(pg) }
\vskip12pt

%oo haypokemon
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{haypokemon(pg,p)}{existeUnPoke(pokesalvajes(pg),claves(pokesalvajes(pg)),p)}
\tadAxioma{existeUnPoke(d,c,p)}{\IF vacio?(c) THEN \textbf{false} ELSE {\IF p $\in$ obtener(dameUno(c), d) THEN \textbf{true} ELSE existeUnPoke(d, sinUno(c),p) FI} FI}
\vskip12pt

%oo pokemonenpos
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{pokemonenpos(pg,p)}{pokeenposaux(pg, claves(pokesalvaje(pg), p))}
\vskip12pt

%oo pokemonenposaux
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{pokeenposaux(pg, claves, p)}{\IF (vacio?(claves)) THEN false ELSE {\IF p $\in$ obtener(dameUno(claves), pokesalvaje(pg)) THEN p ELSE pokeenposaux(pg, sinUno(claves), p) )FI} FI} %debido a que nos aseguramos que este antes de usarlo no se indefine.
\vskip12pt



%oo algunoLlegaADiez
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{algunoLlegaADiez(cpos,pg,p)}{\IF vacio?(cpos) THEN false ELSE {\IF( contadorpos(pg, dameUno(cpos)) == 9 $\land$ distancia(p, dameUno(cpos) $>$ 2)) THEN true ELSE algunoLlegaADiez(sinUno(cpos), pg, p)  FI} FI}
\vskip12pt

%oo LleganADiez
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{LleganADiez(cpos,pg,p)}{\IF vacio?(cpos) THEN \textbf{vacio} ELSE {\IF( contadorpos(pg, dameUno(cpos)) == 9 $\land$ distancia(p, dameUno(cpos) $>$ 2)) THEN Ag(dameUno(cpos), LleganADiez(sinUno(cpos), pg, p)) ELSE LleganADiez(sinUno(cpos), pg, p)  FI} FI}
\vskip12pt



%oo conjuntoPokeEnPos
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{conjuntoPokeEnPos(cpos, pg)}{\IF vacio?(cpos) THEN $ \textbf{vacio}$ ELSE Ag(pokemonenpos(pg, dameUno(cpos))  $\cup$ conjuntoPokeEnPos(pg, sinUno(cpos) )) FI}




%OO jugEnRango
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\tadAxioma{jugEnRango(pg, cpos, cjug,  p)}{\IF DistanciaDeCaptura(p, cpos) ==\textbf{vacio}  THEN \textbf{vacio} ELSE  jugCapturadores(pg, cpos, cjug, dameUno(DistanciaDeCaptura(p, cpos))) FI}
\vskip12pt
%OO DistanciaDeCaptura
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxioma{DistanciaDeCaptura(p, cpos)}{\IF vacio?(cpos)  THEN \textbf{vacio} ELSE {\IF  distancia(p, dameUno(cpos))$\leq$ 2 THEN Ag(dameUno(cpos), DistanciaDeCaptura(p, sinUno(cpos))) ELSE DistanciaDeCaptura(p, sinUno(cpos))    FI}  FI}

%Aclaracion, debido a que no puede haber dos pokemon a menos de distancia 5, este conjunto va a teren 1 elemento
\vskip12pt
%OO jugCapturadores
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxioma{jugCapturadores(pg, cjug, p)}{\IF vacio?(cjug)  THEN \textbf{vacio} ELSE {\IF  distancia(p, posicionActual(dameUno(cjug), pg))$\leq$ 2 THEN Ag(dameUno(cjug), jugCapturadores(pg, sinUno(cjug), p)) ELSE jugCapturadores(pg, sinUno(cjug), p)    FI}  FI}
\vskip12pt

%OO PokemonEnRango
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\tadAxioma{PokemonEnRango(p, cpos, pg)}{\IF  distancia(p, dameUno(cpos))$\leq$ 2 THEN buscarPoke(claves(pokesalvajes(pg)),pokesalvajes(pg), dameUno(cpos)) ELSE PokemonEnRango(p, sinUno(cpos), pg)    FI} 
\vskip12pt
%OO buscarPoke
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{buscarPoke(cpok, dicc, p)}{\IF p $\in$ obtener(dameUno(cpok), dicc) THEN dameUno(cpok) ELSE buscarPoke(sinUno(cpok), dicc, p)    FI} 
\vskip12pt
%OO significados
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{significados(dicc)}{ significadosAux(dicc, claves(dicc))}
\vskip12pt
%OO significadosaux
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{significadosaux(dicc, cla)}{ \IF vacio?(cla) THEN \textbf{vacio} ELSE obtener(dameUno(cla), dicc) $\cup$ significadoaux(dicc,sinUno(cla)) FI}
\vskip12pt

%OO sacarDeDicc
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{sacarDeDicc(dicc, cpos)}{ \IF vacio?(cpos) THEN dicc ELSE  Redefinir(sacarDeDicc(dicc, sinUno(cpos)), buscarPoke(claves(dicc), dicc, dameUno(cpos)), obtener(buscarPoke(claves(dicc), dicc, dameUno(pos)), dicc)-dameUno(cpos)) FI}
\vskip12pt


%OO Redefinir
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{redefinir(dicc, cla, cpos)}{ \IF $\not$ definida(dicc, cla) THEN definir(dicc, cla,cpos) ELSE definir(borrar(dicc, cla), cla, cpos) FI}
\vskip12pt


%OO IndiceDeRareza
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{IndiceDeRareza(pg, poke)}{ 100 - (div(PokemonsDelTipo(pg, poke)x100, PokeTotal(pg)))}
\vskip12pt 
%OO PokemonsDelTipo
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{PokemonsDelTipo(pg, poke)}{$\#$(obtener(poke, pokesalvajes(pg))) + PokeDelTipoAux(pg, jugadores(pg), poke)}
\vskip12pt
%OO PokeDelTipoAux
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{PokeDelTipoAux(pg, cj, poke)}{\IF \textbf{vacio?(cj)} THEN 0 ELSE {\IF poke $\in$ capturados(pg, dameUno(cj)) THEN PokemonsJug(capturados(pg, dameUno(cj)), poke) + PokeDelTipoAux(pg, sinUno(cj), poke) ELSE PokeDelTipoAux(pg, sinUno(cj), poke)   FI} FI}
\vskip12pt
%OO PokemonsJug
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{PokemonsJug(mcp, poke)}{\IF \textbf{vacio?(mcp)} THEN 0 ELSE { \IF (poke == dameUno(mcp)) THEN 1 + PokemonsJug(sinUno(mcp), poke) ELSE PokemonsJug(sinUno(mcp), poke)  FI} FI}
\vskip12pt
%OO PokeTotal
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{PokeTotal(pg)}{CantPokeSalvajes(pg, claves(pokesalvajes(pg))) + CantCapturados(pg, jugadores(pg))}
\vskip12pt
%OO CantPokeSalvajes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{CantPokeSalvajes(pg, cpok)}{\IF \textbf{vacio?(cpok)} THEN 0 ELSE $\#$(obtener(dameUno(cpok), pokesalvajes(pg))) + CantPokeSalvajes(pg, sinUno(cpok)) FI}
\vskip12pt
%OO CantCapturados
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{CantCapturados(pg, cj)}{\IF \textbf{vacio?(cj)} THEN 0 ELSE $\#$(capturados(pg, dameUno(cj))) + CantCapturados(pg, sinUno(cj)) FI}
\vskip12pt





\end{tad}

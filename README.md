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

\tadAxioma{restaEntera(n,m)}{\IF (n == 0) THEN m ELSE {\IF (n == 0) THEN m ELSE restaEntera(prev(n), prev(m)) FI} FI} 

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

\tadAxiomas[\paratodo{nat}{n, m, p, q} \paratodo{posicion}{a, b}]
\tadAlinearAxiomas{restaEntera(n,m)}
\tadAxioma{distancia(a,b)}{raiz((restaEntera($\Pi_1$(a), $\Pi_1$(b)))**2) + ((restaEntera($\Pi_2$(a), $\Pi_2$(b)))**2))}

\end{tad}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newpage

\section{TAD \tadNombre{Mapa}}

\begin{tad}{\tadNombre{Mapa}}
\tadIgualdadObservacional{m}{m'}{mapa}{($\forall$ p:posicion)((p $\in$ posiciones(m)) == (p $\in$ posiciones(m'))) $\land$ ($\forall$ p:posicion)(p $\in$ posiciones(m)) $\impluego$ conectadas(m,p) == conectadas(m',p)}

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
\tadAxiomas[\paratodo{mapa}{m} \paratodo{nat}{n, m} \paratodo{posicion}{p,q,p'} \paratodo{conj(posicion)}{cp, cm, cq}]

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
{CaminosAux(m, p, \textbf{vacio}) - p}
\vskip12pt

% OO caminosAux
\tadAxioma{CaminosAux(m,p, res)}{ \IF vacio?(conectadas(m,p) - res) THEN res ELSE CaminosAux(m, dameUno(conectadas(m,p)- res ), (res $\cup$ conectadas(m,p)) $\cup$ p ) $\cup$ caminosRecursivos(m, sinUno(conectadas(m,p) - res  ),  res $\cup$ conectadas(m,p) $\cup$ p)) FI}
\vskip12pt

% OO caminosRecursivos
\tadAxioma{caminosRecursivos(m, cp, res  )}{\IF vacio? cp THEN res ELSE CaminosAux(m, dameUno(cp), res ) $\cup$ caminosRecursivos(m, sinUno(cp), res) FI} 



\vskip12pt


\end{tad}

\newpage

\section{TAD \tadNombre{PokemonGo}}




\begin{tad}{\tadNombre{PokemonGo}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadIgualdadObservacional{pg}{pg'}{PokemonGo}{($\forall$ p:posicion)((p $\in$ posiciones(m)) == (p $\in$ posiciones(m'))) $\land$ ($\forall$ p:posicion)(p $\in$ posiciones(m)) $\impluego$ conectadas(m,p) == conectadas(m',p)}

\tadGeneros{pokemonGO}
\tadExporta{pokemoGO, generadores, observadores, otras operaciones}
\tadUsa{\tadNombre{Posicion}, \tadNombre{Bool}, \tadNombre{Nat}, \tadNombre{conj},\tadNombre{Multiconj}, \tadNombre{dicc} }


%Observadores
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadObservadores
\tadAlinearFunciones{pokesalvaje}

\tadOperacion{jugConectados}{pokemonGO/pg}{conj(jugadores)}{}
\tadOperacion{jugDesconectados}{pokemonGO/pg}{conj(jugadores)}{}
\tadOperacion{mapa}{pokemonGO}{mapa}{}
\tadOperacion{pokesalvajes}{pokemonGO/pg}{dicc(pokemon, conj(posiciones))}{}
\tadOperacion{capturados}{pokemonGO/pg, jugador/j}{multiconj(pokemon)}{j $\in$ jugadores(pg)}
\tadOperacion{posicion actual}{pokemonGO/pg, jugador/j}{posicion}{j $\in$ jugadores(pg)}
\tadOperacion{sanciones}{pokemonGO/pg, jugador/j}{nat}{j $\in$ jugadores(pg)}
\tadOperacion{contadorpos}{pokemonGO/pg, posicion/p}{nat}{p $\in$ posiciones(mapa(pg))} %aqui puede ser que me falte reestriccion

%Generadores
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadGeneradores

\tadAlinearFunciones{agPokemon~}

\tadOperacion{nvoJuego}{mapa}{pokemonGO}{}

\tadOperacion{agJugador}{pokemonGO/pg, jugador/j, posicion/p }{pokemonGO}{p $\in$ posiciones(mapa(pg)) $\land$ j $\notin$ jugadores(pg) }


\tadOperacion{agPokemon}{pokemonGO/pg, pokemon/p, posicion/a}{pokemonGO}{ a $\in$ posiciones(mapa(pg)) $\land$ (($\forall$ b: posicion, b $\in$ significados(pokesalvajes(pg)) ) distancia(a,b) $\geq$ 5 )))}


%\tadOperacion{agPokemon}{pokemonGO/pg, pokemon/p, posicion/a}{pokemonGO}{ a $\in$ posiciones(mapa(pg)) $\land$(($\forall$ poke: claves(pokesalvajes(pg)))($\forall$ p: posicion $\in$ obtener(poke,pokesalvajes(pg)) distancia(a,pos) $\geq$ 5 )))}

\tadOperacion{Conectarse}{pokemonGO/pg, jugador/j, posicion/p}{pokemonGO}{ j $\in$ jugDesconectados(pg) $\land$ p $\in$ posiciones(mapa(pg))}


\tadOperacion{Desconectarse}{pokemonGO/pg, jugador/j}{pokemonGO}{ j $\in$ jugConectados(pg)} %%deberia ir??

\tadOperacion{Moverse}{pokemonGO/pg, jugador/j, posicion/p}{pokemonGO}{ j $\in$ jugConectados(pg) $\land$ p $\in$ posiciones(mapa(pg))}


%OtrasOperaciones
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadOtrasOperaciones
\tadAlinearFunciones{IndiceDeRareza}

\tadOperacion{IndiceDeRareza}{pokemonGO/pg,pokemon/p}{nat}{p $in$ pokesalvajes(pg)}
\tadOperacion{jugadores}{pokemonGO/pg}{conj(jugadores)}{}
\tadOperacion{haypokemon}{pokemonGO/pg, posicion/p}{bool}{}
\tadOperacion{existeUnPoke}{diccionario(pokemon,conj(posicion)),conj(posicion), posicion/p}{bool}{}
\tadOperacion{pokemonenpos}{pokemonGO/pg, posicion/p}{pokemon}{ p $\in$ posiciones(mapa(pg)) \land haypokemon(pg,p)}
\tadOperacion{pokeenposaux}{pokemonGO/pg, conjunto(pokemon)/cp, posicion/p}{pokemon}{ vacio(claves)== false}
\tadOperacion{conjuntoPokemonEnPos}{conj(posicion)/cpos, pokemonGO/pg}{multiconj(pokemon)}{}
\tadOperacion{algunoLlegaADiez}{conjunto(posicion)/cp, pokemonGO/pg,  posicion/p}{bool}{ cpos \cup posiciones(mapa(pg)) $\land$ p $\in$ posiciones(mapa(pg))}
\tadOperacion{LlegaADiez}{conjunto(posicion)/cpos , conjunto(pokemon)/cp, posicion/p}{conjunto(posiciones)}{cpos \subseteq posiciones(mapa(pg)) $\land$ p $\in$ posiciones(mapa(pg))}

%Axiomas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



\tadAxiomas[\paratodo{pokemonGO}{pg} \paratodo{posicion}{x,y} \paratodo{jugador}{j} \paratodo{pokemon}{p}]
\tadAlinearAxiomas{jugDesconectados(agPokemon(pg, p, a))}


\tadAxioma{jugadores(pg)}{jugConectados(pg) \ \cup \ jugDesconectados(pg) }
\vskip12pt

%OB jugConectados
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxioma{jugConectados(NvoJuego(m))}{\textbf{vacio}}
\tadAxioma{jugConectados(agJugador(pg,j,p))}{ Ag(j, jugConectados(pg)) }
\tadAxioma{jugConectados(agPokemon(pg, p, a ))}{jugConectados(pg)}
\tadAxioma{jugConectados(Conectarse(pg,j, p))}{Ag(j, jugConectados(pg))}
\tadAxioma{jugConectados(Desconectarse(pg, j))}{jugConectados(pg) - j }
\tadAxioma{jugConectados(Moverse(pg, j, p))}{\IF (sanciones(pg, j) == 4 $\land$ (distancia(posicionActual(pg,j), p) $\geq$ 10) $\lor$  ( p $\notin$ conectadas(posicionActual(pg,j)) ) ) THEN jugConectados(pg) -\{ j\} ELSE jugConectados(pg) FI }

\vskip12pt

%OB jugDesconectados
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxioma{jugDesconectados(NvoJuego(m))}{\textbf{vacio}}
\tadAxioma{jugDesconectados(agJugador(pg,j,p))}{jugDesconectados(pg)}
\tadAxioma{jugDesconectados(agPokemon(pg,p,a))}{ jugDesconectados(pg) }
\tadAxioma{jugDesconectados(Conectarse(pg,j, p))}{ jugDesconectados(pg) -j}
\tadAxioma{jugDesconectados(Desconectarse(pg, j))}{Ag(j, jugDesconectados(pg)) }
\tadAxioma{jugDesconectados(Moverse(pg, j, p))}{jugDesconectados(pg)}

\vskip12pt

%OB mapa
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{mapa(NvoJuego(m))}{m}
\tadAxioma{mapa(agJugador(pg,j,p))}{  mapa(pg) }
\tadAxioma{mapa(agPokemon(pg, p, a ))}{mapa(pg)}
\tadAxioma{mapa(Conectarse(pg,j, p))}{ mapa(pg)}
\tadAxioma{mapa(Desconectarse(pg, j))}{mapa(pg)}
\tadAxioma{mapa(Moverse(pg, j, p))}{mapa(pg)}

\vskip12pt


%OB pokesalvaje
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{pokesalvajes(NvoJuego(m))}{\textbf{vacio}}
\tadAxioma{pokesalvajes(agJugador(pg,j,p))}{  pokesalvejes(pg) }%%puede crear opciones de captura
\tadAxioma{pokesalvajes(agPokemon(pg, p, a ))}{\IF $\neg$ \ def?(p,pokesalvajes(pg)) THEN definir(pokesalvajes(pg), p, {a}) ELSE definir(pokesalvajes(pg), p, Ag(a,obtener(pokesalvages(pg), p))) FI}
\tadAxioma{pokesalvajes(Conectarse(pg,j, p))}{ pokesalvejes(pg)}%puede crear opciones de captura
\tadAxioma{pokesalvajes(Desconectarse(pg, j))}{pokesalvejes(pg)}%puede crear opciones de captura
\tadAxioma{pokesalvajes(Moverse(pg, j, p))}{\IF AlgunollegaADiez(significados(pokesalvaje(pg), pg, p)) THEN pokesalvaje(pg) - conjuntoPokeEnPos(lleganADiez(significados(pokesalvajes(pg)),pg, p))   ELSE pokesalvajes(pg)  FI}% crea opciones de captura

\vskip12pt

%OB posicionactual
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxioma{posicionActual(agJugador(pg,j,p), j')}{ \IF j' == j THEN p ELSE posicionActual(pg, j') FI }
\tadAxioma{posicionActual(agPokemon(pg, p, a ),j)}{posicionActual(pg,j)}
\tadAxioma{posicionActual(Conectarse(pg,j, p), j')}{\IF j' == j THEN p ELSE posicionActual(pg, j') FI}
\tadAxioma{posicionActual(Desconectarse(pg, j), j')}{posicionActual(p,j') }%%Verr
\tadAxioma{posicionActual(Moverse(pg, j, p).j')}{ \IF j' == j THEN p ELSE posicionActual(pg, j') FI}  %%Aca tengo dudas....porque al moverse puedfe ser que se expulse, me parece que no hay lio, pero no se....

\vskip12pt

%OB sanciones
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tadAxioma{sanciones(agJugador(pg,j,p), j')}{  \IF j' == j THEN 0 ELSE sanciones(pg, j') FI}
\tadAxioma{sanciones(agPokemon(pg, p, a ),j )}{sanciones(pg, j)}
\tadAxioma{sanciones(Conectarse(pg,j, p), j')}{sanciones(pg, j')}
\tadAxioma{sanciones(Desconectarse(pg, j), j')}{sanciones(pg, j')}
\tadAxioma{sanciones(Moverse(pg, j, p),j')}{\IF (j' == j) $\land$ distancia (posicionActual(pg,j), p) $\geq$ 10  THEN 1 + sanciones(pg,j')  ELSE sanciones(pg, j') FI}

\vskip12pt

%oo otras op
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%oo jugadores
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{jugadores(pg)}{jugConectados(pg) \ \cup \ jugDesconectados(pg) }
\vskip12pt

%oo haypokemon
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{haypokemon(pg,p)}{existeUnPoke(pokesalvajes(pg),claves(pokesalvajes(pg)),p)}
\tadAxioma{existeUnPoke(d,c,p)}{\IF vacio?(c) THEN \textbf{false} ELSE {\IF p $\in$ obtener(d,dameUno(c)) THEN \textbf{true} ELSE existeUnPoke(d, sinUno(c),p) FI} FI}
\vskip12pt

%oo pokemonenpos
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{pokemonenpos(pg,p)}{pokeenposaux(pg, claves(pokesalvaje(pg), p))}
\vskip12pt

%oo pokemonenposaux
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{pokeenposaux(pg, claves, p)}{ \IF p $\in$ obtener(pokesalvaje(pg),dameUno(claves)) THEN p ELSE pokeenposaux(pg, sinUno(claves), p) )FI} %debido a que nos aseguramos que este antes de usarlo no se indefine.
\vskip12pt



%oo algunoLlegaADiez
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{algunoLlegaADiez(cpos,pg,p)}{\IF vacio(cpos) THEN false ELSE {\IF( contadorpos(pg, dameUno(cpos)) == 9 $\land$ distancia(p, dameUno(cpos) $>$ 2)) THEN true ELSE algunoLlegaADiez(sinUno(cpos), pg, p)  FI} FI}
\vskip12pt

%oo LleganADiez
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{LleganADiez(cpos,pg,p)}{\IF vacio(cpos) THEN \textbf{vacio} ELSE {\IF( contadorpos(pg, dameUno(cpos)) == 9 $\land$ distancia(p, dameUno(cpos) $>$ 2)) THEN Ag(dameUno(cpos), LleganADiez(sinUno(cpos), pg, p) ELSE LleganADiez(sinUno(cpos), pg, p)  FI} FI}
\vskip12pt



%oo conjuntoPokeEnPos
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\tadAxioma{conjuntoPokeEnPos(cpos, pg)}{\IF vacio(cpos) THEN $ \textbf{vacio}$ ELSE Ag(pokemonenpos(pg, dameUno(cpos))  $\cup$ conjuntoPokeEnPos(pg, sinUno(cpos) )) FI}

\end{tad}

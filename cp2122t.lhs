\documentclass[a4paper]{article}
\usepackage[a4paper,left=3cm,right=2cm,top=2.5cm,bottom=2.5cm]{geometry}
\usepackage{palatino}
\usepackage[colorlinks=true,linkcolor=blue,citecolor=blue]{hyperref}
\usepackage{graphicx}
\usepackage{cp2122t}
\usepackage{subcaption}
\usepackage{trees}
\usepackage{adjustbox}
\usepackage{color}
\definecolor{red}{RGB}{255,  0,  0}
\definecolor{blue}{RGB}{0,0,255}
\def\red{\color{red}}
\def\blue{\color{blue}}
%================= local x=====================================================%
\def\getGif#1{\includegraphics[width=0.3\textwidth]{cp2122t_media/#1.png}}
\let\uk=\emph
\def\aspas#1{``#1"}
%================= lhs2tex=====================================================%
%include polycode.fmt
%format (div (x)(y)) = x "\div " y
%format succ = "\succ "
%format ==> = "\Longrightarrow "
%format map = "\map "
%format length = "\length "
%format fst = "\p1"
%format p1  = "\p1"
%format snd = "\p2"
%format p2  = "\p2"
%format Left = "i_1"
%format Right = "i_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format >< = "\times"
%format >|<  = "\bowtie "
%format |-> = "\mapsto"
%format . = "\comp "
%format .=?=. = "\mathbin{\stackrel{\mathrm{?}}{=}}"
%format (kcomp (f)(g)) = f "\kcomp " g
%format -|- = "+"
%format conc = "\mathsf{conc}"
%format summation = "{\sum}"
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (frac (a) (b)) = "\frac{" a "}{" b "}"
%format (uncurry f) = "\uncurry{" f "}"
%format (const (f)) = "\underline{" f "}"
%format TLTree = "\mathsf{TLTree}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
\def\ana#1{\mathopen{[\!(}#1\mathclose{)\!]}}
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format Either a b = a "+" b
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textsc{nb}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format outLTree = "\mathsf{out}"
%format inLTree = "\mathsf{in}"
%format inFTree = "\mathsf{in}"
%format outFTree = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format k1 = "k_1 "
%format k2 = "k_2 "
%format h1 = "h_1 "
%format h2 = "h_2 "
%format f1 = "f_1 "
%format f2 = "f_2 "
%format l1 = "l_1 "
%format map1 = "map_1 "
%format map2 = "map_2 "
%format map3 = "map_3"
%format l2 = "l_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format LTree = "{\LTree}"
%format FTree = "{\FTree}"
%format inNat = "\mathsf{in}"
%format (cata (f)) = "\cata{" f "}"
%format (cataNat (g)) = "\cataNat{" g "}"
%format (cataList (g)) = "\cataList{" g "}"
%format (anaList (g)) = "\anaList{" g "}"
%format Nat0 = "\N_0"
%format Rational = "\Q "
%format toRational = " to_\Q "
%format fromRational = " from_\Q "
%format muB = "\mu "
%format (frac (n)(m)) = "\frac{" n "}{" m "}"
%format (fac (n)) = "{" n "!}"
%format (underbrace (t) (p)) = "\underbrace{" t "}_{" p "}"
%format matrix = "matrix"
%%format (bin (n) (k)) = "\Big(\vcenter{\xymatrix@R=1pt{" n "\\" k "}}\Big)"
%format `ominus` = "\mathbin{\ominus}"
%format % = "\mathbin{/}"
%format <-> = "{\,\leftrightarrow\,}"
%format <|> = "{\,\updownarrow\,}"
%format `minusNat`= "\mathbin{-}"
%format ==> = "\Rightarrow"
%format .==>. = "\Rightarrow"
%format .<==>. = "\Leftrightarrow"
%format .==. = "\equiv"
%format .<=. = "\leq"
%format .&&&. = "\wedge"
%format cdots = "\cdots "
%format pi = "\pi "
%format (curry (f)) = "\overline{" f "}"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataFTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (anaLTree (x)) = "\mathopen{[\!(}" x "\mathclose{)\!]}"
%format delta = "\Delta "
\newlabel{eq:fokkinga}{{3.93}{110}{The mutual-recursion law}{section.3.17}{}}
%format (plus (f)(g)) = "{" f "}\plus{" g "}"
%format ++ = "\mathbin{+\!\!\!+}"
%format Integer  = "\mathbb{Z}"
\def\plus{\mathbin{\dagger}}

%---------------------------------------------------------------------------

\title{
          C??lculo de Programas
\\
          Trabalho Pr??tico
\\
          LEI+MiEI --- 2021/22
}

\author{
          \dium
\\
          Universidade do Minho
}


\date\mydate

\makeindex
\newcommand{\rn}[1]{\textcolor{red}{#1}}
\begin{document}

\maketitle

\begin{center}\large
\begin{tabular}{ll}
\textbf{Grupo} nr. & 3
\\\hline
a90234 & Filipa Rebelo
\\
a87956 & Joana Oliveira
\end{tabular}
\end{center}

\section{Pre??mbulo}

\CP\ tem como objectivo principal ensinar
a progra\-ma????o de computadores como uma disciplina cient??fica. Para isso
parte-se de um repert??rio de \emph{combinadores} que formam uma ??lgebra da
programa????o (conjunto de leis universais e seus corol??rios) e usam-se esses
combinadores para construir programas \emph{composicionalmente}, isto ??,
agregando programas j?? existentes.

Na sequ??ncia pedag??gica dos planos de estudo dos cursos que t??m
esta disciplina, opta-se pela aplica????o deste m??todo ?? programa????o
em \Haskell\ (sem preju??zo da sua aplica????o a outras linguagens
funcionais). Assim, o presente trabalho pr??tico coloca os
alunos perante problemas concretos que dever??o ser implementados em
\Haskell.  H?? ainda um outro objectivo: o de ensinar a documentar
programas, a valid??-los e a produzir textos t??cnico-cient??ficos de
qualidade.

Antes de abodarem os problemas propostos no trabalho, os grupos devem ler
com aten????o o anexo \ref{sec:documentacao} onde encontrar??o as instru????es
relativas ao sofware a instalar, etc.

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
module Main where
import Cp
import List hiding (fac)
import Nat
import LTree
import FTree
import Data.List hiding (find)
import Control.Monad
import Control.Applicative hiding ((<|>))
import System.Random hiding (split)
import System.Process
import Data.Hashable
import Test.QuickCheck hiding ((><),choose,collect)
import qualified Test.QuickCheck as QuickCheck
-- import Graphics.Gloss
-- import Graphics.Gloss.Interface.Pure.Game

main = undefined
\end{code}
%endif

\Problema

Num sistema de informa????o distribu??do, uma lista n??o vazia de transa????es
?? vista como um \textit\blockchain\ sempre que possui um valor de \textit{hash}
que ?? dado pela raiz de uma \MerkleTree\ que lhe est?? associada. Isto significa
que cada \textit\blockchain\ est?? estruturado numa \MerkleTree.
Mas, o que ?? uma \MerkleTree?

Uma \MerkleTree\ ?? uma \FTree\ com as seguintes propriedades:
%
\begin{eqnarray}
\fbox{
\begin{minipage}{.85\textwidth}
\begin{enumerate}
\item as folhas s??o pares (|hash|, transa????o) ou simplesmente o |hash| de uma transa????o;
\item os nodos s??o |hashes| que correspondem ?? concatena????o dos |hashes| dos filhos;
\item o |hash| que se encontra na raiz da ??rvore ?? designado |Merkle Root|; como se disse acima, corresponde ao valor de |hash| de todo o bloco de transa????es.
\end{enumerate}
\end{minipage}
}&&
     \label{eq:MTree_props}
\end{eqnarray}


\begin{figure}
\fbox{
\begin{minipage}{\textwidth}\em
\begin{itemize}
\item Se a lista for singular, calcular o |hash| da transa????o.

\item Caso contr??rio,
\begin{enumerate}
\item Mapear a lista com a fun????o |hash|.

\item Se o comprimento da lista for ??mpar, concatenar a lista com o seu ??ltimo valor (que fica duplicado). Caso contr??rio, a lista n??o sofre altera????es.

\item Agrupar a lista em pares.

\item Concatenar os |hashes| do par produzindo uma lista de (sub-)??rvores nas quais a cabe??a ter?? a respetiva concatena????o.

\item Se a lista de (sub-)??rvores n??o for singular, voltar ao passo 2 com a lista das cabe??as como argumento, preservando a lista de (sub-)??rvores. Se a lista for singular, chegamos ?? |Merkle Root|. Contudo, falta compor a |Merkle Tree| final. Para tal, tendo como resultado uma lista de listas de (sub-)??rvores agrupada pelos n??veis da ??rvore final, ?? necess??rio encaixar sucessivamente os tais n??veis formando a |Merkle Tree| completa.
\end{enumerate}
\end{itemize}
\end{minipage}
}\caption{Algoritmo cl??ssico de constru????o de uma \MerkleTree\ \cite{Se19} \label{fig:algMTree}.}
\end{figure}

Assumindo uma lista n??o vazia de transa????es, o algoritmo cl??ssico de constru????o
de uma |Merkle Tree| ?? o que est?? dado na Figura \ref{fig:algMTree}. Contudo,
este algoritmo (que se pode mostrar ser um hilomorfismo de listas n??o vazias)
?? demasiadamente complexo. Uma forma bem mais simples de produzir uma |Merkle
Tree| ?? atrav??s de um hilomorfismo de \LTree s. Come??a-se por, a partir da
lista de transa????es, construir uma \LTree\ cujas folhas s??o as transa????es:
\begin{spec}
list2LTree :: [a] -> LTree a
\end{spec}
Depois, o objetivo ?? etiquetar essa ??rvore com os |hashes|,
\begin{spec}
lTree2MTree :: Hashable a => LTree a -> (underbrace (FTree Integer (Integer, a))(Merkle tree))
\end{spec}
formando uma \MerkleTree\ que satisfa??a os tr??s requisitos em (\ref{eq:MTree_props}).
Em suma, a constru????o de um \blockchain\ ?? um hilomorfismo de \LTree s
\begin{code}
computeMerkleTree :: Hashable a => [a] -> FTree Integer (Integer, a)
computeMerkleTree = lTree2MTree . list2LTree
\end{code}

\begin{enumerate}
\item     Comece por definir o gene do anamorfismo que constr??i \LTree s a partir de listas n??o vazias:

\begin{code}
list2LTree :: [a] -> LTree a
list2LTree = anaLTree g_list2LTree
\end{code}
\textbf{NB}: para garantir que |list2LTree| n??o aceita listas vazias dever??
usar em |g_list2LTree| o inverso |outNEList| do isomorfismo
\begin{code}
inNEList = either singl cons
\end{code}

\item

Assumindo as seguintes fun????es |hash| e |concHash|:\footnote{Para invocar a fun????o |hash|, escreva |Main.hash|.}

\begin{code}
hash :: Hashable a => a -> Integer
hash = toInteger . (Data.Hashable.hash)
concHash :: (Integer, Integer) -> Integer
concHash = add
\end{code}

\noindent defina o gene do catamorfismo que consome a \LTree\ e produz
a correspondente \MerkleTree\ etiquetada com todos os |hashes|:

\begin{code}
lTree2MTree :: Hashable a => LTree a -> FTree Integer (Integer, a)
lTree2MTree = cataLTree g_lTree2MTree
\end{code}

\item Defina |g_mroot| por forma a
\begin{code}
mroot :: Hashable b => [b] -> Integer
mroot = cataFTree g_mroot . computeMerkleTree
\end{code}
nos dar a Merkle \emph{root} de um qualquer bloco |[b]| de transa????es.

\item

Calcule |mroot trs| da sequ??ncia de transa????es |trs| da no anexo e verifique que, sempre que se modifica (e.g.\ fraudulentamente) uma transa????o passada em |trs|, |mroot trs| altera-se necessariamente. Porqu??? (Esse ?? exactamente o princ??pio de funcionamento da tecnologia \blockchain.)
\end{enumerate}

\begin{quote}\small
\vskip 1em \hrule \vskip 1em
\textbf{Valoriza????o} (n??o obrigat??ria): implemente o algoritmo cl??ssico de
constru????o de \MerkleTree s
\begin{spec}
classicMerkleTree :: Hashable a => [a] -> FTree Integer Integer
\end{spec}
sob a forma de um hilomorfismo de listas n??o vazias.
Para isso dever?? definir esse combinador primeiro, da forma habitual:
\begin{spec}
hyloNEList h g = cataNEList h . anaNEList g
\end{spec}
etc.
Depois passe ?? defini????o do gene |g_pairsList| do anamorfismo de listas
\begin{spec}
pairsList :: [a] -> [(a, a)]
pairsList = anaList (g_pairsList)
\end{spec}
que agrupa a lista argumento por pares, duplicando o ??ltimo valor caso seja necess??rio. Para tal, poder?? usar a fun????o (j?? definida)
\begin{spec}
getEvenBlock :: [a] -> [a]
\end{spec}
que, dada uma lista, se o seu comprimento for ??mpar, duplica o ??ltimo valor.

Por fim, defina os genes |divide| e |conquer| dos respetivos anamorfismo e catamorfimo por forma a
\begin{spec}
classicMerkleTree = (hyloNEList conquer divide) . (map Main.hash)
\end{spec}
Para facilitar a defini????o do |conquer|, ter?? apenas de definir o gene |g_mergeMerkleTree| do catamorfismo de ordem superior
\begin{spec}
mergeMerkleTree :: FTree a p -> [FTree a c] -> FTree a c
mergeMerkleTree = cataFTree (g_mergeMerkleTree)
\end{spec}
que comp??e a \FTree\ (?? cabe??a) com a lista de \FTree s (como filhos), fazendo um ``merge'' dos valores interm??dios. Veja o seguinte exemplo de aplica????o da fun????o |mergeMerkleTree|:
\begin{verbatim}
 > l = [Comp 3 (Unit 1, Unit 2), Comp 7 (Unit 3, Unit 4)]
 > 
 > m = Comp 10 (Unit 3, Unit 7)
 > 
 > mergeMerkleTree m l
Comp 10 (Comp 3 (Unit 1,Unit 2),Comp 7 (Unit 3,Unit 4))
\end{verbatim}

\textbf{NB}: o \textit{classicMerkleTree} retorna uma Merkle Tree cujas folhas s??o apenas o |hash| da transa????o e n??o o par (|hash|, transa????o).
\vskip 1em \hrule \vskip 1em
\end{quote}

\Problema

Se se digitar \wc{|man wc|} na shell do Unix (Linux) obt??m-se:
\begin{quote}\small
\begin{verbatim}
NAME
     wc -- word, line, character, and byte count

SYNOPSIS
     wc [-clmw] [file ...]

DESCRIPTION
    The wc utility displays the number of lines, words, and bytes contained in
    each input file,  or standard input (if no file is specified) to the stan-
    dard  output.  A line is defined as  a string of characters delimited by a
    <newline> character.  Characters beyond the final <newline> character will
    not be included in the line count.
    (...)
    The following options are available:
    (...)
        -w   The number of words in each input file is written to the standard
             output.
    (...)
\end{verbatim}
\end{quote}
Se olharmos para o c??digo da fun????o que, em C, implementa esta funcionalidade
\cite{KR78} e nos focarmos apenas na parte que implementa a op????o \verb!-w!,
verificamos que a poder??amos escrever, em Haskell, da forma seguinte:
\begin{code}
wc_w :: [Char] -> Int
wc_w []    = 0
wc_w (c:l) =
     if not (sep c) && lookahead_sep l then wc_w l + 1 else wc_w l
       where
          sep c = ( c == ' ' || c == '\n' || c == '\t')
          lookahead_sep []    = True
          lookahead_sep (c:l) = sep c
\end{code}
Por aplica????o da lei de recursividade m??tua
\begin{eqnarray}
|lcbr(
     f . inT = h . fF(split f g)
     )(
        g . inT = k . fF(split f g)
)|
     & \equiv &
     |split f g = cata(split h k)|
\end{eqnarray}
??s fun????es |wc_w| e |lookahead_sep|, re-implemente a primeira segundo o
modelo \emph{|worker|/|wrapper|} onde |worker| dever?? ser um catamorfismo
de listas:
\begin{spec}
wc_w_final :: [Char] -> Int
wc_w_final = wrapper . (underbrace (cataList (either g1 g2)) worker)
\end{spec}
Apresente os c??lculos que fez para chegar ?? vers??o |wc_w_final| de |wc_w|,
com indica????o dos genes |h|, |k| e |g = either g1 g2|.

\Problema

Neste problema pretende-se gerar o HTML de uma p??gina de um jornal descrita
como uma agrega????o estruturada de blocos de texto ou imagens:
\begin{code}
data Unit a b = Image a | Text b deriving Show
\end{code}
O tipo |Sheet| (=``p??gina de jornal'')
\begin{code}
data Sheet a b i = Rect (Frame i) (X (Unit a b) (Mode i)) deriving Show
\end{code}
?? baseado num tipo indutivo $X$ que, dado em anexo (p??g.~\pageref{sec:C}),
exprime a parti????o de um rect??ngulo (a p??gina tipogr??fica) em v??rios subrect??ngulos
(as caixas tipogr??ficas a encher com texto ou imagens),
segundo um processo de parti????o bin??ria, na horizontal ou na vertical.
Para isso, o tipo
\begin{code}
data Mode i = Hr i | Hl i | Vt i | Vb i deriving Show
\end{code}
especifica quatro variantes de parti????o. O seu argumento dever??
ser um n??mero de 0 a 1, indicando a frac????o da altura (ou da largura) em que o
rect??ngulo ?? dividido, a saber:
\begin{itemize}
\item \texttt{Hr i} ---  parti????o horizontal, medindo $i$ a partir da direita
\item \texttt{Hl i} ---  parti????o horizontal, medindo $i$ a partir da esquerda
\item \texttt{Vt i} ---  parti????o vertical, medindo $i$ a partir do topo
\item \texttt{Vb i} ---  parti????o vertical, medindo $i$ a partir da base
\end{itemize}

Por exemplo, a parti????o dada na figura \ref{fig:1} corresponde ?? parti????o
de um rect??ngulo de acordo com a seguinte ??rvore de parti????es:
%
\begin{eqnarray*}
\mbox{
\tree{|Hl(0.41)|}
\subtree{|Vt(0.48)|}
\leaf{|c|}
\subtree{|Vt(0.36)|}
\leaf{|d|}
\leaf{|e|}
\endsubtree
\endsubtree
\subtree{|Vb(0.6)|}
\leaf{|a |}
\leaf{| b|}
\endsubtree
\endtree
}
\end{eqnarray*}

\begin{figure}
\begin{center}
\unitlength=.05mm
\special{em:linewidth 0.2pt}
\begin{picture}(780.00,960.00)
\put(0.00,0.00){\makebox(320,320)[cc]{$e$}}
\put(0.00,0.00){\line(1,0){320.00}}
\put(0.00,0.00){\line(0,1){320.00}}
\put(0.00,320.00){\line(1,0){320.00}}
\put(320.00,0.00){\line(0,1){320.00}}
\put(0.00,320.00){\makebox(320,180)[cc]{$d$}}
\put(0.00,320.00){\line(0,1){180.00}}
\put(0.00,500.00){\line(1,0){320.00}}
\put(320.00,320.00){\line(0,1){180.00}}
\put(0.00,500.00){\makebox(320,460)[cc]{$c$}}
\put(0.00,500.00){\line(0,1){460.00}}
\put(0.00,960.00){\line(1,0){320.00}}
\put(320.00,500.00){\line(0,1){460.00}}
\put(320.00,0.00){\makebox(460,580)[cc]{$ b$}}
\put(320.00,0.00){\line(1,0){460.00}}
\put(320.00,0.00){\line(0,1){580.00}}
\put(320.00,580.00){\line(1,0){460.00}}
\put(780.00,0.00){\line(0,1){580.00}}
\put(320.00,580.00){\makebox(460,380)[cc]{$a $}}
\put(320.00,580.00){\line(0,1){380.00}}
\put(320.00,960.00){\line(1,0){460.00}}
\put(780.00,580.00){\line(0,1){380.00}}
\end{picture}
\end{center}
\caption{Layout de p??gina de jornal.\label{fig:1}}
\end{figure}

As caixas delineadas por uma parti????o (como a dada acima) correspondem a
folhas da ??rvore de parti????o e podem conter texto ou imagens. ?? o que
se verifica no objecto |example| da sec????o \ref{sec:test_data}
que, processado por |sheet2html| (sec????o \ref{sec:html})
vem a produzir o ficheiro \texttt{jornal.html}.

\paragraph{O que se pretende}
O c??digo em \Haskell\ fornecido no anexo \ref{sec:codigo}
como ``kit'' para arranque deste trabalho n??o est?? estruturado
em termos dos combinadores \emph{cata-ana-hylo} estudados nesta disciplina.
%
O que se pretende ??, ent??o:
\begin{enumerate}
\item     A constru????o de uma biblioteca ``pointfree''
     \footnote{%
          A desenvolver de forma an??loga a outras bibliotecas que
          conhece (\eg\ \LTree, etc).
}
     com base na qual o processamento (``pointwise'') j?? dispon??vel
     possa ser redefinido.
\item     A evolu????o da biblioteca anterior para uma outra que permita
     parti????es $n$-??rias (para \emph{qualquer} $n$ finito)
     e n??o apenas bin??rias. \footnote{
          Repare que ?? a falta desta capacidade expressiva
          que origina, no ``kit'' actual, a defini????o das fun????es
          auxiliares  da sec????o \ref{sec:faux}, por exemplo.
     }
\end{enumerate}

\Problema

Este exerc??cio tem como objectivo determinar todos os caminhos
poss??veis de um ponto \emph{A} para um ponto \emph{B}. Para tal,
iremos utilizar t??cnicas de
\href{https://en.wikipedia.org/wiki/Brute-force_search}{\emph{brute
force}} e
\href{https://en.wikipedia.org/wiki/Backtracking}{\emph{backtracking}}, que podem
ser codificadas no \listM{m??nade das listas} (estudado na \href{https://haslab.github.io/CP/Material/}{aulas}). Comece por implementar a seguinte fun????o auxiliar:

\begin{enumerate}
\item |pairL :: [a] -> [(a,a)]| que dada uma lista |l| de tamanho
maior que |1| produz uma nova lista cujos elementos s??o os pares |(x,y)| de
elementos de |l| tal que |x| precede imediatamente |y|. Por exemplo:
\begin{quote}
     |pairL [1,2] == [(1,2)]|,
\\
     |pairL [1,2,3] == [(1,2),(2,3)]| e
\\
     |pairL [1,2,3,4] == [(1,2),(2,3),(3,4)]|
\end{quote}
Para o caso em que |l = [x]|, i.e. o tamanho de |l| ?? |1|, assuma que |pairL [x] == [(x,x)]|. Implemente esta fun????o como um \emph{anamorfismo de listas}, atentando na sua propriedade:

\begin{itemize}\em
\item      Para todas as listas |l| de tamanho maior que 1,
a lista |map p1 (pairL l)| ?? a lista original |l| a menos do ??ltimo elemento.
Analogamente, a lista |map p2 (pairL l)|  ?? a lista original |l| a menos do primeiro elemento. 
\end{itemize}
\end{enumerate}


De seguida necessitamos de uma estrutura de dados representativa da no????o de espa??o,
para que seja poss??vel formular a no????o de \emph{caminho} de um ponto |A| para um ponto |B|,
por exemplo, num papel quadriculado. No nosso caso vamos ter:
\begin{code}
data Cell = Free | Blocked |  Lft | Rght | Up | Down deriving (Eq,Show)
type Map = [[Cell]]
\end{code}

O terreno onde iremos navegar ?? codificado ent??o numa \emph{matriz} de
c??lulas.  Os valores \emph{Free} and \emph{Blocked} denotam uma c??lula
como livre ou bloqueada, respectivamente (a navega????o entre dois
pontos ter?? que ser realizada \emph{exclusivamente} atrav??s de c??lulas
livres). Ao correr, por exemplo, |putStr $ showM $
map1| no interpretador  ir?? obter a seguinte apresenta????o de um mapa:
\begin{verbatim}
 _  _  _
 _  X  _
 _  X  _
\end{verbatim}
Para facilitar o teste das implementa????es pedidas abaixo, disponibilizamos no anexo \ref{sec:codigo}
a fun????o |testWithRndMap|. Por exemplo, ao correr
|testWithRndMap| obtivemos o seguinte mapa aleatoriamente:
\begin{verbatim}
 _  _  _  _  _  _  X  _  _  X
 _  X  _  _  _  X  _  _  _  _
 _  _  _  _  _  X  _  _  _  _
 _  X  _  _  _  _  _  _  _  X
 _  _  _  _  _  _  X  _  X  _
 _  _  _  _  _  _  _  _  _  _
 _  X  X  _  _  X  _  _  _  _
 _  _  _  _  _  _  _  _  X  _
 _  _  _  _  _  X  _  _  X  _
 _  _  X  _  _  _  _  _  _  X
Map of dimension 10x10.
\end{verbatim}

De seguida, os valores |Lft|, |Rght|,
|Up| e |Down| em |Cell| denotam o facto de uma c??lula ter sido alcan??ada
atrav??s da c??lula ?? esquerda, direita, de cima, ou de baixo, respectivamente.
Tais valores ir??o ser usados na representa????o de caminhos num mapa.

\begin{enumerate}
\setcounter{enumi}{1}
\item

Implemente agora a fun????o |markMap :: [Pos] -> Map -> Map|,
que dada uma lista de posi????es (representante de um \emph{caminho} de um ponto \emph{A} para
um ponto \emph{B}) e um mapa retorna um novo mapa com o caminho l?? marcado.
Por exemplo, ao correr no interpretador,
\begin{center}
|putStr $ showM $ markMap [(0,0),(0,1),(0,2),(1,2)] map1|
\end{center}
dever?? obter a seguinte apresenta????o de um mapa e respectivo caminho:
\begin{verbatim}
 >  _  _
 ^  X  _
 ^  X  _
\end{verbatim}
representante do caso em que subimos duas vezes no mapa e depois viramos ?? direita.
Para implementar a fun????o |markMap| dever?? recorrer ?? fun????o |toCell| (disponibilizada
no anexo \ref{sec:codigo}) e a uma fun????o auxiliar com o tipo |[(Pos,Pos)] -> Map -> Map| definida como
um \emph{catamorfismo de listas}. Tal como anteriormente, anote as propriedades seguintes sobre
|markMap|:\footnote{Ao implementar a fun????o |markMap|, estude tamb??m
a fun????o |subst| (disponibilizada no anexo \ref{sec:codigo}) pois as duas fun????es tem
algumas semelhan??as.}
\begin{itemize}\em
\item      Para qualquer lista |l| a fun????o |markMap l| ?? idempotente.
\item      Todas as posi????es presentes na lista dada como argumento
ir??o fazer com que as c??lulas correspondentes no mapa deixem de ser |Free|.
\end{itemize}
\end{enumerate}

Finalmente h?? que implementar a fun????o |scout :: Map -> Pos -> Pos -> Int -> [[Pos]]|,
que dado um mapa |m|, uma posi????o inicial |s|, uma posi????o alvo |t|, e um n??mero
inteiro |n|, retorna uma lista de caminhos que come??am em |s| e que t??m tamanho m??ximo
|n+1|. Nenhum destes caminhos pode conter |t| como elemento que n??o seja o ??ltimo na lista (i.e. um caminho deve terminar logo que se alcan??a a posi????o |t|). Para al??m disso,
n??o ?? permitido voltar a posi????es previamente visitadas e se ao alcan??ar uma posi????o
diferente de |t| ?? impossivel sair dela ent??o todo o caminho que levou a esta
posi????o deve ser removido (\emph{backtracking}). Por exemplo: \\

\noindent
|scout map1 (0,0) (2,0) 0 == [[(0,0)]]|

\noindent
|scout map1 (0,0) (2,0) 1 == [[(0,0),(0,1)]]|

\noindent
|scout map1 (0,0) (2,0) 4 == [[(0,0),(0,1),(0,2),(1,2),(2,2)]]|

\noindent
|scout map2 (0,0) (2,2) 2 == [[(0,0),(0,1),(1,1)],[(0,0),(0,1),(0,2)]]|

\noindent
|scout map2 (0,0) (2,2) 4 == [[(0,0),(0,1),(1,1),(2,1),(2,2)],[(0,0),(0,1),(1,1),(2,1),(2,0)]]|

\begin{enumerate}
\setcounter{enumi}{2}
\item   Implemente a fun????o
\begin{spec}
scout :: Map -> Pos -> Pos -> Int -> [[Pos]]
\end{spec}
recorrendo ?? fun????o |checkAround| (disponibilizada no anexo \ref{sec:codigo}) e de tal forma a que
|scout m s t| seja um catamorfismos de naturais \emph{mon??dico}.
Anote a seguinte propriedade desta fun????o:

\begin{itemize}\em
\item     \label{en:6a}
Quanto maior for o tamanho m??ximo permitido aos caminhos,  mais caminhos que alcan??am a
posi????o alvo iremos encontrar.
\end{itemize}
\end{enumerate}

\newpage
\part*{Anexos}

\appendix

\section{Documenta????o para realizar o trabalho}
\label{sec:documentacao}
Para cumprir de forma integrada os objectivos Rdo trabalho vamos recorrer
a uma t??cnica de programa\-????o dita
``\litp{liter??ria}'' \cite{Kn92}, cujo princ??pio base ?? o seguinte:
%
\begin{quote}\em Um programa e a sua documenta????o devem coincidir.
\end{quote}
%
Por outras palavras, o c??digo fonte e a documenta????o de um
programa dever??o estar no mesmo ficheiro.

O ficheiro \texttt{cp2122t.pdf} que est?? a ler ?? j?? um exemplo de
\litp{programa????o liter??ria}: foi gerado a partir do texto fonte
\texttt{cp2122t.lhs}\footnote{O sufixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrar?? no
\MaterialPedagogico\ desta disciplina descompactando o ficheiro
\texttt{cp2122t.zip} e executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2122t.lhs > cp2122t.tex
    $ pdflatex cp2122t
\end{Verbatim}
em que \href{https://hackage.haskell.org/package/lhs2tex}{\texttt\LhsToTeX} ??
um pre-processador que faz ``pretty printing''
de c??digo Haskell em \Latex\ e que deve desde j?? instalar executando
\begin{Verbatim}[fontsize=\small,commandchars=\\\{\}]
    $ cabal install lhs2tex --lib
    $ cabal install --ghc-option=-dynamic lhs2tex
\end{Verbatim}
\textbf{NB}: utilizadores do macOS poder??o instalar o |cabal| com o seguinte comando:
\begin{Verbatim}[fontsize=\small,commandchars=\\\{\}]
    $ brew install cabal-install
\end{Verbatim}
Por outro lado, o mesmo ficheiro \texttt{cp2122t.lhs} ?? execut??vel e cont??m
o ``kit'' b??sico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2122t.lhs
\end{Verbatim}

\noindent Abra o ficheiro \texttt{cp2122t.lhs} no seu editor de texto preferido
e verifique que assim ??: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
?? seleccionado pelo \GHCi\ para ser executado.

\subsection{Como realizar o trabalho}
Este trabalho te??rico-pr??tico deve ser realizado por grupos de 3 (ou 4) alunos.
Os detalhes da avalia????o (datas para submiss??o do relat??rio e sua defesa
oral) s??o os que forem publicados na \cp{p??gina da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo
em todos os exerc??cios do trabalho, para assim
poderem responder a qualquer quest??o colocada na
\emph{defesa oral} do relat??rio.

Em que consiste, ent??o, o \emph{relat??rio} a que se refere o par??grafo anterior?
?? a edi????o do texto que est?? a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relat??rio dever?? conter ainda a identifica????o dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relat??rio deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o ??ndice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2122t.aux
    $ makeindex cp2122t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. Dever-se-?? ainda instalar o utilit??rio
\QuickCheck,
que ajuda a validar programas em \Haskell:
\begin{Verbatim}[fontsize=\small,commandchars=\\\{\}]
    $ cabal install QuickCheck --lib
\end{Verbatim}
Para testar uma propriedade \QuickCheck~|prop|, basta invoc??-la com o comando:
\begin{verbatim}
    > quickCheck prop
    +++ OK, passed 100 tests.
\end{verbatim}
Pode-se ainda controlar o n??mero de casos de teste e sua complexidade,
como o seguinte exemplo mostra:\footnote{
Como j?? sabe, os testes normalmente n??o provam a aus??ncia
de erros no c??digo, apenas a sua presen??a (\href{https://www.cs.utexas.edu/users/EWD/transcriptions/EWD03xx/EWD303.html}{cf. arquivo online}). Portanto n??o deve ver o facto
de o seu c??digo passar nos testes abaixo como uma garantia que este est?? livre de erros.}
\begin{verbatim}
    > quickCheckWith stdArgs { maxSuccess = 200, maxSize = 10 } prop
    +++ OK, passed 200 tests.
\end{verbatim}

Qualquer programador tem, na vida real, de ler e analisar (muito!) c??digo
escrito por outros. No anexo \ref{sec:codigo} disponibiliza-se algum
c??digo \Haskell\ relativo aos problemas que se seguem. Esse anexo dever??
ser consultado e analisado ?? medida que isso for necess??rio.

\paragraph{Stack}

O \stack{Stack} ?? um programa ??til para criar, gerir e manter projetos em \Haskell.
Um projeto criado com o Stack possui uma estrutura de pastas muito espec??fica:

\begin{itemize}
\item Os m??dulos auxiliares encontram-se na pasta \emph{src}.
\item O m??dulo principal encontra-se na pasta \emph{app}.
\item A lista de depend??ncias externas encontra-se no ficheiro \emph{package.yaml}.
\end{itemize}

\noindent Pode aceder ao \GHCi\ utilizando o comando:
\begin{verbatim}
stack ghci
\end{verbatim}

\noindent Garanta que se encontra na pasta mais externa \textbf{do projeto}.
A primeira vez que correr este comando as dep??ndencias externas ser??o instaladas automaticamente. Para gerar o PDF, garanta que se encontra na diretoria \emph{app}.

\subsection{Como exprimir c??lculos e diagramas em LaTeX/lhs2tex}
Como primeiro exemplo, estudar o texto fonte deste trabalho para obter o
efeito:\footnote{Exemplos tirados de \cite{Ol18}.}
\begin{eqnarray*}
\start
     |id = split f g|
%
\just\equiv{ universal property }
%
        |lcbr(
          p1 . id = f
     )(
          p2 . id = g
     )|
%
\just\equiv{ identity }
%
        |lcbr(
          p1 = f
     )(
          p2 = g
     )|
\qed
\end{eqnarray*}

Os diagramas podem ser produzidos recorrendo ?? \emph{package} \LaTeX\
\href{https://ctan.org/pkg/xymatrix}{xymatrix}, por exemplo:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0|
           \ar[d]_-{|cataNat g|}
&
    |1 + Nat0|
           \ar[d]^{|id + (cataNat g)|}
           \ar[l]_-{|inNat|}
\\
     |B|
&
     |1 + B|
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\section{C??digo fornecido}\label{sec:codigo}

\subsection*{Problema 1}

Sequ??ncia de transa????es para teste:
\begin{code}
trs = [ ("compra",  "20211102", -50),
        ("venda",   "20211103", 100),
        ("despesa", "20212103", -20),
        ("venda",   "20211205", 250),
        ("venda",   "20211205", 120)]
\end{code}

\begin{code}
getEvenBlock :: [a] -> [a]
getEvenBlock l = if (even(length l)) then l else l++[last l]

firsts = either p1 p1
\end{code}

\subsection*{Problema 2}

\begin{code}
wc_test = "Here is a sentence, for testing.\nA short one."

sp c = ( c == ' ' || c == '\n' || c == '\t')
\end{code}

\subsection*{Problema 3}\label{sec:C}
Tipos:
\begin{code}
data X u i = XLeaf u | Node i (X u i) (X u i) deriving Show

data Frame i = Frame i i deriving Show
\end{code}
Fun????es da API\footnote{
API (=``Application Program Interface'').
}
\begin{code}
printJournal :: Sheet String String Double -> IO ()
printJournal = write . sheet2html

write :: String  -> IO ()
write s = do writeFile "jornal.html" s
             putStrLn "Output HTML written into file `jornal.html'"
\end{code}
Gera????o de HTML: \label{sec:html}
\begin{code}
sheet2html (Rect (Frame w h) y) = htmlwrap (x2html y (w,h))

x2html :: X (Unit String String) (Mode Double) -> (Double, Double) -> String
x2html (XLeaf (Image i)) (w,h)= img w h i

x2html (XLeaf (Text txt)) _ = txt
x2html (Node (Vt i) x1 x2) (w,h) = htab w h (
                                     tr( td w (h*i)     (x2html x1 (w, h*i))) ++
                                     tr( td w (h*(1-i)) (x2html x2 (w, h*(1-i))))
                                   )
x2html (Node (Hl i) x1 x2) (w,h) = htab w h (
                                     tr( td (w*i) h     (x2html x1 (w*i, h)) ++
                                         td (w*(1-i)) h (x2html x2 (w*(1-i), h)))
                                   )

x2html (Node (Vb i) x1 x2) m = x2html (Node (Vt (1 - i)) x1 x2) m
x2html (Node (Hr i) x1 x2) m = x2html (Node (Hl (1 - i)) x1 x2) m
\end{code}
Fun????es auxiliares: \label{sec:faux}
\begin{code}
twoVtImg a b = Node (Vt 0.5) (XLeaf (Image a)) (XLeaf (Image b))

fourInArow a b c d =
        Node (Hl 0.5)
          (Node (Hl 0.5) (XLeaf (Text a)) (XLeaf (Text b)))
          (Node (Hl 0.5) (XLeaf (Text c)) (XLeaf (Text d)))
\end{code}
HTML:
\begin{code}
htmlwrap = html . hd . (title "CP/2122 - sheet2html") . body . divt

html = tag "html" [] . ("<meta charset=\"utf-8\" />"++)

title t = (tag "title" [] t ++)

body = tag "body" [ "BGCOLOR" |-> show "#F4EFD8" ]

hd = tag "head" []

htab w h = tag "table" [
                  "width" |-> show2 w, "height" |-> show2 h,
                  "cellpadding" |-> show2 0, "border" |-> show "1px" ]

tr = tag "tr" []

td w h = tag "td" [ "width" |-> show2 w, "height" |-> show2 h ]

divt = tag "div" [ "align" |-> show "center" ]

img w h i = tag "img" [ "width" |-> show2 w, "src" |-> show i ] ""

tag t l x = "<"++t++" "++ps++">"++x++"</"++t++">\n"
             where ps = unwords [concat[t,"=",v]| (t,v)<-l]

a |-> b = (a,b)

show2 :: Show a => a -> String
show2 = show . show
\end{code}
Exemplo para teste: \label{sec:test_data}
\begin{code}

example :: (Fractional i) => Sheet String String i
example =
   Rect (Frame 650 450)
    (Node (Vt 0.01)
      (Node (Hl 0.15)
         (XLeaf (Image "cp2122t_media/publico.jpg"))
         (fourInArow "Jornal P??blico" "Domingo, 5 de Dezembro 2021" "Simula????o para efeitos escolares" "CP/2122-TP"))
      (Node (Vt 0.55)
          (Node (Hl 0.55)
              (Node (Vt 0.1)
                 (XLeaf (Text
                 "Universidade do Algarve estuda planta capaz de eliminar a doen??a do sobreiro"))
                 (XLeaf (Text
                  "Organismo (semelhante a um fungo) ataca de forma galopante os montados de sobro. O contra-poder para fazer recuar o agente destruidor reside numa planta (marioila), que nasce espont??nea no Algarve e Alentejo.\nComo travar o decl??nio do sobreiro? A ??rvore, classificada como Patrim??nio Nacional de Portugal desde Dezembro de 2011, continua numa lenta agonia. O processo destrutivo - ainda sem fim ?? vista ?? vista - pode agora ser estancado. (...)")))
              (XLeaf (Image
                  "cp2122t_media/1647472.jpg")))
          (Node (Hl 0.25)
              (twoVtImg
                  "cp2122t_media/1647981.jpg"
                  "cp2122t_media/1647982.jpg")
              (Node (Vt 0.1)
                  (XLeaf (Text "Manchester United vence na estreia de Rangnick"))
                  (XLeaf (Text "O Manchester United venceu, este domingo, em Old Trafford, na estreia do treinador alem??o Ralf Rangnick, impondo-se por 1-0 frente ao Crystal Palace de Patrick Vieira gra??as a um golo do brasileiro Fred, j?? no ??ltimo quarto de hora da partida da 15.?? ronda da Liga inglesa. (...)"))))))
\end{code}

\subsection*{Problema 4}\label{sec:D}
Exemplos de mapas:
\begin{code}
map1 = [[Free, Blocked, Free], [Free, Blocked, Free], [Free, Free, Free]]
map2 = [[Free, Blocked, Free], [Free, Free, Free], [Free, Blocked, Free]]
map3 = [[Free, Free, Free] , [Free, Blocked, Free], [Free, Blocked, Free]]
\end{code}
C??digo para impress??es de mapas e caminhos:
\begin{code}
showM :: Map -> String
showM = unlines . (map showL) . reverse

showL  :: [Cell] -> String
showL = cataList (either f1 f2) where
  f1 = const ""
  f2 = (uncurry (++)) . (fromCell >< id)

fromCell Lft = " > "
fromCell Rght = " < "
fromCell Up = " ^ "
fromCell Down = " v "
fromCell Free = " _ "
fromCell Blocked = " X "

toCell (x,y) (w,z) | x < w = Lft
toCell (x,y) (w,z) | x > w = Rght
toCell (x,y) (w,z) | y < z = Up
toCell (x,y) (w,z) | y > z = Down
\end{code}

\noindent
C??digo para valida????o de mapas (??til, por exemplo, para testes
\QuickCheck):
\begin{code}
ncols :: Map -> Int
ncols = (either (const 0) (length . p1)) . outList

nlines :: Map -> Int
nlines = length

isValidMap :: Map -> Bool
isValidMap = (uncurry (&&)) . (split isSquare sameLength) where
  isSquare = (uncurry (==)) . (split nlines ncols)
  sameLength [] = True
  sameLength [x] = True
  sameLength (x1:x2:y) = length x1 == length x2 && sameLength (x2:y)
\end{code}

\noindent
C??digo para gera????o aleat??ria de mapas e automatiza????o de testes
(envolve o m??nade IO):
\begin{code}
randomRIOL :: (Random a) => (a,a) -> Int -> IO [a]
randomRIOL x = cataNat (either f1 f2) where
  f1 = const (return [])
  f2 l = do r1 <- randomRIO x
            r2 <- l
            return $ r1 : r2

buildMat :: Int -> Int -> IO [[Int]]
buildMat n = cataNat (either f1 f2) where
  f1 = const (return [])
  f2 l = do x <- randomRIOL (0::Int,3::Int) n
            y <- l
            return $ x : y

testWithRndMap :: IO ()
testWithRndMap = do
    dim <- randomRIO (2,10) :: IO Int
    out <- buildMat dim dim
    map <- return $ map (map table) out
    putStr $ showM map
    putStrLn $ "Map of dimension " ++ (show dim) ++ "x" ++ (show dim) ++ "."
    putStr "Please provide a target position (must be different from (0,0)): "
    t <- readLn :: IO (Int,Int)
    putStr "Please provide the number of steps to compute: "
    n <- readLn :: IO Int
    let paths = hasTarget t (scout map (0,0) t n) in
      if length paths == 0
      then putStrLn "No paths found."
      else putStrLn $ "There are at least " ++ (show $ length paths) ++
      " possible paths. Here is one case: \n" ++ (showM $ markMap (head paths) map)

table 0 = Free
table 1 = Free
table 2 = Free
table 3 = Blocked

hasTarget y = filter (\l -> elem y l)
\end{code}

\paragraph{Fun????es auxiliares}
|subst :: a -> Int -> [a] -> [a]|, que dado um valor |x| e um inteiro |n|,
produz uma fun????o |f : [a] -> [a]| que dada uma lista |l| substitui o valor na posi????o
|n| dessa lista pelo valor |x|:
\begin{code}
subst :: a -> Int -> [a] -> [a]
subst x = cataNat (either f1 f2) where
  f1 = const (\l -> x : tail l)
  f2 f (h:t) = h : f t
\end{code}
|checkAround :: Map -> Pos -> [Pos]|, que
verifica se as c??lulas adjacentes est??o livres:
\begin{code}
type Pos = (Int,Int)

checkAround :: Map -> Pos -> [Pos]
checkAround m p = concat $ map (\f -> f m p)
                  [checkLeft, checkRight, checkUp, checkDown]

checkLeft :: Map -> Pos -> [Pos]
checkLeft m (x,y) = if x == 0 || (m !! y) !! (x-1) == Blocked
                    then [] else [(x-1,y)]

checkRight :: Map -> Pos -> [Pos]
checkRight m (x,y) = if x == (ncols m - 1) || (m !! y) !! (x+1) == Blocked
                     then [] else [(x+1,y)]

checkUp :: Map -> Pos -> [Pos]
checkUp m (x,y) = if y == (nlines m - 1) || (m !! (y+1)) !! x == Blocked
                  then [] else [(x,y+1)]

checkDown :: Map -> Pos -> [Pos]
checkDown m (x,y) = if y == 0 || (m !! (y-1)) !! x == Blocked
                    then [] else [(x,y-1)]
\end{code}


\subsection*{QuickCheck}

%----------------- Outras defini????es auxiliares -------------------------------------------%
L??gicas:
\begin{code}
infixr 0 .==>.
(.==>.) :: (Testable prop) => (a -> Bool) -> (a -> prop) -> a -> Property
p .==>. f = \a -> p a ==> f a

infixr 0 .<==>.
(.<==>.) :: (a -> Bool) -> (a -> Bool) -> a -> Property
p .<==>. f = \a -> (p a ==> property (f a)) .&&. (f a ==> property (p a))

infixr 4 .==.
(.==.) :: Eq b => (a -> b) -> (a -> b) -> (a -> Bool)
f .==. g = \a -> f a == g a

infixr 4 .<=.
(.<=.) :: Ord b => (a -> b) -> (a -> b) -> (a -> Bool)
f .<=. g = \a -> f a <= g a

infixr 4 .&&&.
(.&&&.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
f .&&&. g = \a -> ((f a) && (g a))

instance Arbitrary Cell where
  -- 1/4 chance of generating a cell 'Block'.
  arbitrary = do x <- chooseInt (0,3)
                 return $ f x where
                   f x = if x < 3 then Free else Blocked
\end{code}

%----------------- Solu????es dos alunos -----------------------------------------%

\section{Solu????es dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas solu????es para os exerc??cios
propostos, de acordo com o "layout" que se fornece. N??o podem ser
alterados os nomes ou tipos das fun????es dadas, mas pode ser adicionado
texto, diagramas e/ou outras fun????es auxiliares que sejam necess??rias.

Valoriza-se a escrita de \emph{pouco} c??digo que corresponda a solu????es
simples e elegantes.

\subsection*{Problema 1} \label{pg:P1}

\par Para chegar ?? defini????o do outNEList usamos a defini????o do inNEList, como ?? poss??vel ver de seguida.

\begin{eqnarray*}
\start
       | outNEList . inNEList = id |
\just{|<=>|}{ Defini????o de in }
       |outNEList . (either singl cons) = id |
\just{|<=>|}{ lei 20 do formulario}
       |either (outNEList.singl) (outNEList.cons)=id |
\just{|<=>|}{lei 17 do formulario}
       |lcbr(id.i1=outNEList.singl) (id.i2=outNEList.cons)|
\just{|<=>|}{ lei 1 do formulario}
        |lcbr(i1=outNEList.singl) (i2=outNEList.cons)|
\just{|<=>|}{ lei 71 e 72 do formulario}
        |lcbr (i1 a = outNEList.(singl a)) (i2(h,t)=outNEList.(cons(a,t)))|
\just{|<=>|}{cons(a,b) = a:b ; singl a = [a] }
        |lcbr (i1 a = outNEList.a) (i2(h,t)=outNEList.(h:t)) |                                
\end{eqnarray*}

Listas vazias:
\begin{code}
outNEList [a]   = i1 (a)
outNEList (h:t) = i2 (h,t)

baseNEList f g = f -|- (f >< g)

recNEList  f   = id -|- (id >< f)

cataNEList g   = g . recNEList (cataNEList g) . outNEList

anaNEList  g   = inNEList . recNEList (anaNEList g) . g

hyloNEList h g = cataNEList h . anaNEList g
\end{code}
Gene do anamorfismo:
\begin{code}
g_list2LTree = (id -|- aux) . outNEList where 
     aux (h,t) = splitAt (div (length (h:t)) 2) (h:t)
\end{code}

Foi desenhado o diagrama do anamorfismo de modo a conseguirmos perceber melhor o nosso objetivo.

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |LTree A|
&
    |A| + |(LTree A)|^{2}
           \ar[l]_-{|inLTree|}
\\
     |A|^{*}   
           \ar[u]_-{|(anaList (g))|}
           \ar[r]^-{|g|}
&
     |A| + (|A|^{*})^{2}
           \ar[u]^{|id| + |(anaList (g))|^{2}}
}
\end{eqnarray*}

\par Assim sendo, foi poss??vel chegar ?? conclus??o de que o gene do anamorfismo devia criar criar um tuplo com duas listas, no caso em que recebe uma lista com mais do que um argumento. Posto isto, recorremos ent??o ?? fun????o \emph{splitAt}, que nos permitiu dividir a lista original em duas e criar o tuplo correspondente. Esta lista ?? sempre dividida a meio de modo a permitir que a ??rvore criada seja equilibrada.\\

Gene do catamorfismo:
\begin{code}
g_lTree2MTree :: Hashable c => Either c (FTree Integer (Integer, c), FTree Integer (Integer, c)) -> FTree Integer (Integer, c)
g_lTree2MTree = either g1 g2 where
     g1 x = Unit (toInteger(Data.Hashable.hash x), x)
     g2 (Unit (h1,x1), Unit (h2,x2)) = Comp (concHash (h1,h2)) (Unit (h1,x1), Unit (h2,x2))
     g2 (Unit (h1,x1), Comp h2 ts2) = Comp (concHash (h1,h2)) (Unit (h1,x1), Comp h2 ts2)
     g2 (Comp h1 ts1, Unit (h2,x2)) = Comp (concHash (h1,h2)) (Unit (h2,x2), Comp h1 ts1)
     g2 (Comp h1 ts1, Comp h2 ts2) = Comp (concHash (h1,h2)) (Comp h1 ts1, Comp h2 ts2) 
\end{code}

Tal como anteriormente baseamos tamb??m a nossa resolu????o num diagrama.

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |LTree A|
           \ar[d]_-{|cataLTree g|}
&
    |A| + |(LTree A)|^2
           \ar[d]^{|id| + |(cataLTree g)|^{2}}
           \ar[l]_-{|inLTree|}
\\
     |FTree Integer (Integer, A)|
&
     |A| + |(FTree Integer (Integer, A))|^{2}
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\par A partir deste foi poss??vel perceber que podemos receber apenas um elemento do tipo A, que ser?? ent??o depois transformado em \emph{FTree}, utilizando o tipo \emph{Unit}. E al??m disso, podemos tamb??m receber pares de \emph{FTree}, que se dever??o juntar e dar ent??o como resultado uma nova \emph{FTree}.\\

Gene de |mroot| ("get Merkle root"):
\begin{code}
g_mroot = firsts
\end{code}

\par Mais uma vez apoiamos a nossa resolu????o num diagrama de maneira a descobrirmos o gene de \emph{mroot}.

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |FTree Integer (Integer, A)|
           \ar[d]_-{|cataFTree g|}
&
    |(Integer, A)| + |Integer| \times |(FTree Integer (Integer, A))|^{2}
           \ar[d]^{|id + id| \times |(cataFTree g)|^{2}}
           \ar[l]_-{|inFTree|}
\\
     |Integer|
&
     |(Integer, A)| + |Integer| \times |Integer|^{2}
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\par Daqui, conseguimos perceber ent??o o que o catamorfismo ir?? receber como alternativas. Do lado esquerdo, temos a informa????o que est?? contida na ra??z da ??rvore, sendo esta um tuplo com o hash e a transa????o associada. Do lado direito, temos o resultado recursivo de aplicar a fun????o \emph{mroot} ??s sub-??rvores e tamb??m o valor que se encontra na sua ra??z. Assim sendo, em ambos os casos, o que iremos querer retirar ir?? ser sempre o que se encontra no lado esquerdo do tuplo da alternativa esquerda. Para tal, decidimos ent??o que faria sentido definir como gene a fun????o \emph{firsts}, uma vez que esta nos permite, numa alternativa, retirar o elemento do lado esquerdo e, de seguida retirar o elemento do lado esquerdo que l?? se encontra, obtendo-se assim a \emph{Merkle root} da ??rvore resultante.

\paragraph{Al??nea 1.4:}
\par No algoritmo de constru????o de uma \emph{Merkle Tree} cada nodo cont??m a soma das transa????es dos filhos.
A \emph{mroot} permite verificar rapidamente se uma transa????o espec??fica ocorreu, em um determinado bloco, com a maior precis??o poss??vel.
Se algum valor da transa????o for alterado, o valor da \emph{mroot} tamb??m ser?? alterado, pois esta cont??m a soma de todo o bloco de transa????es.
Assim, basta alterar-se apenas um valor para que os valores dos seus pais sejam tamb??m alterados.
Conclui-se assim que funcionam como uma blockchain em que, quando se altera a cadeia, os blocos a esta ligados ser??o alterados.\\

Valoriza????o:

\begin{code}
pairsList :: [a] -> [(a, a)]
pairsList = anaList (g_pairsList)

g_pairsList = undefined

classicMerkleTree :: Hashable a => [a] -> FTree Integer Integer
classicMerkleTree = (hyloNEList conquer divide) . (map Main.hash)

divide = undefined

conquer = either head joinMerkleTree where
      joinMerkleTree (l, m) = mergeMerkleTree m (evenMerkleTreeList l)
      mergeMerkleTree = cataFTree (either h1 h2)
      h1 c l = undefined
      h2 (c, (f, g)) l = undefined
      evenMerkleTreeList = undefined
\end{code}

\subsection*{Problema 2}

\begin{code}

wc_w_final :: [Char] -> Int
wc_w_final = wrapper . worker

worker = cataList (either g1 g2)

wrapper = p2

\end{code}
Gene de |worker|:
\begin{code}
g1 = split (const True) (const 0)
g2 = split (sep.p1) (cond((uncurry(&&)).((not.sep)><p1))(succ.p2.p2)(p2.p2))
    where sep c = (c == ' ' || c=='\n' || c== '\t')

\end{code}
Genes |h = either h1 h2| e |k = either k1 k2| identificados no c??lculo:
\begin{code}
h1 = (const True)
h2 = (sep.p1)

k1 = (const 0)
k2 = undefined
\end{code}

|k2= (cond ((uncurry(&&)).((not.sep)><p1)) (succ.p2.p2) (p2.p2))|\\

\par Para resolver este problema come??amos por customizar a lei de recursividade m??tua, para facilitar a compreens??o do racioc??nio alteramos o nome da fun????o \emph{lookaheadsep} para \emph{ls} e da \emph{wc w} para \emph{wc}

\begin{eqnarray*}
\start
       |lcbr (f.in = h.F(split f g)) (g.in = k.F(split f g)) |  
\just{|<=>|}{ |in = (either nil cons)|, |F f| = |id + id >< f| }
       |lcbr(f.(either nil cons) = h.( id + id >< (split f g))) (g.(either nil cons) = k.( id + id >< (split f g))) | 
\just{|<=>|}{ f = ls, g = wc, h = [h1,h2], k = [k1,k2] }
       |lcbr(ls.(either nil cons) = (either h1 h2).(id + id >< (split ls wc))) (wc.(either nil cons) = (either k1 k2).(id + id >< (split ls wc))) |  
\end{eqnarray*}

\par Neste ponto ?? necess??rio customizar a fun????o \emph{ls} e \emph{wc} de modo a conseguir aplicar a lei de \emph{Fokkinga}.
\par Pelo enunciado temos:
\begin{eqnarray*}
\start
       |lcbr (ls.[] = True) (ls.(c:l) = sep c) |
\just{|<=>|}{ [] = nil, (c:l) = cons(c,l) }
\end{eqnarray*}   
 
\par Aplicando a lei (27) do formul??rio,
\begin{eqnarray*}
\start
       |either (ls.nil) (ls.cons)  = either True sep |
\just{|<=>|}{ Defini????o in, Lei (20)}
       |ls.in= either True (sep.fst) |
\just{|<=>|}{ Lei (1) }
       |ls.in= either (True.id) (sep.id.fst) | 
\just{|<=>|}{ Lei (12)}   
       |ls.in= either (True.id) ((sep.fst).( id >< (split ls wc))) |   
\just{|<=>|}{ Lei (22)}   
       |ls.in= (either True (sep.fst)).(id + id >< (split ls wc))) |             
\end{eqnarray*}

\par Neste ponto falta apenas customizar a fun????o \emph{wc} para aplicar a lei de \emph{Fokkinga}.
\par Pelo enunciado temos:

\begin{eqnarray*}
\start
       |lcbr (wc.nil =(const 0)) (wc.cons = (uncurry(&&)).(split((not.sep).p1)(ls.snd))->(succ.wc.p2) ,(wc.p2) |
\just{|<=>|}{ Lei (11)}  
       |lcbr (wc.nil =(const 0)) (wc.cons = (uncurry(&&)).((not.sep)><ls).(split p1 p2)->(succ.wc.p2),(wc.p2) |
\just{|<=>|}{ Lei (8)}  
       |lcbr (wc.nil =(const 0)) (wc.cons = (uncurry(&&)).((not.sep)><ls)->(succ.wc.p2),(wc.p2)) |
\just{|<=>|}{ Lei (27)} 
       |(either (wc.nil)(wc.cons)) = (either (const 0) ((uncurry(&&)).((not.sep)><ls)->(succ.wc.p2),(wc.p2)))|
\just{|<=>|}{ Lei (20)}
       |wc.(either nil cons) =  (either (const 0) ((uncurry(&&)).((not.sep)><ls)->(succ.wc.p2),(wc.p2)))|
\just{|<=>|}{ Defini????o de in }
       |wc.in = (either (const 0) ((uncurry(&&)).((not.sep)><ls)->(succ.wc.p2),(wc.p2)))|     
\just{|<=>|}{ Lei (7), wc = |snd. (split ls wc )|, ls = |fst.(split ls wc)|}
       |wc.in = either (const 0) ((uncurry(&&).(not.sep >< p1.(split(ls)(wc))))-> (succ.p2.(split(ls)(wc).p2)),(p2.(split(ls)(wc).p2)) ) |
\just{|<=>|}{ Lei (14), Lei(13)}
|wc.in = either (const 0) ( (uncurry(&&).(not.sep >< p1).(id >< (split(ls)(wc))))-> (succ.p2.p2.(id >< split(ls)(wc))), (p2.p2.(id >< split(ls)(wc)) ) |
\just{|<=>|}{ Lei (32)}
       |wc.in = either (const 0) (((uncurry(&&).(not.sep >< p1))-> (succ.p2.p2) ,(p2.p2) ).(id >< split(ls)(wc)) ) |
\just{|<=>|}{ Lei (22)}
       |wc.in = either (const 0) ((uncurry(&&).(not.sep >< p1)) ->(succ.p2.p2),(p2.p2) ).(id + (id >< split(ls)(wc)) ) |
\end{eqnarray*}

\par Neste ponto reunimos todas as condi????es para aplicar a lei de \emph{Fokkinga}.

\begin{eqnarray*}
\start
        |lcbr (ls.nil = True) (ls.cons=(sep.p1).(id + (id >< split(ls)(wc) )))|
\just={}     
        |lcbr (wc.nil = (const 0)) (wc.cons= (uncurry(&&).(not.sep >< p1)) ) -> (succ.p2.p2, p2.p2).(id + (id >< split(ls)(wc)) ))|
\just={ Lei (50)}
        |split(ls)(wc) = cataList( split (either (True) (sep.p1))  ( either (const 0) (uncurry(&&).(not.sep >< p1) -> succ.p2.p2, p2.p2) )|
\just={ Lei (28)}
        |split(ls)(wc) = cataList(either( split (True)(const 0) ) ( split (sep.p1) (uncurry(&&).(not.sep >< p1) -> succ.p2.p2, p2.p2) ) ) |
\end{eqnarray*}

\begin{code}
prop_wc_w :: String -> Bool
prop_wc_w s = wc_w s == wc_w_final s
\end{code}

\subsection*{Problema 3}

\begin{code}
inX :: Either u (i, (X u i, X u i)) -> X u i
inX = undefined

outX (XLeaf u) = undefined
outX (Node i l r) = undefined

baseX f h g = undefined

recX f = undefined

cataX g = undefined
\end{code}

Inserir a partir daqui o resto da resolu????o deste problema:

....
\begin{code}
\end{code}

\subsection*{Problema 4}

\begin{code}
pairL :: [a] -> [(a,a)]
pairL = anaList g where
  g = (id -|- (split (pairFirstTwo.cons) f2)).outList where
     pairFirstTwo [x] = (x,x)
     pairFirstTwo (a:b:as) = (a,b)
     f2 (h,t) = if length t == 1 then [] else t
\end{code}

Para descobrir o gene do anamorfismo, come??amos por desenhar o diagrama correspondente.

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |[(a,a)]|
&
    1 + |(a,a)| \times |[(a,a)]|
           \ar[l]_-{|inList|}
\\
     |[a]|   
           \ar[u]_-{|(anaList (g))|}
           \ar[r]^-{|g|}
&
     1 + |(a,a)| \times |[a]|
           \ar[u]^{|1+id >< (anaList (g))|}
}
\end{eqnarray*}

Daqui conseguimos concluir que, para o caso em que a lista n??o fosse vazia, teri??mos que criar uma fun????o auxiliar, que nos permitisse agrupar apenas os dois primeiros elementos da lista, e de seguida, aplic??-la ?? cauda da lista. Assim sendo, criamos ent??o a fun????o \emph{pairFirstTwo}, que ser?? aplicada ao resultado de cons, que ??, neste caso, a lista recebida como argumento. Para evitar que o ??ltimo elemento seja repetido, criamos ent??o a fun????o \emph{f2} que v?? se o tamanho da cauda da lista ?? igual a 1 e caso seja, descarta-a. Isto permite que, quando chegarmos ao caso em que a lista tenha apenas dois elementos, estes se juntem num par e o ??ltimo elemento n??o fique repetido. 

\begin{code}
markMap :: [Pos] -> Map -> Map
markMap l = cataList (either (const id) f2) (pairL l) where 
     f2 :: ((Pos,Pos), Map -> Map) -> (Map -> Map)
     f2 (((x1,y1), (x2,y2)),f) m = if (((!!) ((!!) m y1) x1) == Blocked)
                                   then f m 
                                   else subst(subst (toCell (x1,y1) (x2,y2)) x1 ((!!) (f m) y1)) y1 (f m) 
\end{code}

Come??amos por desenhar o diagrama do catamorfismo correspondente ?? fun????o auxiliar.

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |[(Pos,Pos)]|
           \ar[d]_-{|cataList g|}
&
    |1 + (Pos,Pos) >< [(Pos,Pos)]|
           \ar[d]^{|id + id >< (cataNat g)|}
           \ar[l]_-{|inList|}
\\
     |f|
&
     |1 + ((Pos,Pos),f)|
           \ar[l]^-{|g = either (const id) f2|}
}
\end{eqnarray*}

Olhando para o diagrama acima ?? ent??o poss??vel perceber que \emph{f2} receber?? como argumento um par. Do lado esquerdo est?? presente um par de posi????es, correspondente ao primeiro elemento da lista original e, do lado direito uma fun????o que permitir?? alterar o mapa com as posi????es presentes na cauda da lista.

Tendo a fun????o auxiliar o tipo |[(Pos,Pos)] -> Map -> Map|, ?? ent??o poss??vel concluir que \emph{f} ter?? o tipo |Map -> Map| e, consequentemente, \emph{f2} o tipo |((Pos,Pos), Map -> Map) -> (Map -> Map)|.

Para a implementa????o de \emph{f2} utilizamos ent??o a fun????o auxiliar \emph{subst}, que nos permite susbtituir no mapa alterado pela fun????o \emph{f}, o resultado da fun????o \emph{toCell} aplicada ??s posi????es que se encontram no in??cio da lista. ?? tida em causa a situa????o em que nos encontramos numa c??lula que est?? bloqueada, sendo que neste caso n??o fazemos qualquer tipo de altera????o ao mapa.

\begin{code}
scout :: Map -> Pos -> Pos -> Int -> [[Pos]]
scout m s t = cataNat (either f1 ((>>= f2 m s))) where
  f1 = undefined
  f2 = undefined
\end{code}


\paragraph{Valoriza????o} (opcional) Completar as seguintes fun????es de teste no \QuickCheck\ para verifica????o de propriedades das fun????es pedidas, a saber:

\begin{propriedade}  A lista correspondente ao lado esquerdo
dos pares em (|pairL l|) ?? a lista original |l| a menos do ??ltimo elemento.
Analogamente, a lista correspondente ao lado direito
dos pares em (|pairL l|) ?? a lista original |l| a menos do primeiro elemento:

\begin{code}
prop_reconst l = (l /= [] && (length l /= 1) && init l == (map p1 (pairL l)) && tail l == (map p2 (pairL l))) || (length l == 1 && l == (map p1 (pairL l)) && l == (map p2 (pairL l))) || l == []
\end{code}
\end{propriedade}

\begin{propriedade} 
Assuma que uma linha (de um mapa) ?? prefixa de uma outra linha. Ent??o a representa????o
da primeira linha tamb??m prefixa a representa????o da segunda linha:
\end{propriedade}
\begin{code}
prop_prefix2 l l' = undefined
\end{code}
\begin{propriedade} 
Para qualquer linha (de um mapa), a sua representa????o  deve conter um n??mero de s??mbolos correspondentes a um tipo c??lula igual
ao n??mero de vezes que esse tipo de c??lula aparece na linha em quest??o.
\end{propriedade}
\begin{code}
prop_nmbrs l c = undefined

count :: (Eq a) => a -> [a] -> Int
count = undefined
\end{code}

\begin{propriedade} 
Para qualquer lista |l| a fun????o |markMap l| ?? idempotente.
\end{propriedade}
\begin{code}
inBounds m (x,y) = undefined

prop_idemp2 l m = undefined
\end{code}
\begin{propriedade} 
Todas as posi????es presentes na lista dada como argumento ir??o fazer com que
as c??lulas correspondentes no mapa deixem de ser |Free|.
\end{propriedade}
\begin{code}
prop_extr2 l m = undefined
\end{code}

\begin{propriedade} 
Quanto maior for o tamanho m??ximo dos caminhos  mais caminhos que alcan??am a
posi????o alvo iremos encontrar:
\end{propriedade}
\begin{code}
prop_reach m t n n' = undefined
\end{code}


%----------------- ??ndice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2122t}

%----------------- Fim do documento -------------------------------------------%
\end{document}

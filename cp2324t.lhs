\documentclass[11pt, a4paper, fleqn]{article}
\usepackage{cp2324t}
\makeindex

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
%format (lcbr3 (x)(y)(z)) = "\begin{lcbr}" x "\\" y "\\" z "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format Either a b = a "+" b
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textbf{NB}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format outLTree = "\mathsf{out}"
%format inLTree = "\mathsf{in}"
%format inFTree = "\mathsf{in}"
%format outFTree = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format l2 = "l_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format LTree = "{\LTree}"
%format FTree = "{\FTree}"
%format inNat = "\mathsf{in}"
%format (cata (f)) = "\llparenthesis\, " f "\,\rrparenthesis"
%format (cataNat (g)) = "\cataNat{" g "}"
%format (cataList (g)) = "\llparenthesis\, " g "\,\rrparenthesis"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataFTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataRose (x)) = "\llparenthesis\, " x "\,\rrparenthesis_\textit{\tiny R}"
%format (ana (g)) = "\ana{" g "}"
%format (anaList (g)) = "\anaList{" g "}"
%format (anaLTree (g)) = "\lanabracket\," g "\,\ranabracket"
%format (anaRose (g)) = "\lanabracket\," g "\,\ranabracket_\textit{\tiny R}"
%format (hylo (g) (h)) = "\llbracket\, " g ",\," h "\,\rrbracket"
%format (hyloRose (g) (h)) = "\llbracket\, " g ",\," h "\,\rrbracket_\textit{\tiny R}"
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
%format delta = "\Delta "
%format (plus (f)(g)) = "{" f "}\plus{" g "}"
%format ++ = "\mathbin{+\!\!+}"
%format Integer  = "\mathbb{Z}"
%format (Cp.cond (p) (f) (g)) = "\mcond{" p "}{" f "}{" g "}"
%format (square (x)) = x "^2"

%format (cataTree (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis_{\textit{\tiny T}}"
%format (cataForest (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis_{\textit{\tiny F}}"
%format (anaTree (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket_{\textit{\tiny T}}"
%format (anaForest (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket_{\textit{\tiny F}}"
%format (hyloTree (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket_{\textit{\tiny T}}"
%format (hyloForest (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket_{\textit{\tiny F}}"
%format inTree = "\mathsf{in}_{Tree}"
%format inForest = "\mathsf{in}_{Forest}"
%format outTree = "\mathsf{out}_{Tree}"
%format outForest = "\mathsf{out}_{Forest}"

%format (cata' (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis"
%format (ana' (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket"
%format (hylo' (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket"
%------------------------------------------------------------------------------%


%====== DEFINIR GRUPO E ELEMENTOS =============================================%

\group{G14}
\studentA{100594}{João Manuel Machado Lopes}
\studentB{100665}{Tiago Nuno Magalhães Teixeira}
\studentC{100693}{Luís Vítor Lima Barros}

%==============================================================================%

\begin{document}
\sffamily
\setlength{\parindent}{0em}
\emergencystretch 3em
\renewcommand{\baselinestretch}{1.25} 
\input{Cover}
\pagestyle{pagestyle}

\newgeometry{left=25mm,right=20mm,top=25mm,bottom=25mm}
\setlength{\parindent}{1em}

\section*{Preâmbulo}

\CP\ tem como objectivo principal ensinar a progra\-mação de computadores
como uma disciplina científica. Para isso parte-se de um repertório de \emph{combinadores}
que formam uma álgebra da programação % (conjunto de leis universais e seus
corolários) e usam-se esses combinadores para construir programas \emph{composicionalmente},
isto é, agregando programas já existentes.

Na sequência pedagógica dos planos de estudo dos cursos que têm
esta disciplina, opta-se pela aplicação deste método à programação
em \Haskell\ (sem prejuízo da sua aplicação a outras linguagens
funcionais). Assim, o presente trabalho prático coloca os
alunos perante problemas concretos que deverão ser implementados em
\Haskell. Há ainda um outro objectivo: o de ensinar a documentar
programas, a validá-los e a produzir textos técnico-científicos de
qualidade.

Antes de abodarem os problemas propostos no trabalho, os grupos devem ler
com atenção o anexo \ref{sec:documentacao} onde encontrarão as instruções
relativas ao sofware a instalar, etc.

Valoriza-se a escrita de \emph{pouco} código que corresponda a soluções
simples e elegantes que utilizem os combinadores de ordem superior estudados
na disciplina.

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
module Main where
import Cp
import List hiding (fac)
import Nat hiding (aux)
import LTree
import FTree
import Probability
import Data.List hiding (find)
import Svg hiding (for)
import Control.Monad
import Control.Applicative hiding ((<|>))
import System.Process
import Data.Char
import Control.Concurrent

main = undefined
\end{code}
%endif

\Problema

Este problema, retirado de um \emph{site} de exercícios de preparação para entrevistas de emprego, 
tem uma formulação simples:
\begin{quote}\em
Dada uma matriz de uma qualquer dimensão, listar todos os seus elementos rodados em espiral. 
Por exemplo, dadas as seguintes matrizes:

	\figura

\noindent
dever-se-á obter, respetivamente, |[1,2,3,6,9,8,7,4,5]| e |[1,2,3,4,8,12,11,10,9,5,6,7]|.
\\ $\Box$
\end{quote}

\noindent
Valorizar-se-ão as soluções \emph{pointfree} que empreguem os combinadores
estudados na disciplina, e.g. |f.g|, |split f g|, |f >< g|, |either f g|, |f+g|, bem como
catamorfismos e anamorfismos. 

Recomenda-se a escrita de \emph{pouco} código e de soluções simples
e fáceis de entender. Recomenda-se que o código venha acompanhado de uma
descrição de como funciona e foi concebido, apoiado em diagramas explicativos.
Para instruções sobre como produzir esses diagramas e exprimir raciocínios
de cálculo, ver o anexo \ref{sec:diagramas}.

\Problema

Este problema, que de novo foi retirado de um \emph{site} de exercícios de preparação para entrevistas de emprego, tem uma formulação muito simples:
\begin{quote}\em
Inverter as vogais de um \emph{string}.
\end{quote}
Esta formulação deverá ser generalizada a:
\begin{quote}\em
Inverter os elementos de uma dada lista que satisfazem um dado predicado.
\end{quote}

\noindent
Valorizam-se as soluções tal como no problema anterior e fazem-se as mesmas
recomendações.

\Problema

Sistemas como \href{https://chat.openai.com/}{chatGPT} etc baseiam-se em
algoritmos de aprendizagem automática que usam determinadas funções matemáticas,
designadas \emph{activation functions} (AF), para modelar aspectos não li\-neares
do mundo real. Uma dessas AFs é a
\href{https://www.ml-science.com/tanh-activation-function}{tangente hiperbólica},
definida como o quociente do seno e coseno
\href{https://en.wikipedia.org/wiki/Hyperbolic_functions}{hiperbólicos}, 
\begin{eqnarray}
	\tanh x = \frac{\sinh x}{\cosh x}
	\label{eq:tanh}
\end{eqnarray}
podendo estes ser definidos pelas seguintes \taylor{séries de Taylor}:
\begin{eqnarray}
\start
	\sum_{k=0}^\infty \frac{x^{2k+1}}{(2k+1)!}=\sinh x
	\label{eq:sinh}
\more
	\sum_{k=0}^\infty \frac{x^{2k}}{(2k)!}=\cosh x
	\nonumber
\end{eqnarray}

Interessa que estas funções sejam implementadas de forma muito eficiente,
desdobrando-as em ope\-rações aritméticas elementares. Isso pode ser conseguido
através da chamada \pd{programação dinâmica} que, em \cp{Cálculo de Programas},
é feita de forma \emph{correct-by-construction} derivando-se ciclos-\textbf{for} via
lei de recursividade mútua generalizada a tantas funções quanto necessário
--- ver o anexo \ref{sec:mr}. 

O objectivo desta questão é codificar como um ciclo-\textsf{for} (em Haskell) a função
\begin{eqnarray}
	snh\ x\ i = \sum_{k=0}^i \frac{x^{2k+1}}{(2k+1)!}
\end{eqnarray}
que implementa |sinh x|, uma das funções de |tanh x| (\ref{eq:tanh}), através
da soma das |i| primeiras parcelas da sua série (\ref{eq:sinh}).

Deverá ser seguida a regra prática do anexo \ref{sec:mr} e documentada a
solução proposta com todos os cálculos que se fizerem.

\Problema

Uma empresa de transportes urbanos pretende fornecer um serviço de previsão
de atrasos dos seus autocarros que esteja sempre actual, com base em \emph{feedback}
dos seus paassageiros. Para isso, desenvolveu uma \emph{app} que instala
num telemóvel um botão que indica coordenadas GPS a um serviço central, de
forma anónima, sugerindo que os passageiros o usem preferencialmente sempre
que o autocarro onde vão chega a uma paragem.

Com base nesses dados, outra funcionalidade da \emph{app} informa os utentes
do serviço sobre a probabilidade do atraso que possa haver entre duas paragens
(partida e chegada) de uma qualquer linha.

Pretende-se implementar esta segunda funcionalidade assumindo disponíveis
os dados da primeira. No que se segue, ir-se-á trabalhar sobre um modelo
intencionalmente \emph{muito simplificado} deste sistema, em que se usará
o mónade das distribuições probabilísticas (ver o anexo \ref{sec:probabilities}).
Ter-se-á, então:
\begin{itemize}
\item paragens de autocarro
\begin{code}
data Stop = S0 | S1 | S2 | S3 | S4 | S5 deriving (Show,Eq,Ord,Enum)
\end{code}
que formam a linha |[S0 .. S5]| assumindo a ordem determinada pela instância
de |Stop| na classe |Enum|;
\item	segmentos da linha, isto é, percursos entre duas paragens consecutivas:
\begin{code}
type Segment = (Stop, Stop)
\end{code}
\item os dados obtidos a partir da \emph{app} dos passageiros que, após algum
processamento, ficam disponíveis sob a forma de pares
	\emph{(segmento, atraso observado)}:
\begin{code}
dados :: [(Segment, Delay)]
\end{code}
(Ver no apêndice \ref{sec:codigo}, página \pageref{pg:dados}, uma pequena amostra
destes dados.)
\end{itemize}
A partir destes dados, há que:
\begin{itemize}
\item	gerar a base de dados probabilística
\begin{code}
db :: [(Segment, Dist Delay)]
\end{code}
que regista, estatisticamente, a probabilidade dos atrasos (|Delay|) que
podem afectar cada segmento da linha. Recomenda-se aqui a definição de uma
função genérica
\begin{code}
mkdist :: Eq a => [a] -> Dist a
\end{code}
que faça o sumário estatístico de uma qualquer lista finita, gerando a
distribuição de ocorrência dos seus elementos.
\item
com base em |db|, definir a função probabilística
\begin{code}
delay :: Segment -> Dist Delay
\end{code}
que dará, para cada segmento, a respectiva distribuição de atrasos.
\end{itemize}
Finalmente, o objectivo principal é definir a função probabilística:
\begin{code}
pdelay :: Stop -> Stop -> Dist Delay
\end{code}
|pdelay a b| deverá informar qualquer utente que queira ir da paragem |a| até à
paragem |b| de uma dada linha sobre a probabilidade de atraso acumulado no
total do percurso |[a..b]|.

Valorizar-se-ão as soluções que usem funcionalidades monádicas genéricas
estudadas na disciplina e que sejam elegantes, isto é, poupem código desnecessário.

\newpage
\part*{Anexos}

\appendix

\section{Natureza do trabalho a realizar}
\label{sec:documentacao}
Este trabalho teórico-prático deve ser realizado por grupos de 3 alunos.
Os detalhes da avaliação (datas para submissão do relatório e sua defesa
oral) são os que forem publicados na \cp{página da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo em \textbf{todos}
os exercícios do trabalho, para assim poderem responder a qualquer questão
colocada na \emph{defesa oral} do relatório.

Para cumprir de forma integrada os objectivos do trabalho vamos recorrer
a uma técnica de programa\-ção dita ``\litp{literária}'' \cite{Kn92}, cujo
princípio base é o seguinte:
%
\begin{quote}\em
	Um programa e a sua documentação devem coincidir.
\end{quote}
%
Por outras palavras, o \textbf{código fonte} e a \textbf{documentação} de um
programa deverão estar no mesmo ficheiro.

O ficheiro \texttt{cp2324t.pdf} que está a ler é já um exemplo de
\litp{programação literária}: foi gerado a partir do texto fonte
\texttt{cp2324t.lhs}\footnote{O sufixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrará no \MaterialPedagogico\
desta disciplina des\-com\-pactando o ficheiro \texttt{cp2324t.zip}.

Como se mostra no esquema abaixo, de um único ficheiro (|lhs|)
gera-se um PDF ou faz-se a interpretação do código \Haskell\ que ele inclui:

	\esquema

Vê-se assim que, para além do \GHCi, serão necessários os executáveis \PdfLatex\ e
\LhsToTeX. Para facilitar a instalação e evitar problemas de versões e
conflitos com sistemas operativos, é recomendado o uso do \Docker\ tal como
a seguir se descreve.

\section{Docker} \label{sec:docker}

Recomenda-se o uso do \container\ cuja imagem é gerada pelo \Docker\ a partir do ficheiro
\texttt{Dockerfile} que se encontra na diretoria que resulta de descompactar
\texttt{cp2324t.zip}. Este \container\ deverá ser usado na execução
do \GHCi\ e dos comandos relativos ao \Latex. (Ver também a \texttt{Makefile}
que é disponibilizada.)

Após \href{https://docs.docker.com/engine/install/}{instalar o Docker} e
descarregar o referido zip com o código fonte do trabalho,
basta executar os seguintes comandos:
\begin{Verbatim}[fontsize=\small]
    $ docker build -t cp2324t .
    $ docker run -v ${PWD}:/cp2324t -it cp2324t
\end{Verbatim}
\textbf{NB}: O objetivo é que o container\ seja usado \emph{apenas} 
para executar o \GHCi\ e os comandos relativos ao \Latex.
Deste modo, é criado um \textit{volume} (cf.\ a opção \texttt{-v \$\{PWD\}:/cp2324t}) 
que permite que a diretoria em que se encontra na sua máquina local 
e a diretoria \texttt{/cp2324t} no \container\ sejam partilhadas.

Pretende-se então que visualize/edite os ficheiros na sua máquina local e que
os compile no \container, executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2324t.lhs > cp2324t.tex
    $ pdflatex cp2324t
\end{Verbatim}
\LhsToTeX\ é o pre-processador que faz ``pretty printing'' de código Haskell
em \Latex\ e que faz parte já do \container. Alternativamente, basta executar
\begin{Verbatim}[fontsize=\small]
    $ make
\end{Verbatim}
para obter o mesmo efeito que acima.

Por outro lado, o mesmo ficheiro \texttt{cp2324t.lhs} é executável e contém
o ``kit'' básico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2324t.lhs
\end{Verbatim}

\noindent Abra o ficheiro \texttt{cp2324t.lhs} no seu editor de texto preferido
e verifique que assim é: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
é seleccionado pelo \GHCi\ para ser executado.

\section{Em que consiste o TP}

Em que consiste, então, o \emph{relatório} a que se referiu acima?
É a edição do texto que está a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relatório deverá conter ainda a identificação dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relatório deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o índice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2324t.aux
    $ makeindex cp2324t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. (Como já se disse, pode fazê-lo
correndo simplesmente \texttt{make} no \container.)

No anexo \ref{sec:codigo} disponibiliza-se algum código \Haskell\ relativo
aos problemas que são colocados. Esse anexo deverá ser consultado e analisado
à medida que isso for necessário.

Deve ser feito uso da \litp{programação literária} para documentar bem o código que se
desenvolver, em particular fazendo diagramas explicativos do que foi feito e
tal como se explica no anexo \ref{sec:diagramas} que se segue.

\section{Como exprimir cálculos e diagramas em LaTeX/lhs2TeX} \label{sec:diagramas}

Como primeiro exemplo, estudar o texto fonte (\lhstotex{lhs}) do que está a ler\footnote{
Procure e.g.\ por \texttt{"sec:diagramas"}.} onde se obtém o efeito seguinte:\footnote{Exemplos
tirados de \cite{Ol18}.}
\begin{eqnarray*}
\start
|
	id = split f g
|
\just\equiv{ universal property }
|
     lcbr(
          p1 . id = f
     )(
          p2 . id = g
     )
|
\just\equiv{ identity }
|
     lcbr(
          p1 = f
     )(
          p2 = g
     )
|
\qed
\end{eqnarray*}

Os diagramas podem ser produzidos recorrendo à \emph{package} \Xymatrix, por exemplo:
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

\section{Regra prática para a recursividade mútua em |Nat0|}\label{sec:mr}

Nesta disciplina estudou-se como fazer \pd{programação dinâmica} por cálculo,
recorrendo à lei de recursividade mútua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol18}, página \pageref{eq:fokkinga}.}

Para o caso de funções sobre os números naturais (|Nat0|, com functor |fF
X = 1 + X|) é fácil derivar-se da lei que foi estudada uma
	\emph{regra de algibeira}
	\label{pg:regra}
que se pode ensinar a programadores que não tenham estudado
\cp{Cálculo de Programas}. Apresenta-se de seguida essa regra, tomando como
exemplo o cálculo do ciclo-\textsf{for} que implementa a função de Fibonacci,
recordar o sistema:
\begin{spec}
fib 0 = 1
fib(n+1) = f n

f 0 = 1
f (n+1) = fib n + f n
\end{spec}
Obter-se-á de imediato
\begin{code}
fib' = p1 . for loop init where
   loop(fib,f)=(f,fib+f)
   init = (1,1)
\end{code}
usando as regras seguintes:
\begin{itemize}
\item	O corpo do ciclo |loop| terá tantos argumentos quanto o número de funções mutuamente recursivas.
\item	Para as variáveis escolhem-se os próprios nomes das funções, pela ordem
que se achar conveniente.\footnote{Podem obviamente usar-se outros símbolos, mas numa primeira leitura
dá jeito usarem-se tais nomes.}
\item	Para os resultados vão-se buscar as expressões respectivas, retirando a variável |n|.
\item	Em |init| coleccionam-se os resultados dos casos de base das funções, pela mesma ordem.
\end{itemize}
Mais um exemplo, envolvendo polinómios do segundo grau $ax^2 + b x + c$ em |Nat0|.
Seguindo o método estudado nas aulas\footnote{Secção 3.17 de \cite{Ol18} e tópico
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade mútua} nos vídeos de apoio às aulas teóricas.},
de $f\ x = a x^2 + b x + c$ derivam-se duas funções mutuamente recursivas:
\begin{spec}
f 0 = c
f (n+1) = f n + k n

k 0 = a + b
k(n+1) = k n + 2 a
\end{spec}
Seguindo a regra acima, calcula-se de imediato a seguinte implementação, em Haskell:
\begin{code}
f' a b c = p1 . for loop init where
  loop(f,k) = (f+k,k+2*a)
  init = (c,a+b) 
\end{code}

\section{O mónade das distribuições probabilísticas} \label{sec:probabilities}
%format B = "\mathit B"
%format C = "\mathit C"
Mónades são functores com propriedades adicionais que nos permitem obter
efeitos especiais em progra\-mação. Por exemplo, a biblioteca \Probability\
oferece um mónade para abordar problemas de probabilidades. Nesta biblioteca,
o conceito de distribuição estatística é captado pelo tipo
\begin{eqnarray}
     |newtype Dist a = D {unD :: [(a, ProbRep)]}|
     \label{eq:Dist}
\end{eqnarray}
em que |ProbRep| é um real de |0| a |1|, equivalente a uma escala de $0$ a
$100 \%$.

Cada par |(a,p)| numa distribuição |d::Dist a| indica que a probabilidade
de |a| é |p|, devendo ser garantida a propriedade de  que todas as probabilidades
de |d| somam $100\%$.
Por exemplo, a seguinte distribuição de classificações por escalões de $A$ a $E$,
\[
\begin{array}{ll}
A & \rule{2mm}{3pt}\ 2\%\\
B & \rule{12mm}{3pt}\ 12\%\\
C & \rule{29mm}{3pt}\ 29\%\\
D & \rule{35mm}{3pt}\ 35\%\\
E & \rule{22mm}{3pt}\ 22\%\\
\end{array}
\]
será representada pela distribuição
\begin{code}
d1 :: Dist Char
d1 = D [('A',0.02),('B',0.12),('C',0.29),('D',0.35),('E',0.22)]
\end{code}
que o \GHCi\ mostrará assim:
\begin{Verbatim}[fontsize=\small]
'D'  35.0%
'C'  29.0%
'E'  22.0%
'B'  12.0%
'A'   2.0%
\end{Verbatim}
É possível definir geradores de distribuições, por exemplo distribuições \emph{uniformes},
\begin{code}
d2 = uniform (words "Uma frase de cinco palavras")
\end{code}
isto é
\begin{Verbatim}[fontsize=\small]
     "Uma"  20.0%
   "cinco"  20.0%
      "de"  20.0%
   "frase"  20.0%
"palavras"  20.0%
\end{Verbatim}
distribuição \emph{normais}, eg.\
\begin{code}
d3 = normal [10..20]
\end{code}
etc.\footnote{Para mais detalhes ver o código fonte de \Probability, que é uma adaptação da
biblioteca \PFP\ (``Probabilistic Functional Programming''). Para quem quiser saber mais
recomenda-se a leitura do artigo \cite{EK06}.}
|Dist| forma um \textbf{mónade} cuja unidade é |return a = D [(a,1)]| e cuja composição de Kleisli
é (simplificando a notação)
\begin{spec}
  ((kcomp f g)) a = [(y,q*p) | (x,p) <- g a, (y,q) <- f x]
\end{spec}
em que |g: A -> Dist B| e |f: B -> Dist C| são funções \textbf{monádicas} que representam
\emph{computações probabilísticas}.

Este mónade é adequado à resolução de problemas de \emph{probabilidades e estatística} usando programação funcional, de forma elegante e como caso particular da programação monádica.

\section{Código fornecido}\label{sec:codigo}

\subsection*{Problema 1}

\begin{code}
m1 = [[1,2,3], [4,5,6], [7,8,9]]
m2 = [[1,2,3,4], [5,6,7,8], [9,10,11,12]]
m3 = words "Cristina Monteiro Carvalho Sequeira"

test1 = matrot m1 == [1,2,3,6,9,8,7,4,5]
test2 = matrot m2 == [1,2,3,4,8,12,11,10,9,5,6,7]
test3 = matrot m3 == "CristinaooarieuqeSCMonteirhlavra"
\end{code}

\subsection*{Problema 2}

\begin{code}
test4 = reverseVowels "" == ""
test5 = reverseVowels "ácidos" == "ocidás"
test6 = reverseByPredicate even [1..20] == [1,20,3,18,5,16,7,14,9,12,11,10,13,8,15,6,17,4,19,2]
\end{code}

\subsection*{Problema 3}

Nenhum código é fornecido neste problema.

\subsection*{Problema 4}
Os atrasos, medidos em minutos, são inteiros:
\begin{code}
type Delay = Integer
\end{code}
Amostra de dados apurados por passageiros: \label{pg:dados}
\begin{code}
dados = [((S0,S1),0),((S0,S1),2),((S0,S1),0),((S0,S1),3),((S0,S1),3),
         ((S1,S2),0),((S1,S2),2),((S1,S2),1),((S1,S2),1),((S1,S2),4),
         ((S2,S3),2),((S2,S3),2),((S2,S3),4),((S2,S3),0),((S2,S3),5),
         ((S3,S4),2),((S3,S4),3),((S3,S4),5),((S3,S4),2),((S3,S4),0),
         ((S4,S5),0),((S4,S5),5),((S4,S5),0),((S4,S5),7),((S4,S5),-1)]
\end{code}
\emph{``Funcionalização'' de listas}:
\begin{code}
mkf :: Eq a => [(a, b)] -> a -> Maybe b
mkf = flip Prelude.lookup
\end{code}
Ausência de qualquer atraso:
\begin{code}
instantaneous :: Dist Delay
instantaneous = D [ (0,1) ]
\end{code}

%----------------- Soluções dos alunos -----------------------------------------%

\section{Soluções dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas soluções para os exercícios
propostos, de acordo com o ``layout'' que se fornece.
Não podem ser alterados os nomes ou tipos das funções dadas, mas pode ser
adicionado texto ao anexo, bem como diagramas e/ou outras funções auxiliares
que sejam necessárias.

\noindent
\textbf{Importante}: Não pode ser alterado o texto deste ficheiro fora deste anexo.

\subsection*{Problema 1}
     Para este problema partimos o problema em duas partes. Sabemos que a travessia em espiral é resultante da consecutiva travessia e remoção das bordas da matriz (primeira linhas -> ultima coluna -> última linha ao contrario -> primeira coluna de baixo para cima).
Sendo de destacar que este processo termina quando a matriz esitver vaiza, comportamento o qual que vai ser detetado pela função \textit{outMat}.
     Dito isto, para a resolução deste problema, criamos uma função auxiliar que recebe uma matriz e devolve o par 
da lista correspondente à sua borda e a sua matriz interior. Para esta função funcionar, recorremos a uma função que determina quando uma matriz é vazia \textit{isEmpty},
de forma a determinar o ponto de paragem.
Tendo as funções auxiliares todas devidamente definidas, a função principal \textit{matrot} vai recorrer ao anamorfismo de listas, construindo assim, apartir da matriz inicial, 
uma lista com todas as suas bordas, por fim junta todos estes valores com \textit{concat} de modo ao resultado corresponder 
a uma lista única que representa a rotação em espiral.

Desenhando o diagrama da função principal, obtemos a seguinte firuga:


\begin{eqnarray*}
\xymatrix@@C=2cm{
     |A|^*
& 
& 
\\
     |A|^{**} 
          \ar[u]^{concat}
&
&
     |1 + | |A|^* |x| |A|^{**}  
          \ar[ll]_-{|inList|} 
\\
     |A|^{**}
          \ar[r]_-{|outMat|} 
          \ar[u]^{|anaList testBordas|} 
& 
     |1 + | |A|^{**} 
          \ar[r]_-{|id + bordas|} 
&
     |1 + | |A|^* |x| |A|^{**} 
          \ar[u]_-{|id+id x (cataNat g)|}
}
\end{eqnarray*}

\begin{code}

matrot:: Eq a => [[a]] -> [a]
matrot= concat  . anaList testBordas



testBordas = (id -|- bordas) . outMat


outMat all@((_:_):_) = i2 all
outMat _    = i1 ()


isEmpty:: [[a]] ->Bool
isEmpty= either true false . outMat


applyConcFirst = (conc >< id) . assocl

           
insertPair = (cons >< cons) . assocr. (assocl >< id) . ((id><swap)><id). (assocr><id) . assocl

applyNotEmpty = Cp.cond (isEmpty) (split nil nil)


getLastColumn ::  [[a]] -> ([a], [[a]]) 
getLastColumn =  applyNotEmpty (cataList g)
     where g = either (split nil nil) (insertPair. ((split last init)>< id))
          

getFirstColumnReversed ::  [[a]] -> ([a], [[a]])
getFirstColumnReversed =  (reverse >< id) . (applyNotEmpty (cataList g))
     where g = either (split nil nil) (insertPair. ((split head tail)>< id))

getLastReversed ::  [[a]] -> ([a], [[a]])
getLastReversed =  applyNotEmpty (split (reverse.last) init)

getFirstLine ::  [[a]] -> ([a], [[a]])
getFirstLine =  applyNotEmpty (split head tail)  

 
bordas:: [[a]] -> ([a],[[a]])
bordas = applyConcFirst .(id>< getFirstColumnReversed) . applyConcFirst .(id >< getLastReversed) . applyConcFirst .(id >< getLastColumn) . getFirstLine


\end{code}

\subsection*{Problema 2}


     Face ao problema dado, começamos por fazer uma análise do mesmo e chegamos à conclusão de que a função \textit{reverseVowels} é um caso específico da função \textit{reverseByPredicate} cujo
predicado se trata de uma função que avalia se um caracter é uma vogal. Logo, criamos a função \textit{isVowel} e defenimos a primeira função através das duas funções mencionadas
anteriormente.


     Partindo então para a função genérica, começamos por inserir um indice da sua posição em cada elemento da lista de forma a manter informação das suas posições iniciais, resulando assim numa lista de pares: \((indice,valor)\).
Posteriormente, separamos os elementos cujo valor respeita ou não o predicado , recorrendo assim à funcçao \textit{splitByPredicate}, esta recebe uma função que avalia um elemento e uma lista, transofrmando esta 
num par de listas em que a primeira corresponde aos elementos que respeitam o predicado e a segunda os restantes. 
De seguida, invertemos a ordem dos valores da primeira lista , através da função \textit{reverseP2}, e mantemos a outra inalterada. 
Por fim, juntamos as duas listas e reordenamos de acordo com os índices e retiramos os mesmos , recorrendo assim à função \textit{sortOnAndRemoveP1}.


Diagrama da função \textit{reverseP2}:
\begin{eqnarray*}
\xymatrix@@C=2cm{
     |(A x B)|^* 
          \ar[r]^{|unzip|} 
& 
     | A |^* | x | | B|^* 
          \ar[r]^{|id x reverse|} 
& 
     |A|^* | x | |B|^* \ar[r]^{|uncurry zip|} & |(A x B)|^*
}
\end{eqnarray*}

Diagrama da função \textit{splitByPredicate}:
\begin{eqnarray*}
\xymatrix@@C=2cm{
 && |A|^* \ar[dd]^{|splitByPredicate p|} \ar[ddrr]^-{|filter not p|} \ar[ddll]_-{|filter p|} &  \\
 \\
|A|^* && |A|^* | x | |A|^* \ar[ll]^{|p1|} \ar[rr]_-{|p2|} && |A|^*
}
\end{eqnarray*}

Diagrama da função principal:

\begin{eqnarray*}
\xymatrix@@C=2cm{
 |A|^* \ar[r]^{|zip|}  \ar[d]_-{|reverseByPredicate p|}& |(Nat0 x A)|^* \ar[rr]^{|splitByPredicate (p . p2)|} & & |(Nat0 x A)|^* |x (Nat0 x A)|^* \ar[d]^{|reverseP2 x id|}  \\
 |A|^* & & |(Nat0 x A)|^* \ar[ll]^{|sortOnAndRemoveP1|} & |(Nat0 x A)|^* |x (Nat0 x A)|^* \ar[l]^{|conc|}*
}
\end{eqnarray*}

\begin{code}

reverseVowels :: String -> String
reverseVowels = reverseByPredicate isVowel

isVowel = flip elem "áàãaeéiouyÁÀAEÉIOUY"


reverseByPredicate :: (a -> Bool) -> [a] -> [a]
reverseByPredicate p = sortOnAndRemoveP1 . conc . ( reverseP2 >< id). splitByPredicate (p . p2) .zip nat0

reverseP2 = uncurry zip . ( id >< reverse) . unzip

sortOnAndRemoveP1= map p2 . (sortOn p1)

splitByPredicate p = split (filter p)  (filter (not . p))


\end{code}

\subsection*{Problema 3}


     Para este problema, começamos por analisar as fórmulas matemáticas. Tanto no cosseno hiperbólico quanto no seno hiperbólico, 
é notável que a função objetivo apresenta uma forma semelhante. 
     
     
     Dito isto, se criarmos uma função auxiliar para ser aplicada a \(k\), nomeadamente:

\begin{eqnarray}
    senhk (k) &=& 2k + 1 \label{eq:senhk} \\
    coshk (k) &=& 2k \label{eq:coshk}
\end{eqnarray}


     Dito isto, criamos uma função genérica para os dois casos:
\begin{eqnarray}
    f(x, j) &=& \frac{x^j}{j!} \label{eq:f}
\end{eqnarray}

     Resultando assim nos seguintes somatórios:
\begin{eqnarray}
\start
	\sum_{k=0}^\infty f(x,senhk(k))=\sinh x
	\label{eq:sinh}
\more
	\sum_{k=0}^\infty f(x,coshk(k))=\sinh x
	\nonumber
\end{eqnarray}


     De modo a simplificar os calculos é establecido um valor maximo que \(k\) pode atingir : \(i\).

     Dito isto, podemos partir qualquer um dos somatórios em duas casos diferentes, um caso de paragem quando temos \(i = 0\), e um intermédio/inicial:

\begin{eqnarray}
\start
	\sum_{k=0}^{0} f(x,senhk(k))= f(x,senhk(0)) = f (x,2*0 + 1) = f(x,1)= \frac{x^1}{1!} = x
	\label{eq:paragem}
\more
	\sum_{k=0}^{i} f(x,coshk(k))= f(x,senhk(i)) +\sum_{k=0}^{i-1} f(x,coshk(k))
	\nonumber
\end{eqnarray}

     Partindo agora para a implementação em si, de modo a podermos utilizar o for preedefinido, as funçoes de paragem e intermédias devolvem uma par que corresponde: valor de \(i\) e o valor do sumatório para \(k\) de  \(0\) até \(i\).
Tendo isto em conta, establecemos o valor do caso de paragem na função \textit{start} e o caso intermédio através da função \textit{loop} ,à qual acrescentamos como argumento a função
\textit{senhk}, de modo a este loop poder ser reutilizado para posteriormente construir a função do \(cosh\).
 
     Dito isto a função loop, além de receber o valor de x e a função a ser aplicada ao índice correspondente, vai receber também um par que corresponde ao valor do indice anterior e o sumatório até aquele instante.
Com essas informações, incrementa o índice, utiliza a função \textit{f} que representa a função objetivo para calcular a nova parcela e soma esta ao valor acumulado no sumatório até ao momento.

     Terminado assim o ciclo, pretendemos apenas devolver ao utilizador o resultado do sumatório, ou seja o segundo elemento do par calculado, 
utilizando assim o \textit{wrapper}.

\begin{code}

snh x = wrapper . worker where
        worker = for ((loop x senhk)) ((start x senhk))
        wrapper = p2



senhk = succ . (* 2)



incrementaIndice = (succ >< id) 


loop x func = (id >< myadd). assocr . ((split id ((f x) .func)) >< id) . incrementaIndice

myadd = uncurry (+)


f x = (uncurry (/)) . (id >< fromInteger) . (split (Nat.exp x) Nat.fac) 


start x func= (0,f x (func 0))
\end{code}

\subsection*{Problema 4}
     
     
     Para este problema, começamos por criar a função \textit{mkdist} que para uma dada lista, cria a sua distribuição, sendo as probabilidades determinadas apartir do número de vezes que um dado elemento encontra-se presente na lista.
Para este efeito, a função começa por determinar a probabilidade de cada elemento  da lista, sem ter em conta repetidos. De seguida, utiliza a função \textit{insereProb}, passando
como argumento o par da probabilidade de cada elemento e a lista. Esta função auxiliar recebe um par de um elemento qualquer e uma lista e devolve uma lista em que os
seus elementos são os mesmos que a lista inicial, contudo dentro de um par em que o segundo elemento foi o elemento passado como argumento.
Estando assim os pares de elementos e a sua probabilidade definidos, usamos a função \textit{mkD}, responsável por criar a estrutura de dados desejada devidamente normalizada.

     De modo a criar a base de dados \textit{db}, passamos os dados como argumento à função \textit{criarBase}, esta será responsável por agrupar os dados de acordo com os segmentos e criar as respetivas distribuições
dos seus atrasos, devolvendo assim uma lista de pares de \textbf{Segment} e \textbf{Dist}.

     A função \textit{delay} procura na base de dados a distribuição correspondente ao segmento, caso não encontre nada sobre o mesmo, podemos assumir que não houve atrasos ou seja a probabilidade de o atraso ser 0 é igual a 1.

     Analisando o problema, é visível que o atraso é acumulativo, ou seja, de modo a combinar dois segmentos o atraso no primeiro vai afectar o atraso no segundo. Dito isto esta combinação é realizada
pela função \textit{combinaDelays} responsável por combinar duas distribuições, sendo que os respetivos valores ão ser somados, representando assim a acumulação de atrasos.
Seguindo o mesmo raciocínio, de modo a combinar uma lista de distribuições numa única distribuição, utilizamos a função \textit{combinaListDelays} que corresponde ao catamorfismo de listas que calcula a distribuição final.

Por fim criamos uma função auxiliar \textit{parteSegments} que determina todas as sequências intermédias entre dois \textbf{Enum} do mesmo tipo, obtendo assim o seguinte 
efeito para o nosso caso especifico, determinando todos os segmentos interiores entre
duas paragens.

\(parteSegments (S1,S4) = [(S1,S2),(S2,S3),(S3,S4)] \)

Recorrendo assim às funções auxiliares mencionadas anteriormente, podemos finalmente construir a função \textit{pdelay}, responsável por calcuar a distribuição de atrasos
entre duas paragens, começando por criar a lista de segmentos seguida da transformação dos segmentos nas suas distribuições de atrasos. E por fim, combinar as distribuições
da lista, utilizando assim a função \textit{combinaListDelays}, 
utilizando a função curry de modo aos dois argumentos recebidos poderem ser passados como um par para a função \textit{parteSegments} no início da sua composição.
\begin{code}

db = criaBase dados

criaBase = (map (id >< mkdist)) . (map (split (p1 . head) ((map p2)))) . (groupBy (curry equalFirst))

mkdist = mkD. insereProb . (split ( (1 /). fromIntegral .length) id)

insereProb :: (b,[a]) -> [(a, b)]
insereProb = uncurry $ (map . flip (,)) 

equalFirst :: Eq a => ((a,b),(a,c)) -> Bool
equalFirst =  uncurry (==) . (p1 >< p1)

combinaListDelays = cataList (either (const instantaneous) combinaDelays)

combinaDelays = uncurry (joinWith (+))

delay = (either (const instantaneous) id) . outMaybe . (mkf db)

parteSegments :: Enum a => (a,a) -> [(a,a)]
parteSegments = uncurry zip . split (listEnums . (id >< pred)) (listEnums . (succ >< id))
     where listEnums = uncurry enumFromTo

pdelay = curry (combinaListDelays . (map delay) .  parteSegments)

\end{code}

%----------------- Índice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2324t}

%----------------- Fim do documento -------------------------------------------%
\end{document}
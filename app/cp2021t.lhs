\documentclass[a4paper]{article}
\usepackage[a4paper,left=3cm,right=2cm,top=2.5cm,bottom=2.5cm]{geometry}
\usepackage{palatino}
\usepackage[colorlinks=true,linkcolor=blue,citecolor=blue]{hyperref}
\usepackage{graphicx}
\usepackage{cp2021t} \usepackage{subcaption} \usepackage{adjustbox}
\usepackage{color}
\definecolor{red}{RGB}{255,  0,  0}
\definecolor{blue}{RGB}{0,0,255}
\def\red{\color{red}}
\def\blue{\color{blue}}
%================= local x=====================================================%
\def\getGif#1{\includegraphics[width=0.3\textwidth]{cp2021t_media/#1.png}}
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
%format (const f) = "\underline{" f "}"
%format TLTree = "\mathsf{TLTree}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
\def\ana#1{\mathopen{[\!(}#1\mathclose{)\!]}}
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format (cataA (f) (g)) = "\cata{" f "~" g "}_A"
%format (anaA (f) (g)) = "\ana{" f "~" g "}_A"
%format (cataB (f) (g)) = "\cata{" f "~" g "}_B"
%format (cata (f)) = "\cata{" f "}"
%format (anaB (f) (g)) = "\ana{" f "~" g "}_B"
%format Either a b = a "+" b
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textsc{nb}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format e1 = "e_1 "
%format e2 = "e_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format BTree = "\fun{BTree} "
%format LTree = "\mathsf{LTree}"
%format inNat = "\mathsf{in}"
%format (cataNat (g)) = "\cata{" g "}"
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
%format (anaLTree (x)) = "\mathopen{[\!(}" x "\mathclose{)\!]}"
%format delta = "\Delta "

%---------------------------------------------------------------------------

\title{
       	Cálculo de Programas
\\
       	Trabalho Prático
\\
       	MiEI+LCC --- 2020/21
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
\textbf{Grupo} nr. & 95
\\\hline
a93325 & Henrique Costa
\\
a93163 & José Pedro Fernandes
\\
a93246 & Matilde Bravo
\\
a93272 & Pedro Alves
\end{tabular}
\end{center}

\section{Preâmbulo}

\CP\ tem como objectivo principal ensinar
a progra\-mação de computadores como uma disciplina científica. Para isso
parte-se de um repertório de \emph{combinadores} que formam uma álgebra da
programação (conjunto de leis universais e seus corolários) e usam-se esses
combinadores para construir programas \emph{composicionalmente}, isto é,
agregando programas já existentes.

Na sequência pedagógica dos planos de estudo dos dois cursos que têm
esta disciplina, opta-se pela aplicação deste método à programação
em \Haskell\ (sem prejuízo da sua aplicação a outras linguagens
funcionais). Assim, o presente trabalho prático coloca os
alunos perante problemas concretos que deverão ser implementados em
\Haskell.  Há ainda um outro objectivo: o de ensinar a documentar
programas, a validá-los e a produzir textos técnico-científicos de
qualidade.

\section{Documentação} Para cumprir de forma integrada os objectivos
enunciados acima vamos recorrer a uma técnica de programa\-ção dita
``\litp{literária}'' \cite{Kn92}, cujo princípio base é o seguinte:
%
\begin{quote}\em Um programa e a sua documentação devem coincidir.
\end{quote}
%
Por outras palavras, o código fonte e a documentação de um
programa deverão estar no mesmo ficheiro.

O ficheiro \texttt{cp2021t.pdf} que está a ler é já um exemplo de
\litp{programação literária}: foi gerado a partir do texto fonte
\texttt{cp2021t.lhs}\footnote{O suffixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrará no
\MaterialPedagogico\ desta disciplina descompactando o ficheiro
\texttt{cp2021t.zip} e executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2021t.lhs > cp2021t.tex
    $ pdflatex cp2021t
\end{Verbatim}
em que \href{https://hackage.haskell.org/package/lhs2tex}{\texttt\LhsToTeX} é
um pre-processador que faz ``pretty printing''
de código Haskell em \Latex\ e que deve desde já instalar executando
\begin{Verbatim}[fontsize=\small]
    $ cabal install lhs2tex --lib
\end{Verbatim}
Por outro lado, o mesmo ficheiro \texttt{cp2021t.lhs} é executável e contém
o ``kit'' básico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2021t.lhs
\end{Verbatim}

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
module Main where
import Cp
import List hiding (fac)
import Nat
import LTree
import Data.List hiding (find)
import Test.QuickCheck hiding ((><),choose,collect)
import qualified Test.QuickCheck as QuickCheck
import Graphics.Gloss
import Graphics.Gloss.Interface.Pure.Game
import Control.Monad
import Control.Applicative hiding ((<|>))
import System.Process
\end{code}
%endif

\noindent Abra o ficheiro \texttt{cp2021t.lhs} no seu editor de texto preferido
e verifique que assim é: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
é seleccionado pelo \GHCi\ para ser executado.

\section{Como realizar o trabalho}
Este trabalho teórico-prático deve ser realizado por grupos de 3 (ou 4) alunos.
Os detalhes da avaliação (datas para submissão do relatório e sua defesa
oral) são os que forem publicados na \cp{página da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo
de trabalho por forma a poderem responder às questões que serão colocadas
na \emph{defesa oral} do relatório.

Em que consiste, então, o \emph{relatório} a que se refere o parágrafo anterior?
É a edição do texto que está a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relatório deverá conter ainda a identificação dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relatório deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o índice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2021t.aux
    $ makeindex cp2021t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. Dever-se-á ainda instalar o utilitário
\QuickCheck,
que ajuda a validar programas em \Haskell\ e a biblioteca \gloss{Gloss} para
geração de gráficos 2D:
\begin{Verbatim}[fontsize=\small]
    $ cabal install QuickCheck gloss --lib
\end{Verbatim}
Para testar uma propriedade \QuickCheck~|prop|, basta invocá-la com o comando:
\begin{verbatim}
    > quickCheck prop
    +++ OK, passed 100 tests.
\end{verbatim}
Pode-se ainda controlar o número de casos de teste e sua complexidade,
como o seguinte exemplo mostra:
\begin{verbatim}
    > quickCheckWith stdArgs { maxSuccess = 200, maxSize = 10 } prop
    +++ OK, passed 200 tests.
\end{verbatim}
Qualquer programador tem, na vida real, de ler e analisar (muito!) código
escrito por outros. No anexo \ref{sec:codigo} disponibiliza-se algum
código \Haskell\ relativo aos problemas que se seguem. Esse anexo deverá
ser consultado e analisado à medida que isso for necessário.

\subsection{Stack}

O \stack{Stack} é um programa útil para criar, gerir e manter projetos em \Haskell.
Um projeto criado com o Stack possui uma estrutura de pastas muito específica:

\begin{itemize}
\item Os módulos auxiliares encontram-se na pasta \emph{src}.
\item O módulos principal encontra-se na pasta \emph{app}.
\item A lista de depêndencias externas encontra-se no ficheiro \emph{package.yaml}.
\end{itemize}

Pode aceder ao \GHCi\ utilizando o comando:
\begin{verbatim}
stack ghci
\end{verbatim}

Garanta que se encontra na pasta mais externa \textbf{do projeto}.
A primeira vez que correr este comando as depêndencias externas serão instaladas automaticamente.

Para gerar o PDF, garanta que se encontra na diretoria \emph{app}.

\Problema

Os \emph{tipos de dados algébricos} estudados ao longo desta disciplina oferecem
uma grande capacidade expressiva ao programador. Graças à sua flexibilidade,
torna-se trivial implementar \DSL s
e até mesmo \href{http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf}{linguagens de programação}.

Paralelamente, um tópico bastante estudado no âmbito de \DL\
é a derivação automática de expressões matemáticas, por exemplo, de derivadas.
Duas técnicas que podem ser utilizadas para o cálculo de derivadas são:

\begin{itemize}
\item \emph{Symbolic differentiation}
\item \emph{Automatic differentiation}
\end{itemize}

\emph{Symbolic differentiation} consiste na aplicação sucessiva de transformações
(leia-se: funções) que sejam congruentes com as regras de derivação. O resultado
final será a expressão da derivada.

O leitor atento poderá notar um problema desta técnica: a expressão
inicial pode crescer de forma descontrolada, levando a um cálculo pouco eficiente.
\emph{Automatic differentiation} tenta resolver este problema,
calculando \textbf{o valor} da derivada da expressão em todos os passos.
Para tal, é necessário calcular o valor da expressão \textbf{e} o valor da sua derivada.

Vamos de seguida definir uma linguagem de expressões matemáticas simples e
implementar as duas técnicas de derivação automática.
Para isso, seja dado o seguinte tipo de dados,

\begin{code}
data ExpAr a = X
           | N a
           | Bin BinOp (ExpAr a) (ExpAr a)
           | Un UnOp (ExpAr a)
           deriving (Eq, Show)
\end{code}

\noindent
onde |BinOp| e |UnOp| representam operações binárias e unárias, respectivamente:

\begin{code}
data BinOp = Sum
           | Product
           deriving (Eq, Show)

data UnOp = Negate
          | E
          deriving (Eq, Show)
\end{code}

\noindent
O construtor |E| simboliza o exponencial de base $e$.

Assim, cada expressão pode ser uma variável, um número, uma operação binária
aplicada às devidas expressões, ou uma operação unária aplicada a uma expressão.
Por exemplo,
\begin{spec}
Bin Sum X (N 10)
\end{spec}
designa |x+10| na notação matemática habitual.

\begin{enumerate}
\item A definição das funções |inExpAr| e |baseExpAr| para este tipo é a seguinte:
\begin{code}
inExpAr = either (const X) num_ops where
  num_ops = either N ops
  ops     = either bin (uncurry Un)
  bin(op, (a, b)) = Bin op a b

baseExpAr f g h j k l z = f -|- (g -|- (h >< (j >< k) -|- l >< z))
\end{code}

  Defina as funções |outExpAr| e |recExpAr|,
  e teste as propriedades que se seguem.
  \begin{propriedade}
    |inExpAr| e |outExpAr| são testemunhas de um isomorfismo,
    isto é,
    |inExpAr . outExpAr = id| e |outExpAr . idExpAr = id|:
\begin{code}
prop_in_out_idExpAr :: (Eq a) => ExpAr a -> Bool
prop_in_out_idExpAr = inExpAr . outExpAr .==. id

prop_out_in_idExpAr :: (Eq a) => OutExpAr a -> Bool
prop_out_in_idExpAr = outExpAr . inExpAr .==. id
\end{code}
    \end{propriedade}

  \item Dada uma expressão aritmética e um escalar para substituir o |X|,
	a função

\begin{quote}
      |eval_exp :: Floating a => a -> (ExpAr a) -> a|
\end{quote}

\noindent calcula o resultado da expressão. Na página \pageref{pg:P1}
    esta função está expressa como um catamorfismo. Defina o respectivo gene
    e, de seguida, teste as propriedades:
    \begin{propriedade}
       A função |eval_exp| respeita os elementos neutros das operações.
\begin{code}
prop_sum_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idr a exp = eval_exp a exp .=?=. sum_idr where
  sum_idr = eval_exp a (Bin Sum exp (N 0))

prop_sum_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idl a exp = eval_exp a exp .=?=. sum_idl where
  sum_idl = eval_exp a (Bin Sum (N 0) exp)

prop_product_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idr a exp = eval_exp a exp .=?=. prod_idr where
  prod_idr = eval_exp a (Bin Product exp (N 1))

prop_product_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idl a exp = eval_exp a exp .=?=. prod_idl where
  prod_idl = eval_exp a (Bin Product (N 1) exp)

prop_e_id :: (Floating a, Real a) => a -> Bool
prop_e_id a = eval_exp a (Un E (N 1)) == expd 1

prop_negate_id :: (Floating a, Real a) => a -> Bool
prop_negate_id a = eval_exp a (Un Negate (N 0)) == 0
\end{code}
    \end{propriedade}
    \begin{propriedade}
      Negar duas vezes uma expressão tem o mesmo valor que não fazer nada.
\begin{code}
prop_double_negate :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_double_negate a exp = eval_exp a exp .=?=. eval_exp a (Un Negate (Un Negate exp))
\end{code}
    \end{propriedade}

  \item É possível otimizar o cálculo do valor de uma expressão aritmética tirando proveito
  dos elementos absorventes de cada operação. Implemente os genes da função
\begin{spec}
      optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
\end{spec}
  que se encontra na página \pageref{pg:P1} expressa como um hilomorfismo\footnote{Qual é a vantagem de implementar a função |optimize_eval| utilizando um hilomorfismo em vez de utilizar um catamorfismo com um gene "inteligente"?}
  e teste as propriedades:

    \begin{propriedade}
      A função |optimize_eval| respeita a semântica da função |eval|.
\begin{code}
prop_optimize_respects_semantics :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_optimize_respects_semantics a exp = eval_exp a exp .=?=. optmize_eval a exp
\end{code}
    \end{propriedade}


\item Para calcular a derivada de uma expressão, é necessário aplicar transformações
à expressão original que respeitem as regras das derivadas:\footnote{%
	Apesar da adição e multiplicação gozarem da propriedade comutativa,
	há que ter em atenção a ordem das operações por causa dos testes.}

\begin{itemize}
  \item Regra da soma:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)+g(x))=\frac{d}{dx}(f(x))+\frac{d}{dx}(g(x))
\end{eqnarray*}
  \item Regra do produto:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)g(x))=f(x)\cdot \frac{d}{dx}(g(x))+\frac{d}{dx}(f(x))\cdot g(x)
\end{eqnarray*}
\end{itemize}

  Defina o gene do catamorfismo que ocorre na função
    \begin{quote}
      |sd :: Floating a => ExpAr a -> ExpAr a|
    \end{quote}
  que, dada uma expressão aritmética, calcula a sua derivada.
  Testes a fazer, de seguida:
    \begin{propriedade}
       A função |sd| respeita as regras de derivação.
\begin{code}
prop_const_rule :: (Real a, Floating a) => a -> Bool
prop_const_rule a = sd (N a) == N 0

prop_var_rule :: Bool
prop_var_rule = sd X == N 1

prop_sum_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_sum_rule exp1 exp2 = sd (Bin Sum exp1 exp2) == sum_rule where
  sum_rule = Bin Sum (sd exp1) (sd exp2)

prop_product_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_product_rule exp1 exp2 = sd (Bin Product exp1 exp2) == prod_rule where
  prod_rule =Bin Sum (Bin Product exp1 (sd exp2)) (Bin Product (sd exp1) exp2)

prop_e_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_e_rule exp = sd (Un E exp) == Bin Product (Un E exp) (sd exp)

prop_negate_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_negate_rule exp = sd (Un Negate exp) == Un Negate (sd exp)
\end{code}
    \end{propriedade}

\item Como foi visto, \emph{Symbolic differentiation} não é a técnica
mais eficaz para o cálculo do valor da derivada de uma expressão.
\emph{Automatic differentiation} resolve este problema cálculando o valor
da derivada em vez de manipular a expressão original.

  Defina o gene do catamorfismo que ocorre na função
    \begin{spec}
    ad :: Floating a => a -> ExpAr a -> a
    \end{spec}
  que, dada uma expressão aritmética e um ponto,
  calcula o valor da sua derivada nesse ponto,
  sem transformar manipular a expressão original.
  Testes a fazer, de seguida:

    \begin{propriedade}
       Calcular o valor da derivada num ponto |r| via |ad| é equivalente a calcular a derivada da expressão e avalia-la no ponto |r|.
\begin{code}
prop_congruent :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_congruent a exp = ad a exp .=?=. eval_exp a (sd exp)
\end{code}
    \end{propriedade}
\end{enumerate}

\Problema

Nesta disciplina estudou-se como fazer \pd{programação dinâmica} por cálculo,
recorrendo à lei de recursividade mútua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol18}, página \pageref{eq:fokkinga}.}

Para o caso de funções sobre os números naturais (|Nat0|, com functor |fF
X = 1 + X|) é fácil derivar-se da lei que foi estudada uma
	\emph{regra de algibeira}
	\label{pg:regra}
que se pode ensinar a programadores que não tenham estudado
\cp{Cálculo de Programas}. Apresenta-se de seguida essa regra, tomando como exemplo o
cálculo do ciclo-\textsf{for} que implementa a função de Fibonacci, recordar
o sistema
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
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade mútua} nos vídeos das aulas teóricas.},
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
O que se pede então, nesta pergunta?
Dada a fórmula que dá o |n|-ésimo \catalan{número de Catalan},
\begin{eqnarray}
	C_n = \frac{(2n)!}{(n+1)! (n!) }
	\label{eq:cat}
\end{eqnarray}
derivar uma implementação de $C_n$ que não calcule factoriais nenhuns.
Isto é, derivar um ciclo-\textsf{for}
\begin{spec}
cat = cdots . for loop init where cdots
\end{spec}
que implemente esta função.

\begin{propriedade}
A função proposta coincidem com a definição dada:
\begin{code}
prop_cat = (>=0) .==>. (catdef  .==. cat)
\end{code}
\end{propriedade}
%
\textbf{Sugestão}: Começar por estudar muito bem o processo de cálculo dado
no anexo \ref{sec:recmul} para o problema (semelhante) da função exponencial.


\Problema

As \bezier{curvas de Bézier}, designação dada em honra ao engenheiro
\href{https://en.wikipedia.org/wiki/Pierre_B%C3%A9zier}{Pierre Bézier},
são curvas ubíquas na área de computação gráfica, animação e modelação.
Uma curva de Bézier é uma curva paramétrica, definida por um conjunto
$\{P_0,...,P_N\}$ de pontos de controlo, onde $N$ é a ordem da curva.

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.8\textwidth]{cp2021t_media/Bezier_curves.png}
  \caption{Exemplos de curvas de Bézier retirados da \bezier{ Wikipedia}.}
\end{figure}

O algoritmo de \emph{De Casteljau} é um método recursivo capaz de calcular
curvas de Bézier num ponto. Apesar de ser mais lento do que outras abordagens,
este algoritmo é numericamente mais estável, trocando velocidade por correção.

De forma sucinta, o valor de uma curva de Bézier de um só ponto $\{P_0\}$
(ordem $0$) é o próprio ponto $P_0$. O valor de uma curva de Bézier de ordem
$N$ é calculado através da interpolação linear da curva de Bézier dos primeiros
$N-1$ pontos e da curva de Bézier dos últimos $N-1$ pontos.

A interpolação linear entre 2 números, no intervalo $[0, 1]$, é dada pela
seguinte função:

\begin{code}
linear1d :: Rational -> Rational -> OverTime Rational
linear1d a b = formula a b where
  formula :: Rational -> Rational -> Float -> Rational
  formula x y t = ((1.0 :: Rational) - (toRational t)) * x + (toRational t) * y
\end{code}
%
A interpolação linear entre 2 pontos de dimensão $N$ é calculada através
da interpolação linear de cada dimensão.

O tipo de dados |NPoint| representa um ponto com $N$ dimensões.
\begin{code}
type NPoint = [Rational]
\end{code}
Por exemplo, um ponto de 2 dimensões e um ponto de 3 dimensões podem ser
representados, respetivamente, por:
\begin{spec}
p2d = [1.2, 3.4]
p3d = [0.2, 10.3, 2.4]
\end{spec}
%
O tipo de dados |OverTime a| representa um termo do tipo |a| num dado instante
(dado por um |Float|).
\begin{code}
type OverTime a = Float -> a
\end{code}
%
O anexo \ref{sec:codigo} tem definida a função
    \begin{spec}
    calcLine :: NPoint -> (NPoint -> OverTime NPoint)
    \end{spec}
que calcula a interpolação linear entre 2 pontos, e a função
    \begin{spec}
    deCasteljau :: [NPoint] -> OverTime NPoint
    \end{spec}
que implementa o algoritmo respectivo.

\begin{enumerate}

\item Implemente |calcLine| como um catamorfismo de listas,
testando a sua definição com a propriedade:
    \begin{propriedade} Definição alternativa.
\begin{code}
prop_calcLine_def :: NPoint -> NPoint -> Float -> Bool
prop_calcLine_def p q d = calcLine p q d ==  zipWithM linear1d p q d
\end{code}
    \end{propriedade}

\item Implemente a função |deCasteljau| como um hilomorfismo, testando agora a propriedade:
    \begin{propriedade}
      Curvas de Bézier são simétricas.
\begin{code}
prop_bezier_sym :: [[Rational]] -> Gen Bool
prop_bezier_sym l = all (< delta) . calc_difs . bezs <$> elements ps  where
  calc_difs = (\(x, y) -> zipWith (\w v -> if w >= v then w - v else v - w) x y)
  bezs t    = (deCasteljau l t, deCasteljau (reverse l) (fromRational (1 - (toRational t))))
  delta = 1e-2
\end{code}
    \end{propriedade}

  \item Corra a função |runBezier| e aprecie o seu trabalho\footnote{%
        A representação em Gloss é uma adaptação de um
        \href{https://github.com/hrldcpr/Bezier.hs}{projeto}
        de Harold Cooper.} clicando na janela que é aberta (que contém, a verde, um ponto
        inicila) com o botão esquerdo do rato para adicionar mais pontos.
        A tecla |Delete| apaga o ponto mais recente.

\end{enumerate}

\Problema

Seja dada a fórmula que calcula a média de uma lista não vazia $x$,
\begin{equation}
avg\ x = \frac 1 k\sum_{i=1}^{k} x_i
\end{equation}
onde $k=length\ x$. Isto é, para sabermos a média de uma lista precisamos de dois catamorfismos: o que faz o somatório e o que calcula o comprimento a lista.
Contudo, é facil de ver que
\begin{quote}
	$avg\ [a]=a$
\\
	$avg (a:x) = \frac 1 {k+1}(a+\sum_{i=1}^{k} x_i) = \frac{a+k(avg\ x)}{k+1}$ para $k=length\ x$
\end{quote}
Logo $avg$ está em recursividade mútua com $length$ e o par de funções pode ser expresso por um único catamorfismo, significando que a lista apenas é percorrida uma vez.

\begin{enumerate}

\item	Recorra à lei de recursividade mútua para derivar a função
|avg_aux = cata (either b q)| tal que
|avg_aux = split avg length| em listas não vazias.

\item	Generalize o raciocínio anterior para o cálculo da média de todos os elementos de uma \LTree\ recorrendo a uma única travessia da árvore (i.e.\ catamorfismo).

\end{enumerate}
Verifique as suas funções testando a propriedade seguinte:
\begin{propriedade}
A média de uma lista não vazia e de uma \LTree\ com os mesmos elementos coincide,
a menos de um erro de 0.1 milésimas:
\begin{code}
prop_avg :: Ord a => [a] -> Property
prop_avg = nonempty .==>. diff .<=. const 0.000001 where
   diff l = avg l - (avgLTree . genLTree) l
   genLTree = anaLTree lsplit
   nonempty = (>[])
\end{code}
\end{propriedade}

\Problema	(\textbf{NB}: Esta questão é \textbf{opcional} e funciona como \textbf{valorização} apenas para os alunos que desejarem fazê-la.)

\vskip 1em \noindent
Existem muitas linguagens funcionais para além do \Haskell, que é a linguagem usada neste trabalho prático. Uma delas é o \Fsharp\ da Microsoft. Na directoria \verb!fsharp! encontram-se os módulos \Cp, \Nat\ e \LTree\ codificados em \Fsharp. O que se pede é a biblioteca \BTree\ escrita na mesma linguagem.

Modo de execução: o código que tiverem produzido nesta pergunta deve ser colocado entre o \verb!\begin{verbatim}! e o \verb!\end{verbatim}! da correspondente parte do anexo \ref{sec:resolucao}. Para além disso, os grupos podem demonstrar o código na oral.

\newpage

\part*{Anexos}

\appendix

\section{Como exprimir cálculos e diagramas em LaTeX/lhs2tex}
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

Os diagramas podem ser produzidos recorrendo à \emph{package} \LaTeX\
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

\section{Programação dinâmica por recursividade múltipla}\label{sec:recmul}
Neste anexo dão-se os detalhes da resolução do Exercício \ref{ex:exp} dos apontamentos da
disciplina\footnote{Cf.\ \cite{Ol18}, página \pageref{ex:exp}.},
onde se pretende implementar um ciclo que implemente
o cálculo da aproximação até |i=n| da função exponencial $exp\ x = e^x$,
via série de Taylor:
\begin{eqnarray}
	exp\ x
& = &
	\sum_{i=0}^{\infty} \frac {x^i} {i!}
\end{eqnarray}
Seja $e\ x\ n = \sum_{i=0}^{n} \frac {x^i} {i!}$ a função que dá essa aproximação.
É fácil de ver que |e x 0 = 1| e que $|e x (n+1)| = |e x n| + \frac {x^{n+1}} {(n+1)!}$.
Se definirmos $|h x n| = \frac {x^{n+1}} {(n+1)!}$ teremos |e x| e |h x| em recursividade
mútua. Se repetirmos o processo para |h x n| etc obteremos no total três funções nessa mesma
situação:
\begin{spec}
e x 0 = 1
e x (n+1) = h x n + e x n

h x 0 = x
h x (n+1) = x/(s n) * h x n

s 0 = 2
s (n+1) = 1 + s n
\end{spec}
Segundo a \emph{regra de algibeira} descrita na página \ref{pg:regra} deste enunciado,
ter-se-á, de imediato:
\begin{code}
e' x = prj . for loop init where
     init = (1,x,2)
     loop(e,h,s)=(h+e,x/s*h,1+s)
     prj(e,h,s) = e
\end{code}

\section{Código fornecido}\label{sec:codigo}

\subsection*{Problema 1}

\begin{code}
expd :: Floating a => a -> a
expd = Prelude.exp

type OutExpAr a = Either () (Either a (Either (BinOp, (ExpAr a, ExpAr a)) (UnOp, ExpAr a)))
\end{code}

\subsection*{Problema 2}
Definição da série de Catalan usando factoriais (\ref{eq:cat}):
\begin{code}
catdef n = div (fac((2*n))) ((fac((n+1))*(fac n)))
\end{code}
Oráculo para inspecção dos primeiros 26 números de Catalan\footnote{Fonte:
\catalan{Wikipedia}.}:
\begin{code}
oracle = [
    1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900, 2674440, 9694845,
    35357670, 129644790, 477638700, 1767263190, 6564120420, 24466267020,
    91482563640, 343059613650, 1289904147324, 4861946401452
    ]
\end{code}

\subsection*{Problema 3}
Algoritmo:
\begin{spec}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau [] = nil
deCasteljau [p] = const p
deCasteljau l = \pt -> (calcLine (p pt) (q pt)) pt where
  p = deCasteljau (init l)
  q = deCasteljau (tail l)
\end{spec}
Função auxiliar:
\begin{spec}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine [] = const nil
calcLine(p:x) = curry g p (calcLine x) where
   g :: (Rational, NPoint -> OverTime NPoint) -> (NPoint -> OverTime NPoint)
   g (d,f) l = case l of
       []     -> nil
       (x:xs) -> \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z
\end{spec}
2D:
\begin{code}
bezier2d :: [NPoint] -> OverTime (Float, Float)
bezier2d [] = const (0, 0)
bezier2d l = \z -> (fromRational >< fromRational) . (\[x, y] -> (x, y)) $ ((deCasteljau l) z)
\end{code}
Modelo:
\begin{code}
data World = World { points :: [NPoint]
                   , time :: Float
                   }
initW :: World
initW = World [] 0

tick :: Float -> World -> World
tick dt world = world { time=(time world) + dt }

actions :: Event -> World -> World
actions (EventKey (MouseButton LeftButton) Down _ p) world =
  world {points=(points world) ++ [(\(x, y) -> map toRational [x, y]) p]}
actions (EventKey (SpecialKey KeyDelete) Down _ _) world =
    world {points = cond (== []) id init (points world)}
actions _ world = world

scaleTime :: World -> Float
scaleTime w = (1 + cos (time w)) / 2

bezier2dAtTime :: World -> (Float, Float)
bezier2dAtTime w = (bezier2dAt w) (scaleTime w)

bezier2dAt :: World -> OverTime (Float, Float)
bezier2dAt w = bezier2d (points w)

thicCirc :: Picture
thicCirc = ThickCircle 4 10

ps :: [Float]
ps = map fromRational ps' where
  ps' :: [Rational]
  ps' = [0, 0.01..1] -- interval
\end{code}
Gloss:
\begin{code}
picture :: World -> Picture
picture world = Pictures
  [ animateBezier (scaleTime world) (points world)
  , Color white . Line . map (bezier2dAt world) $ ps
  , Color blue . Pictures $ [Translate (fromRational x) (fromRational y) thicCirc | [x, y] <- points world]
  , Color green $ Translate cx cy thicCirc
  ] where
  (cx, cy) = bezier2dAtTime world
\end{code}
Animação:
\begin{code}
animateBezier :: Float -> [NPoint] -> Picture
animateBezier _ [] = Blank
animateBezier _ [_] = Blank
animateBezier t l = Pictures
  [ animateBezier t (init l)
  , animateBezier t (tail l)
  , Color red . Line $ [a, b]
  , Color orange $ Translate ax ay thicCirc
  , Color orange $ Translate bx by thicCirc
  ] where
  a@(ax, ay) = bezier2d (init l) t
  b@(bx, by) = bezier2d (tail l) t
\end{code}
Propriedades e \emph{main}:
\begin{code}
runBezier :: IO ()
runBezier = play (InWindow "Bézier" (600, 600) (0,  0))
  black 50 initW picture actions tick

runBezierSym :: IO ()
runBezierSym = quickCheckWith (stdArgs {maxSize = 20, maxSuccess = 200} ) prop_bezier_sym
\end{code}

Compilação e execução dentro do interpretador:\footnote{Pode ser útil em testes
envolvendo \gloss{Gloss}. Nesse caso, o teste em causa deve fazer parte de uma função
|main|.}
\begin{code}
main = runBezier

run = do { system "ghc cp2021t" ; system "./cp2021t" }
\end{code}

\subsection*{QuickCheck}
Código para geração de testes:
\begin{code}
instance Arbitrary UnOp where
  arbitrary = elements [Negate, E]

instance Arbitrary BinOp where
  arbitrary = elements [Sum, Product]

instance (Arbitrary a) => Arbitrary (ExpAr a) where
  arbitrary = do
    binop <- arbitrary
    unop  <- arbitrary
    exp1  <- arbitrary
    exp2  <- arbitrary
    a     <- arbitrary

    frequency . map (id >< pure) $ [(20, X), (15, N a), (35, Bin binop exp1 exp2), (30, Un unop exp1)]


infixr 5 .=?=.
(.=?=.) :: Real a => a -> a -> Bool
(.=?=.) x y = (toRational x) == (toRational y)


\end{code}

\subsection*{Outras funções auxiliares}
%----------------- Outras definições auxiliares -------------------------------------------%
Lógicas:
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
\end{code}

%----------------- Soluções dos alunos -----------------------------------------%

\section{Soluções dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas soluções para os exercícios
propostos, de acordo com o "layout" que se fornece. Não podem ser
alterados os nomes ou tipos das funções dadas, mas pode ser adicionado
texto, disgramas e/ou outras funções auxiliares que sejam necessárias.

Valoriza-se a escrita de \emph{pouco} código que corresponda a soluções
simples e elegantes.

\subsection*{Problema 1} \label{pg:P1}
São dadas:
\begin{code}
cataExpAr g = g . recExpAr (cataExpAr g) . outExpAr
anaExpAr g = inExpAr . recExpAr (anaExpAr g) . g
hyloExpAr h g = cataExpAr h . anaExpAr g

eval_exp :: Floating a => a -> (ExpAr a) -> a
eval_exp a = cataExpAr (g_eval_exp a)

optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
optmize_eval a = hyloExpAr (gopt a) clean

sd :: Floating a => ExpAr a -> ExpAr a
sd = p2 . cataExpAr sd_gen

ad :: Floating a => a -> ExpAr a -> a
ad v = p2 . cataExpAr (ad_gen v)
\end{code}
Definir:

\subsubsection*{outExpAr}
\par
A implementação desta função é deduzida a partir da própria propriedade
enunciada:

\linebreak
\linebreak
\textit{outExpAr . inExpAr .==. id}

\linebreak
\linebreak

\par
Deste modo, para descobrirmos \textbf{outExpAr} basta fazermos sua composição
com \textbf{inExpAr} e igualarmos ao \textbf{id}. Aplicando algumas propriedades,
    temos:

\begin{eqnarray*}
\start
| outExpAr . inExpAr = id |
%
\just\equiv{def-inExpAr}
%
    |outExpAr . either (const X) (num_ops) = id|
%
\just\equiv{ fusão-|+| }
%
    |either (outExpAr . const X) (outExpAr . num_ops) = id|
%
\just\equiv{ Universal-|+|, Natural-id}
%
    |lcbr(
          outExpAr . (const X) = i1
    )(
          outExpAr . num_ops = i2
    )|
%
\just\equiv{def-|num_ops|}
%
    |lcbr(
          outExpAr . (const X) = i1
    )(
          outExpAr . (either (N) (ops)) = i2
    )|
%
\just\equiv{fusão-|+|}
%
    |lcbr(
          outExpAr . (const X) = i1
    )(
          either (outExpAr . N) (outExpAr . ops) = i2
    )|
%
\just\equiv{Universal-|+|}
%
\left\{
   \begin{array}{lll}
      |outExpAr . (const X) = i1|\\
      |outExpAr . N = i2 . i1|\\
      |outExpAr . ops = i2 . i2|
  \end{array}
\right.
%
\just\equiv{def-ops}
%
\left\{
   \begin{array}{lll}
      |outExpAr . (const X) = i1|\\
      |outExpAr . N = i2 . i1|\\
      |outExpAr . (either (bin) (uncurry Un)) = i2 . i2|
  \end{array}
\right.
%
\just\equiv{fusao-|+|}
%
\left\{
   \begin{array}{lll}
      |outExpAr . (const X) = i1|\\
      |outExpAr . N = i2 . i1|\\
      |either (outExpAr . bin) (outExpAr . (uncurry Un)) = i2 . i2|
  \end{array}
\right.
%
\just\equiv{universal-|+|}
%
\left\{
   \begin{array}{llll}
      |outExpAr . (const X) = i1|\\
      |outExpAr . N = i2 . i1|\\
      |outExpAr . bin = i2 . i2 . i1|\\
      |outExpAr . (uncurry Un) = i2 . i2 .i2|
  \end{array}
\right.
%
\just\equiv{introdução de variáveis-|+|, def-comp}
%
\left\{
   \begin{array}{llll}
      |outExpAr (const X a) = i1(a)|\\
      |outExpAr (N a) = i2 (i1(a))|\\
      |outExpAr (bin a) = i2 (i2 (i1 (a)))|\\
      |outExpAr (uncurry Un a) = i2(i2(i2(a)))|
  \end{array}
\right.
%
\qed
\end{eqnarray*}

Transformando esse sistema de equações para notação de \textbf{Haskell}, temos a
solução:

\begin{code}
outExpAr :: ExpAr a -> Either () (Either a (Either (BinOp, (ExpAr a, ExpAr a)) (UnOp, ExpAr a)))
outExpAr (X) = i1 ()
outExpAr (N a) = i2 (i1 (a))
outExpAr (Un op a) = i2 (i2 (i2 (op,a)))
outExpAr (Bin op a b) = i2 (i2 (i1 (op, (a , b))))
\end{code}

\subsubsection*{recExpAr}
\par
Sabendo agora o \textit{tipo de saída do outExpAr}, passamos a conhecer o
\textit{tipo de entrada da função recExpAr}. Como tal função será a
responsável por chamar recursivamente o catamorfismo para as "\textit{ExpAr's}"
presentes no tipo de entrada, basta separarmos a função nos casos específicos em
que temos de invocar o catamorfismo recursivamente, isto é, caso o tipo de
entrada for do tipo \textbf{(BinOp,(ExpAr a,ExpAr a)} ou  \textbf{(UnOp,ExpAr a)}. Caso
            contrário, não haverá recursividade e basta invocarmos o \textbf{id}

\linebreak
Para uma melhor ilustração deste processo, segue um diagrama do estado da
resolução até este momento:

\par

\begin{eqnarray*}
\xymatrix@@C=3cm{
    |ExpAr a|
           \ar[d]_-{|cataExpAr (gene)|}
           \ar[r]_-{|outExpAr|}
&
    |1 + (A + ((BinOp, (ExpAr a, ExpAr a)) + (UnOp, ExpAr a)))|
           \ar[d]^-{|recExpAr (cataExpAr (gene))|}
\\
     |(Floating) C|
&
     |1 + (A + ((BinOp,(C,C) + (UnOp, C))))|
           \ar[l]^-{gene}
}
\end{eqnarray*}

Concluindo, temos então recExpAr como:

\begin{code}

recExpAr f = id -|- (id -|- ((f1 f) -|- (f2 f))) where
  f1 f (op,(a,b)) = (op, (f a, f b))
  f2 f (op,a) = (op, f a)


\end{code}

\subsubsection*{g\_eval\_exp}

Estamos agora perante o \textbf{gene} mencionado no diagrama anterior. Este gene
terá o \textit{tipo de entrada} correspondente ao tipo de saída da função
\textbf{recExpAr} que consiste basicamente nos \textit{termos de uma expressão} já
processados atomicamente, prontos para serem consumidos pelos operadores matemáticos
envolvidos na questão.

Para os casos mais simples, isto é, a função receber um
termo \textit{etiquetado somente à esquerda}, basta retornar o valor numérico
associado ao gene. Por outras palavras, estamos a substituir uma constante
\textbf{X} por um dado valor. Como o gene parte de uma união disjunta, o seu
corpo principal será composto por um \textbf{either}. E, como um \textbf{either}
possui funções internamente para processar seu argumento, devemos inserir a
função \textbf{const value} para representar o caso mencionado anteriormente
(onde \textit{value} representa o valor da variável \textit{x}). Outro caso
simples é dos \textit{inputs etiquetados à direita e à esquerda}, isto é, que
chegam por exemplo como \textit{i2(i1(input))}. Este será o caso em que
estaremos presente um número por si só, e então basta aplicar a identidade. De resto é feito \textbf{pattern matching} para os pares correspondentes a
\textit{(BinOp,(value1,value2))} ou \textit{(Unop,value)} para de seguida aplicar o
operador respetivo. Uma observação a ser feita é que nesta altura do
"catamorfismo" estamos já a lidar com números em concreto, e por isso aplicamos
as operações básicas da aritmética. Para a exponenciação utilizamos a função
\textbf{expd} disponibilizada.

Segue então o gene proposto:

\begin{code}
g_eval_exp a = either (const a) resto where
  resto = either id resto2
  resto2 = either bin un where
  bin(Sum,(c,d)) = c + d
  bin(Product,(c,d)) = c * d
  un(Negate,c) = (-1) * c
  un(E,c) = expd c

\end{code}

\subsubsection*{clean e gopt}

Perante este hilomorfismo proposto no enunciado para optimizar o cálculo de uma
expressão aritmética, consluímos que só seria possível realizar tal optimização
à nível do gene \textbf{clean} do anamorfismo. Isto porque apenas durante tal
gene temos as entidades suficientes que são passíveis de serem optimizadas. Tal
gene \textbf{clean} recebe uma \textbf{ExpAr a} como parâmetro, e para tirarmos
partido dos elementos absorventes das operações aritméticas, consideramos os
seguintes casos:

\begin{itemize}
\item	Parâmetro é um operador unário de exponenciação e a expressão aritmética
associada a ele é o número zero, isto é, \textbf{N 0}. Por outras palavras,
          qualquer número elevado à zero é 1, sendo este um caso de optimização.
\item	Parâmetro é o operador binário Product e uma de suas expressões
associadas é o número zero, isto é, \textbf{N 0}. Nesse caso o resultado pode
ser optimizado para o número zero, pois qualquer número à multiplicar por zero é
0.
\end{itemize}

Como \textbf{gopt} terá o mesmo tipo de g\_eval\_exp , não há forma de
otimizar algo nesta etapa do hilomorfismo por conta de já estarmos perante os
valores em concreto envolvidos nas operações aritméticas.

\begin{code}
clean :: (Floating a, Eq a) => ExpAr a -> Either () (Either a (Either (BinOp, (ExpAr a, ExpAr a)) (UnOp, ExpAr a)))
clean (X) = i1 ()
clean (N a) = i2 (i1 (a))
clean (Un op a) |(op == E) && a == (N 0) = i2(i1(1))
                | otherwise = i2 (i2 (i2 (op,a)))
clean (Bin op a b)    | (op == Product) && (a == (N 0) || b == (N 0))  =  i2(i1(0))
                      | otherwise = i2 (i2 (i1 (op, (a , b))))

gopt a = g_eval_exp a
\end{code}

\subsection*{sd\_gen}

A implementação do gene do catamorfismo responsável por calcular a derivada de
uma expressão, baseia-se nomeadamente nas próprias regras de derivação
enunciadas. Um dos tópicos mais relevantes aqui é o facto de lidarmos com
derivadas e isto implicar: \textit{manter o conhecimento da expressão original}.
Por outras palavras, muitas das regras de derivação envolvem a continuação da
expressão original nos termos derivados e esse mecanismo está presente nos tipos
de entrada e saída de \textbf{sd\_gen}. Tal função deve retornar um par
   correspondente há expressão original e a expressão derivada, para assim ter
   no gene do catamorfismo as ferramentas necessárias de derivação. Por conta
   disto, do lado do tipo de entrada, encontramos também pares de elementos
   (expressão original, expressão derivada),
   seja nos casos mais simples (número ou constante), seja como parâmetros dos
   operadores binários e unários. Assim, basta apenas aplicar as regras de
   derivação manuseando as componentes originais e as já derivadas:

\begin{code}
sd_gen :: Floating a =>
    Either () (Either a (Either (BinOp, ((ExpAr a, ExpAr a), (ExpAr a, ExpAr a))) (UnOp, (ExpAr a, ExpAr a))))
    -> (ExpAr a, ExpAr a)
sd_gen = either (split (const X) (N . (const 1))) resto where
  resto = either (split (N . id) (N . (const 0))) resto2 where
  resto2 = either f1 f2 where
  f1(Sum, ((a,b),(c,d))) = (Bin Sum a c, Bin Sum b d)
  f1(Product, ((a,b),(c,d))) = (Bin Product a c, Bin Sum (Bin Product a d) (Bin Product b c))
  f2(Negate,(a,b)) = (Un Negate a, Un Negate b)
  f2(E,(a,b)) = (Un E a, Bin Product (Un E a) b)
  --(a,b) originais (c,b) derivadas
\end{code}

\subsection*{ad\_gen}

A diferença desta função (em comparação com a anterior) consiste no
processamento da expressão derivada durante o catamorfismo. Ou seja, reduzimos
drasticamente consumo de memória, tornando a derivação mais eficiente. Para isso
ser feito, tal gene retornará um par composto pela expressão original (à
semelhança do gene anterior) e a derivada já calculada. Logo, teremos uma
construção deste gene muito parecida com a do problema anterior, diferindo na
utilização dos operadores aritméticos para o cálculo da derivada. Utilizamos a
função \textbf{eval\_exp} dos problemas anteriores para calcular o valor da
derivada de uma expressão.


\begin{code}
ad_gen :: Floating a =>
    a -> Either () (Either a (Either (BinOp, ((ExpAr a, a), (ExpAr a, a))) (UnOp, (ExpAr a, a)))) -> (ExpAr a, a)
ad_gen v = either (split (const X) (const 1)) resto where
  resto = either (split (N . id) (const 0)) resto2 where
  resto2 = either f1 f2 where
  f1(Sum, ((a,b),(c,d))) = (Bin Sum a c, b + d)
  f1(Product, ((a,b),(c,d))) = (Bin Product a c, ((eval_exp v a) * d )+ (b * (eval_exp v c)))
  f2(Negate,(a,b)) = (Un Negate a, (-1) * b)
  f2(E,(a,b)) = (Un E a, (expd (eval_exp v a)) * b )

\end{code}


\subsection*{Problema 2}

Começamos por tentar definir \textit{cat} recursivamente. Para isso, vamos determinar o valor de \textit{cat (n + 1)}:

\begin{math}
Cat_n = \frac{(2n)!}{(n+1)!(n!)}

Cat_{n+1} = \frac{(2(n+1))!}{(n+2)!(n+1)!}

= \frac{(2n+2)(2n+1)(2n)!}{(n+2)(n+1!)(n+1)n!}

= \frac{(2n)!}{(n+1)!n!} \times \frac{(2n+2)(2n+1)}{(n+2)(n+1)}

= Cat_n \times (\frac{2(n+1)(2n+1)}{(n+1)(n+2)})

= Cat_n \times \frac{4n + 2}{n + 2}

= \frac{(4n + 2) \times Cat_n}{n + 2}
\end{math}

Conseguimos, então, extrair o numerador e denominador da fração para as suas
próprias funções:

\begin{spec}
top n = 4*n + 2
-- Equivalente a:
top 0 = 2
top (n + 1) = 4 + top n
\end{spec}

\begin{spec}
bot n = n + 2
-- Equivalente a
bot 0 = 2
bot (n + 1) = 1 + bot n
\end{spec}

Podemos definir todas as funções necessárias para utilizar a regra de algibeira:

\begin{spec}
cat 0 = 1
cat (n + 1) = div ((top n) * (cat n)) (bot n)
top 0 = 2
top (n + 1) = 4 + top n
bot 0 = 2
bot (n + 1) = 1 + bot n
\end{code}

Aplicando a regra de algibeira chegamos então à solução:

\begin{code}
cat = prj . for loop inic where
  loop (cat, top, bot) = (div (top * cat) bot, top + 4, bot + 1)
  inic = (1, 2, 2)
  prj (cat, top, bot) = cat
\end{code}

\subsection*{Problema 3}

\begin{eqnarray*}
\start
    |lcbr(
          calcLine [] = const nil
    )(
          calcLine (p:x) = (curry g) p (calcLine x)
    )|
%
\just\equiv{nil x = []}
%
    |lcbr(
          calcLine (nil x) = const nil
    )(
          calcLine (p:x) = (curry g) p (calcLine x)
    )|
%
\just\equiv{Def-comp}
%
    |lcbr(
          (calcLine . nil ) x = const nil
    )(
          calcLine (p:x) = (curry g) p (calcLine x)
    )|
%
\just\equiv{Def-const}
%
    |lcbr(
          (calcLine . nil ) x = (const (const nil)) x
    )(
          calcLine (p:x) = (curry g) p (calcLine x)
    )|
%
\just\equiv{nil x = []; def-comp, def-const, cons(h,t) = h:t}
%
    |lcbr(
          (calcLine . nil) x = const (const nil) x
    )(
          (calcLine . cons) (p,x) = (curry g) p (calcLine x)
    )|
%
\just\equiv{def curry, Igualdade extensional}
%
    |lcbr(
          calcLine . nil = const (const nil)
    )(
          (calcLine . cons) (p,x) = g(p , calcLine x)
    )|
%
\just\equiv{Def-x, def-id, igualdade extensional, def-comp}
%
    |lcbr(
          calcLine . nil = const (const nil)
    )(
          calcLine . cons = f . (id x calcLine)
    )|
%
\just\equiv{Eq-+}
%
    | [calcLine . nil, calcLine . cons] = [const(const nil), g . (id ><
            calcLine)] |
%
\just\equiv{Fusão-+}
%
| calcLine . [nil, cons] = [ const (const nil), g. (id >< calcLine)] |
%
\just\equiv{Nat-id, absorção-+}
%
| calcLine . [nil, cons] = [ const(const nil), g ] . (id + id >< calcLine) |
%
\just\equiv{inL = [nil,cons], F f = id + id x f}
%
| calcLine . [nil, cons] = [ const(const nil), g ] . F calcLine |
%
\just\equiv{Universal-cata}
%
| calcLine = cataLTree [ const(const nil), g ] |
%
\qed
\end{eqnarray*}


\begin{code}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine = cataList (either (const (const nil)) g) where
   g :: (Rational, NPoint -> OverTime NPoint) -> (NPoint -> OverTime NPoint)
   g (d,f) l = case l of
       []     -> nil
       (x:xs) -> \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z
\end{code}

\begin{code}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau = hyloAlgForm alg coalg where
   coalg = divide
   alg = conquer

divide [] = i1 []
divide [a] = i1 a
divide l = i2 (init l, tail l)

quer (x,y)= \pt->calcLine (x pt) (y pt) pt

conquer = either const quer

hyloAlgForm f g =  (cataLTree f) .  (anaLTree g)
\end{code}

\subsection*{Problema 4}

Solução para listas não vazias:
\begin{code}
avg = p1.avg_aux
\end{code}

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |A|^{+}
           \ar[d]_-{|split avg length|}
&
    |A + A| \times |A|^{+}
           \ar[d]^{|id + (split avg length)|}
           \ar[l]_-{|inNat|}
\\
     |A| \times |Nat0|
&
     |A + A| \times (|A| \times |Nat0|)
           \ar[l]^-{|g|}
}
\end{eqnarray*}

A partir do diagrama facilmente chegamos ao gene. Caso a sequência seja unitária então o
resultado é o próprio número com length de 1. Se não, aplicamos a definição de avg e aplicamos
a função succ à length que já tinha sido calculada.


\begin{code}
outSList([a]) = i1(a)
outSList(a:b) = i2(a,b)

cataSList g = g . (id -|- id >< cataSList g) . outSList

avg_aux = cataSList (either (split id one) (split k (succ . p2 . p2)))
    where
        k :: (Double,(Double,Integer)) -> Double
        k (a,(b,c)) = (a + c' * b) / (c'+1)
            where
                c' = fromIntegral c
\end{code}

Solução para árvores de tipo \LTree:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |LTree Num|
           \ar[d]_-{|split avg length|}
&
    |Num + LTree Num| \times |LTree Num|
           \ar[d]^{|id| + |(split avg length)|^{2}}
           \ar[l]_-{|inNat|}
\\
     |Num| \times |Nat0|
&
     |Num| + ((|Num| \times |Nat0|) \times (|Num| \times |Nat0|))
           \ar[l]^-{|g|}
}
\end{eqnarray*}

sendo
\begin{code} avg :: LTree Num -> Num \end{code} e \begin{code} length :: LTree A -> Nat0 \end{code}
ao aplicar o functor de Ltrees  \textbf{F
} \begin{code}(split avg length)\end{code}
Sabemos que o tipo do resultado desta aplicação será:
\begin{eqnarray*}
    Num + ((Num \times $\mathbb{N}_{0}$ ) \times (Num \times $\mathbb{N}_{0}$ ))
\end{eqnarray*}

      Sendo que o segundo operando da soma de tipos é um produto de tipos em que cada operando é constituido por
um par de (média, tamanho). Desta forma já sabemos como descrever o gene deste catamorfismo.
O primeiro operando do either é para o caso em que se trata de uma folha. Ou seja o resultado será um par com
o número e length 1. Ou seja a função é \begin{code}(split id one)\end{code} No caso de se tratar de fork então calculamos o primeiro elemento do
par resultado aplicando a função k, que através de dois pares com informação das médias e números de elementos calcula a média
resultante. O segundo elemento do par resultado é calculado através da soma dos tamanhos.




\begin{code}
avgLTree = p1.cataLTree gene where
    gene = either (split id one) (split k (add . (p2 >< p2)))
    k :: ((Double,Integer),(Double,Integer)) -> Double
    k ((a,b),(c,d)) = (a*b' + c*d') / (b' + d')
        where
           b' = fromIntegral b
           d' = fromIntegral d

\end{code}


\subsection*{Problema 5}
Inserir em baixo o código \Fsharp\ desenvolvido, entre \verb!\begin{verbatim}! e \verb!\end{verbatim}!:
module BTree.

\Fsharp\  mostrou ser uma linguagem bastante semelhante a Haskell, sendo a diferença
principal a sintaxe (por exemplo, requirir o uso de \textit{let} antes da
definição de funções). A parte mais difícil desta "tradução" foi a diferença
na omissão de argumentos, algo que, em geral, não é possível em \Fsharp\ .

\begin{verbatim}
open Cp

// (1) Datatype definition -----------------------------------------------------
type BTree<'a> = Empty | Node of 'a * (BTree<'a> * BTree<'a>)

let inBTree x = either (konst Empty) Node x
let outBTree x =
    match x with
    | Empty -> i1 ()
    | Node (a,(t1,t2)) -> i2 (a, (t1, t2))

// (2) Ana + cata + hylo -------------------------------------------------------
let baseBTree f g = id -|- (f >< (g >< g))
let recBTree g = baseBTree id g
let rec cataBTree g x = (g << recBTree (cataBTree g) << outBTree) x
let rec anaBTree g x = (inBTree << recBTree (anaBTree g) << g) x
let hyloBTree h g x = (cataBTree h << anaBTree g) x


// (3) Map ---------------------------------------------------------------------
let fmap f x = cataBTree (inBTree << baseBTree f id) x

// (4) Examples ----------------------------------------------------------------

// (4.1) Inmersion (mirror) ----------------------------------------------------
let invBTree x = cataBTree (inBTree << (id -|- (id >< swap))) x

// (4.2) Counting --------------------------------------------------------------
let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x

// (4.3) Serialization ---------------------------------------------------------
let inord y =
    let join (x, (l, r)) = l @ [x] @ r
    either nil join y
let inordt x = cataBTree inord x // in-order traversal

let preord y =
    let f (x, (l, r)) = x::(l @ r)
    either nil f y
let preordt x = cataBTree preord x // pre-order traversal

let postordt y = // post-order traversal
    let f (x, (l, r)) = l @ r @ [x]
    cataBTree (either nil f) y

// (4.4) Quicksort -------------------------------------------------------------
let rec part p x =
    match x with
    | [] -> ([], [])
    | (h::t) -> let s, l = part p t
                if p h then (h::s,l) else (s,h::l)

let qsep x =
    match x with
    | [] -> i1 ()
    | (h::t) -> let s, l = part (fun n -> n < h) t
                i2 (h, (s, l))

let qSort x = hyloBTree inord qsep x

// (4.5) Traces ----------------------------------------------------------------
let rec union a b =
    match b with
    | [] -> a
    | h::t when List.contains h a -> union a t
    | h::t -> h::(union a t)

let tunion (a, (l, r))
    = union (List.map (fun x -> a::x) l) (List.map (fun x -> a::x) r)
let traces x = cataBTree (either (konst [[]]) tunion) x

// (4.6) Towers of Hanoi -------------------------------------------------------
let present = inord
let strategy (d, n)
    = if n = 0 then i1 () else i2 ((n - 1, d), ((not d, n - 1), (not d, n - 1)))

let hanoi x = hyloBTree present strategy x

// The Towers of Hanoi problem comes from a puzzle marketed in 1883
// by the French mathematician Édouard Lucas, under the pseudonym
// Claus. The puzzle is based on a legend according to which
// there is a temple, apparently in Bramah rather than in Hanoi as
// one might expect, where there are three giant poles fixed in the
// ground. On the first of these poles, at the time of the world's
// creation, God placed sixty four golden disks, each of different
// size, in decreasing order of size. The Bramin monks were given
// the task of moving the disks, one per day, from one pole to another
// subject to the rule that no disk may ever be above a smaller disk.
// The monks' task would be complete when they had succeeded in moving
// all the disks from the first of the poles to the second and, on
// the day that they completed their task the world would come to
// an end!

// There is a well­known inductive solution to the problem given
// by the pseudocode below. In this solution we make use of the fact
// that the given problem is symmetrical with respect to all three
// poles. Thus it is undesirable to name the individual poles. Instead
// we visualize the poles as being arranged in a circle; the problem
// is to move the tower of disks from one pole to the next pole in
// a specified direction around the circle. The code defines H n d
// to be a sequence of pairs (k,d') where n is the number of disks,
// k is a disk number and d and d' are directions. Disks are numbered
// from 0 onwards, disk 0 being the smallest. (Assigning number 0
// to the smallest rather than the largest disk has the advantage
// that the number of the disk that is moved on any day is independent
// of the total number of disks to be moved.) Directions are boolean
// values, true representing a clockwise movement and false an anti­clockwise
// movement. The pair (k,d') means move the disk numbered k from
// its current position in the direction d'. The semicolon operator
// concatenates sequences together, [] denotes an empty sequence
// and [x] is a sequence with exactly one element x. Taking the pairs
// in order from left to right, the complete sequence H n d prescribes
// how to move the n smallest disks one­by­one from one pole to the
// next pole in the direction d following the rule of never placing
// a larger disk on top of a smaller disk.

// H 0     d = [],
// H (n+1) d = H n ¬d ; [ (n, d) ] ; H n ¬d.

// (excerpt from R. Backhouse, M. Fokkinga / Information Processing
// Letters 77 (2001) 71--76)


// (5) Depth and balancing (using mutual recursion) --------------------------
let baldepth n =
    let h (a, ((b1, b2), (d1, d2)))
            = (b1 && b2 && abs (d1 - d2) <= 1, 1 + max d1 d2)
    let f ((b1, d1), (b2, d2)) = ((b1, b2), (d1, d2))
    let g x = either (konst (true, 1)) (h << (id >< f)) x
    cataBTree g n

let balBTree x = (p1 << baldepth) x
let depthBTree x = (p2 << baldepth) x

\end{verbatim}

%----------------- Fim do anexo com soluções dos alunos ------------------------%

%----------------- Índice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2021t}

%----------------- Fim do documento -------------------------------------------%
\end{document}

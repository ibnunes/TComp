(* TEORIA DA COMPUTAÇÃO 2019/2020
 *
 * Autor: Igor Nunes (Nº 41381)
 * Data:  11/06/2020 (versão 1)
 *
 * Recorre a um autómato minimalista.
 * 
 * Changelog:
 *    0.1 (28/mai/2020) -> Esboço do código
 *    1.0 (17/jun/2020) -> Primeira versão
 *    1.1 (04/jul/2020) -> Optimização (buffering)
 *)

(* 
 * ===== PbD: Problema D =====
 * Documentação adicionada a 17/06/2020.
 * Bibliografia: aulas da unidade curricular e apontamentos do professor.
 * Exemplo de execução no final.
 *)

(* Tipo de dados:  regexp
 * ----------------------
 * Extraído do código fornecido no Problema C.
 *)
type regexp =
  | V  
  | E
  | C of char
  | U of regexp * regexp 
  | P of regexp * regexp 
  | S of regexp


(* Função:  string_of_regexp
 * -------------------------
 * Produz uma string correspondente à expressão regular de input.
 * Código fornecido pelo professor.
 * Extraído do código fornecido no Problema C.
 *)
let rec string_of_regexp s =
  match s with
  | V        -> "0"
  | E        -> "1"
  | C  c     -> String.make 1 c    
  | U (f, g) -> "(" ^ (string_of_regexp f) ^ " + " ^ (string_of_regexp g) ^ ")"
  | P (f, g) -> "(" ^ (string_of_regexp f) ^ " . " ^ (string_of_regexp g) ^ ")"
  | S s      -> (string_of_regexp s) ^ "*"


(* Operador:  <|
 * -------------
 * Equivale ao operador . de Haskell
 * 
 * Operador:  <<
 * -------------
 * Equivale ao operador $ de Haskell
 * 
 * Função:  subtract
 * -----------------
 * Equivale à função subtract de Haskell
 *)
let (<|) f g x = f (g x)
let (<<) f x   = f x
let subtract x y = y - x


(* Tipo de dados:  label
 * ---------------------
 * Representa o rótulo de uma transição no autómato.
 * 
 * Para o rótulo optei pelo tipo de dados 'label' uma vez que Null pode representar
 * directamente uma transição 0, Epsilon representa uma transição Ɛ, enquanto
 * Char c representa uma transição com o caracter c.
 * 
 * Criado e usado originalmente no Problema C.
 *)
type label =
  | Null
  | Epsilon
  | Char of char


(* Tipo de dados:  transition
 * --------------------------
 * Representa uma transição no autómato. É um tuplo com os seguintes 2 elementos:
 *   -> Estado para o qual transita;
 *   -> Rótulo da transição (caracter, Ɛ ou 0).
 * 
 * Criado e usado originalmente no Problema C.
 *)
type transition = int * label


(* Tipo de dados:  automata
 * ------------------------
 * Representa um autómato.
 * Um autómato é um array de listas de transições.
 * Cada índice do array representa um nó do autómato, e este tem uma lista de
 * transições possíveis.
 * Um estado final é um nó cuja lista de transições é vazia.
 * 
 * O array irá permitir acesso directo, que é mais eficiente, e permitirá
 * simular um sistema com um "apontador" na execução do autómato.
 * 
 * Detalhes do uso descritos na secção "Exemplo de execução".
 * 
 * Criado e usado originalmente no Problema C.
 *)
type automata = transition list array


(* Constante:  t_null
 * ------------------
 * Lista de transições vazia.
 * Um nó do autómato que armazene um t_null é um estado final.
 * 
 * Criado e usado originalmente no Problema C.
 *)
let t_null : transition list = []


(* Constante:  init_automata
 * -------------------------
 * Autómato inicial.
 * 
 *   n: número de estados do autómato.
 * 
 * Inicializa com a constante t_null.
 * 
 * Criado e usado originalmente no Problema C.
 *)
let init_automata n : automata = Array.make n t_null


(* Função:  make_matrix
 * --------------------
 * Cria uma matriz max * max * max+1 que serve de buffer de memória para o
 * Algoritmo de MacNaughton-Yamada.
 *)
let make_matrix max : regexp option array array array =
  Array.init max (fun _ -> Array.init max (fun _ -> (Array.init (max + 1) (fun _ -> None))))


(* Função:  simplify
 * -----------------
 * Simplifica o autómato e aplica as regras indicadas no enunciado, nomeadamente:
 * 
 *   1. 0+r = r+0 = r
 *   2. 0.r = r.0 = 0
 *   3. 0* = Ɛ
 *   4. A+B ordano segundo 0 < Ɛ < c.
 * 
 * Aplica uma simplificação adicional inspirado pelo código originalmente fornecido
 * pelo professor.
 *)
let rec simplify s =
  match s with
  | U (f, g) -> (
    let f, g = simplify f, simplify g in
    match f, g with
    | C a, C b -> if a > b then U (C b, C a) else U (C a, C b)
    | V, x
    | x, V     -> x
    | E, C a
    | C a, E   -> U (E, C a)
    | _        -> U (f, g)
  )
  | P (f, g) -> (
    let f, g = simplify f, simplify g in
    match f, g with
    | V, _
    | _, V -> V
    | _    -> P (f, g)
  )
  | S f      -> (
    let f = simplify f in
    match f with
    | E
    | V -> E
    | U (E, g)
    | U (g, E) -> S g
    | _ -> S f
  )
  | _        -> s


(* Funções auxiliares para debug
 * -----------------------------
 * NÃO são utilizadas na versão final!
 * O seu propósito é meramente para debugging.
 *)
let printt (i, c) =
  match c with
  | Null    -> Printf.printf "(%2d, 0); " i
  | Epsilon -> Printf.printf "(%2d, epsilon); " i
  | Char c  -> Printf.printf "(%2d, '%c'); " i c
let printl l =
  Printf.printf "\t[";
  List.iter printt l;
  Printf.printf "]\n"
let printa a =
  Array.iteri (fun i a -> Printf.printf "%2d: " i; printl a) a
let printres s a =
  Printf.printf "%s -> [" s;
  List.iter (Printf.printf "%d; ") a;
  Printf.printf "]\n"
let pausea a =
  let () = printa a in let _ = read_line () in ()


(* Função:  union
 * --------------
 * Une duas expressões regulares.
 * Recebe A e B, e devolve A+B.
 *)
let union a b = U (a, b)


(* Função:  regexp_of_label
 * ------------------------
 * Transforma uma etiqueta de uma transição na expressão regular correspondente.
 * Utilizado na aplicação do algoritmo de McNaughton-Yamada.
 *)
let regexp_of_label = function
| Null    -> V
| Epsilon -> E
| Char c  -> C c


(* Função:  yamada
 * ---------------
 * Aplica o algoritmo de McNaughton-Yamada para obter a expressão regular
 * correspondente a um dado autómato.
 * 
 * L(A) = união de R(i,f,n+1) para todos os estados iniciais i e finais f, onde:
 * 
 * [1]:
 *   [1.1] -> R(i,j,k+1) = R(i,j,k) + R(i,k,k).R(k,k,k)*.R(k,j,k)
 *   [1.2] -> R(i,j,1) = | i=j -> Ɛ+a | otherwise -> a, where a = {a | (i) -- a --> (f)}
 * 
 * Uma vez que só existe 1 estado final e existem vários estados finais, a função
 * mapeia os estados finais com a subfunção 'run' e une as expressões regulares
 * com recurso a um fold_left que aplica a função 'union'.
 * 
 * 
 * Subfunção:  run
 * ---------------
 * Aplica recursivamente a expressão [1].
 * 
 * 'run i f j' corresponde a R(i,j,k+1) da expressão [1].
 * Quando j = 1, invoca a subfunção 'step', sendo esta a condição de paragem da
 * função recursiva, uma vez que é uma transição simples (directo de i a f).
 * 
 * Esta função recorre à matriz 'm' de buffering. Se a célula (i,f,k) contiver
 * None, significa que esta célula ainda não foi calculada, pelo que é preenchida
 * com o resultado (Some <resultado>).
 * É feita então a chamada recursiva de 'run i f j', a qual fará então a extracção
 * do tipo option recentemente criado.
 * 
 * 
 * Subfunção:  step
 * ----------------
 * Verifica todas as transições existentes do estado i ao estado f e devolve
 * a expressão regular correspondente.
 * 
 * Por exemplo, se de 2 a 4 existirem as transições A e B, será devolvido A+B.
 * Não havendo transições, devolve 0 (null).
 *)
let yamada (a : automata) (n : int) (si : int) (sf : int list) m =
  let step i f =
    let t = List.filter (fun (x, _) -> x = f) a.(i) in
      if t = [] then V
      else
        List.fold_left union V <|
        List.map (
          fun (_, l) ->
            let l = regexp_of_label l
            in if i = f then union E l else l
        ) << t
  in
  let rec run i f j =
    if j = 0 then step i f
    else
      let k = j - 1 in
        match m.(i).(f).(k) with
        | None   -> m.(i).(f).(k) <- Some (U (run i f k, P (run i k k, P (S (run k k k), run k f k)))); run i f j
        | Some r -> r
  in
    List.fold_left union V <| List.map (fun f -> run si f n) << sf



(* Função:  read_final_states
 * --------------------------
 * Traduz uma linha lida do stdin contendo uma string de estados finais numa
 * int list com os referidos estados finais.
 * 
 * Subtrai 1 uma vez que o Array que representa o autómato é zero-indexed.
 *)
let read_final_states () =
  List.map (subtract 1 <| int_of_string) <| String.split_on_char ' ' << read_line ()


(* Função:  read_initial_state
 * ---------------------------
 * Traduz uma linha lida do stdin num int contendo o estado inicial.
 * 
 * Subtrai 1 uma vez que o Array que representa o autómato é zero-indexed.
 *)
let read_initial_state () =
  subtract 1 << read_int ()


(* Função:  read_transition
 * ------------------------
 * Obtém do stdin uma string com 3 elementos esperados para formar uma transição:
 *   -> i: estado de partida
 *   -> c: etiqueta de transição
 *   -> j: estado de chegada
 * 
 * A etiqueta é construída conforme seja 0, Ɛ ou um caracter c com o tipo de dados
 * 'label' previamente descrito.
 * 
 * Se não forem obtidos exactamente 3 elementos, é gerado um erro.
 * Se não for possível o typecast ou os estados forem out of bounds, é
 * igualmente gerado um erro.
 * 
 * Subtrai 1 uma vez que o Array que representa o autómato é zero-indexed.
 *)
let read_transition (a : automata) =
  match String.split_on_char ' ' (read_line ()) with
  | [i; c; j] -> begin
    try
      let i = subtract 1 << int_of_string i in
      let j = subtract 1 << int_of_string j in
      let c = c.[0] in
        if c = '0' then a.(i) <- (j, Null) :: a.(i)
        else if c = '1' then a.(i) <- (j, Epsilon) :: a.(i)
        else a.(i) <- (j, Char c) :: a.(i)
    with _ -> failwith "read_transition: got 3 but not correct"
  end
  | _ -> failwith "read_transition: not 3 elements"


(* Função:  read_automata
 * ----------------------
 * Lê m transições que constituem o autómato de n estados.
 * 
 * É gerado um autómato (Array) inicial com n elementos e é chamada a função
 * read_transaction m vezes para obter as m transições do stdin.
 * 
 * A função auxiliar 'geta' é encapsulada para poder passar o autómato em
 * construção por parâmetro.
 * 
 * O autómato resultante é devolvido.
 *)
let read_automata m n =
  let rec geta m a =
    if m = 0 then a
    else (read_transition a; geta (m - 1) a)
  in geta m << init_automata n


(* BLOCO PRINCIPAL (main do programa)
 * ---------------
 * 1. Lê n, especificando o conjunto S = {1..n}.
 * 2. Lê i, que identifica que estado de Q é o estado inicial.
 * 3. Lê f, cardinalidade do conjunto F dos estados finais.
 * 4. Lê sf. o conjunto dos estados finais.
 * 5. Lê m, a cardinalidade de R𝛿.
 * 6. Lê a, o autómato com n estados e um total de m transições.
 * 7. Determina a expressão regular.
 * 8. Simplifica a expressão regular obtida em 7.
 * 9. Escreve a expressão regular na forma de uma string formatada.
 *)
let () =
  let n  = read_int () in
  let i  = read_initial_state () in
  let _  = read_int () in
  let sf = read_final_states () in
  let m  = read_int () in
  let a  = read_automata m n in
  let y  = simplify << yamada a n i sf (make_matrix n) in
    Printf.printf "%s\n" << string_of_regexp y


(* EXEMPLO DE EXECUÇÃO
 * -------------------
 * Seja dado o seguinte autómato:
 * 
 *                              + a +
 *                              \  /
 *                              V |
 *   (1) -- a --> (2) -- b --> ([3])
 * 
 * O input correspondente será:
 * 
 *    3
 *    1
 *    1
 *    3
 *    3
 *    1 a 2
 *    2 b 3
 *    3 a 3
 * 
 * Usando as funções de input desenvolvidas, obteremos as seguintes informações
 * acerca do autómato:
 * 
 *   Estado inicial -> 0
 *   Estados finais -> [2; ]
 *    0:     [( 1, 'a'); ]
 *    1:     [( 2, 'b'); ]
 *    2:     [( 2, 'a'); ]
 * 
 * Nota: como é usado um Array para representar o autómato, tudo passa a ser
 * indexado a zero. Os arrays permitem acesso directo e mais célere, daí a sua
 * escolha para esta representação.
 * 
 * A função 'yamada' é então chamada, a qual irá determinar que o autómato será
 * dado por L(A) = R(1,3,4).
 * 
 * R(i,j,k+1) é calculado pela função recursiva 'run'. Neste caso, 'run' será
 * invocada com os valores 0, 2 e 3 (devido à indexação a zero).
 * 
 *   R(0,2,3) = R(0,2,2) + R(0,2,2).R(2,2,2)*.R(2,2,2)
 * 
 * Ora, temos então que:
 * 
 *   R(0,2,2) = R(0,2,1) + R(0,1,1).R(1,1,1)*.R(1,2,1)
 *   R(2,2,2) = R(2,2,1) + R(2,1,1).R(1,1,1)*.R(1,2,1)
 * 
 * Por sua vez:
 * 
 *   R(0,1,1) = R(0,1,0) + R(0,0,0).R(0,0,0)*.R(0,1,0)
 *   R(0,2,1) = R(0,2,0) + R(0,0,0).R(0,0,0)*.R(0,2,0)
 *   R(1,1,1) = R(1,1,0) + R(1,0,0).R(0,0,0)*.R(0,1,0)
 *   R(1,2,1) = R(1,2,0) + R(1,0,0).R(0,0,0)*.R(0,2,0)
 *   R(2,1,1) = R(2,1,0) + R(2,0,0).R(0,0,0)*.R(0,1,0)
 *   R(2,2,1) = R(2,2,0) + R(2,0,0).R(0,0,0)*.R(0,2,0)
 * 
 * E por fim:
 * 
 *   R(0,0,0) = 0
 *   R(0,1,0) = a
 *   R(0,2,0) = 0
 *   R(1,0,0) = 0
 *   R(1,1,0) = 0
 *   R(1,2,0) = b
 *   R(2,0,0) = 0
 *   R(2,1,0) = 0
 *   R(2,2,0) = Ɛ + a
 * 
 * Portanto:
 * 
 *   R(0,1,1) =       a + 0 . (0* . a) = a
 *   R(0,2,1) =       0 + 0 . (0* . 0) = 0
 *   R(1,1,1) =       0 + 0 . (0* . a) = 0
 *   R(1,2,1) =       b + 0 . (0* . 0) = b
 *   R(2,1,1) =       0 + 0 . (0* . a) = 0
 *   R(2,2,1) = (Ɛ + a) + 0 . (0* . 0) = Ɛ + a
 * 
 *   R(0,2,2) =       0 + a . (0* . b) = a . (Ɛ . b)
 *   R(2,2,2) = (Ɛ + a) + 0 . (0* . b) = Ɛ + a
 * 
 * E assim:
 * 
 *   L(A) = (a . (Ɛ . b)) + (a . (Ɛ . b)) . ((Ɛ + a)* . (Ɛ + a))
 * 
 * Após simplificação, temos o seguinte output:
 * 
 *   ((a . (1 . b)) + ((a . (1 . b)) . (a* . (1 + a))))
 * 
 * A simplificação apenas ocorre com a expressão regular final.
 * Contudo, para simplificação do exemplo, fui simplificando logo os casos com 0.
 * 
 * NOTA FINAL:
 * É usado um mecanismo de buffering que evita o cálculo recorrente de R's que já
 * foram previamente determinados. Um tipo de dados do tipo option, inserido numa
 * matrix n x n x n+1, alberga esta informação.
 * Uma célula com None signica que ainda não foi calculado.
 * Uma célula com Some r já foi calculada, pelo que é imediatamente devolvido r.
 *)

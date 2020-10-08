(* TEORIA DA COMPUTAÇÃO 2019/2020
 *
 * Autor: Igor Nunes (Nº 41381)
 * Data:  21/07/2020 (versão 2)
 * 
 * 
 * Changelog:
 *    0.1 (20/jun/2020) -> Início da primeira tentativa de implementação, entretanto abandonada
 *    0.2 (13/jul/2020) -> Segunda tentativa, entretanto abandonada
 *    1.0 (19/jul/2020) -> Primeira versão
 *    1.1 (21/jul/2020) -> Correcção do conjunto FOLLOW
 *)

(* AGRADECIMENTOS:
 * Agradeço a ajuda imprescindível da Raquel Guerra que me ajudou a compreender a matéria
 * subordinada ao presente problema. Os seus conhecimentos de Processamento de Linguagens
 * revelaram-se-me essenciais.
 *)

(* 
 * ===== PbE: Problema E =====
 * Documentação adicionada a 21/07/2020.
 * Bibliografia:
 *   -> Aulas da UC Teoria da Computação;
 *   -> Apontamentos da UC de Processamento de Linguagens.
 *   -> Apontamentos da UC de Métodos de Programação III da Universidade do Minho.
 *   -> Código Haskell desenvolvido por João Saraiva, da Universidade do Minho, sob a licença LGPL.
 * Exemplo de execução no final.
 *)


(* Operadores e funções do Haskell
 * 
 *  +---------+---------+
 *  |  OCaml  | Haskell |
 *  +---------+---------+
 *  |    <|   |   .     |
 *  |    <<   |   $     |
 *  |  flip   |  flip   |
 *  +---------+---------+
 *)
let (<|) f g x = f (g x)
let (<<) f x   = f x
let flip f x y = f y x


(* Função:  unique
 * ---------------
 * Devolve uma lista com os elementos não repetidos.
 * FONTE: função 'normalize' desenvolvida pelo professor.
 * NOTA: equivale à função 'nub' do Haskell.
 *)
let unique l =
  let tbl = Hashtbl.create (List.length l) in
  let f l e = try let _ = Hashtbl.find tbl e in l
              with Not_found ->  Hashtbl.add tbl e (); e::l
  in  List.rev (List.fold_left f [] l)

(* Função 'delete' do Haskell *)
let rec delete e l =
  match l with
  | [] -> []
  | h :: t -> if h = e then t else h :: (delete e t)

(* Função 'union' do Haskell *)
let union xs ys = xs @ List.fold_left (flip delete) (unique ys) xs


(* Função:  ntsort
 * ---------------
 * Devolve uma lista de caracteres organizada por ordem alfabética.
 * Caso especial: 'S' está antes de todos os restantes caracteres.
 *)
let ntsort =
  List.sort (
    fun a b ->
      if a = 'S' then -1
      else if b = 'S' then 1
      else Char.code a - Char.code b
  )

(* Função:  tsort
 * --------------
 * Devolve uma lista de caracteres organizada por ordem alfabética.
 * Caso especial: '#' está antes de todos os restantes caracteres.
 *)
let tsort =
  List.sort (
    fun a b ->
      if a = '#' then -1
      else if b = '#' then 1
      else Char.code a - Char.code b
  )


(* Função:  sfst
 * -------------
 * Devolve o primeiro caracter de uma string não nula.
 * De "string first".
 *)
let sfst s = s.[0]

(* Função:  mkstr
 * --------------
 * Devolve a string correspondente a um caracter.
 * De "make string".
 *)
let mkstr c = String.make 1 c

(* Função:  capstring_of_bool
 * --------------
 * Devolve a string capitalizada de um booleano.
 * De "capitzalized string of boolean".
 *)
let capstring_of_bool b = if b then "True" else "False"


(* 
 * Seja G a linguagem algébrica definida por G = (∑,N,P,S).
 *)

(* Tipo de dados:  symbol
 * ----------------------
 * Símbolo:
 *   -> T: terminal (char minúsculo (Some c) ou Ɛ (None))
 *   -> N: não terminal (char maiúsculo).
 *)
type symbol =
  | T of char option
  | N of char

(* Tipo de dados:  production
 * --------------------------
 * Produção: um conjunto de símbolos.
 *)
type production = symbol list

(* Tipo de dados:  rule
 * --------------------
 * Regra da gramática: um não-terminal e a respectiva produção.
 *)
type rule = char * production

(* Tipo de dados:  nt_list
 * -----------------------
 * Lista de não terminais (caracteres).
 *)
type nt_list = char list

(* Tipo de dados:  grammar
 * -----------------------
 * Gramática: lista de não-terminais e a respectiva gramática.
 * A gramática per se é uma hash table. A cada não-terminal corresponde uma ou mais produções.
 *)
type grammar = nt_list * (char, production) Hashtbl.t

(* Tipos de dados:  null_t, first_t, follow_t
 * ------------------------------------------
 * Hash tables que armazenam os resultados dos cálculos dos vários conjuntos.
 *)
type null_t = (char, bool) Hashtbl.t
type first_t = (char, char list) Hashtbl.t
type follow_t = (char, char list) Hashtbl.t

(* Constante:  separator
 * ---------------------
 * Separador usado na definição de uma regra.
 *)
let separator = "->"


(* Funções:  string_of_*
 * ---------------------
 * Convertem tipos de dados em representações string.
 * 
 * NOTA: as funções utilizadas no output são as seguintes:
 *    -> string_of_null
 *    -> string_of_first
 *    -> string_of_follow
 *)
let string_of_symbol = function
  | T None   -> "Ɛ"
  | T Some c -> mkstr c
  | N c      -> mkstr c

let string_of_production =
  List.fold_left ((^) <| (flip (^) << " ")) "" <| List.map string_of_symbol

let string_of_rule (nt, p) =
  mkstr nt ^ " " ^ separator ^ " " ^ string_of_production p

let string_of_grammar (nt, g) =
  (List.fold_left ((^) <| (flip (^) << " ")) "" <| List.map mkstr << nt) ^ "\n" ^
  Hashtbl.fold (fun nt p s -> s ^ string_of_rule (nt, p) ^ "\n") g ""

let string_of_null nt (r : null_t) =
  List.fold_left (
    fun s x ->
      s ^ "NULL(" ^ (mkstr x) ^ ") = " ^ (capstring_of_bool << Hashtbl.find r x) ^ "\n"
  ) "" nt

let string_of_first nt (r : first_t) =
  List.fold_left (
    fun s x ->
      let y = (List.fold_left ((^) <| (flip (^) << " ")) "" <| List.map mkstr <| tsort <| Hashtbl.find r << x)
      in s ^ "FIRST(" ^ (mkstr x) ^ ") = " ^ String.trim y ^ "\n"
  ) "" nt

let string_of_follow nt (r : follow_t) =
  List.fold_left (
    fun s x ->
      let y = (List.fold_left ((^) <| (flip (^) << " ")) "" <| List.map mkstr <| tsort <| Hashtbl.find r << x)
      in s ^ "FOLLOW(" ^ (mkstr x) ^ ") = " ^ String.trim y ^ "\n"
  ) "" nt


(* Função:  rhs_nt
 * ---------------
 * Extrai o "right hand side" de um não-terminal, i.e., as produções.
 *)
let rhs_nt ((_, g) : grammar) (nt : symbol) : production list =
  match nt with
  | N c -> Hashtbl.find_all g c
  | _   -> []


(* Funções:  nullable*
 * -------------------
 * Determinam o valor NULL para cada não terminal.
 *)
let rec nullable_nt g nt =
  nullable_nt' g [] nt
and nullable_nt' g v nt =
  List.fold_left (||) false (List.map (nullable g v) (rhs_nt g nt))
and nullable g v sy =
  match sy with
  | []                        -> true
  | (T None) :: t             -> true
  | (T Some h) :: t           -> false
  | h :: t when List.mem h v  -> false
  | h :: t                    -> (nullable_nt' g (h::v) h) && (nullable g v t)


(* Função:  compute_null
 * ---------------------
 * Preenche a hashtable do conjunto NULL com recurso à função nullable_nt.
 *)
let compute_null g : null_t =
  let (nt, _) = g in
  let n = List.length nt in
  let r = Hashtbl.create n in
  let () = List.iter (
      fun x ->
        Hashtbl.add r x (nullable_nt g (N x))
    ) nt
  in r


(* Funções:  first*
 * ----------------
 * Determinam o valor FIRST para cada não terminal.
 *)
let first (g : grammar) (n : null_t) (sy : production) =
  let rec first' (g : grammar) (v : production) (sy : production) =
    match sy with
    | []                          -> []
    | (T None) :: _               -> []
    | (T Some h) :: _             -> [h]
    | h :: t when List.mem h v    -> first' g v t
    | h :: t when nullable_nt g h -> union (first' g (h::v) t) (first_rhs g v h)
    | h :: t                      -> first_rhs g v h
  and first_rhs g v nt =
    List.concat <| List.map (first' g (nt::v)) << (rhs_nt g nt) 
  in unique << first' g [] sy

let first_n g nt n = unique <| List.concat << List.map (first g n) (rhs_nt g nt)


(* Função:  compute_first
 * ----------------------
 * Preenche a hashtable do conjunto FIRST com recurso à função first_n.
 *)
let compute_first (g : grammar) (null : null_t) : first_t =
  let (nt, _) = g in
  let n = List.length nt in
  let r = Hashtbl.create n in
  let () = List.iter (
      fun x ->
        Hashtbl.add r x (first_n g (N x) null)
    ) nt
  in r



(* Função:  rhs_with_nt
 * --------------------
 * Extrai da gramática g todas as produções que contenham o não-terminal nt.
 *)
let rhs_with_nt ((_, g) : grammar) (nt : symbol) : (symbol * production) list =
  Hashtbl.fold (fun x y r -> if List.mem nt y then (N x, y) :: r else r) g []

(* Função:  suffices
 * -----------------
 * Extrai os lados direitos a um não-terminal de uma produção.
 * Por exemplo, se for dada a produção
 *    S -> B D B e
 * será devolvido
 *    [(S, D B e), (S, e)]
 * NOTA: A função está escrita de forma genérica.
 *)
let suffices nt (lhs, rhs) =
  let rec rhs_suffices_nt l nt =
    match l with
    | []                  -> []
    | h :: t when h = nt  -> (lhs, t) :: rhs_suffices_nt t nt
    | _ :: t              -> rhs_suffices_nt t nt
  in rhs_suffices_nt rhs nt


(* Função:  rhs_suffices
 * ---------------------
 * Extrai todos os lados direitos a um não-terminal de todas as produções que
 * contenham o esse não-terminal.
 * 
 * Composição das funções suffices e rhs_with_nt.
 *)
let rhs_suffices g nt =
  List.concat << List.map (suffices nt) (rhs_with_nt g nt)


(* Funções:  follow*
 * -----------------
 * Determinam o valor FOLLOW para cada não terminal.
 *)
let follow (g : grammar) (n : null_t) (f : first_t) (nt : symbol) =
  let rec follow' g v nt =
    if List.mem nt v then []
    else List.concat << List.map (follow'' g (nt::v)) (rhs_suffices g nt)
  and follow'' g v (l,r) =
    if nullable g [] r then union (first g n r) (follow' g v l)
    else first g n r
  in unique << follow' g [] nt


(* Função:  compute_follow
 * -----------------------
 * Preenche a hashtable do conjunto FOLLOW com recurso à função follow.
 * 
 * NOTA: a regra "fantasma" 0 -> S # permite calcular correctamente os follows
 * tendo em conta o caracter terminal #.
 *)
let compute_follow (g : grammar) (null : null_t) (f : first_t) : follow_t =
  let (nt, gr) = g in
  (* let nt = '0' :: nt in *)
  let () = Hashtbl.add gr '0' [N 'S'; T (Some '#')] in
  let g = (nt, gr) in
  let n = List.length nt in
  let r = Hashtbl.create n in
  let () = List.iter (
      fun x ->
        Hashtbl.add r x (follow g null f (N x))
    ) nt
  in r



(* Função:  read_grammar
 * ---------------------
 * Lê uma gramática do input.
 * 
 *   n: número de linhas esperadas de input.
 * 
 * returns: hash table com a gramática.
 * 
 * 
 * Sub-funções:  parse_*
 * ---------------------
 * Fazem o parse das strings de input de forma a obter os vários elementos de
 * uma linguagem: regras, produções, e símbolos terminais e não-terminais.
 * 
 * 
 * Sub-função:  nonterm_of_grammar
 * -------------------------------
 * Após criada a hash table, são obtidas as chaves desta, i.e., os não-terminais.
 * Será útil para calcular e apresentar logo por ordem os Null, First e Follow.
 *)
let read_grammar n : grammar =
  let parse_symbol c =
    if (c >= 'A') && (c <= 'Z') then N c
    else if (c >= 'a') && (c <= 'z') then T (Some c)
    else if (c = '_') then T (None)
    else failwith "parse_symbol: no valid symbol"
  in
  let rec parse_production p : production =
    match p with
    | []      -> []
    | x :: xs -> (parse_symbol x) :: (parse_production xs)
  in
  let parse_rule r : rule =
    match String.split_on_char ' ' r with
    | [] -> failwith "rule: is empty"
    | nt :: sep :: p when sep = separator -> (sfst nt, parse_production <| List.map sfst << p)
    | _  -> failwith "parse_rule: invalid syntax"
  in
  let nonterm_of_grammar g =
    ntsort <| unique << Hashtbl.fold (fun nt _ l -> nt :: l) g []
  in
  let tbl = Hashtbl.create n in
  let rec read i =
    if i = 0 then (nonterm_of_grammar tbl, tbl)
    else
      let s = read_line () in
      let (nt, r) = parse_rule s in
      let () = Hashtbl.add tbl nt r in
        read (i - 1)
  in read n


(* BLOCO PRINCIPAL
 * ---------------
 * 1) Obtém a gramática do stdin.
 * 2) Calcula o conjunto NULL e apresenta-o.
 * 3) Calcula o conjunto FIRST e apresenta-o.
 * 4) Calcula o conjunto FOLLOW e apresenta-o.
 *)
let () =
  let n = read_int () in
  let g = read_grammar n in
  let (nt, _) = g in
  let thenull = compute_null g in
  let () = Printf.printf "%s" <| string_of_null nt << thenull in
  let thefirst = compute_first g thenull in
  let () = Printf.printf "%s" <| string_of_first nt << thefirst in
  let thefollow = compute_follow g thenull thefirst in
  let () = Printf.printf "%s" <| string_of_follow nt << thefollow in
    ()

(* DOCUMENTAÇÃO
 * ------------
 * 
 * Os métodos de cálculo relativos a nullable, first e follow seguem um princípio
 * puramente funcional, fortemente inspirado em programação Haskell.
 * 
 * A explicação do objectivo de cada função é brevemente descrito junto de cada uma.
 * 
 * Os resultados são armazenados em hash tables, onde para cada não-terminal (char)
 * corresponde um resultado (bool para NULL, char list para FIRST e FOLLOW).
 * 
 * A própria gramática é armazenada numa hash table, onde a cada não-terminal (char)
 * correspondem várias bindings do tipo production.
 * 
 * Logo no momento de leitura da gramática do input é guardada numa char list os
 * não-terminais pela ordem de apresentação do output. Tal permite que a hash table
 * seja acedida logo pela ordem correcta, reduzindo assim as vezes em que é necessário
 * recorrer a algoritmos de ordenação.
 * 
 * Os métodos de cálculo chamam-se uns aos outros, notoriamente:
 *   -> FIRST invoca NULL.
 *   -> FOLLOW invoca NULL e FIRST.
 * 
 * Porquanto esta técnica não seja a mais eficiente, foi a qual optei por se aproximar
 * mais dos meus conhecimentos de Haskell e por representar, na minha óptica, de forma
 * mais directa as regras dos conjuntos que se procura calcular.
 * 
 * 
 * TRABALHO FUTURO
 * ---------------
 * Optimizações são possíveis através do uso mais consistente dos resultados armazenados
 * nas hash tables.
 * 
 * Contudo, a falta de tempo não permitiu, à data de entrega desta versão, a plena
 * implementação destas optimizações.
 * 
 * Algumas adaptações adicionais seriam necessárias no armazenamento de resultados
 * a fim de garantir uma optimização mais plena e consistente.
 * 
 * 
 * EXECUÇÃO
 * --------
 * 
 * As regras estão implementadas de forma directa no código.
 * 
 * A fim de evitar chamadas recursivas infinitas, foi implementado um sistema de
 * memorização dos não-terminais já visitados.
 * 
 * 
 * ALTERNATIVA
 * -----------
 * 
 * Um código com recurso ao Teorema do Ponto Fixo de Tarsky foi inicialmente
 * concebido, mas dificuldades na sua implementação levaram a que procurasse
 * uma alternativa recorrendo a um paradigma puramente funcional inspirado em
 * Haskell, o que me permitiu implementar directamente as regras dos conjuntos
 * a calcular.
 * 
 * Esta versão, ainda não funcional, encontra-se guardada para futura referência
 * e pode ser consultada para apreciação adicional.
 *)
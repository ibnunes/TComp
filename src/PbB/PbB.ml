(* TEORIA DA COMPUTAÇÃO 2019/2020
 *
 * Autor: Igor Nunes (Nº 41381)
 * Data:  04/05/2020 (versão 2)
 *
 * Novo algoritmo baseado em suffix arrays.
 * (Versão 1 recorria a programação dinâmica)
 *
 * Vantagem no tempo:
 *    -> Complexidade de tempo inferior a O(mn) ou O(n²) (versão 1);
 *    -> Testes práticos indicam redução para cerca de 1/3 do tempo;
 *    -> Demora menos de 0.5 segundos para 2 caudas de DNA até 10000 de comprimento.
 *
 * Desvantagem na memória:
 *    -> Muito maior consumo de memória para casos grandes;
 *    -> Caso dos 2×100000 gerou um bloqueio do computador.
 * 
 * Changelog:
 *    1.0 (25/abr/2020) -> primeira versão
 *    1.1 (25/abr/2020) -> correcção de bug na análise da diagonal
 *    2.0 (04/mai/2020) -> novo algoritmo com base em suffix arrays
 *)

(* 
 * ===== PbBsa: Problema B com Suffix Arrays =====
 * Documentação adicionada a 11/05/2020.
 * Bibliografia indicada no final do código-fonte.
 *)

(*
 * NOTA PESSOAL
 * ------------
 * O ciclo 'for' facilitou o percorrer de todos os arrays, mas é perfeitamente
 * possível implementar com recurso a programação funcional pura.
 *)

(* TIPOS DE DADOS
 * --------------
 * element -> tuplo composto por índice do sufixo e a string sufixo per se
 * suffix  -> array de sufixos (suffix array), baseado no tipo element
 * prefix  -> array de prefixos (prefix array), 
 *)
type element = (int * string)
type suffix  = element array
type prefix  = int array


(* CONSTANTES
 * ----------
 * null_element -> elemento "nulo" de um suffix array
 * separator    -> separador das 2 strings
 *                 ('|' tem código ASCII superior a qualquer letra, o que é útil
 *                  no sorting da suffix array)
 *)
let null_element : element = (0, "")
let separator = '|'


(* === DEBUG ===
 * Estas funções são para uso único e exclusivo durante o processo de
 * implementação e teste.
 * Não são usadas em qualquer lado na versão final.
 *)
let printe = fun (i, s) -> Printf.printf "(%3d, %s)\n" i s
let prints = Array.iter printe
let printp = Array.iter (Printf.printf "%3d\n")
(* ============= *)


(* Função:  lcp
 * ------------
 * Longest Common Prefix
 * 
 *  s: 1ª string
 *  t: 2ª string
 * 
 *  return: Comprimento do maior prefixo comum entre as 2 strings
 * 
 * Exemplo: "aabbab" e "aabab" têm como maior prefixo "aab",
 *          logo será devolvido 3.
 *)
let lcp s t =
  let n = min (String.length s) (String.length t) in
  let rec run i =
    if i = n then i
    else (
      if s.[i] = t.[i] then run (i + 1)
      else i
    )
  in run 0


(* Função:  max_of_prefix
 * ----------------------
 * Maior prefixo de todos os prefixos.
 * 
 *  p: prefix array (argumento oculto do tipo int array)
 * 
 *  return: maior valor inteiro da prefix array
 * 
 * Recorre a um fold left clássico com a função max, começando com o
 * menor valor dos inteiros.
 *)
let max_of_prefix = Array.fold_left max (min_int)


(* Função:  compare
 * ----------------
 * Função comparadora entre dois valores do tipo 'element'.
 * 
 *  (_, x): 1º element, sendo 'x' a 1ª string
 *  (_, y): 2º element, sendo 'y' a 2ª string
 * 
 *  return: valor inteiro que determina a ordem lexicográfica entre as 2 strings
 * 
 * Função que encapsula a String.compare de forma a poder ser usada diretamente
 * sem recurso ao mecanismo "fun" do OCaml.
 *)
let compare (_, x) (_, y) = String.compare x y


(* Função:  suffix_of_string
 * -------------------------
 * Cria a suffix array ordenada por ordem lexicográfica.
 * 
 *  s: string, que são as 2 strings de input separadas por 'separator'
 * 
 *  return: suffix array lexicograficamente ordenado
 * 
 * == ALGORITMO ==
 * 1. Seja n o comprimento da string de entrada s.
 * 2. É criado um array de n elementos, inicialmente nulos.
 * 3. Para cada i de 0 até n-1, extrair o sufixo de comprimento i da string s,
 *    mantendo registo do índice i num tuplo na forma (índice, sufixo).
 * 4. Ordenar lexicograficamente o array.
 * 5. Retornar a suffix array e o seu tamanho num tuplo (suffix_array, tamanho).
 *)
let suffix_of_string s : (suffix * int) =
  let n = String.length s in
  let result = Array.make n null_element in
  let () = for i = 0 to n - 1 do
    result.(i) <- (i + 1, String.sub s i (n - i))
  done in
  let () = Array.sort compare result
  in (result, n)


(* Função:  prefix_of_suffix
 * -------------------------
 * Cria uma prefix array com base numa suffix array.
 * 
 *  s: suffix array
 *  n: comprimento da suffix array 's'
 * 
 *  return: prefix array correspondente à suffix array 's'
 * 
 * Uma prefix array é um array de inteiros, int array.
 * 
 * == Algoritmo ==
 * 1. Seja result uma prefix array com n elementos inicializados a (-1).
 * 2. Para cada i de 1 até n-1:
 *    a) Calcular o maior prefixo comum (longest common prefix) entre as strings
 *       s[i-1] e s[i].
 *    b) Guardar o valor calculado em result[i].
 * 3. Devolver result.
 *)
let prefix_of_suffix s n : prefix =
  let result = Array.make n (-1) in
  let () = for i = 1 to n - 1 do
    result.(i) <- lcp (snd s.(i-1)) (snd s.(i))
  done
  in result


(* Função:  check
 * --------------
 * Dadas 2 strings, verifica se ambas NÃO pertencem à string original de input.
 * 
 * == Algoritmo ==
 * Uma e apenas uma das strings deve ter o separador 'separator'.
 * 
 * == Exemplos ==
 * 1. "ab|cd" e "cd" não pertencem ambas à mesma string original.
 * 2. "ab|cd" e "b|cd" pertencem ambas à 1ª string original.
 * 3. "cd" e "d" pertencem ambas à 2ª string original.
 *)
let check (_, x) (_, y) =
  (String.contains x separator && not (String.contains y separator)) ||
  (not (String.contains x separator) && String.contains y separator)


(* Função:  search_lcs
 * -------------------
 * Longest Commum Substring
 * 
 *  s: suffix array
 *  p: prefix array
 *  n: comprimento de ambos os arrays
 * 
 *  return: comprimento da maior substring comum
 * 
 * Se a cada 2 strings não pertencerem ambas à mesma string original, guardar
 * o máximo valor entre o máximo previamente existente e o novo armazenado no
 * array de prefixos.
 *)
let search_lcs s p n =
  let result = ref 0 in
  let () = for i = 1 to n - 1 do
    if check s.(i-1) s.(i) then result := max !result p.(i);
  done
  in !result


(* BLOCO PRINCIPAL (main do programa)
 * ---------------
 * 1. Lê as 2 strings a comparar.
 * 2. Concatena as strings, colocando o separador entre elas.
 * 3. Constrói a suffix array ('s', de "suffix") e devolve o seu comprimento ('sz', de "size").
 * 4. Constrói a prefix array ('p', de "prefix") a partir da suffix array.
 * 5. Determina o comprimento da maior substring e imprime o resultado.
 *)
let () =
  let a, b     = read_line (), read_line ()        in  (* 1 *)
  let test     = a ^ (String.make 1 separator) ^ b in  (* 2 *)
  let (s, sz)  = suffix_of_string test             in  (* 3 *)
  let p        = prefix_of_suffix s sz             in  (* 4 *)
    Printf.printf "%d\n" (search_lcs s p sz)           (* 5 *)


(* BIBLIOGRAFIA
 * ------------
 * Estudei primeiramente a possibilidade de usar uma suffix tree, e só depois me
 * decidi em usar suffix arrays por fornecerem uma solução igualmente mais rápida,
 * mas também mais simples de implementar.
 * 
 * A minha primeira pesquisa incidiu bastante no Algoritmo de Ukkonen por apresentar
 * a promessa de uma solução de ordem O(n) com recurso a generalized suffix trees.
 * 
 * A minha pesquisa por suffix trees começou com os seguintes links:
 * [Consultados dentre 26 de Abril e 4 de Maio de 2020]
 * [A] https://cs.uwaterloo.ca/~plragde/flaneries/FDS/Text_Processing.html
 * [B] http://www.allisons.org/ll/AlgDS/Tree/Suffix/
 * [C] (Dois links associados com uma implementação de Ukkonen em OCaml)
 *    [C.1] https://www.lri.fr/~filliatr/ftp/ocaml/ds/suffix_tree.mli.html
 *    [C.2] https://www.lri.fr/~filliatr/ftp/ocaml/ds/suffix_tree.ml.html
 * [D] https://www.geeksforgeeks.org/suffix-tree-application-5-longest-common-substring-2/
 * 
 * Com este último exemplo a demonstrar a complexidade de implementação na
 * linguagem C, decidi então enveredar pela opção das suffix arrays.
 * 
 * Algoritmo final implementado com base na resposta à seguinte questão do Stack Exchange:
 * [E] https://cs.stackexchange.com/questions/9555/computing-the-longest-common-substring-of-two-strings-using-suffix-arrays
 *    [Consultado a 04 de Maio de 2020]
 * 
 * Ideia testada e comparada com o seguinte site:
 * [F] http://www.allisons.org/ll/AlgDS/Strings/Suffix/
 * 
 *)

(* EXEMPLO DE EXECUÇÃO
 * -------------------
 * Usei extensivamente o exemplo dado no link [E] para poder testar o meu código
 * à medida que o ia implementando.
 * 
 * Neste caso, sejam:
 *   s = 'abcabc'
 *   t = 'bc'
 * 
 * São concatenadas então para:
 *   test = 'abcabc|bc'
 * 
 * Usando a função 'suffix_of_string', é construída a respectiva suffix array.
 * Seja SA esta suffix array.
 * 
 * SA = [|
 *        (0, 'abcabc|bc');
 *        (1, 'bcabc|bc');
 *        (2, 'cabc|bc');
 *        (3, 'abc|bc');
 *        (4, 'bc|bc');
 *        (5, 'c|bc');
 *        (6, '|bc');
 *        (7, 'bc');
 *        (8, 'c')
 *      |]
 * ( array inicial )
 * 
 * A função 'suffix_of_string' trata igualmente da sua ordenação lexicográfica,
 * resultando no seguinte:
 * 
 * SA = [|
 *        (3, 'abc|bc');
 *        (0, 'abcabc|bc');
 *        (7, 'bc');
 *        (4, 'bc|bc');
 *        (1, 'bcabc|bc');
 *        (8, 'c');
 *        (5, 'c|bc');
 *        (2, 'cabc|bc');
 *        (6, '|bc')
 *      |]
 * ( resultado final )
 * 
 * Este suffix array tem tamanho 9, pelo que é devolvido o tuplo (SA, 9).
 * 
 * A função 'prefix_of_suffix' recebe SA e o taanho 9, construindo a respectiva
 * prefix array, a que iremos chamar PA.
 * Esta função irá comparar os elementos da SA dois a dois da seguinte forma (exemplo):
 * 
 *        (3, 'abc|bc');
 *             ^^^^
 *             |||X <-- maior prefixo comum = 3
 *             VVVV
 *        (0, 'abcabc|bc');
 * 
 * O resultado da função será então o seguinte:
 * 
 * PA = [| 0; 3; 0; 2; 2; 0; 1; 1; -1 |]
 *                                 ^
 *                                 |
 * (O último elemento do array é neutro e sem significado prático)
 * 
 * Percorrendo PA, determinamos que 3 é o maior exemplo, mas este corresponde
 * ao índice 1, ou seja, a SA[0] e SA[1]:
 *        (3, 'abc|bc');
 *        (0, 'abcabc|bc');
 * 
 * Mas ambas as strings contêm o separador '|', o que significa que o prefixo
 * de tamanho 3 pertence à 1ª string original. Não nos interessa.
 * 
 * O próximo máximo é 2, no índice 3 de PA, o que corresponde a SA[2] e SA[3]:
 *        (7, 'bc');
 *        (4, 'bc|bc');
 * 
 * Ora, uma string tem o separador e outra não, portanto o prefixo de tamanho 2
 * pretence às 2 strings originais distintas!
 * 
 * Este é o nosso resultado: 2.
 * 
 * Facilmente poderíamos indicar igualmente qual a substring uma vez que basta
 * extrair os 2 primeiro elementos de uma das strings, resultandos em 'bc'.
 *)

(* TEORIA DA COMPUTAÇÃO 2019/2020
 *
 * Autor: Igor Nunes (Nº 41381)
 * Data:  19/fev/2020
 *
 * Uso do Algoritmo de Wagner-Fischer para calcular a Distância de Levenshtein
 *
 * Changelog:
 *    1.0 (19/fev/2020) -> primeira versão
 *    1.1 (19/fev/2020) -> optimização: uso de memória reduzido para uma matriz de 2 linhas
 *    1.2 (20/fev/2020) -> optimização após análise de casos maiores
 *    1.3 (20/fev/2020) -> optimização: recurso a listas (resultou em menor tempo de execução)
 *    1.4 (26/fev/2020) -> optimização no uso das listas
 *    1.5 (04/mar/2020) -> abandono da list_of_string
 *    1.6 (04/mar/2020) -> regresso ao uso de Arrays: redução de ~20% do tempo de execução
 *)


(* Obtém mínimo entre 3 números *)
let min3 a b c = min a (min b c)


(* Distância de Levenshtein
 *    initlist n        ->  inicializa um Array de dimensão n+1 
 *    dists i n m d     ->  percorre as linhas da matriz conforme a string s
 *    distt c j d0 z    ->  percorre as colunas da matriz conforme a string t e o caracter c
 *)
let distance s t =
  let initarray n = Array.init (n + 1) (fun i -> i) in
  let rec dists i n m d =
    let rec distt c j d0 z r =
      if j = n then r else
        let sc = if t.[j] = c then 0 else 1 in
        let m = min3 (1 + d0.(j+1)) (1 + z) (sc + d0.(j)) in
        let () = r.(j+1) <- m in
          distt c (j + 1) d0 m r
    in
      if i > m then d.(n) else
        let d1 = Array.make (n + 1) 0 in
        let () = d1.(0) <- i in
        let d1 = distt s.[i-1] 0 d i d1 in
          dists (i + 1) n m d1
  in
    let n = String.length t in
    let m = String.length s in
    let d = initarray n in
      dists 1 n m d


(* Função main *)
let () =
  let a, b = read_line (), read_line () in
  let d = distance a b in
    Printf.printf "%d\n" d
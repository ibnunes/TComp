(* TEORIA DA COMPUTAÇÃO 2019/2020
 *
 * Autor: Igor Nunes (Nº 41381)
 * Data:  01/06/2020 (versão 2)
 *
 * Recorre a um autómato minimalista construído com o Método de Thompson.
 * 
 * Changelog:
 *    1.0 (28/mai/2020) -> Primeira versão
 *    1.1 (29/mai/2020) -> Correcção de bug na interpretação do 0
 *    1.2 (30/mai/2020) -> Aumento de performance
 *    1.3 (01/jun/2020) -> Corrige bug que levava a loops infinitos
 *                         Introduz simplificação da expressão regular
 *    2.0 (01/jun/2020) -> Novo algoritmo de pesquisa (segundo Thompson)
 *)

(* 
 * ===== PbC: Problema C =====
 * Documentação adicionada a 29/05/2020.
 * Documentação actualizada a 11/06/2020.
 * Bibliografia indicada no final do código-fonte.
 * Exemplo de execução após a bibliografia.
 *)

(* ÍNDICE
 * ------
 * 
 * -> [Código fornecido pelo professor]
 * 
 * -> Tipo de dados:  label
 * -> Tipo de dados:  transition
 * -> Tipo de dados:  automata
 * 
 * -> Constante:  t_null
 * -> Constante:  init_automata
 * 
 * -> Função:  simplify
 * -> Função:  automata_of_regexp
 * -> Função:  search_pattern
 * 
 * -> Bloco principal (main do programa)
 * 
 * -> (Bibliografia)
 * -> (Exemplo de execução)
 *)


(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 * * * * * * * * * * * * * * * * * * * * * * CÓDIGO FORNECIDO PELO PROFESSOR * * * * * * * * * * * * * * * * * * * * * *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

type regexp =
 | V  
 | E
 | C of char
 | U of regexp * regexp 
 | P of regexp * regexp 
 | S of regexp

module Parser_regexp = struct

  
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | RPAREN
    | LPAREN
    | EPS
    | EOF
    | EMP
    | CONC
    | CHAR of (
       (char)
  )
    | AST
    | ALT
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState12
  | MenhirState7
  | MenhirState6
  | MenhirState1
  | MenhirState0


let rec _menhir_goto_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_expr -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv47 * _menhir_state * 'tv_term)) * _menhir_state * 'tv_expr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv45 * _menhir_state * 'tv_term)) * _menhir_state * 'tv_expr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (e1 : 'tv_term)), _, (e2 : 'tv_expr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_expr = 
                                ( P (e1, e2) )
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv46)) : 'freshtv48)
    | MenhirState12 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv51 * _menhir_state * 'tv_term)) * _menhir_state * 'tv_expr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv49 * _menhir_state * 'tv_term)) * _menhir_state * 'tv_expr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (e1 : 'tv_term)), _, (e2 : 'tv_expr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_expr = 
                                ( U (e1, e2) )
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv50)) : 'freshtv52)
    | MenhirState1 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv59 * _menhir_state) * _menhir_state * 'tv_expr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv55 * _menhir_state) * _menhir_state * 'tv_expr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv53 * _menhir_state) * _menhir_state * 'tv_expr) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (e : 'tv_expr)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_atom = 
                                ( e )
             in
            _menhir_goto_atom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv54)) : 'freshtv56)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv57 * _menhir_state) * _menhir_state * 'tv_expr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv58)) : 'freshtv60)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv73 * _menhir_state * 'tv_expr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EOF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv69 * _menhir_state * 'tv_expr) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv67 * _menhir_state * 'tv_expr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (le : 'tv_expr)) = _menhir_stack in
            let _2 = () in
            let _v : (
       (regexp)
            ) = 
                                ( le )
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv65) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : (
       (regexp)
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv63) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : (
       (regexp)
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv61) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let ((_1 : (
       (regexp)
            )) : (
       (regexp)
            )) = _v in
            (Obj.magic _1 : 'freshtv62)) : 'freshtv64)) : 'freshtv66)) : 'freshtv68)) : 'freshtv70)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv71 * _menhir_state * 'tv_expr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv72)) : 'freshtv74)
    | _ ->
        let (() : unit) = () in
        ((Printf.fprintf stderr "Internal failure -- please contact the parser generator's developers.\n%!";
        assert false) : 'freshtv75)

and _menhir_goto_term : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_term -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState0 | MenhirState12 | MenhirState6 | MenhirState1 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv39 * _menhir_state * 'tv_term) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ALT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv31 * _menhir_state * 'tv_term) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | CHAR _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _v
            | EMP ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState12
            | EPS ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState12
            | LPAREN ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState12
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12) : 'freshtv32)
        | CONC ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv33 * _menhir_state * 'tv_term) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | CHAR _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
            | EMP ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState6
            | EPS ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState6
            | LPAREN ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState6
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6) : 'freshtv34)
        | EOF | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv35 * _menhir_state * 'tv_term) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (e : 'tv_term)) = _menhir_stack in
            let _v : 'tv_expr = 
                                ( e )
             in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv36)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv37 * _menhir_state * 'tv_term) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv38)) : 'freshtv40)
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv43 * _menhir_state * 'tv_factor) * _menhir_state * 'tv_term) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv41 * _menhir_state * 'tv_factor) * _menhir_state * 'tv_term) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (e1 : 'tv_factor)), _, (e2 : 'tv_term)) = _menhir_stack in
        let _v : 'tv_term = 
                                ( P (e1, e2) )
         in
        _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v) : 'freshtv42)) : 'freshtv44)

and _menhir_goto_factor : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_factor -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv29 * _menhir_state * 'tv_factor) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHAR _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
    | EMP ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | EPS ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LPAREN ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | ALT | CONC | EOF | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv27 * _menhir_state * 'tv_factor) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (e : 'tv_factor)) = _menhir_stack in
        let _v : 'tv_term = 
                                ( e )
         in
        _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v) : 'freshtv28)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState7) : 'freshtv30)

and _menhir_goto_atom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_atom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv25 * _menhir_state * 'tv_atom) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AST ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv21 * _menhir_state * 'tv_atom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv19 * _menhir_state * 'tv_atom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (e : 'tv_atom)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_factor = 
                                ( S e )
         in
        _menhir_goto_factor _menhir_env _menhir_stack _menhir_s _v) : 'freshtv20)) : 'freshtv22)
    | ALT | CHAR _ | CONC | EMP | EOF | EPS | LPAREN | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv23 * _menhir_state * 'tv_atom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (e : 'tv_atom)) = _menhir_stack in
        let _v : 'tv_factor = 
                                ( e )
         in
        _menhir_goto_factor _menhir_env _menhir_stack _menhir_s _v) : 'freshtv24)) : 'freshtv26)

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState12 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv9 * _menhir_state * 'tv_term)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv10)
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv11 * _menhir_state * 'tv_factor) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv12)
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv13 * _menhir_state * 'tv_term)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv14)
    | MenhirState1 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv15 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv16)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv17) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv18)

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHAR _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | EMP ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | EPS ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LPAREN ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState1

and _menhir_run2 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv7) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _1 = () in
    let _v : 'tv_atom = 
                                ( E )
     in
    _menhir_goto_atom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv8)

and _menhir_run3 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv5) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _1 = () in
    let _v : 'tv_atom = 
                                ( V )
     in
    _menhir_goto_atom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv6)

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
       (char)
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv3) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((c : (
       (char)
    )) : (
       (char)
    )) = _v in
    ((let _v : 'tv_atom = 
                                ( C c )
     in
    _menhir_goto_atom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv4)

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and regexpr : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
       (regexp)
) =
  fun lexer lexbuf ->
    let _menhir_env =
      let (lexer : Lexing.lexbuf -> token) = lexer in
      let (lexbuf : Lexing.lexbuf) = lexbuf in
      ((let _tok = Obj.magic () in
      {
        _menhir_lexer = lexer;
        _menhir_lexbuf = lexbuf;
        _menhir_token = _tok;
        _menhir_error = false;
      }) : _menhir_env)
    in
    Obj.magic (let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1) = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    ((let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CHAR _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | EMP ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | EPS ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LPAREN ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0) : 'freshtv2))

  



end

module Lexer_regexp = struct
 
  open Parser_regexp

  exception Error of string


  let __ocaml_lex_tables = {
    Lexing.lex_base =
    "\000\000\245\255\246\255\247\255\248\255\249\255\250\255\251\255\
      \252\255\253\255\254\255\255\255";
    Lexing.lex_backtrk =
    "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255";
    Lexing.lex_default =
    "\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000";
    Lexing.lex_trans =
    "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\011\000\011\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \011\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \004\000\003\000\007\000\009\000\000\000\000\000\008\000\000\000\
      \006\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\010\000\010\000\010\000\010\000\010\000\010\000\010\000\
      \010\000\010\000\010\000\010\000\010\000\010\000\010\000\010\000\
      \010\000\010\000\010\000\010\000\010\000\010\000\010\000\010\000\
      \010\000\010\000\010\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\010\000\010\000\010\000\010\000\010\000\010\000\010\000\
      \010\000\010\000\010\000\010\000\010\000\010\000\010\000\010\000\
      \010\000\010\000\010\000\010\000\010\000\010\000\010\000\010\000\
      \010\000\010\000\010\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \002\000";
    Lexing.lex_check =
    "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\000\000\000\000\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \000\000\000\000\000\000\000\000\255\255\255\255\000\000\255\255\
      \000\000\000\000\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\255\255\255\255\255\255\255\255\255\255\
      \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
      \000\000\000\000\000\000\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
      \000\000";
    Lexing.lex_base_code =
    "";
    Lexing.lex_backtrk_code =
    "";
    Lexing.lex_default_code =
    "";
    Lexing.lex_trans_code =
    "";
    Lexing.lex_check_code =
    "";
    Lexing.lex_code =
    "";
  }

  let rec tokenize lexbuf =
    __ocaml_lex_tokenize_rec lexbuf 0
  and __ocaml_lex_tokenize_rec lexbuf __ocaml_lex_state =
    match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
        | 0 ->
                                        ( tokenize lexbuf )

    | 1 ->
  let
                          s
  = Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
                                        ( CHAR s )

    | 2 ->
                                        ( ALT )

    | 3 ->
                                        ( CONC )

    | 4 ->
                                        ( AST )

    | 5 ->
                                        ( EMP )

    | 6 ->
                                        ( EPS )

    | 7 ->
                                        ( LPAREN )

    | 8 ->
                                        ( RPAREN )

    | 9 ->
                                        ( EOF )

    | 10 ->
        ( raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) )

    | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
        __ocaml_lex_tokenize_rec lexbuf __ocaml_lex_state

  ;;
end

(* --------------------------------- fim lexing/parsing code ----------------------------------------------------- *)

open Parser_regexp


(* função principal de leitura de uma expressão regular (a partir de uma string) *)
let regexp st =
  let linebuf = Lexing.from_string st in
  try regexpr Lexer_regexp.tokenize linebuf
  with _ -> failwith "regexp: input problem"


(* **************************************************************************************************************** *)
(* ********************************************   Começar aqui **************************************************** *)


(* exemplo de código para ilustrar o uso da função regexp e o tipo regexp *)
let rec string_of_regexp s =
  match s with
  | V       -> "0"
  | E       -> "1"
  | C  c    -> String.make 1 c    
  | U (f,g) -> "("^(string_of_regexp f)^" + "^(string_of_regexp g)^")"
  | P (f,g) -> "("^(string_of_regexp f)^" . "^(string_of_regexp g)^")"
  | S s     -> (string_of_regexp s)^"*"

(*
let () =
  let r = regexp Sys.argv.(1) in
  let () = print_string "input: " in
    print_endline (string_of_regexp r)
*)

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 * * * * * * * * * * * * * * * * * * * * FIM DO CÓDIGO FORNECIDO PELO PROFESSOR  * * * * * * * * * * * * * * * * * * * *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)


(* Tipo de dados:  label
 * ---------------------
 * Representa o rótulo de uma transição no autómato.
 * 
 * Para o rótulo optei pelo tipo de dados 'label' uma vez que None pode representar
 * directamente uma transição 0, Epsilon representa uma transição Ɛ, enquanto
 * Char c representa uma transição com o caracter c.
 *)
type label =
  | None
  | Epsilon
  | Char of char


(* Tipo de dados:  transition
 * --------------------------
 * Representa uma transição no autómato. É um tuplo com os seguintes 2 elementos:
 *   -> Estado para o qual transita;
 *   -> Rótulo da transição (caracter, Ɛ ou 0).
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
 *)
type automata = transition list array


(* Constante:  t_null
 * ------------------
 * Lista de transições vazia.
 * Um nó do autómato que armazene um t_null é um estado final.
 *)
let t_null : transition list = []


(* Constante:  init_automata
 * -------------------------
 * Autómato inicial, ou autómato "pai".
 * Qualquer expressão regular começa com este autómato.
 * 
 *   (0) --- Ɛ ---> (1)
 * 
 *     0:     [( 1, epsilon); ]
 *     1:     []
 * 
 * Qualquer cauda de DNA será automaticamente aceite por este autómato.
 *)
let init_automata : automata = [| [(1, Epsilon)]; t_null |]

(* Função:  sigma
 * --------------
 * Adiciona uma lista de transições ∑* a uma lista s já existente e com estado
 * destino i.
 * 
 * Útil para criar esta transição ∑* nos estados inicial e final a fim de criar
 * a expressão regular ∑*.R.∑* a fim de se poder aplicar o Algoritmo de Thopson.
 *)
let sigma s i : transition list = (i, Char 'A') :: (i, Char 'T') :: (i, Char 'G') :: (i, Char 'C') :: s


(* Funções auxiliares para debug
 * -----------------------------
 * NÃO são utilizadas na versão final!
 * O seu propósito é meramente para debugging.
 *)
let printt (i, c) =
  match c with
  | None    -> Printf.printf "(%2d, 0); " i
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


(* Função:  simplify
 * -----------------
 * Utiliza identidades das expressões regulares para simplificar a regex 's'.
 * São elas as seguintes:
 * 
 *   1.  0 + R = R
 *   2.  0 . R = 0
 *   3.  Ɛ . R = R
 *   4.  Ɛ + R = R*
 *   5.  Ɛ* = 0* = Ɛ
 *   6.  R + R = R
 *   7.  R* . R* = R*
 *   8.  ( R* )* = R*
 *   9.  Ɛ + RR* = R*
 *  10.  ( P* . Q* )* = ( P* + Q* )* = (P + Q)*
 * 
 * No caso de casos como A+B+C+A é usada a função auxiliar 'recunion' para
 * deixar apenas os casos únicos das uniões uma vez que A + A = A.
 * 
 * 
 * Sub-função:  recunion
 * ---------------------
 * Trata da identidade A + A = A de forma recursiva sobre uniões consecutivas.
 * 
 * 
 * NOTA: o uso recursivo e conjunto de 'simplify' e 'recunion' trata de forma
 * simples todos os casos de repetições nas uniões.
 * 
 * NOTA 2: A simplificação não é obrigatória, mas ajuda a evitar redundâncias.
 *)
let rec simplify s =
  let rec recunion h s =
    match s with
    | U (f, g) when f = h -> g
    | U (f, g) when g = h -> f
    | U (f, g)            -> U (recunion h f, recunion h g)
    | _                   -> s
  in
  match s with
  | V        -> V
  | E        -> E
  | C  c     -> C c
  | U (f, g) ->
    let s = U (simplify f, simplify g) in (
      match s with
      | U (U (f, g), h)              -> U (h, recunion h (U (f, g)))
      | U (h, U (f, g))              -> U (h, recunion h (U (f, g)))
      | U (E, P (f, S g)) when f = g -> S f
      | U (E, P (S g, f)) when f = g -> S f
      | U (P (f, S g), E) when f = g -> S f
      | U (P (S g, f), E) when f = g -> S f
      | U (V, g)                     -> g
      | U (f, V)                     -> f
      | U (f, g)          when f = g -> f
      | _                            -> s
    )

  | P (f, g) ->
    let s = P (simplify f, simplify g) in (
      match s with
      | P (S f, S g) when f = g -> S f
      | P (V, g)                -> V
      | P (f, V)                -> V
      | P (E, g)                -> g
      | P (f, E)                -> f
      | _                       -> s
    )

  | S  s     ->
    let s = S (simplify s) in (
      match s with
      | S (P (S f, S g)) -> S (U (f, g))
      | S (U (S f, S g)) -> S (U (f, g))
      | S (S r)          -> S r
      | S E              -> E
      | S V              -> E
      | _                -> s
    )


(* Função:  automata_of_regexp
 * ---------------------------
 * Gera um autómato a partir da expressão regular.
 * 
 *   rex: a expressão regular, do tipo de dados regexp.
 * 
 * returns: autómato correspondente à expressão regular.
 * 
 * 
 * Dada a expressão regular R, o autómato L gerado é dado pelo seguinte:
 * 
 * R = 'A'
 * 
 *   (0) --- A ---> (1)
 * 
 * 
 * R = 'A.B'
 * 
 *   (0) --- A ---> (2) --- B ---> (1)
 * 
 * 
 * R = 'A+B'
 * 
 *       /-- Ɛ --> (2) --- A ---> (4) -- Ɛ --\
 *      /                                    V
 *   (0)                                     (1)
 *      \                                    ^
 *       \-- Ɛ --> (3) --- B ---> (5) -- Ɛ --/
 * 
 * 
 * R = 'A*'
 * 
 *                     /--- Ɛ ----\
 *                    V            \
 *   (0) --- Ɛ ---> (2) --- A ---> (3) --- Ɛ ---> (1)
 *    \                                           ^
 *     \------------------- Ɛ -------------------/
 * 
 * 
 * R = '0'
 * 
 *   (0) --- 0 ---> (1)
 * 
 * 
 * R = '1'
 * 
 *   (0) --- Ɛ ---> (1)
 * 
 * 
 * Este algoritmo tira partido do facto do tipo de dados regexp ser indutivo.
 * O algoritmo assume que, a cada ponto, foi recebido um sub-autómato init_automata no seguinte formato:
 * 
 *   (i) --- Ɛ ---> (l)
 * 
 * É também recebido o valor 'top', o qual indica qual o maior nó existente até ao momento.
 * O autómato é expandido entre os nós i e l, sendo criados quantos nós sejam necessários.
 * Em particular:
 *   -> A.B gera mais 1 nó;
 *   -> A+B gera mais 4 nós;
 *   -> A* gera mais 2 nós.
 * 
 * Uma vez que cada índice i do array do tipo 'automata' corresponde ao nó i do autómato,
 * basta-nos fazer um append, quando necessário, dos novos nós, sendo as suas transições
 * actualizadas de acordo com as regras supra-mencionadas.
 * 
 * Os nós são criados percorrendo a expressão regular recursivamente, uma das vantagens
 * dos tipos de dados indutivos como é o regexp.
 * 
 * 
 * CURIOSIDADE: Devido à forma como o algoritmo funciona, o estado final em qualquer
 * autómato será sempre o estado 1, sendo o inicial o estado 0.
 * 
 * 
 * Sub-função:  run
 * ----------------
 * Alberga o algoritmo anteriormente narrado, sendo a função recursiva propriamente dita.
 * Os parâmetros i, l e top foram já descritos.
 * A função é chamada com i=0, l=1 e top=1, conforme o autómato "pai" (onde a = init_automata).
 * 
 * A sub-função 'run' retorna um tuplo (top, a), onde 'top' é o novo estado com o n° mais
 * elevado (é preciso manter track de qual o estado com maior número a todo o momento),
 * e 'a' é o autómato actualizado.
 *)
let automata_of_regexp (rex : regexp) : automata =
  let rec run (r : regexp) (a : automata) (i : int) (l : int) (top : int) =
    match r with
    | V        ->                   (* 0 *)
      a.(i) <- [(l, None)];
      (top, a)

    | E        ->                   (* 1 *)
      a.(i) <- [(l, Epsilon)];
      (top, a)

    | C  c     ->                   (*  A  *)
      a.(i) <- [(l, Char c)];
      (top, a)

    | U (f, g) ->                   (*  A+B  *)
      let newtop = top + 4 in
      let a = Array.append a (Array.make 4 t_null) in
        a.(i)      <- [(top+1, Epsilon); (top+2, Epsilon)];
        a.(top+3)  <- [(l, Epsilon)];
        a.(newtop) <- [(l, Epsilon)];
      let (xl, a) = run f a (top+1) (top+3) newtop in
      let (yl, a) = run g a (top+2) (newtop) xl in
        (yl, a)

    | P (f, g) ->                   (*  A.B  *)
      let newtop = top + 1 in
      let a = Array.append a (Array.make 1 t_null) in
        a.(i)      <- [(newtop, Epsilon)];
        a.(newtop) <- [(l, Epsilon)];
      let (xl, a) = run f a i newtop newtop in
      let (yl, a) = run g a newtop l xl in
        (yl, a)

    | S  s     ->                   (*  A*  *)
      let newtop = top + 2 in
      let a = Array.append a (Array.make 2 t_null) in
        a.(i)     <- [(l, Epsilon); (top+1, Epsilon)];
        a.(top+2) <- [(top+1, Epsilon); (l, Epsilon)];
      let (xl, a) = run s a (top+1) (top+2) newtop in
        (xl, a)

  in
    let (_, a) = run rex init_automata 0 1 1
    in
      a.(0) <- sigma a.(0) 0;
      a.(1) <- sigma a.(1) 1;
      a


(* Função:  unique
 * ---------------
 * Devolve uma lista com os elementos não repetidos.
 * É assumido que a lista está ordenada.
 *)
let rec unique = function
| []           -> []
| x :: y :: ys -> if x = y then unique (y :: ys) else x :: unique (y :: ys)
| x :: xs      -> x :: unique xs


(* Função:  search_pattern
 * -----------------------
 * Procura numa cauda de DNA se existe uma sequência que cumpra o padrão 
 * dado pela expressão regular.
 * 
 *   a: o autómato que representa a expressão regular.
 *   s: a cauda de DNA.
 * 
 * returns: booleano que indica se tal sequência existe ou não.
 * 
 * A função 'jump' salta as transições Ɛ e a função 'check' verifica se já foi
 * alcançado o estado final.
 * 
 * 
 * Constante:  len
 * ---------------
 * Comprimento da cauda de DNA.
 * 
 * 
 * Sub-função:  check
 * ------------------
 * Invoca a função 'jump' para alcançar os próximos estados e verifica se um
 * deles é o estado final, 1, o que indica que foi encontrada uma subexpressão
 * de s que é reconhecida pelo autómato a.
 * 
 * Para tal ordena os estados recebidos e purga os elementos repetidos que possam
 * ter sobrado recorrendo à função 'unique'.
 * 
 * De seguida é analisado com a função List.mem se um dos novos estados é o
 * estado final 1.
 * 
 * Em caso afirmativo, é devolvido TRUE.
 * Em caso negativo, verifica com o próximo caracter da string.
 * 
 * Este processo implementa o Algoritmo de Thompson, o qual é linear, O(n).
 * 
 * 
 * Sub-função:  jump
 * -----------------
 * Faz o salto automático pelos vários estados Ɛ a partir do estado i sabendo
 * que o caracter c provocará a próxima transição, se possível.
 * Recorre a uma função auxiliar interna 'inner'.
 * 
 * A função 'inner' mantém memória dos estados já visitados através do parâmetro v.
 * 
 * É feito um mapeamento para a lista de transições de a.(i), i.e., o estado i
 * do autómato a.
 * 
 * Caso a transição seja válida (i.e., a transição é provocada pelo caracter ch),
 * então alcançamos um novo estado intermédio, o qual é devolvido.
 * 
 * Caso a transição seja Ɛ e o estado já tenha sido visitado, é igualmente
 * armazenado, se não transita para o próximo estado.
 * 
 * Se o estado for 1, então é final e é imediatamente devolvido k (= 1).
 *)
let search_pattern (a : automata) (s : string) =
  let jump (ch : char) (i : int) =
    let rec inner (i : int) (v : int list) =
      List.concat (List.map (
        fun (k, l) ->
          match l with
          | None    -> []
          | Epsilon -> if k <> 1 then (if not (List.mem k v) then inner k (k :: v) else [k]) else [k]
          | Char c  -> if c = ch then [k] else []
      ) a.(i))
    in inner i []
  in
  let len = String.length s in
  let res = ref [0] in
  let rec check i =
    if i < len then (
      res := unique (List.sort (-) (List.concat (List.map (jump s.[i]) !res)));
      if List.mem 1 !res then true else check (i + 1)
    ) else false
  in check 0


(* BLOCO PRINCIPAL (main do programa)
 * ---------------
 * 1. Lê 'r', a string com a expressão regular.
 * 2. Obtém 'rex', a expressão regular, a partir de 'r'.
 * 3 Simplifica a expressão regular usando as identidades.
 * 4. Lê 'dna', a cauda de DNA a verificar.
 * 5. Constrói o autómato correspondente a 'sre'.
 * 6. Determina se existe um padrão e armazena em 'result'.
 * 7. Imprime o resultado sob a forma de YES ou NO.
 * 
 * As linhas comentadas remontam à fase de debugging durante a implementação
 * dos algoritmos. Foram igualmente úteis para obter uma representação do
 * autómato construído para escrever a secção "Exemplo de execução".
 *)
let () =
  let r   = read_line () in
  let rex = regexp r in
  let sre = simplify rex in
  let dna = read_line () in
  let aut = automata_of_regexp sre in
  let result = search_pattern aut dna in
    Printf.printf "%s\n" (if result then "YES" else "NO")


(* BIBLIOGRAFIA
 * ------------
 * -> Aulas teóricas e práticas relevantes do professor regente.
 * -> https://deniskyashif.com/2019/02/17/implementing-a-regular-expression-engine/
 *    Em particular a secção "Thompson’s Construction"
 *    [Consultado a 28/05/2020]
 *)


(* EXEMPLO DE EXECUÇÃO
 * -------------------
 * Assumindo que a expressão regular é obtida pela função 'regexp', a qual foi fornecida.
 * 
 * Façamos um exemplo simples com a expressão regular "(A+T)*GC".
 * 
 * O output em "modo debug" (i.e., com os prints sem comentário) será o seguinte:
 * 
 *    regex: (A+T)*GC
 *    regex: ((A + T)* . (G . C))
 *    Input: ACD (3)
 *    
 *     0:     [( 2, epsilon); ( 3, epsilon); ]
 *     1:     []
 *     2:     [( 9, 'G'); ]
 *     3:     [( 5, epsilon); ( 6, epsilon); ]
 *     4:     [( 3, epsilon); ( 2, epsilon); ]
 *     5:     [( 7, 'A'); ]
 *     6:     [( 8, 'T'); ]
 *     7:     [( 4, epsilon); ]
 *     8:     [( 4, epsilon); ]
 *     9:     [( 1, 'C'); ]
 * 
 * Vamos entender como o algoritmo chegou a este resultado.
 * 
 * A construção do autómato começa com o autómato init_automata:
 * 
 *   (0) --- Ɛ ---> (1)
 * 
 *     0:     [( 1, epsilon); ]
 *     1:     []
 * 
 * Inicialmente é dado um produto do tipo X.Y (onde X = (A + T)* e Y = (G . C)),
 * pelo que é criado 1 nó:
 * 
 *   (0) --- [X] ---> (2) --- [Y] ---> (1)
 * 
 *     0:     [( 1, epsilon); ]
 *     1:     []
 *     2:     []
 * 
 * Entre os nós 0 e 2 será construída a parte do autómato referente a X, e entre
 * 2 e 1 a parte referente a Y.
 * O algoritmo faz a construção da esquerda para a direita, pelo que começa com X.
 * 
 * Sendo X = (A + T)*, estamos perante uma regex do tipo Z*. São criados, portanto,
 * 2 nós, ficando o autómato com este aspecto:
 * 
 *                     /---- Ɛ -----\
 *                    V              \
 *   (0) --- Ɛ ---> (3) --- [Z] ---> (4) --- Ɛ ---> (2) --- [Y] ---> (1)
 *     \                                            ^
 *      \------------------- Ɛ --------------------/
 * 
 * Neste ponto, o array terá o seguinte conteúdo:
 * 
 *     0:     [( 2, epsilon); ( 3, epsilon); ]
 *     1:     []
 *     2:     []
 *     3:     [( 5, epsilon); ( 6, epsilon); ]
 *     4:     [( 3, epsilon); ( 2, epsilon); ]
 * 
 * Sendo Z = A + T, então são criados mais 4 nós:
 * 
 *                     /------------------ Ɛ --------------------\
 *                    /                                           \
 *                   / /--- Ɛ ---> (5) --- [W] ---> (7) --- Ɛ ---\ \
 *                  V /                                          V \
 *   (0) --- Ɛ ---> (3)                                          (4) --- Ɛ ---> (2) --- [Y] ---> (1)
 *     \              \                                          ^              ^
 *      \              \--- Ɛ ---> (6) --- [K] ---> (8) --- Ɛ ---/              /
 *       \                                                                     /
 *        \------------------------------- Ɛ ---------------------------------/
 * 
 *     0:     [( 2, epsilon); ( 3, epsilon); ]
 *     1:     []
 *     2:     []
 *     3:     [( 5, epsilon); ( 6, epsilon); ]
 *     4:     [( 3, epsilon); ( 2, epsilon); ]
 *     5:     []
 *     6:     []
 *     7:     [( 4, epsilon); ]
 *     8:     [( 4, epsilon); ]
 * 
 * Uma vez que W = A e K = T, ou seja, caracteres, é a condição final da chamada recursiva
 * e o autómato ganha o seguinte aspecto:
 * 
 *                     /------------------ Ɛ ------------------\
 *                    /                                         \
 *                   / /--- Ɛ ---> (5) --- A ---> (7) --- Ɛ ---\ \
 *                  V /                                        V \
 *   (0) --- Ɛ ---> (3)                                        (4) --- Ɛ ---> (2) --- [Y] ---> (1)
 *     \              \                                        ^              ^
 *      \              \--- Ɛ ---> (6) --- T ---> (8) --- Ɛ ---/              /
 *       \                                                                   /
 *        \------------------------------- Ɛ -------------------------------/
 * 
 *     0:     [( 2, epsilon); ( 3, epsilon); ]
 *     1:     []
 *     2:     []
 *     3:     [( 5, epsilon); ( 6, epsilon); ]
 *     4:     [( 3, epsilon); ( 2, epsilon); ]
 *     5:     [( 7, 'A'); ]
 *     6:     [( 8, 'T'); ]
 *     7:     [( 4, epsilon); ]
 *     8:     [( 4, epsilon); ]
 * 
 * A chamada recursiva do membro esquerdo de X.Y termina, passando a ser tratado por
 * fim o membro direito, Y = G . C.
 * Sendo de novo do tipo W.Z, é criado um novo nó entre 2 e 1:
 * 
 *                     /------------------ Ɛ ------------------\
 *                    /                                         \
 *                   / /--- Ɛ ---> (5) --- A ---> (7) --- Ɛ ---\ \
 *                  V /                                        V \
 *   (0) --- Ɛ ---> (3)                                        (4) --- Ɛ ---> (2) --- [W] ---> (9) --- [Z] ---> (1)
 *     \              \                                        ^              ^
 *      \              \--- Ɛ ---> (6) --- T ---> (8) --- Ɛ ---/              /
 *       \                                                                   /
 *        \------------------------------- Ɛ -------------------------------/
 * 
 *     0:     [( 2, epsilon); ( 3, epsilon); ]
 *     1:     []
 *     2:     []
 *     3:     [( 5, epsilon); ( 6, epsilon); ]
 *     4:     [( 3, epsilon); ( 2, epsilon); ]
 *     5:     [( 7, 'A'); ]
 *     6:     [( 8, 'T'); ]
 *     7:     [( 4, epsilon); ]
 *     8:     [( 4, epsilon); ]
 *     9:     []
 * 
 * W e Z são tratados individualmente e da esquerda para a direita, mas sendo ambos
 * caracteres, vamos simplificar e substituir aqui directamente num passo só:
 * 
 *                     /------------------ Ɛ ------------------\
 *                    /                                         \
 *                   / /--- Ɛ ---> (5) --- A ---> (7) --- Ɛ ---\ \
 *                  V /                                        V \
 *   (0) --- Ɛ ---> (3)                                        (4) --- Ɛ ---> (2) --- G ---> (9) --- C ---> (1)
 *     \              \                                        ^              ^
 *      \              \--- Ɛ ---> (6) --- T ---> (8) --- Ɛ ---/              /
 *       \                                                                   /
 *        \------------------------------- Ɛ -------------------------------/
 * 
 * Os estados 2 e 9 são os actualizados neste passo:
 * 
 *     0:     [( 2, epsilon); ( 3, epsilon); ]
 *     1:     []
 *     2:     [( 9, 'G'); ]
 *     3:     [( 5, epsilon); ( 6, epsilon); ]
 *     4:     [( 3, epsilon); ( 2, epsilon); ]
 *     5:     [( 7, 'A'); ]
 *     6:     [( 8, 'T'); ]
 *     7:     [( 4, epsilon); ]
 *     8:     [( 4, epsilon); ]
 *     9:     [( 1, 'C'); ]
 * 
 * Por fim são adicionadas as transições ∑* aos estados inicial (0) e final (1).
 * 
 *     0:     [( 2, epsilon); ( 3, epsilon); ( 0, 'A'); ( 0, 'T'); ( 0, 'G'); ( 0, 'C'); ]
 *     1:     [( 1, 'A'); ( 1, 'T'); ( 1, 'G'); ( 1, 'C'); ]
 * 
 * E termina assim a construção do autómato.
 * 
 * Vamos agora percorrê-lo com a sequência de DNA "AGCT". Este exemplo com este
 * autómato será bastante simples.
 * 
 * O primeiro nucleotídeo a analisar é o 'A', no índice 0. 
 * 
 * O autómato entra no estado 0:
 * 
 * --> 0:     [( 2, epsilon); ( 3, epsilon); ( 0, 'A'); ( 0, 'T'); ( 0, 'G'); ( 0, 'C'); ]
 *     1:     [( 1, 'A'); ( 1, 'T'); ( 1, 'G'); ( 1, 'C'); ]
 *     2:     [( 9, 'G'); ]
 *     3:     [( 5, epsilon); ( 6, epsilon); ]
 *     4:     [( 3, epsilon); ( 2, epsilon); ]
 *     5:     [( 7, 'A'); ]
 *     6:     [( 8, 'T'); ]
 *     7:     [( 4, epsilon); ]
 *     8:     [( 4, epsilon); ]
 *     9:     [( 1, 'C'); ]
 * 
 * Saltam-se os estados Ɛ e procuram-se transições válidas, i.e., que sejam provocadas
 * pelo caracter 'A'.
 * Os próximos estados são 2 e 3, ambos Ɛ.
 * 
 *     2:     [( 9, 'G'); ]
 * 
 * O estado 2 transita para o estado 9 com o caracter 'G', o qual não é 'A'. Logo,
 * é descartado.
 * 
 * O estado 3 transita para os estados 5 e 6, também ambos Ɛ.
 * 
 *     3:     [( 5, epsilon); ( 6, epsilon); ]
 * 
 * O estado 6 transita para 8 com o caracter 'T', sendo portanto descartado.
 * 
 *     6:     [( 8, 'T'); ]
 * 
 * Já o estado 5 transita para o 7 com 'A', sendo então memorizado.
 * 
 *     5:     [( 7, 'A'); ]
 * 
 * Naturalmente, a transição ∑* é sempre válida, pelo que o estado inicial estará
 * sempre presente na lista de estados actuais.
 * 
 * Assim sendo, os estados actuais são [0; 7] e o próximo caracter é 'G'.
 * 
 * --> 0:     [( 2, epsilon); ( 3, epsilon); ( 0, 'A'); ( 0, 'T'); ( 0, 'G'); ( 0, 'C'); ]
 *     1:     [( 1, 'A'); ( 1, 'T'); ( 1, 'G'); ( 1, 'C'); ]
 *     2:     [( 9, 'G'); ]
 *     3:     [( 5, epsilon); ( 6, epsilon); ]
 *     4:     [( 3, epsilon); ( 2, epsilon); ]
 *     5:     [( 7, 'A'); ]
 *     6:     [( 8, 'T'); ]
 * --> 7:     [( 4, epsilon); ]
 *     8:     [( 4, epsilon); ]
 *     9:     [( 1, 'C'); ]
 * 
 * O processo é feito para ambos os estados, resumidamente:
 * 
 *   0 --+-- ∑* --> (0) [OK]
 *       |
 *       +-- Ɛ ---> 2 -- G --> (9) [OK]
 *       |
 *       +-- Ɛ ---> 3 --+-- Ɛ --> 5 -- A --X 7
 *                      |
 *                      +-- Ɛ --> 6 -- T --X 8
 * 
 *   7 -- Ɛ --> 4 --+-- Ɛ --> 2 -- G --> (9) [OK]
 *                  |
 *                  +-- Ɛ --> 3 --+-- Ɛ --> 5 -- A --X 7
 *                                |
 *                                +-- Ɛ --> 6 -- T --X 8
 * 
 * Os estados actuais passam então a ser [0; 9].
 * 
 * --> 0:     [( 2, epsilon); ( 3, epsilon); ( 0, 'A'); ( 0, 'T'); ( 0, 'G'); ( 0, 'C'); ]
 *     1:     [( 1, 'A'); ( 1, 'T'); ( 1, 'G'); ( 1, 'C'); ]
 *     2:     [( 9, 'G'); ]
 *     3:     [( 5, epsilon); ( 6, epsilon); ]
 *     4:     [( 3, epsilon); ( 2, epsilon); ]
 *     5:     [( 7, 'A'); ]
 *     6:     [( 8, 'T'); ]
 *     7:     [( 4, epsilon); ]
 *     8:     [( 4, epsilon); ]
 * --> 9:     [( 1, 'C'); ]
 * 
 * Sendo o próximo caracter 'C', o processo repete-se:
 * 
 * 0 --+-- ∑* --> (0) [OK]
 *       |
 *       +-- Ɛ ---> 2 -- G --X 9
 *       |
 *       +-- Ɛ ---> 3 --+-- Ɛ --> 5 -- A --X 7
 *                      |
 *                      +-- Ɛ --> 6 -- T --X 8
 * 
 * 9 -- C --> (1) [OK]
 * 
 * Os estados actuais são [0; 1].
 * 
 * Um dos estados é 1! Isto significa que atingimos o estado final e detectámos
 * uma subsequência reconhecida pela regex (em particular, "AGC").
 * 
 * O algoritmo é então interrompido e devolve TRUE.
 * 
 * Se, por exemplo, a cauda de DNA fosse apenas "AG", teríamos chegado ao
 * estado 9, mas o índice 2 da string é out of bounds, pelo que seria retornado
 * FALSE pois não havia sido possível alcançar a um estado final por falta de
 * nucleotídeos que satisfizessem a expressão regular.
 *)
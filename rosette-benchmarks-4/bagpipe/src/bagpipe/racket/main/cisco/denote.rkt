#lang s-exp rosette

(require "../util/util.rkt")
(require "../network/network.rkt")
(require "../util/extraction-rosette.rkt")

(provide (all-defined-out))

; Following is a good reference for policy syntax and semantics
; http://www.cisco.com/c/en/us/td/docs/routers/asr9000/software/asr9k_r4-2/routing/configuration/guide/b_routing_cg42asr9k/b_routing_cg42asr9k_chapter_0110.html

; UNINTUITIVE PARTS OF THE SEMANTICS

; A policy does not modify route attribute values until all tests have
; been completed. In other words, comparison operators always run on the
; initial data in the route. Intermediate modifications of the route
; attributes do not have a cascading effect on the evaluation of the
; policy.

; The drop statement indicates that the action to take is to discard the
; route. When a route is dropped, no further execution of policy
; occurs. For example, if after executing the first two statements of a
; policy the drop statement is encountered, the policy stops and the
; route is discarded.

; A route is dropped at the end of policy processing unless either the
; policy modifies a route attribute or it passes the route by means of
; an explicit pass statement.

(define (denote-policy kind as r n a)
  (define r* (as-lookup-router as r))
  (define n* (as-lookup-neighbor r* n))
  (define policy (record-field 'Neighbor kind n*))
  (define stmts (record-data 'Inlined policy))
  (define res (denote-stmts stmts a (unmodified)))
  (if (or (unmodified? res) (dropped? res)) #f res))

(define (denote-stmts stmts a0 a)
  (if (null? stmts) a
    (let* ([a* (denote-stmt (car stmts) a0 a)])
      (if (dropped? a*) a* (denote-stmts (cdr stmts) a0 a*)))))

(define (denote-stmt stmt a0 a)
  (match stmt
    ((IfThenElse body) (ite (first body) (second body) a0 a))
    ((Drop _) (dropped))
    ((Pass _) (modify identity a0 a))
    ((SetCommunity cs) (modify (curry set-communities cs #t) a0 a))
    ((DeleteCommunityIn cs) (modify (curry set-communities cs #f) a0 a))
    ((SetLocalPref n) (modify (curry set-local-pref n) a0 a))
    ((SetMed n) (modify (curry set-med n) a0 a))
    ((SetMedIGP) (modify (curry set-med (symbolic-med)) a0 a))
    ((Unsupported _) a)))

(define (denote-expression expr a0)
  (match expr
    ((Not e) (not (denote-expression e a0)))
    ((InAsPath ps) (in-as-path ps a0))
    ((InDestination ps) (in-destination ps a0))
    ((CommunityMatchesAny cs) (in-community cs a0))))

(define (set-communities cs b a)
  (if (null? cs) a
    (let* ([c  (symbolize (record-data 'Reference (car cs)))]
           [a* (announcement-community-set a c b)])
      (set-communities (cdr cs) b a*))))

(define (set-med n a)
  (announcement-med-set a n))

(define (set-local-pref n a)
  (announcement-pref-set a n))

(define (in-as-path paths a)
  (if (null? paths) #f
    (let* ([c (symbolize (record-data 'Reference (car paths)))])
      (or (announcement-aspath-test a c)
          (in-as-path (cdr paths) a)))))

(define (in-community communities a)
  (if (null? communities) #f
    (let* ([c (symbolize (record-data 'Reference (car communities)))])
      (or (announcement-community-test a c)
          (in-community (cdr communities) a)))))

(define (in-destination prefixes a)
  (if (null? prefixes) #f
    (let* ([bps (record-data 'Inlined (car prefixes))]
           [p (announcement-prefix a)])
      (or (ormap (curry matches-bound-prefix p) bps)
          (in-destination (cdr prefixes) a)))))

; ('IfThenElse (IFS ELS))
; IFS = (IF0 IF1 ...)
; IF = (EXPR STMTS)
; ELS = STMTS
(define (ite ifs els a0 a)
  (if (null? ifs) (denote-stmts els a0 a)
    (let* ([expr (first (car ifs))]
           [smts (second (car ifs))]
           [ifs* (cdr ifs)])
      (if (denote-expression expr a0)
        (denote-stmts smts a0 a)
        (ite ifs* els a0 a)))))

(define (matches-bound-prefix p* bp)
  (define p (to-prefix (first (record-data 'BoundPrefix bp))))
  (if (not p) #f
    (let* ([lowerBound (second (record-data 'BoundPrefix bp))]
           [upperBound (third (record-data 'BoundPrefix bp))]
           [l (prefix-length p)]
           [l* (prefix-length p*)])
      (and (<= lowerBound l*) (>= upperBound l*)
        (rosette-eq? (take (ip-bits (prefix-ip p*)) l) 
                     (take (ip-bits (prefix-ip p )) l))))))

(define (to-ipv4 i)
  (if (not (ipv4? i)) #f
    (let* ([a (first (record-data 'IPV4 i))]
           [b (second (record-data 'IPV4 i))]
           [c (third (record-data 'IPV4 i))]
           [d (fourth (record-data 'IPV4 i))])
      (ip a b c d))))

(define (to-prefix p)
  (define i (to-ipv4 (first (record-data 'Prefix p))))
  (define l (second (record-data 'Prefix p)))
  (and i (prefix i l)))

(define (ipv4? ip) (rosette-eq? 'IPV4 (first ip)))

(define (as-lookup-router as ip)
  (findf [lambda (r)
    (rosette-eq? ip (to-ipv4 (record-field 'Router '_routerIP r)))
  ] (record-field 'Config '_routers as)))

(define (as-lookup-neighbor r ip)
  (findf [lambda (n)
    (rosette-eq? ip (to-ipv4 (record-field 'Neighbor '_neighborIP n)))
  ] (record-field 'Router '_neighbors r)))

(define (dropped) 'dropped)
(define (dropped? a) (rosette-eq? 'dropped a))

(define (unmodified) 'unmodified)
(define (unmodified? a) (rosette-eq? 'unmodified a))

(define (modify f a0 a)
  (if (unmodified? a) (f a0) (f a)))

; the layout of a dict is `((key value) (key* value*) ...)
(define (dict-lookup key dict)
  (second (findf [lambda (entry) (rosette-eq? key (first entry))] dict)))

; the layout of a record is `(name data)
(define (record-data name record)
  (if (rosette-eq? (first record) name)
    (second record)
    undefined))

(define (record-field name field record)
  (dict-lookup field (record-data name record)))

(define (symbolize s)
  (if (string? s) (string->symbol s) s))

#lang s-exp rosette

(require "parser.rkt")
(require "denote.rkt")
(require "../util/util.rkt")
(require "../network/network.rkt")

(provide cache cache? cache-as cache-internal-routers cache-router-external-neighbors)

(define (cache as) `(Cache ,as ,(internal as) ,(external as)))
(define (cache? c) (and (pair? c) (rosette-eq? 'Cache (first c))))
(define (cache-as c) (second c))
(define (cache-internal-routers c) (third c))
(define (cache-router-external-neighbors c r)
  (cdr (findf [lambda (e)
    (rosette-eq? r (car e))
  ] (fourth c))))
 
(define (internal as)
  (map [lambda (r)
    (to-ipv4 (record-field 'Router '_routerIP r))
  ] (record-field 'Config '_routers as)))

(define (external as)
  (map [lambda (r)
    (define asn (record-field 'Router '_asn r))
    (define ns (filter [lambda (n)
      (not (rosette-eq? asn (record-field 'Neighbor '_neighborAsn n)))
    ] (record-field 'Router '_neighbors r)))
    (define nIPs (map to-ipv4 (filter ipv4? (map (curry record-field 'Neighbor '_neighborIP) ns))))
    (define rIP (to-ipv4 (record-field 'Router '_routerIP r)))
    (cons rIP nIPs)
  ] (record-field 'Config '_routers as)))

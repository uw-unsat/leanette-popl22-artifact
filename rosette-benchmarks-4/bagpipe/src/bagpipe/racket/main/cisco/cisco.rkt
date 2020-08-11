#lang s-exp rosette

(require "parser.rkt")
(require "denote.rkt")
(require "cache.rkt")
(require "../util/util.rkt")
(require "../network/network.rkt")

(provide as-from-configs as-denote-import as-denote-export
         as-internal-routers as-router-external-neighbors as-environment)

(define (as-from-configs configs)
  (cache (cisco->sexp configs)))

(define (as-denote-import as r i a)
  (denote-policy '_importPolicy (cache-as as) r i a))

(define (as-denote-export as r o a)
  (denote-policy '_exportPolicy (cache-as as) r o a))

(define (as-environment as)
  (define communities (map (compose symbolize first) (record-field 'Config '_communitySets (cache-as as))))
  (define paths (map (compose symbolize first) (record-field 'Config '_asPathSets (cache-as as))))
  (environment communities paths))

(define (as-internal-routers as) (cache-internal-routers as))

(define (as-router-external-neighbors as r) (cache-router-external-neighbors as r))

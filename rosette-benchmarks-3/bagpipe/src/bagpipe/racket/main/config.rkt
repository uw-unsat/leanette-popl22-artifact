#lang s-exp rosette

(current-bitwidth 10)

(require "util/util.rkt")
(require "network/network.rkt")
(require (prefix-in juniper- "juniper/juniper.rkt"))
(require (prefix-in cisco- "cisco/cisco.rkt"))

(provide as-from-configs as-denote-import as-denote-export
         as-internal-routers as-router-external-neighbors as-environment)

; this interface provides a couple of opaque types
; as: represents an entire as, including router topology and configs
; router: represents a router

(define (dispatch as j c)
  (case (car as) 
    [(juniper) (curry j (cdr as))]
    [(cisco)   (curry c (cdr as))]))

; create an as from a config written in a certain language
(define (as-from-configs lang configs)
  (cons lang (case lang
    [(juniper) (juniper-as-from-configs configs)]
    [(cisco) (cisco-as-from-configs configs)])))

; takes an as, two routers, a prefix, and an announcement
; returns a modified annoucement or #f if dropped
(define (as-denote-import as r i a)
  ((dispatch as juniper-as-denote-import cisco-as-denote-import) r i a))

; takes an as, two routers, a prefix, and an announcement
; returns a modified annoucement or #f if dropped
(define (as-denote-export as r o a)
  ((dispatch as juniper-as-denote-export cisco-as-denote-export) r o a))

; takes an as, returns an environment
(define (as-environment as)
  (dispatch as juniper-as-environment cisco-as-environment))

; takes an as, returns a list of routers
(define (as-internal-routers as) 
  (dispatch as juniper-as-internal-routers cisco-as-internal-routers))

; takes an as and router, returns a list of routers
(define (as-router-external-neighbors as r)
  ((dispatch as juniper-as-router-external-neighbors cisco-as-router-external-neighbors) r))

#lang s-exp rosette

(require "../util/util.rkt")
(require "ip.rkt")
(require "prefix.rkt")

(provide default-announcement announcement?
         announcement-prefix announcement-prefix-set
         announcement-community-test announcement-community-set
         announcement-aspath-test announcement-aspath-set
         announcement-pref announcement-pref-set announcement-pref-update
         announcement-med-set announcement-nexthop-set
         environment environment-merge
         count-aspaths count-communities
         environment-aspaths environment-communities
         symbolic-announcement symbolic-med
         tracked-announcement
         current original path 
         available? not-available)

(define (announcement communities prefix aspath pref med nexthop) 
  `(Announcement ,communities ,prefix ,aspath ,pref ,med ,nexthop))
(define (announcement? a) (and (pair? a) (rosette-eq? (first a) 'Announcement)))
(define (announcement-communities a) (second a))
(define (announcement-prefix a) (third a))
(define (announcement-aspath a) (fourth a))
(define (announcement-pref a) (fifth a))
(define (announcement-med a) (sixth a))
(define (announcement-nexthop a) (seventh a))

(define (announcement-aspath-set a p b)
  (announcement (announcement-communities a)
                (announcement-prefix a)
                (subset-set (announcement-aspath a) p b)
                (announcement-pref a)
                (announcement-med a)
                (announcement-nexthop a)))

(define (announcement-aspath-test a p)
  (subset-ref (announcement-aspath a) p))

(define (announcement-community-set a c b)
  (announcement (subset-set (announcement-communities a) c b) 
                (announcement-prefix a) 
                (announcement-aspath a)
                (announcement-pref a)
                (announcement-med a)
                (announcement-nexthop a)))

(define (announcement-community-test a c)
  (subset-ref (announcement-communities a) c))

(define (announcement-prefix-set a prefix)
  (announcement (announcement-communities a)
                prefix
                (announcement-aspath a)
                (announcement-pref a)
                (announcement-med a)
                (announcement-nexthop a)))

(define (announcement-pref-set a pref)
  (announcement (announcement-communities a)
                (announcement-prefix a) 
                (announcement-aspath a)
                pref
                (announcement-med a)
                (announcement-nexthop a)))

(define (announcement-pref-update a f)
  (announcement (announcement-communities a)
                (announcement-prefix a) 
                (announcement-aspath a)
                (f (announcement-pref a))
                (announcement-med a)
                (announcement-nexthop a)))

(define (announcement-med-set a med)
  (announcement (announcement-communities a)
                (announcement-prefix a) 
                (announcement-aspath a)
                (announcement-pref a)
                med
                (announcement-nexthop a)))

(define (announcement-nexthop-set a nexthop)
  (announcement (announcement-communities a)
                (announcement-prefix a) 
                (announcement-aspath a)
                (announcement-pref a)
                (announcement-med a)
                nexthop))

(define (environment communities aspaths) `(Environment ,communities ,aspaths))
(define (environment? c) (and (pair? c) (rosette-eq? 'Environment (first c))))
(define (environment-communities c) (second c))
(define (environment-aspaths c) (third c))

(define (count-communities env)
  (length (environment-communities env)))

(define (count-aspaths env)
  (length (environment-aspaths env)))

(define (environment-merge es)
  (environment (remove-duplicates (flatten (map environment-communities es)))
               (remove-duplicates (flatten (map environment-aspaths es)))))

(define (default-announcement prefix env)
  (announcement
    (subset (environment-communities env))
    prefix
    (subset (environment-aspaths env))
    200
    0
    (ip 0 0 0 0)))

(define (symbolic-communities env)
  (symbolic-subset (environment-communities env)))

(define (symbolic-aspath env)
  (symbolic-subset (environment-aspaths env)))

(define (symbolic-med)
  (define-symbolic* med integer?)
  med)

(define (symbolic-announcement env)
  (define prefix (symbolic-prefix))
  (define comms (symbolic-communities env))
  (define aspath (symbolic-aspath env))
  (define med (symbolic-med))
  (define nexthop (symbolic-ip))
  (announcement comms prefix aspath 100 med nexthop))

(define (tracked-announcement a0 a path) 
  `(TrackedAnnouncement ,a0 ,a ,path))
(define (not-available)
  `(NotAvailable))

(define (original c) (second c))
(define (current c) (third c))
(define (path c) (fourth c))
(define (available? c) (not (rosette-eq? c `(NotAvailable))))

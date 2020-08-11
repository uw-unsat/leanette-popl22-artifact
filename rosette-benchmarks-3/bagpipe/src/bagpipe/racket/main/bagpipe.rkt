#lang racket

(require "util/util.rkt")
(require "util/extraction-racket.rkt")
(require "network/network.rkt")
(require "config.rkt")
(require "setup.rkt")
(require "bgpv.rkt")

(provide verify verify? help)

(define (format-ip ip)
  (string-join (list
    (~a (bits->number (take (drop (ip-bits ip)  0) 8)))
    (~a (bits->number (take (drop (ip-bits ip)  8) 8)))
    (~a (bits->number (take (drop (ip-bits ip) 16) 8)))
    (~a (bits->number (take (drop (ip-bits ip) 24) 8)))
  ) "."))

(define (center-ip ip)
  (~a (format-ip ip) #:align 'center #:min-width 15))

(define (format-cidr cidr)
  (match cidr ((Prefix ip len) (string-append (format-ip ip) "/" (~a len)))))

(define (format-list l)
  (string-append "[" (string-join l ", ") "]"))

(define (format-subset s)
  (format-list (map ~a (subset->list s))))

(define (format-announcement a)
  (if (rosette-eq? a 'not-available) 
    "not-available"
    (match a ((Announcement coms p path pref med nexthop)
      (string-append "{ pref: " (~a pref) 
                     ", coms: " (format-subset coms) 
                     ", path: " (format-subset path) 
                     ", nhop: " (format-ip nexthop) 
                     ", med:  " (~a med)
                     "}")))))

(define (format-path-yaml path)
  (format-list (map format-ip path)))
 
(define (format-path suffix path)
  (if (or (empty? path) (empty? (cdr path)))
    (list
      (string-append "                             ")
      (string-append "                                ")
      (string-append "                                ")
      (string-append "                                |  ")
      (string-append "                                "))
  (if (empty? (cddr path))
    (list
      (string-append (center-ip (cadr path)) "              ")
      (string-append "    ______                      ")
      (string-append "   |      |                     ")
      (string-append "   | a0" suffix " -|---------------------|->")
      (string-append "   |______|                     "))
    (list
      (string-append (center-ip (caddr path)) "              ")
      (string-append "    ______                      ")
      (string-append "   |      |    " (center-ip (cadr path)) "  ")
      (string-append "   | a0" suffix " -|--------->[]---------|->")
      (string-append "   |______|                     ")))))

(define (format-counter-example r i o p ai0 aip ai0* aip* ai ai* al al* ae)
  (define s (append (list "                                ")
                    (format-path "*" aip*) 
                    (list "                                ")
                    (format-path " " aip )))
  (define t (list
    (string-append    "     " (center-ip r))
    (string-append "    ___________________ ")
    (string-append    "| in   . loc  . out |")
    (string-append    "|      .      .     |")
    (string-append       " ai* -> al*.     |")
    (string-append    "|      .   |  .     |")
    (string-append    "|      .   |  .     |  " (center-ip o))
    (string-append "   |      .   '--> ae -|------->[]")
    (string-append    "|      .      .     |")
    (string-append    "|      .      .     |")
    (string-append       " ai  -> al .     |")
    (string-append    "|______.______._____|")))
  (define st (map string-append s t))
  (define u (list
    (string-append "")
    (string-append "p   = " (format-cidr p))
    (string-append "a0  = " (format-announcement ai0))
    (string-append "a0* = " (format-announcement ai0*))
    (string-append "ai  = " (format-announcement ai))
    (string-append "ai* = " (format-announcement ai*))
    (string-append "al  = " (format-announcement al))
    (string-append "al* = " (format-announcement al*))
    (string-append "ae  = " (format-announcement ae))))
  (string-join (append st u) "\n"))

(define (format-counter-example-yaml r i o p ai0 aip ai0* aip* ai ai* al al* ae)
  (string-join (list
    (string-append "- r: " (format-ip r))
    (string-append "  o: " (format-ip o))
    (string-append "  aip:  " (format-path-yaml aip))
    (string-append "  aip*: " (format-path-yaml aip*))
    (string-append "  p: " (format-cidr p))
    (string-append "  a0:  " (format-announcement ai0))
    (string-append "  a0*: " (format-announcement ai0*))
    (string-append "  ai:  " (format-announcement ai))
    (string-append "  ai*: " (format-announcement ai*))
    (string-append "  al:  " (format-announcement al))
    (string-append "  al*: " (format-announcement al*))
    (string-append "  ae:  " (format-announcement ae))) "\n"))

(define (path->list path)
  (match path 
    ((Start r) (match r ((ExistT rt r) 
      (list r))))
    ((Hop _ r rc path) (match r ((ExistT rt r)
      (cons r (path->list path)))))))

(define (unpack-tracking a f)
  (match a
    ((NotAvailable)
      (f 'not-available 'not-available '()))
    ((Available a)
      (match a 
        ((Build_Tracking a0 a path) 
          (f a0 a (path->list path)))))))

(define (unpack-incoming i f)
  (match i 
    ((Injected) (f 'injected))
    ((Received i)
      (match i ((ExistT record ic)   ; connection
      (match record ((ExistT it i)   ; router  type
        (f i))))))))

(define (unpack-counter-example record f)
  ; unpack tuple
  (match record ((ExistT r record)
  (match record ((Pair record ae)
  (match record ((Pair record al*)
  (match record ((Pair record al)
  (match record ((Pair record ai*)
  (match record ((Pair record ai)
  (match record ((Pair record p)
  (match record ((Pair i o)
  ; unpack o
  (match o ((ExistT record oc)   ; connection 
  (match record ((ExistT ot o)   ; router type
  ; unpack i
  (unpack-incoming i (lambda (i)
  ; unpack tracking
  (unpack-tracking ai  (lambda (ai0  ai  aip )
  (unpack-tracking ai* (lambda (ai0* ai* aip*)
  (unpack-tracking al  (lambda (al0  al  alp )
  (unpack-tracking al* (lambda (al0* al* alp*)
  (unpack-tracking ae  (lambda (ae0  ae  aep )
    (f r i o p ai0 aip ai0* aip* ai ai* al al* ae))))))))))))))))))))))))))))))))))

(define (mapCoqList f l)
  (match l
    ((Cons h t) `(Cons ,(f h) ,(mapCoqList f t)))
    ((Nil) '(Nil))))

(define (verify args)
  (define as (load-as args))
  (write-string "done loading as\n") (flush-output)
  (define prop (load-prop args))
  (write-string "done loading property\n") (flush-output)
  (define driver (load-driver args))
  (write-string (string-append "done loading driver " (~a driver) "\n"))
  (define rs (as-internal-routers as))
  (write-string (string-append "checking routers: " (format-list (map format-ip rs)) "\n"))
  (for ([r rs]) 
    (define ns (as-router-external-neighbors as r))
    (write-string (string-append "  router: " (format-ip r) " has " (~a (length ns)) " external neighbors: " (format-list (map format-ip ns)) "\n")))
  (flush-output)
  (define res (@ bgpv as driver prop))
  (write-string "----- [RESULTS] -----\n")
  (mapCoqList (lambda (record) 
                (write-string (string-append 
                  (unpack-counter-example record format-counter-example-yaml) 
                  "\n"))) res)
  (write-string (match res
    ((Cons _ __) "policy does not hold")
    ((Nil) "policy holds")))
  (write-string "\n")
  (flush-output))

(define (verify? args)
  (and (>= (length args) 2)
       (equal? (first args) "verify")))

(define (help)
  (displayln #<<HELP
Usage: bagpipe COMMAND

The bagpipe commands are:
   verify SETUP ARGS     Verifies the setup in SETUP/setup.rkt. setup.rkt
                         must define two variables called `as` and a `policy`;
                         the former defines the AS that bagpipe verifies using 
                         the POLICY defined by the latter. ARGS is passed to 
                         both the AS and POLICY.

   help                  Display this help message and exit.
HELP
   ))

(module+ main
  (define cl-args (vector->list (current-command-line-arguments)))
  (cond
    [(verify? cl-args) (verify (cdr cl-args))]
    [else (help)]))

#lang racket

(require "util/list.rkt")
(require "util/rosette.rkt")
(require "util/extraction-racket.rkt")
(require (except-in "network/network.rkt" current original path))
(require "config.rkt")
(require "bgpv-core.rkt")
(require "setup.rkt")

(require racket/place)
(require racket/place/distributed)
(require racket/serialize)

(provide bgpv #;bgpv-place)

(define place-batch-size 8)
(define symbolic-batch-size 1)
(define parallel-batch-size 65536)

(define (coq-list-length l)
  (match l
    ((Nil) 0)
    ((Cons _ l*) (add1 (coq-list-length l*)))))

(define (coq-list-split-at n l)
  (if (rosette-eq? n 0)
    (cons '(Nil) l)
    (match l
      ((Nil) (cons '(Nil) l))
      ((Cons h l*) (begin
        (define split (coq-list-split-at (sub1 n) l*))
        (define lhs (car split))
        (define rhs (cdr split))
        (cons `(Cons ,h ,lhs) rhs))))))

(define (coq-list-chunks n l)
  (match l
    ((Nil) '(Nil))
    ((Cons _ __) (begin
     (define split (coq-list-split-at n l))      
     (define lhs (car split))
     (define rhs (cdr split))
     `(Cons ,lhs ,(coq-list-chunks n rhs))))))

(define (times count f) (for ([i (in-range count)]) (f)))

(define (forever f) (f) (forever f))

(define (coq-list->symbolic l)
  (match l ((Cons h l*)
  (match l* 
    ((Nil) h)
    ((Cons _ __)
      (@ symbolic-boolean (lambda (_) h) (lambda (_) (coq-list->symbolic l*)) void))))))

#|
(define (bgpv-place ch)
  (define cpu (deserialize (place-channel-get ch)))
  (define node (deserialize (place-channel-get ch)))
  (write-string (string-append "# place started at " (~a node) " on cpu " (~a cpu) "\n"))
  (flush-output)
  (define setup (deserialize (place-channel-get ch)))
  (define query (deserialize (place-channel-get ch)))
  (write-string (string-append "# place loaded setup at " (~a node) " on cpu " (~a cpu) "\n"))
  (flush-output)
  (times place-batch-size (lambda ()
    (define routings (deserialize (place-channel-get ch)))
    (define res (@ bgpvCore~ setup query (coq-list->symbolic routings)))
    (place-channel-put ch (serialize (@ optionToSpace listSpace (@ listHead res))))))
  (write-string (string-append "# place done at " (~a node) " on cpu " (~a cpu) "\n"))
  (flush-output))
  |#

(define (bgpv-place* cpu node setup query routings)
  (define res (@ bgpvCore~ setup query (coq-list->symbolic routings)))
  (@ optionToSpace listSpace (@ listHead res)))

(define (cpus)
  (with-handlers ([exn:fail? (lambda (e) (list 0))])
  (match-let ([(list out in pid err ctrl) (process "nproc")])
    (ctrl 'wait)
    (define res (read-line out))
    (close-output-port in)
    (close-input-port out)
    (close-input-port err)
    (stream->list (in-range (string->number res))))))

(define (nodes)
  (define evars (environment-variables-names (current-environment-variables)))
  (append* (list "localhost") (for/list ([evar evars])
    (define r (regexp-match #rx"^([^_]+)_NAME$" evar))
    (if r (list (string-downcase (bytes->string/utf-8 (second r)))) '()))))

(define distributed-bgpv-scheduler (lambdas (setup query routings)
  (define checks (coq-list-length routings))
  (write-string (string-append "total number of checks " (~a checks) "\n"))
  (flush-output)

  (define work-queue (make-channel))
  (define thd (current-thread))

  (define nodes* (nodes))
  (define cpus* (cpus))
  (write-string (string-append "nodes: " (~a nodes*) "\n"))
  (write-string (string-append "cpus: " (~a cpus*) "\n"))
  (flush-output)

  (define (do-work routings)
    (bgpv-place* #f #f setup query routings))
  
  #|
  ; start threads/nodes
  (for*/list ([node nodes*] [cpu cpus*])
    (thread (lambda ()
      (write-string (string-append "# node at " (~a node) " on cpu " (~a cpu) "\n"))
      (flush-output)
      (define nd (create-place-node node #:listen-port (+ 1234 cpu)))
      (forever (lambda ()
        (define ch (dynamic-place #:at nd (quote-module-path) 'bgpv-place))
        (place-channel-put ch (serialize cpu))
        (place-channel-put ch (serialize node))
        (place-channel-put ch serializedSetup)
        (place-channel-put ch serializedQuery)
        (times place-batch-size (lambda ()
          (define routings (channel-get work-queue))
          (place-channel-put ch (serialize routings))
          (define res (deserialize (place-channel-get ch)))
          (thread-send thd res))))))))
  |#

  ; provide work for threads
  (define count 0)
  (define work-to-do '())
  (@ bind listSpace 
    (coq-list-chunks parallel-batch-size routings) (lambda (sub-routings)
      (define jobs (@ bind listSpace 
        (coq-list-chunks symbolic-batch-size sub-routings) (lambda (sub-sub-routings)
          (set! count (+ count symbolic-batch-size))
          (write-string (string-append "checking " (~a count) " of " (~a checks) " at " (~a (current-seconds)) "\n"))
          (flush-output)
          (set! work-to-do (cons sub-sub-routings work-to-do))
          ;(channel-put work-queue sub-sub-routings)
          (@ single listSpace count))))

      (write-string (string-append "collecting " (~a (coq-list-length jobs)) " results\n"))
      (flush-output)

      ; collect results
      (define (do-next _)
        (define j (car work-to-do))
        (set! work-to-do (cdr work-to-do))
        (do-work j))
      (@ bind listSpace jobs do-next)))))


(define __ 'unused)


(define app (lambdas (l m)
  (match l
     ((Nil) m)
     ((Cons a l1) `(Cons ,a ,(@ app l1 m))))))
  
(define projT1 (lambda (x)
  (match x
     ((ExistT a _) a))))

(define hd_error (lambda (l)
  (match l
     ((Nil) `(None))
     ((Cons x _) `(Some ,x)))))

(define in_dec (lambdas (h a l)
  (match l
     ((Nil) `(Right))
     ((Cons y l0)
       (let ((s (@ h y a)))
         (match s
            ((Left) `(Left))
            ((Right)
              (match (@ in_dec h a l0)
                 ((Left) `(Left))
                 ((Right) `(Right))))))))))
  
(define map (lambdas (f l)
  (match l
     ((Nil) `(Nil))
     ((Cons a t) `(Cons ,(f a) ,(@ map f t))))))
  
(define concat (lambda (l)
  (match l
     ((Nil) `(Nil))
     ((Cons h t) (@ app h (concat t))))))
  
(define bindList (lambdas (l f) (concat (@ map f l))))

(define eqDecide (lambda (eqDec) eqDec))

(define eqDecSigT (lambdas (h h0 x x~)
  (match x
     ((ExistT x0 b)
       (match x~
          ((ExistT x1 b0)
            (let ((s (@ eqDecide h x0 x1)))
              (match s
                 ((Left)
                   (let ((s0 (@ eqDecide (h0 x1) b0 b)))
                     (match s0
                        ((Left) `(Left))
                        ((Right) `(Right)))))
                 ((Right) `(Right))))))))))

(define eqDecSigT~ (lambdas (h h0) (@ eqDecSigT h h0)))

(define empty (lambda (basic)
  (match basic
     ((Build_Basic _ empty0 _ _ _) (empty0 __)))))

(define single (lambdas (basic x)
  (match basic
     ((Build_Basic _ _ single0 _ _) (@ single0 __ x)))))

(define union (lambdas (basic x x0)
  (match basic
     ((Build_Basic _ _ _ union0 _) (@ union0 __ x x0)))))

(define bind (lambdas (basic x x0)
  (match basic
     ((Build_Basic _ _ _ _ bind0) (@ bind0 __ __ x x0)))))

(define full (lambdas (_ full0) full0))

(define concat0 (lambda (l)
  (match l
     ((Nil) `(Nil))
     ((Cons h t) (@ app h (concat0 t))))))
  
(define search (lambdas (_ search0 x) (@ search0 __ x)))

(define denoteListToEnsemble __)

(define listSpace `(Build_Basic ,(lambda (_) denoteListToEnsemble)
  ,(lambda (_) `(Nil)) ,(lambdas (_ a) `(Cons ,a ,`(Nil))) ,(lambdas (_ l l~)
  (@ app l l~)) ,(lambdas (_ _ s f) (concat0 (@ map f s)))))

(define listSearch (lambdas (_ l)
  (match l
     ((Nil) `(Uninhabited))
     ((Cons a _) `(Solution ,a)))))

(define enumerate (lambda (enumerable) enumerable))

(define enumerableSigT (lambdas (_ h0 _ h2)
  (@ bindList (enumerate h0) (lambda (a)
    (@ map (lambda (x) `(ExistT ,a ,x)) (enumerate (h2 a)))))))

(define enumerableEmptySet `(Nil))

(define enumerableUnit `(Cons ,`(Tt) ,`(Nil)))

(define enumerableSigT~ (lambdas (h h0 h1 h2) (@ enumerableSigT h h0 h1 h2)))

(define enumerableFull (lambda (h) (h listSpace)))

(define symbolicEmpty symbolic-void)

(define symbolicSingle (lambdas (a _) a))

(define symbolicUnion
  symbolic-boolean)

(define symbolicBind (lambdas (s f v) (@ f (s v) v)))

(define symbolicSearch (lambda  (e) (solve/evaluate/concretize e)))

(define denotationSymbolic __)

(define rosetteBasic `(Build_Basic ,(lambda (_) denotationSymbolic)
  ,(lambda (_) symbolicEmpty) ,(lambda (_) symbolicSingle) ,(lambda (_)
  symbolicUnion) ,(lambdas (_ _) symbolicBind)))

(define rosetteSearch (lambda (_) symbolicSearch))

(define original (lambdas (_ _ t)
  (match t
     ((Build_Tracking original0 _ _) original0))))

(define current (lambdas (_ _ t)
  (match t
     ((Build_Tracking _ current0 _) current0))))

(define path (lambdas (_ _ t)
  (match t
     ((Build_Tracking _ _ path0) path0))))

(define eqDecRouterType (lambdas (a a~)
  (match a
     ((Internal)
       (match a~
          ((Internal) `(Left))
          ((External) `(Right))))
     ((External)
       (match a~
          ((Internal) `(Right))
          ((External) `(Left)))))))

(define enumerableRouterType `(Cons ,`(Internal) ,`(Cons ,`(External)
  ,`(Nil))))

(define eqDecRouters (lambda (singleASTopologyClass)
  (match singleASTopologyClass
     ((Build_SingleASTopologyClass eqDecRouters0 _ _ _ _) eqDecRouters0))))

(define enumerableRouters (lambda (singleASTopologyClass)
  (match singleASTopologyClass
     ((Build_SingleASTopologyClass _ enumerableRouters0 _ _ _)
       enumerableRouters0))))

(define eqDecNeighbor (lambda (singleASTopologyClass)
  (match singleASTopologyClass
     ((Build_SingleASTopologyClass _ _ eqDecNeighbor0 _ _) eqDecNeighbor0))))

(define enumerableNeighbor (lambda (singleASTopologyClass)
  (match singleASTopologyClass
     ((Build_SingleASTopologyClass _ _ _ enumerableNeighbor0 _)
       enumerableNeighbor0))))

(define singleASInitialUninterpretedState (lambda (singleASTopologyClass)
  (match singleASTopologyClass
     ((Build_SingleASTopologyClass _ _ _ _
       singleASInitialUninterpretedState0)
       singleASInitialUninterpretedState0))))

(define singleASMode (lambdas (_ s d _)
  (match s
     ((ExistT x _)
       (match x
          ((Internal)
            (match d
               ((ExistT x0 _)
                 (match x0
                    ((Internal) `(Ibgp))
                    ((External) `(Ebgp))))))
          ((External)
            (match d
               ((ExistT x0 _)
                 (match x0
                    ((Internal) `(Ebgp))
                    ((External) (error "absurd case")))))))))))

(define singleASTopology (lambda (h) `(Build_TopologyClass
  ,(@ eqDecSigT~ eqDecRouterType (eqDecRouters h))
  ,(@ enumerableSigT~ eqDecRouterType enumerableRouterType (eqDecRouters h)
     (enumerableRouters h)) ,(lambdas (s d a a~)
  (match s
     ((ExistT x r)
       (match x
          ((Internal)
            (match d
               ((ExistT x0 r0)
                 (match x0
                    ((Internal)
                      (let ((s0
                        (@ eqDecide (@ eqDecRouters h `(Internal)) r r0)))
                        (match s0
                           ((Left) (error "absurd case"))
                           ((Right)
                             (match a
                                ((Tt)
                                  (match a~
                                     ((Tt) `(Left)))))))))
                    ((External) (@ eqDecide (@ eqDecNeighbor h r r0) a a~))))))
          ((External)
            (match d
               ((ExistT x0 r0)
                 (match x0
                    ((Internal) (@ eqDecide (@ eqDecNeighbor h r0 r) a a~))
                    ((External) (error "absurd case")))))))))) ,(lambdas (s
  d)
  (match s
     ((ExistT x r)
       (match x
          ((Internal)
            (match d
               ((ExistT x0 r0)
                 (match x0
                    ((Internal)
                      (let ((s0
                        (@ eqDecide (@ eqDecRouters h `(Internal)) r r0)))
                        (match s0
                           ((Left) enumerableEmptySet)
                           ((Right) enumerableUnit))))
                    ((External) (@ enumerableNeighbor h r r0))))))
          ((External)
            (match d
               ((ExistT x0 r0)
                 (match x0
                    ((Internal) (@ enumerableNeighbor h r0 r))
                    ((External) enumerableEmptySet))))))))) ,(singleASMode h)
  ,(singleASInitialUninterpretedState h))))

(define eqDecSig (lambdas (h a0 a~0)
  (let ((s (@ eqDecide h a0 a~0)))
    (match s
       ((Left) `(Left))
       ((Right) `(Right))))))

(define fullList (lambdas (h0 l)
  (match l
     ((Nil) (empty h0))
     ((Cons y l0)
       (@ union h0 (@ single h0 y)
         (@ bind h0 (@ full h0 (@ fullList h0 l0)) (lambda (x)
           (@ single h0 x))))))))
  
(define fullOutgoing (lambdas (_ _ h _ fullNeighbors0 fullRouters s r)
  (@ union s
    (@ bind s (@ full s (@ fullRouters s `(Internal))) (lambda (d)
      (let ((s0 (@ eqDecide (@ eqDecRouters h `(Internal)) r d)))
        (match s0
           ((Left) (empty s))
           ((Right)
             (@ single s `(ExistT ,`(ExistT ,`(Internal) ,d)
               ,(let ((s1
                  (match h
                     ((Build_SingleASTopologyClass eqDecRouters0 _ _ _ _)
                       (@ eqDecRouters0 `(Internal) r d)))))
                  (match s1
                     ((Left) (error "absurd case"))
                     ((Right) `(Tt)))))))))))
    (@ bind s (@ full s (@ fullNeighbors0 s r)) (lambda (x)
      (match x
         ((ExistT d n) (@ single s `(ExistT ,`(ExistT ,`(External) ,d) ,n)))))))))

(define fullReceivedIncoming (lambdas (_ _ h _ fullNeighbors0 fullRouters s
  r)
  (@ union s
    (@ bind s (@ full s (@ fullRouters s `(Internal))) (lambda (d)
      (let ((s0 (@ eqDecide (@ eqDecRouters h `(Internal)) r d)))
        (match s0
           ((Left) (empty s))
           ((Right)
             (@ single s `(ExistT ,`(ExistT ,`(Internal) ,d)
               ,(let ((s1
                  (match h
                     ((Build_SingleASTopologyClass eqDecRouters0 _ _ _ _)
                       (@ eqDecRouters0 `(Internal) d r)))))
                  (match s1
                     ((Left) (error "absurd case"))
                     ((Right) `(Tt)))))))))))
    (@ bind s (@ full s (@ fullNeighbors0 s r)) (lambda (x)
      (match x
         ((ExistT d n) (@ single s `(ExistT ,`(ExistT ,`(External) ,d) ,n)))))))))

(define fullIncoming (lambdas (plainPrefix plainAttributes h h0
  fullNeighbors0 fullRouters s r)
  (@ union s (@ single s `(Injected))
    (@ bind s
      (@ full s
        (@ fullReceivedIncoming plainPrefix plainAttributes h h0
          fullNeighbors0 fullRouters s r)) (lambda (i)
      (@ single s `(Received ,i)))))))

(define fullNeighbor (lambdas (h fullNeighbors0 s s0 d)
  (@ bind s (@ full s (@ fullNeighbors0 s s0)) (lambda (x)
    (match x
       ((ExistT d~ c)
         (let ((s1 (@ eqDecide (@ eqDecRouters h `(External)) d~ d)))
           (match s1
              ((Left) (@ single s c))
              ((Right) (empty s))))))))))

(define listSearch0 (lambdas (bA~ sS~ s)
  (match (@ search bA~ sS~ s)
     ((Solution a) `(Cons ,a ,`(Nil)))
     ((Uninhabited) `(Nil)))))

(define optionToSpace (lambdas (h1 o)
  (match o
     ((Some a) (@ single h1 a))
     ((None) (empty h1)))))

(define fullRouting (lambdas (plainPrefix plainAttributes h h0 fullNeighbors0
  fullRouters h1 r)
  (@ union h1
    (@ bind h1
      (@ full h1
        (@ fullIncoming plainPrefix plainAttributes h h0 fullNeighbors0
          fullRouters h1 r)) (lambda (s)
      (@ single h1 `(OnlyNotAvailable ,s))))
    (@ bind h1 (@ full h1 (@ fullRouters h1 `(Internal))) (lambda (ri)
      (@ bind h1 (@ full h1 (@ fullRouters h1 `(External))) (lambda (re)
        (@ bind h1 (@ full h1 (@ fullNeighbor h fullNeighbors0 h1 ri re))
          (lambda (n) (@ single h1 `(AllAvailable ,ri ,re ,n)))))))))))

(define fullSigT (lambdas (h1 h2 h3)
  (@ bind h1 (@ full h1 h2) (lambda (a)
    (@ bind h1 (@ full h1 (h3 a)) (lambda (b) (@ single h1 `(ExistT ,a ,b))))))))

(define fullProd (lambdas (s h1 h2)
  (@ bind s (@ full s h1) (lambda (a)
    (@ bind s (@ full s h2) (lambda (b) (@ single s `(Pair ,a ,b))))))))

(define parallelBGPV (lambdas (_ _ plainPrefix _ plainAttributes _ h h0
  fullNeighbors0 fullRouters _ bA~ _ bgpvScheduler0 q)
  (@ bgpvScheduler0 q
    (@ full bA~
      (@ fullSigT bA~ (@ fullRouters bA~ `(Internal)) (lambda (a)
        (@ fullProd bA~
          (@ fullProd bA~
            (@ fullOutgoing plainPrefix plainAttributes h h0 fullNeighbors0
              fullRouters bA~ a)
            (@ fullRouting plainPrefix plainAttributes h h0 fullNeighbors0
              fullRouters bA~ a))
          (@ fullRouting plainPrefix plainAttributes h h0 fullNeighbors0
            fullRouters bA~ a))))))))

(define pickOne (lambdas (s sS s0)
  (match (@ listSearch0 s sS s0)
     ((Nil) (empty s))
     ((Cons a _) (@ single s a)))))

(define parallelBGPVImport (lambdas (_ _ plainPrefix _ plainAttributes _ h h0
  fullNeighbors0 fullRouters _ bA~ pS~ bgpvScheduler0 q)
  (@ bgpvScheduler0 q
    (@ bind bA~ (@ full bA~ (@ fullRouters bA~ `(Internal))) (lambda (r)
      (@ bind bA~
        (@ pickOne bA~ pS~
          (@ full bA~
            (@ fullOutgoing plainPrefix plainAttributes h h0 fullNeighbors0
              fullRouters bA~ r))) (lambda (o)
        (@ bind bA~
          (@ full bA~
            (@ fullRouting plainPrefix plainAttributes h h0 fullNeighbors0
              fullRouters bA~ r)) (lambda (r0)
          (@ single bA~ `(ExistT ,r ,`(Pair ,`(Pair ,o ,r0) ,r0))))))))))))

(define parallelBGPVExport (lambdas (_ _ plainPrefix _ plainAttributes _ h h0
  fullNeighbors0 fullRouters _ bA~ _ bgpvScheduler0 q)
  (@ bgpvScheduler0 q
    (@ bind bA~ (@ full bA~ (@ fullRouters bA~ `(Internal))) (lambda (r)
      (@ bind bA~
        (@ full bA~
          (@ fullOutgoing plainPrefix plainAttributes h h0 fullNeighbors0
            fullRouters bA~ r)) (lambda (o)
        (@ bind bA~
          (@ full bA~
            (@ fullRouting plainPrefix plainAttributes h h0 fullNeighbors0
              fullRouters bA~ r)) (lambda (r0)
          (@ single bA~ `(ExistT ,r ,`(Pair ,`(Pair ,o ,r0) ,r0))))))))))))

(define parallelBGPVPreference (lambdas (_ _ plainPrefix _ plainAttributes _
  h h0 fullNeighbors0 fullRouters _ bA~ pS~ bgpvScheduler0 q)
  (@ bgpvScheduler0 q
    (@ bind bA~ (@ full bA~ (@ fullRouters bA~ `(Internal))) (lambda (r)
      (@ bind bA~
        (@ pickOne bA~ pS~
          (@ full bA~
            (@ fullOutgoing plainPrefix plainAttributes h h0 fullNeighbors0
              fullRouters bA~ r))) (lambda (o)
        (@ bind bA~
          (@ full bA~
            (@ fullRouting plainPrefix plainAttributes h h0 fullNeighbors0
              fullRouters bA~ r)) (lambda (r0)
          (@ bind bA~
            (@ full bA~
              (@ fullRouting plainPrefix plainAttributes h h0 fullNeighbors0
                fullRouters bA~ r)) (lambda (r~)
            (@ single bA~ `(ExistT ,r ,`(Pair ,`(Pair ,o ,r0) ,r~))))))))))))))

(define eqDecideIP (lambdas (a b) (if (eq? a b) '(Left) '(Right))))

(define eqDecIP eqDecideIP)

(define solver rosetteBasic)

(define eqDecideCIDR eq-dec?)

(define enumerableCIDR __)

(define fullCIDR (lambda (_) (symbolic-prefix)))

(define fullCIDR0 fullCIDR)

(define eqDecCIDR eqDecideCIDR)

(define cidrPrefix `(Build_PrefixClass ,eqDecCIDR ,enumerableCIDR))

(define eqDecideBGPAttributes (lambdas (_) eq-dec?))

(define leDecBGPAttributes
  (lambdas (a a*) (if (<= (announcement-pref a) (announcement-pref a*)) '(True) '(False))))

(define eqDecBGPAttributes eqDecideBGPAttributes)

(define bgpAttributes `(Build_PathAttributesClass ,eqDecBGPAttributes
  ,leDecBGPAttributes))

(define fullBGPAttributes
  (lambdas (as _) (symbolic-announcement (as-environment as))))

(define fullBGPAttributes0 (lambda (setup) (fullBGPAttributes setup)))

(define internals (lambdas (as) (coqify-list (as-internal-routers as))))

(define neighbors
  (lambdas (as r) (coqify-list (as-router-external-neighbors as r))))

(define fullRouter (lambdas (setup h t)
  (match t
     ((Internal)
       (@ bind h (@ full h (@ fullList h (internals setup))) (single h)))
     ((External)
       (@ bind h (@ full h (@ fullList h (internals setup))) (lambda (ri)
         (@ bind h (@ full h (@ fullList h (@ neighbors setup ri)))
           (lambda (x) (@ single h x)))))))))

(define fullNeighbors (lambdas (setup h r)
  (@ bind h (@ full h (@ fullList h (@ neighbors setup r))) (lambda (x)
    (@ single h `(ExistT ,x ,__))))))

(define fullNeighbor0 (lambdas (setup h riOk d)
  (let ((s (@ in_dec (eqDecide eqDecIP) d (@ neighbors setup riOk))))
    (match s
       ((Left) (@ single h __))
       ((Right) (empty h))))))

(define bagpipeTopology (lambda (setup) `(Build_SingleASTopologyClass
  ,(lambda (t)
  (match t
     ((Internal) (eqDecide (eqDecSig eqDecIP)))
     ((External) (eqDecide (eqDecSig eqDecIP))))) ,(lambda (t)
  (enumerableFull (lambda (s) (@ fullRouter setup s t)))) ,(lambdas (_ _ _ _)
  `(Left)) ,(lambdas (s d)
  (enumerableFull (lambda (s0) (@ fullNeighbor0 setup s0 s d)))) ,`(Tt))))

(define denoteImport denote-import)

(define denoteExport denote-export)

(define bestIncomingBGP (lambda (_) __))

(define racketRouterExternal router-external)

(define racketRouterInternal router-internal)

(define racketRouterInjected (injected))

(define rackifyRouter (lambdas (_ x)
  (match x
     ((ExistT t r)
       (match t
          ((Internal) (racketRouterInternal r))
          ((External) (racketRouterExternal r)))))))

(define racketNil '())

(define racketSnoc (lambdas (l a) (append l (list a))))

(define rackifyPath (lambdas (setup path0)
  (match path0
     ((Start r) (@ racketSnoc racketNil (@ rackifyRouter setup r)))
     ((Hop _ r _ path1)
       (@ racketSnoc (@ rackifyPath setup path1) (@ rackifyRouter setup r))))))
  
(define racketRoutingInformationNotAvailable (not-available))

(define racketRoutingInformationAvailable
  (lambdas (a0 a path) (tracked-announcement a0 a path)))

(define rackifyRoutingInformation (lambdas (setup a)
  (match a
     ((Available a0)
       (@ racketRoutingInformationAvailable
         (@ original (singleASTopology (bagpipeTopology setup)) bgpAttributes
           a0)
         (@ current (singleASTopology (bagpipeTopology setup)) bgpAttributes
           a0)
         (@ rackifyPath setup
           (@ path (singleASTopology (bagpipeTopology setup)) bgpAttributes
             a0))))
     ((NotAvailable) racketRoutingInformationNotAvailable))))

(define racketDenoteQuery denote-prop)

(define denoteQuery (lambdas (setup q r i o p ai al~ al ao)
  (@ racketDenoteQuery q (@ rackifyRouter setup `(ExistT ,`(Internal) ,r))
    (match i
       ((Injected) racketRouterInjected)
       ((Received i0) (@ rackifyRouter setup (projT1 i0))))
    (@ rackifyRouter setup (projT1 o)) p
    (@ rackifyRoutingInformation setup ai)
    (@ rackifyRoutingInformation setup al~)
    (@ rackifyRoutingInformation setup al)
    (@ rackifyRoutingInformation setup ao))))

(define bagpipeConfiguration (lambda (setup)
  `(Build_SingleASConfigurationClass ,(denoteImport setup) ,(lambdas (r _)
  (@ denoteExport setup r)) ,(bestIncomingBGP setup))))

(define bgpvScheduler distributed-bgpv-scheduler)

(define bgpvAll (lambda (setup)
  (@ parallelBGPV solver rosetteSearch cidrPrefix fullCIDR0 bgpAttributes
    (fullBGPAttributes0 setup) (bagpipeTopology setup)
    (bagpipeConfiguration setup) (fullNeighbors setup) (fullRouter setup)
    (denoteQuery setup) listSpace listSearch (bgpvScheduler setup))))

(define bgpvImport (lambda (setup)
  (@ parallelBGPVImport solver rosetteSearch cidrPrefix fullCIDR0
    bgpAttributes (fullBGPAttributes0 setup) (bagpipeTopology setup)
    (bagpipeConfiguration setup) (fullNeighbors setup) (fullRouter setup)
    (denoteQuery setup) listSpace listSearch (bgpvScheduler setup))))

(define bgpvExport (lambda (setup)
  (@ parallelBGPVExport solver rosetteSearch cidrPrefix fullCIDR0
    bgpAttributes (fullBGPAttributes0 setup) (bagpipeTopology setup)
    (bagpipeConfiguration setup) (fullNeighbors setup) (fullRouter setup)
    (denoteQuery setup) listSpace listSearch (bgpvScheduler setup))))

(define bgpvPreference (lambda (setup)
  (@ parallelBGPVPreference solver rosetteSearch cidrPrefix fullCIDR0
    bgpAttributes (fullBGPAttributes0 setup) (bagpipeTopology setup)
    (bagpipeConfiguration setup) (fullNeighbors setup) (fullRouter setup)
    (denoteQuery setup) listSpace listSearch (bgpvScheduler setup))))

(define elimExecutionMode
  (lambdas (m imp exp pref all) (case m ((import) imp) ((export) exp) ((preference) pref) ((all) all))))

(define bgpv (lambdas (setup m)
  (@ elimExecutionMode m (bgpvImport setup) (bgpvExport setup)
    (bgpvPreference setup) (bgpvAll setup))))

(define listHead (lambda (l) (hd_error l)))


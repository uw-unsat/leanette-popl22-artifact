#lang s-exp rosette

(require racket/format)

(current-bitwidth 10)

(require "util/list.rkt")
(require "util/rosette.rkt")
(require "util/extraction-rosette.rkt")
(require (except-in "network/network.rkt" current original path))
(require "config.rkt")
(require "setup.rkt")

(provide bgpvCore~)

(define __ 'unused)


(define negb (lambda (b)
  (match b
     ((True) `(False))
     ((False) `(True)))))

(define fst (lambda (p)
  (match p
     ((Pair x _) x))))

(define snd (lambda (p)
  (match p
     ((Pair _ y) y))))

(define app (lambdas (l m)
  (match l
     ((Nil) m)
     ((Cons a l1) `(Cons ,a ,(@ app l1 m))))))
  
(define projT1 (lambda (x)
  (match x
     ((ExistT a _) a))))

(define projT2 (lambda (x)
  (match x
     ((ExistT _ h) h))))

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

(define sumbool2bool (lambda (b)
  (match b
     ((Left) `(True))
     ((Right) `(False)))))

(define sumBoolAnd (lambdas (e e~)
  (match e
     ((Left)
       (match e~
          ((Left) `(Left))
          ((Right) `(Right))))
     ((Right) `(Right)))))

(define bool2sumbool (lambda (b)
  (match b
     ((True) `(Left))
     ((False) `(Right)))))

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

(define enumerate (lambda (enumerable) enumerable))

(define enumerableSigT (lambdas (_ h0 _ h2)
  (@ bindList (enumerate h0) (lambda (a)
    (@ map (lambda (x) `(ExistT ,a ,x)) (enumerate (h2 a)))))))

(define enumerableEmptySet `(Nil))

(define enumerableUnit `(Cons ,`(Tt) ,`(Nil)))

(define enumerableSigT~ (lambdas (h h0 h1 h2) (@ enumerableSigT h h0 h1 h2)))

(define enumerableFull (lambda (h) (h listSpace)))

(define eqDecPathAttributes (lambda (pathAttributesClass)
  (match pathAttributesClass
     ((Build_PathAttributesClass eqDecPathAttributes0 _)
       eqDecPathAttributes0))))

(define leDecPathAttributes (lambda (pathAttributesClass)
  (match pathAttributesClass
     ((Build_PathAttributesClass _ leDecPathAttributes0)
       leDecPathAttributes0))))

(define bindRoutingInformation (lambdas (_ a f)
  (match a
     ((Available a0) (f a0))
     ((NotAvailable) `(NotAvailable)))))

(define leDecRoutingInformation (lambdas (h0 a a~)
  (match a
     ((Available a0)
       (match a~
          ((Available a~0) (@ leDecPathAttributes h0 a0 a~0))
          ((NotAvailable) `(False))))
     ((NotAvailable) `(True)))))

(define eqDecMode (lambdas (a a~)
  (match a
     ((Ibgp)
       (match a~
          ((Ibgp) `(Left))
          ((Ebgp) `(Right))))
     ((Ebgp)
       (match a~
          ((Ibgp) `(Right))
          ((Ebgp) `(Left)))))))

(define eqDecRouter (lambda (topologyClass)
  (match topologyClass
     ((Build_TopologyClass eqDecRouter0 _ _ _ _ _) eqDecRouter0))))

(define eqDecConnection (lambda (topologyClass)
  (match topologyClass
     ((Build_TopologyClass _ _ eqDecConnection0 _ _ _) eqDecConnection0))))

(define mode (lambda (topologyClass)
  (match topologyClass
     ((Build_TopologyClass _ _ _ _ mode0 _) mode0))))

(define import (lambdas (_ _ _ _ configurationClass)
  (match configurationClass
     ((Build_ConfigurationClass import0 _ _ _) import0))))

(define export (lambdas (_ _ _ _ configurationClass)
  (match configurationClass
     ((Build_ConfigurationClass _ export0 _ _) export0))))

(define originate (lambdas (_ _ _ _ configurationClass)
  (match configurationClass
     ((Build_ConfigurationClass _ _ originate0 _) originate0))))

(define bestIncoming (lambdas (_ _ _ _ configurationClass)
  (match configurationClass
     ((Build_ConfigurationClass _ _ _ bestIncoming0) bestIncoming0))))

(define originate~ (lambdas (h h0 h1 r h2 p a)
  (match a
     ((Available a0) (@ originate h h0 h1 r h2 p a0))
     ((NotAvailable) `(True)))))

(define import~ (lambdas (h h0 h1 r h2 s p a)
  (@ bindRoutingInformation h0 a (@ import h h0 h1 r h2 s p))))

(define export~ (lambdas (h h0 h1 r h2 i o p a)
  (match i
     ((Injected)
       (@ bindRoutingInformation h0 a (@ export h h0 h1 r h2 i o p)))
     ((Received s)
       (match s
          ((ExistT x ci)
            (match o
               ((ExistT x0 co)
                 (match (@ sumBoolAnd
                          (@ eqDecide eqDecMode (@ mode h1 x r ci) `(Ibgp))
                          (@ eqDecide eqDecMode (@ mode h1 r x0 co) `(Ibgp)))
                    ((Left) `(NotAvailable))
                    ((Right)
                      (@ bindRoutingInformation h0 a
                        (@ export h h0 h1 r h2 i o p))))))))))))

(define symbolicEmpty (lambda  (_) (assert false)))

(define symbolicSingle (lambdas (a _) a))

(define symbolicUnion
  (lambdas (s t v) (define-symbolic* b boolean?) (if b (s v) (t v))))

(define symbolicBind (lambdas (s f v) (@ f (s v) v)))

(define symbolicSearch (lambda  (e) (solve/evaluate/concretize e)))

(define denotationSymbolic __)

(define rosetteBasic `(Build_Basic ,(lambda (_) denotationSymbolic)
  ,(lambda (_) symbolicEmpty) ,(lambda (_) symbolicSingle) ,(lambda (_)
  symbolicUnion) ,(lambdas (_ _) symbolicBind)))

(define rosetteSearch (lambda (_) symbolicSearch))

(define eqDecidePath (lambdas (h0 p p~)
  (match p
     ((Start r)
       (match p~
          ((Start r~)
            (let ((s (@ eqDecide (eqDecRouter h0) r r~)))
              (match s
                 ((Left) `(Left))
                 ((Right) `(Right)))))
          ((Hop _ _ _ _) `(Right))))
     ((Hop r d c p0)
       (match p~
          ((Start _) `(Right))
          ((Hop r~ d~ c~ p~0)
            (let ((s
              (@ sumBoolAnd (@ eqDecide (eqDecRouter h0) r r~)
                (@ eqDecide (eqDecRouter h0) d d~))))
              (match s
                 ((Left)
                   (let ((s0
                     (@ sumBoolAnd
                       (@ eqDecide (@ eqDecConnection h0 r~ d~) c c~)
                       (@ eqDecidePath h0 p0 p~0))))
                     (match s0
                        ((Left) `(Left))
                        ((Right) `(Right)))))
                 ((Right) `(Right))))))))))
  
(define eqDecPath (lambda (h0) (eqDecidePath h0)))

(define original (lambdas (_ _ t)
  (match t
     ((Build_Tracking original0 _ _) original0))))

(define current (lambdas (_ _ t)
  (match t
     ((Build_Tracking _ current0 _) current0))))

(define path (lambdas (_ _ t)
  (match t
     ((Build_Tracking _ _ path0) path0))))

(define eqDecTracking (lambdas (h0 plainAttributes a a~)
  (match a
     ((Build_Tracking original0 current0 path0)
       (match a~
          ((Build_Tracking original1 current1 path1)
            (match (@ eqDecide (eqDecPathAttributes plainAttributes)
                     original0 original1)
               ((Left)
                 (match (@ eqDecide (eqDecPathAttributes plainAttributes)
                          current0 current1)
                    ((Left)
                      (match (@ eqDecide (eqDecPath h0) path0 path1)
                         ((Left) `(Left))
                         ((Right) `(Right))))
                    ((Right) `(Right))))
               ((Right) `(Right)))))))))

(define trackingAttributes (lambdas (h0 plainAttributes)
  `(Build_PathAttributesClass ,(@ eqDecTracking h0 plainAttributes)
  ,(lambdas (a a~)
  (@ leDecPathAttributes plainAttributes (@ current h0 plainAttributes a)
    (@ current h0 plainAttributes a~))))))

(define trackingConfiguration (lambdas (h h0 plainAttributes
  plainConfiguration r) `(Build_ConfigurationClass ,(lambdas (s p a)
  (match a
     ((Build_Tracking a0 a1 p0)
       (match (@ import h plainAttributes h0 r (plainConfiguration r) s p a1)
          ((Available a~) `(Available ,`(Build_Tracking ,a0 ,a~ ,p0)))
          ((NotAvailable) `(NotAvailable)))))) ,(lambdas (s d p a)
  (match a
     ((Build_Tracking a0 a1 p0)
       (match (@ export h plainAttributes h0 r (plainConfiguration r) s d p
                a1)
          ((Available a~) `(Available ,`(Build_Tracking ,a0 ,a~ ,`(Hop ,r
            ,(projT1 d) ,(projT2 d) ,p0))))
          ((NotAvailable) `(NotAvailable)))))) ,(lambdas (p a)
  (match a
     ((Build_Tracking a0 a1 p0)
       (sumbool2bool
         (@ sumBoolAnd
           (@ sumBoolAnd
             (bool2sumbool
               (@ originate h plainAttributes h0 r (plainConfiguration r) p
                 a1))
             (@ eqDecide (eqDecPathAttributes plainAttributes) a1 a0))
           (@ eqDecide (eqDecPath h0) p0 `(Start ,r))))))) ,(lambda (f)
  (@ bestIncoming h plainAttributes h0 r (plainConfiguration r) (lambda (i)
    (match (f i)
       ((Available a) `(Available ,(@ current h0 plainAttributes a)))
       ((NotAvailable) `(NotAvailable)))))))))

(define transmit (lambdas (h h0 plainAttributes plainConfiguration p p0 a)
  (match p
     ((Start r)
       (match (@ originate~ h plainAttributes h0 r (plainConfiguration r) p0
                a)
          ((True) a)
          ((False) `(NotAvailable))))
     ((Hop r d c p~)
       (let ((i
         (match p~
            ((Start _) `(Injected))
            ((Hop s _ c0 _) `(Received ,`(ExistT ,s ,c0))))))
         (@ export~ h plainAttributes h0 r (plainConfiguration r) i `(ExistT
           ,d ,c) p0
           (@ import~ h plainAttributes h0 r (plainConfiguration r) i p0
             (@ transmit h h0 plainAttributes plainConfiguration p~ p0 a))))))))
  
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

(define intImport (lambdas (_ _ _ singleASConfigurationClass)
  (match singleASConfigurationClass
     ((Build_SingleASConfigurationClass intImport0 _ _) intImport0))))

(define intExport (lambdas (_ _ _ singleASConfigurationClass)
  (match singleASConfigurationClass
     ((Build_SingleASConfigurationClass _ intExport0 _) intExport0))))

(define bestIncoming~ (lambdas (_ _ _ singleASConfigurationClass)
  (match singleASConfigurationClass
     ((Build_SingleASConfigurationClass _ _ bestIncoming~0) bestIncoming~0))))

(define singleASConfiguration (lambdas (plainPrefix plainAttributes h h0 r)
  (match r
     ((ExistT x x0)
       (match x
          ((Internal) `(Build_ConfigurationClass ,(lambdas (i p a)
            (@ intImport plainPrefix plainAttributes h h0 x0 i p a))
            ,(lambdas (o p a)
            (@ intExport plainPrefix plainAttributes h h0 x0 o p a))
            ,(lambdas (_ _) `(False)) ,(lambda (f)
            (@ bestIncoming~ plainPrefix plainAttributes h h0 `(ExistT
              ,`(Internal) ,x0) f))))
          ((External) `(Build_ConfigurationClass ,(lambdas (i _ a)
            (match i
               ((Injected) `(Available ,a))
               ((Received _) `(NotAvailable)))) ,(lambdas (_ _ _ a)
            `(Available ,a)) ,(lambdas (_ _) `(True)) ,(lambda (f)
            (@ bestIncoming~ plainPrefix plainAttributes h h0 `(ExistT
              ,`(External) ,x0) f)))))))))

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
  
(define trackingAttributes~ (lambdas (plainAttributes h)
  (@ trackingAttributes (singleASTopology h) plainAttributes)))

(define trackingConfiguration~ (lambdas (plainPrefix plainAttributes h h0)
  (@ trackingConfiguration plainPrefix (singleASTopology h) plainAttributes
    (@ singleASConfiguration plainPrefix plainAttributes h h0))))

(define feasiblePath (lambdas (h r ri re n)
  (match (@ eqDecide (@ eqDecRouters h `(Internal)) r ri)
     ((Left) `(Pair ,`(Received ,`(ExistT ,`(ExistT ,`(External) ,re) ,n))
       ,`(Hop ,`(ExistT ,`(External) ,re) ,`(ExistT ,`(Internal) ,r) ,n
       ,`(Start ,`(ExistT ,`(External) ,re)))))
     ((Right)
       (let ((c
         (let ((s (@ eqDecide (@ eqDecRouters h `(Internal)) ri r)))
           (match s
              ((Left) (error "absurd case"))
              ((Right) `(Tt))))))
         `(Pair ,`(Received ,`(ExistT ,`(ExistT ,`(Internal) ,ri) ,c)) ,`(Hop
         ,`(ExistT ,`(Internal) ,ri) ,`(ExistT ,`(Internal) ,r) ,c ,`(Hop
         ,`(ExistT ,`(External) ,re) ,`(ExistT ,`(Internal) ,ri) ,n ,`(Start
         ,`(ExistT ,`(External) ,re))))))))))

(define transmit~ (lambdas (plainPrefix plainAttributes h h0 r ri re n p a0)
  (let ((sP (@ feasiblePath h r ri re n)))
    `(Pair ,(fst sP)
    ,(match (@ transmit plainPrefix (singleASTopology h) plainAttributes
              (@ singleASConfiguration plainPrefix plainAttributes h h0)
              (snd sP) p `(Available ,a0))
        ((Available a) `(Available ,`(Build_Tracking ,a0 ,a ,(snd sP))))
        ((NotAvailable) `(NotAvailable)))))))

(define listSearch (lambdas (bA~ sS~ s)
  (match (@ search bA~ sS~ s)
     ((Solution a) `(Cons ,a ,`(Nil)))
     ((Uninhabited) `(Nil)))))

(define routingToTracking (lambdas (bA plainPrefix plainAttributes
  fullPathAttributes h h0 r p r0)
  (match r0
     ((OnlyNotAvailable s) (@ single bA `(ExistT ,s ,`(NotAvailable))))
     ((AllAvailable ri re n)
       (@ bind bA (@ full bA fullPathAttributes) (lambda (a0)
         (@ single bA
           (let ((sai
             (@ transmit~ plainPrefix plainAttributes h h0 r ri re n p a0)))
             `(ExistT ,(fst sai) ,(snd sai))))))))))

(define bgpvCore (lambdas (bA pS plainPrefix fullPrefix plainAttributes
  fullPathAttributes h h0 denoteQuery0 q v)
  (match v
     ((ExistT r p)
       (match p
          ((Pair p0 x)
            (match p0
               ((Pair d r0)
                 (@ listSearch bA pS
                   (@ bind bA (@ full bA fullPrefix) (lambda (p1)
                     (@ bind bA
                       (@ routingToTracking bA plainPrefix plainAttributes
                         fullPathAttributes h h0 r p1 r0) (lambda (x0)
                       (match x0
                          ((ExistT s s0)
                            (@ bind bA
                              (@ routingToTracking bA plainPrefix
                                plainAttributes fullPathAttributes h h0 r p1
                                x) (lambda (x1)
                              (match x1
                                 ((ExistT s~ s1)
                                   (let ((al~
                                     (@ import~ plainPrefix
                                       (@ trackingAttributes~ plainAttributes
                                         h) (singleASTopology h) `(ExistT
                                       ,`(Internal) ,r)
                                       (@ trackingConfiguration~ plainPrefix
                                         plainAttributes h h0 `(ExistT
                                         ,`(Internal) ,r)) s p1 s0)))
                                     (let ((al
                                       (@ import~ plainPrefix
                                         (@ trackingAttributes~
                                           plainAttributes h)
                                         (singleASTopology h) `(ExistT
                                         ,`(Internal) ,r)
                                         (@ trackingConfiguration~
                                           plainPrefix plainAttributes h h0
                                           `(ExistT ,`(Internal) ,r)) s~ p1
                                         s1)))
                                       (let ((ao
                                         (@ export~ plainPrefix
                                           (@ trackingAttributes~
                                             plainAttributes h)
                                           (singleASTopology h) `(ExistT
                                           ,`(Internal) ,r)
                                           (@ trackingConfiguration~
                                             plainPrefix plainAttributes h h0
                                             `(ExistT ,`(Internal) ,r)) s~ d
                                           p1 al)))
                                         (match (sumbool2bool
                                                  (@ sumBoolAnd
                                                    (bool2sumbool
                                                      (@ leDecRoutingInformation
                                                        (@ trackingAttributes~
                                                          plainAttributes h)
                                                        al~ al))
                                                    (bool2sumbool
                                                      (negb
                                                        (@ denoteQuery0 q r s
                                                          d p1 s0 al~ al ao)))))
                                            ((True)
                                              (@ single bA `(ExistT ,r
                                                ,`(Pair ,`(Pair ,`(Pair
                                                ,`(Pair ,`(Pair ,`(Pair
                                                ,`(Pair ,s ,d) ,p1) ,s0) ,s1)
                                                ,al~) ,al) ,ao))))
                                            ((False) (empty bA)))))))))))))))))))))))))

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

(define fullNeighbor (lambdas (setup h riOk d)
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
  (enumerableFull (lambda (s0) (@ fullNeighbor setup s0 s d)))) ,`(Tt))))

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

(define bgpvCore~ (lambda (setup)
  (@ bgpvCore solver rosetteSearch cidrPrefix fullCIDR0 bgpAttributes
    (fullBGPAttributes0 setup) (bagpipeTopology setup)
    (bagpipeConfiguration setup) (denoteQuery setup))))


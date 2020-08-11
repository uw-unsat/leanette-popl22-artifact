#lang racket

; some data structures (e.g., a digraph)

(provide
 digraph?
 make-digraph
 dg-identity-node-key?
 serialize-digraph
 deserialize-digraph
 dg-node-ref
 dg-node-value
 dg-edge-value
 dg-edge-source
 dg-edge-target
 dg-nodes
 dg-order
 dg-size
 dg-edge-values
 dg-add-node!
 dg-outgoing-edges
 dg-outgoing-neighbors
 dg-out-degree
 dg-sink?
 dg-sources
 dg-sinks
 dg-add-edge!
 dg-reachable?
 dg-all-reachable-nodes 
 dg-filter-nodes
 dg-reverse-edges
 dg-shortest-path
 dg-all-reverse-paths
 dg-topological-sort)

(require
  data/queue
  "util.rkt")

(struct node (val out-edges))
(struct edge (val src dst))
(struct digraph (nodes key-fn))

(define (make-digraph node-key-fn)
  (digraph (make-hash) node-key-fn))

; #f iff the node key function is the identity
(define (dg-identity-node-key? grph)
  (eq? identity (digraph-key-fn grph)))

; maps both node and edge values of the graph then dumps nodes as a list
; the caller is going to have to remember the key-fn manually, unfortunately.
(define (serialize-digraph node-fn edge-fn grph)
  (define nodes (dg-nodes grph))
  (define node-to-index (for/hasheq ([i (in-range (length nodes))]) (values (list-ref nodes i) i)))
  (map
    (λ (n)
      (match-define (node val out-edges) n)
      (define new-edges
        (map
          (λ (e)
            (match-define (edge val src dst) e)
            (list 'edge (edge-fn val) (hash-ref node-to-index dst)))
          (unbox out-edges)))
      (list 'node (node-fn val) new-edges))
    nodes))

(define (deserialize-digraph key-fn node-fn edge-fn serialized-graph)
  (define grph (make-digraph key-fn))
  (define nodes
    (for/list ([n serialized-graph])
      (match-define (list 'node val _) n)
      (dg-add-node! grph (node-fn val))))
  (for ([n serialized-graph]
        [nde nodes]
        #:when #t
        [e (third n)])
    (match-define (list 'edge val dst) e)
    (dg-add-edge! nde (list-ref nodes dst) (edge-fn val)))
  grph)

(define (listbox-add! bx val)
  (update-box! bx (λ (lst) (cons val lst))))

(define dg-node-value node-val)

(define dg-edge-value edge-val)
(define dg-edge-source edge-src)
(define dg-edge-target edge-dst)

(define (dg-node-ref grph key #:default [default #f])
  (hash-ref (digraph-nodes grph) key default))

(define (dg-nodes grph)
  (hash-values (digraph-nodes grph)))

(define (dg-order grph)
  (hash-count (digraph-nodes grph)))

(define (dg-size grph)
  (for/sum ([n (dg-nodes grph)])
    (length (unbox (node-out-edges n)))))

(define (dg-edge-values grph)
  (for*/list ([n (dg-nodes grph)]
              [e (unbox (node-out-edges n))])
    (edge-val e)))

; digraph?, any? -> node?
(define (dg-add-node! grph val)
  (define key ((digraph-key-fn grph) val))
  (define nodes (digraph-nodes grph))
  (when (hash-has-key? nodes key) (error "node already exists!"))
  (define n (node val (box empty)))
  (hash-set! nodes key n)
  n)

; node? -> (listof edge?)
(define (dg-outgoing-edges nde)
  (unbox (node-out-edges nde)))

; node? -> (listof node?)
(define (dg-outgoing-neighbors nde)
  (map edge-dst (unbox (node-out-edges nde))))

(define (dg-out-degree nde)
  (length (dg-outgoing-edges nde)))

(define (dg-sink? nde)
  (= (dg-out-degree nde) 0))

(define (dg-add-edge! src-node dst-node edge-value)
  (node-val dst-node)
  (listbox-add! (node-out-edges src-node) (edge edge-value src-node dst-node)))

(define (dg-reachable? start-node end-node #:filter-edge [filter-edge (λ (_) #t)])
  ; do a dfs until we find end-node or exhaust
  (define visited (mutable-set))
  (define (dfs n)
    (set-add! visited n)
    (or
      (equal? n end-node)
      (ormap
        (λ (e)
          (define next (edge-dst e))
          (and
            (filter-edge (edge-val e))
            (not (set-member? visited next))
            (dfs next)))
        (unbox (node-out-edges n)))))
  (dfs start-node))

(define (dg-all-reachable-nodes start-nodes)
  (define visited (mutable-seteq))
  (define (rec nde)
    (set-add! visited nde)
    (for ([e (in-list (unbox (node-out-edges nde)))]
          #:when (not (set-member? visited (edge-dst e))))
      (rec (edge-dst e))))
  (for-each rec start-nodes)
  visited)

; returns a new graph with only the nodes for which proc evaluates to true.
; will preserve all edges for which both source and target are in the filtered set
(define (dg-filter-nodes proc graph)
  (match-define (digraph old-nodes key-fn) graph)
  (define nodes (for/hash ([(k v) old-nodes] #:when (proc v)) (values k (node k (box #f)))))
  (for ([(k v) old-nodes] #:when (proc v))
    (define nde (hash-ref nodes k))
    (define edges
      (filter-map
        (λ (e)
          (match-define (edge val src dst) e)
          (and (proc src)
               (proc dst)
               (edge val (hash-ref nodes (node-val src)) (hash-ref nodes (node-val dst)))))
        (unbox (node-out-edges v))))
    (set-box! (node-out-edges nde) edges))
  (digraph nodes key-fn))

(define (dg-reverse-edges old-grph)
  (define new-grph (make-digraph (digraph-key-fn old-grph)))

  (for ([nde (dg-nodes old-grph)])
    (dg-add-node! new-grph (node-val nde)))

  (for ([nde (dg-nodes old-grph)])
    (for ([e (unbox (node-out-edges nde))])
      (match-define (edge val src dst) e)
      (dg-add-edge! (dg-node-ref new-grph (node-val dst))
                    (dg-node-ref new-grph (node-val src))
                    val)))

  new-grph)

(define (dg-shortest-path grph start-node goal-nodes #:filter-edge [filter-edge (λ (_) #t)] #:edge-cost [edge-cost (λ (_) 1)])
  ;(dprintf "finding shortest path from ~a to ~a" (node-val start-node) (map node-val goal-nodes))

  (define nodes (dg-nodes grph))
  (define node-to-index (for/hasheq ([i (in-range (length nodes))]) (values (list-ref nodes i) i)))
  (define (nvref vec nde)
    (vector-ref vec (hash-ref node-to-index nde)))
  (define (nvset! vec nde x)
    (vector-set! vec (hash-ref node-to-index nde) x))
  (define distances (make-vector (length nodes) 100000))
  (define prev (make-vector (length nodes) #f))
  (nvset! distances start-node 0)
  (define to-visit (list->vector nodes))

  (define (visit-cost x)
    (if x (nvref distances x) 10000000))

  (define (loop)
    (define next (vector-argmin visit-cost to-visit))
    ;(dprint next)
    (when next
      (nvset! to-visit next #f)
      (define d (nvref distances next))
      (for ([e (dg-outgoing-edges next)]
            #:when (filter-edge (edge-val e)))
        ;(dprintf "looking at edge ~a" (edge-val e))
        (define dst (edge-dst e))
        (define alt (+ d (edge-cost (edge-val e))))
        (when (< alt (nvref distances dst))
          ;(dprintf "updating cost to ~a for node ~a" alt (node-val dst))
          (nvset! distances dst alt)
          (nvset! prev dst e)))
      (loop)))
  (loop)

  (define closest-goal (argmin (λ (n) (nvref distances n)) goal-nodes))

  (unless (or (nvref prev closest-goal) (eq? closest-goal start-node))
    (dprintf "reachable? ~a" (ormap (λ (n) (dg-reachable? start-node n #:filter-edge filter-edge)) goal-nodes))
    (dprint nodes)
    (dprint (node-val start-node))
    (dprint closest-goal)
    (dprint (node-val closest-goal))
    (dprint (eq? start-node closest-goal))
    (dprint distances)
    (dprint prev)
    (error "something is wrong!"))

  (define (build-path n acc)
    (cond
     [(eq? n start-node)
      acc]
     [else
      (define e (nvref prev n))
      (build-path (edge-src e) (cons (edge-val e) acc))]))
  (build-path closest-goal empty))

; node? -> edge-value? list list
; returns all paths (reversed) from src-node to sinks, avoiding cycles.
(define (dg-all-reverse-paths start-node)
  (define (rec nde acc visited)
    (define new-visited (set-add visited nde))
    (match (unbox (node-out-edges nde))
     ['() (list acc)]
     [edges
      (for*/list ([e (in-list edges)]
                  #:when (not (set-member? visited (edge-dst e)))
                  [r (in-list (rec (edge-dst e) (cons (edge-val e) acc) new-visited))])
        r)]))
  (rec start-node empty (seteq)))

(define (dg-sources grph)
  (define nodes (dg-nodes grph))
  ; we don't store incoming edges, so have to calculate it instead
  (define has-incoming? (make-hasheq))
  (for* ([n nodes]
         [d (dg-outgoing-neighbors n)])
    (hash-set! has-incoming? d #t))
  (filter (λ (n) (not (hash-ref has-incoming? n #f))) nodes))

(define (dg-sinks grph)
  (filter dg-sink? (dg-nodes grph)))

; digraph? -> (listof node?)
; Given a DAG, returns a list of nodes in (arbitrary) topological order.
; For any node, it will be earlier in the list than any of its outgoing neighbors.
(define (dg-topological-sort grph)
  (define all-nodes (dg-nodes grph))
  ; we don't store incoming edges, so have to calculate it instead
  (define incoming (make-hasheq)) ; node? -> (setof node?)
  (for* ([n all-nodes]
         [d (dg-outgoing-neighbors n)])
    (hash-update! incoming d (curry cons n) empty))
  ; they are currently lists, turn them all into sets
  (for ([n all-nodes]) (hash-update! incoming n list->seteq empty))
  ; then go through them in an order consistent with a topological sort
  (let loop ([remaining (list->seteq all-nodes)] [visited (seteq)] [acc empty])
    (cond
     [(set-empty? remaining) (reverse acc)]
     [else
      ; find any remaining node for which we've visited all incoming edges
      (define next
        (findf
          (λ (n) (set-empty? (set-subtract (hash-ref incoming n) visited)))
          (set->list remaining)))
      (unless next
        (error "graph is not a DAG! cannot find topological sort!"))
      (loop (set-remove remaining next) (set-add visited next) (cons next acc))])))


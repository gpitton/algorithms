#lang racket

;; collections of simple implementations of essential
;; weighted-graph algorithms.


;; x: from
;; y: to
;; w: weight
(struct edge (x y w)
  ;; needs to be transparent, or equal? will not work as expected.
  #:transparent
  #:methods gen:custom-write
  ;; pretty printing
  [(define (write-proc edge port mode)
     (fprintf port
              "~a -- ~a, w: ~a;"
              (edge-x edge)
              (edge-y edge)
              (edge-w edge)))])


;; TODO enforce y to have the same "type" of x
(provide (contract-out
          [struct edge ((x any/c)
                        (y any/c)
                        (w positive?))]))


;; vs: list of vertices
;; edges: array, edges[v] is a list with the edges from v.
(struct graph (vs edges)
  #:transparent
  #:methods gen:custom-write
  ;; pretty printing
  [(define (write-proc graph port mode)
     (fprintf port "Weighted graph with vertices:\n")
     (for ([v (in-list (graph-vs graph))])
       (fprintf port "~a " v))
     (fprintf port "\nAnd edges:\n")
     (for ([es (in-list (graph-edges graph))])
       (fprintf port "~a: " (edge-x (car es)))
       (for ([e (in-list es)])
         (fprintf port "~a w: ~a, " (edge-y e) (edge-w e)))
       (fprintf port "\n")))])


(provide (contract-out
          [struct graph ((vs (listof any/c))
                         (edges (listof (listof edge?))))]))


;; Updates the list of lists of edges E by including the edge el in
;; position n (invariant to check: (edge-x el) must be equal to n,
;; because we are adding an edge issuing from the vertex n.
(define (update-edges E el n)
  (cond [(null? E) '()]
        [(zero? n)
         (cons (cons el (car E)) (cdr E))]
        [else (cons (car E)
                    (update-edges (cdr E) el (sub1 n)))]))


;; simple priority queue.
(define (make-queue) '())
;; inserts an element el with priority w in the queue.
(define (queue-push queue el w)
  (let ([x (cons w el)])
    (cond [(null? queue) (list x)]
          [(< w (caar queue)) (cons x queue)]
          [else (cons (car queue)
                      (queue-push (cdr queue) el w))])))
;; inserts all the elements of items (which is a list) into the queue. 
(define (extend-queue queue items)
  (if (null? items)
      queue
      (let*
          ([el (car items)]
           [w (edge-w el)])
        (extend-queue (queue-push queue el w)
                      (cdr items)))))
;; returns the first element of the queue and updates the queue.
(define (queue-pop queue)
  (if (null? queue)
      (error "empty queue!")
      (values (cdar queue) (cdr queue))))


;; very simple linked list implementation for a union-find partition.
;; set items are stored in a list. The representative
;; is a representative that is used to identify the set.
(struct partition (repr items)
  ;; needs to be transparent because we need to compare partitions later,
  ;; in partition-union.
  #:transparent)

(define (make-partition x)
  (partition x (list x)))

;; generate a partition with one set (with one element) for every
;; element of the input list l.
(define (partition-from-list l)
  (map make-partition l))

;; returns the partition p (not the representative!) where el belongs.
;; If el does not belong to any partition, returns #f.
(define (partition-find el S)
  ;; auxiliary function to loop through all the partitions T of S.
  (define (search-in-set T)
    (if (member el (partition-items T))
        T
        #f))
              
  ;; main iteration.
  (define (partition-aux S)
    (if (null? S) #f
        (let
            ([p (search-in-set (car S))])
          (if p
              p
              (partition-aux (cdr S))))))
  (partition-aux S))
      
;; returns a partition (linked list of set-items) obtained by
;; merging the two partitions p1 and p2.
(define (partition-union p1 p2)
  (let
      ([r1 (partition-repr p1)]
       [r2 (partition-repr p2)]
       [merge-aux (lambda (a b)
                    (remove-duplicates
                     (append (partition-items a)
                             (partition-items b))))])
    (if (= r1 r2)
        (partition r1 (merge-aux p1 p2))
        ;; choose as representative for the union the
        ;; representative of the smaller partition.
        (let
            ([len1 (length (partition-items p1))]
             [len2 (length (partition-items p2))])
          (if (>= len1 len2)
              (partition r1 (merge-aux p1 p2))
              (partition r1 (merge-aux p2 p1)))))))

;; given a list l of partitions, returns a new list where the two partitions
;; p1 and p2 are merged.
;; TODO check that p1 and p2 belong to l.
(define (merge-partitions l p1 p2)
  (if (null? l) ;; perform the merging and return.
      (list (partition-union p1 p2))
      (let
          ([current-repr (partition-repr (car l))]
           [repr1 (partition-repr p1)]
           [repr2 (partition-repr p2)])
        ;; do not worry about checking if p1 or p2 are null:
        ;; the iteration should be correct anyway
        (cond
          ;; p1 and p2 must not appear in l in after merging,
          ;; their union will be merged at the end of the recursion.
          ;; TODO: this could be optimised with call/cc
          [(or (equal? current-repr repr1)
               (equal? current-repr repr2))
           (merge-partitions (cdr l) p1 p2)]
          [else
           (cons (car l)
                 (merge-partitions (cdr l) p1 p2))]))))


;; experimental implementation of Prim's algorithm
;; for finding minimal spanning trees of weighted graphs.
(define (minimum-tree-prim G
                           #:starting-vertex [starting-vertex 0])
  ;; number of vertices
  (define n (length (graph-vs G)))
  
  #|
    ;; maximal weight of any edge in the graph.
    (define maxw (for*/fold ([maxw (edge-w (caar (graph-edges G)))])
                            ([edges (in-list (graph-edges G))]
                             [e (in-list edges)])
                   (max (edge-w e) maxw)))
    |#
  

  ;; returns a list with the edges from E that have
  ;; an element of A as target (i.e. in the y field).
  (define (edges-with-target E A)
    (cond [(null? E) '()]   ;; base-case for the recursion.
          [(null? A) '()]   ;; sanity check: if A is empty there is
          ;; nothing to target.
          [else
           (let ([el (car E)])
             (if (member (edge-y el) A)
                 ;; el points to an element of A: add it to the list.
                 (cons el (edges-with-target (cdr E) A))
                 ;; el does not point to A: keep iterating.
                 (edges-with-target (cdr E) A)))]))

  ;; removes from queue all the edges that arrive in y.
  (define (remove-target queue y)
    (if (empty? queue)
        '()
        (let*
            ([item (car queue)]
             ;; (car item) is the priority in the queue,
             ;; (cdr item) is the edge.
             [e (cdr item)])
          (if (= (edge-y e) y)
              ;; found an edge pointing to y: it should not appear
              ;; in the result.
              (remove-target (cdr queue) y)
              ;; the current edge does not point to y: keep iterating.
              (cons item (remove-target (cdr queue) y))))))
                          
            
  ;; helper function for iterating until all vertices are added to
  ;; tree.
  ;; T is a list with the vertices already in the tree
  ;; A is a list with the vertices that are not in the tree yet.
  ;; Q is a priority queue of edges between vertices in T and vertices
  ;; in A, sorted by weight (low to high).
  ;; w is the weight of the tree built so far.
  ;; E is a list with the edges in the minimal tree, in the same
  ;; "list of lists" form as in the graph struct.
  (define (prim-aux T A Q w E)
    (cond
      ;; base case for the iteration: return what we found.
      [(null? A) (values (graph T E) w)]
      ;; sanity check
      [(null? Q) (error "Graph not connected!")]
      [else
       (let-values
           ;; e is going to be the next edge of the tree.
           ([(e Q-rest) (queue-pop Q)])
         (let*
             ([v (edge-y e)]
              [dw (edge-w e)]
              ;; reverse the edge e
              [er (edge v (edge-x e) dw)]
              ;; edges issuing from v, connecting to a vertex in A.
              [E-next
               (edges-with-target
                (list-ref (graph-edges G) v)
                A)]
              ;; remove all the elements that arrive in v from the queue.
              [Q-lean (remove-target Q-rest v)]
              [Q-next (extend-queue Q-lean E-next)]
              ;; update the edges of the minimal tree by adding e
              ;; at the root position
              [E-x (update-edges E e (edge-x e))]
              ;; update the edges of the minimal tree by adding (The reverse of) e
              ;; at the leaf position
              [E-y (update-edges E-x er (edge-y e))])
           (prim-aux (cons v T)  ;; v now becomes part of the tree.
                     (remove v A)
                     Q-next
                     (+ w dw)    ;; update the total tree weight
                     E-y)))]))

  ;; start the iteration.
  (prim-aux starting-vertex
            (remove starting-vertex (graph-vs G))
            (extend-queue (make-queue)
                          (list-ref (graph-edges G) starting-vertex))
            0
            (make-list n '())))


;; TODO enforce the "type" of starting-vertex to be
;; the same as the "type" of the vertices of the graph.
(provide (contract-out
          (minimum-tree-prim
           (->* (graph?)
                ;; optional arguments
                (#:starting-vertex any/c)
                ;; return values
                (values graph? number?)))))


(define (minimum-tree-kruskal G)
  ;; number of vertices
  (define n (length (graph-vs G)))
  (define vs (graph-vs G))
  (define edges (graph-edges G))
  ;; auxiliary function with the main logic:
  ;; S is the current partition of the vertices, stored as a list
  ;; of partitions.
  ;; w is the current weight,
  ;; Q is the queue of edges, sorted from lowest weight
  ;; to highest weight,
  ;; E are the edges of the minimal tree (in construction).
  (define (kruskal-aux S w Q E)
    (if (= (length S) 1)
        ;; algorithm terminates: build graph and return.
        (values (graph vs E) w)
        (let-values
            ;; e is the next edge that we need to add to the tree.
            ([(e Q-rest) (queue-pop Q)])
          (let
              ([dw (edge-w e)]
               ;; find the representative of the partition for the two
               ;; endpoints of the current edge e.
               [p1 (partition-find (edge-x e) S)]
               [p2 (partition-find (edge-y e) S)])
            (if (eq? p1 p2)
                ;; the edge is not relevant because it connects two vertices
                ;; which are already in the same partition: keep iterating.
                (kruskal-aux S w Q-rest E)
                ;; merge the two partitions and recur.
                (let*
                    ([S-next (merge-partitions S p1 p2)]
                     [E-x (update-edges E e (edge-x e))]
                     [E-next (update-edges E-x e (edge-y e))])
                  (kruskal-aux S-next
                               (+ w dw)
                               Q-rest
                               E-next)))))))
  ;; start iterating.
  (kruskal-aux (partition-from-list vs)
               0
               (extend-queue (make-queue)
                             ;; flatten edges
                             (foldl append '() edges))
               (make-list n '())))


;; TODO enforce the "type" of starting-vertex to be
;; the same as the "type" of the vertices of the graph.
(provide (contract-out
          (minimum-tree-kruskal
           (-> graph?
               ;; return values
               (values graph? number?)))))

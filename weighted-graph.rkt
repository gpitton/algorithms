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


;; simple priority queue.
(define (make-queue) '())
;; inserts an element el with priority w in the queue.
(define (queue-push queue el w)
  (let ([x (cons w el)])
    (cond [(null? queue) (list x)]
          [(< w (caar queue)) (cons x queue)]
          [else (cons (car queue)
                      (queue-push (cdr queue) el w))])))
;; inserts all the elements of items into the queue. 
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
;; set items are stored as a value-representative pair. The representative
;; is a representative that is used to identify the set.
(struct set-item (val repr))
;; we represent a partition of a set as a triple: representative (an element
;; of the set used to identify the partition, a pointer to the last item of
;; the partition, a list with the items in the set.
(struct partition (repr last items))
(define (make-partition x)
  (let ([el (set-item x x)])
    (partition el el (list el))))
(define (partition-find el p)
  (letrec ([items (partition-items p)]
           [repr (partition-repr p)]
           [find-aux
            (lambda (p)
              (cond [(null? p) #f]
                    [(eq? (set-item-val (car p)) el) repr]
                    [else (find-aux (cdr p))]))])
    (find-aux items)))
(define (partition-union p1 p2)
  (letrec
      ([items1 (partition-items p1)]
       [items2 (partition-items p2)]
       [repr1 (partition-repr p1)]
       [repr2 (partition-repr p2)]
       [tail1 (partition-last p1)]
       [tail2 (partition-last p2)]
       [merge-items
        ;; we accumulate the resulting list of items in p1
        ;; and the tail in last1.
        (lambda (p1 p2 last1 repr1)
          (if (null? p2) (values last1 p1)
              (let*
                  ([current-tail (car p2)]
                   [val (set-item-val current-tail)]
                   [next-tail (set-item val repr1)])
                (merge-items (append p1 (list next-tail))
                             (cdr p2)
                             next-tail
                             repr1))))]
       [union-aux
        (lambda (p1 p2)
          (cond ;[(null? items1) (values tail2 p2)] ;; useless check: the partition is never empty
            ;[(null? items2) (values tail1 p1)] ;; useleess check as above
            [(> (length items1) (length items2))
             ;; take the representative from p1 and append p2 to p1
             (merge-items p1 p2 tail1 repr1)]
            [else
             ;; take the representative from p2 and append p1 to p2
             (merge-items p2 p1 tail2 repr2)]))])
    ;; set up the recursion and construct a new partition struct
    ;; with the results.
    (let-values
        ([(merged-tail merged-items)
          (union-aux items1 items2)])
      (let
          ([repr (set-item-val (car merged-items))])
        (partition repr merged-tail merged-items)))))


;; experimental implementation of Prim's algorithm
;; for finding minimal spanning trees of weighted graphs.
(define (minimum-tree-prim G
                           #:starting-vertex [starting-vertex 0])
  ;; number of vertices
  (define n (length (graph-vs G)))
  
  #|
    ;; maximal weight
    (define maxw (for*/fold ([maxw (edge-w (caar (graph-edges graph)))])
                            ([edges (in-list (graph-edges graph))]
                             [e (in-list edges)])
                   (max (edge-w e) maxw)))
    |#
  
  ;; Updates the list of lists of edges E with element el in position n.
  (define (update-edges E el n)
    (cond [(null? E) '()]
          [(zero? n)
           (cons (cons el (car E)) (cdr E))]
          [else (cons (car E)
                      (update-edges (cdr E) el (sub1 n)))]))

  ;; returns a list with the edges from E that have
  ;; an element of A as target.
  (define (find-missing-edges E A)
    (cond [(null? E) '()]
          [(null? A) '()]
          [else
           (let ([el (car E)])
             (if (member (edge-y el) A)
                 (cons el (find-missing-edges (cdr E) A))
                 (find-missing-edges (cdr E) A)))]))

  ;; removes from queue all the edges that arrive in y.
  (define (remove-target queue y)
    (if (empty? queue)
        '()
        (let*
            ([item (car queue)]
             [e (cdr item)])
          (if (= (edge-y e) y)
              (remove-target (cdr queue) y)
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
    (cond [(empty? A) (values (graph T E) w)]
          [(empty? Q) (error "Graph not connected!")]
          [else
           (let-values
               ;; e is going to be the next edge of the tree.
               ([(e Q-rest) (queue-pop Q)])
             (let*
                 ([v (edge-y e)]
                  [dw (edge-w e)]
                  ;; reverse the edge e
                  [er (edge v (edge-x e) dw)]
                  ;; edges issuing from v, connecting a vertex in A.
                  [E-next
                   (find-missing-edges (list-ref (graph-edges G) v) A)]
                  ;; remove all the elements that arrive in v from the queue.
                  [Q-lean (remove-target Q-rest v)]
                  [Q-next (extend-queue Q-lean E-next)]
                  ;; update edges at the root position
                  [E-x (update-edges E e (edge-x e))]
                  ;; update edges at the leaf position
                  [E-y (update-edges E-x er (edge-y e))])
               (prim-aux (cons v T)  ;; v now becomes part of the tree.
                         (remove v A)
                         Q-next
                         (+ w dw)
                         E-y)))]))

  ;; start the algorithm
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


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
  
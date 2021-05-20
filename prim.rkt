#lang racket

;; experimental implementation of Prim's algorithm
;; for finding minimal spanning trees of weighted graphs.

(require rackunit)


;; x: from
;; y: to
;; w: weight
(struct edge (x y w)
  ;; needs to be transparent, or equal? will not work as expected.
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc edge port mode)
     (fprintf port
              "~a -- ~a, w: ~a;"
              (edge-x edge)
              (edge-y edge)
              (edge-w edge)))])


;; vs: list of vertices
;; edges: array, edges[v] is a list with the edges from v.
(struct graph (vs edges))


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


;; vertices for this example (taken from figure 6.3 in Skiena's book)
(define vertices '(0 1 2 3 4 5 6))
(define edges
  ;; edges that have vertex 0 as one of the endpoints
  (list (list (edge 0 1 7) (edge 0 2 4) (edge 0 3 2) (edge 0 4 5))
        ;; edges that have vertex 1 as one of the endpoints
        (list (edge 1 0 7) (edge 1 2 9) (edge 1 5 5))
        (list (edge 2 0 4) (edge 2 1 9) (edge 2 3 3) (edge 2 5 7) (edge 2 6 4))
        (list (edge 3 0 2) (edge 3 2 3) (edge 3 4 2))
        (list (edge 4 0 5) (edge 4 3 2))
        (list (edge 5 1 5) (edge 5 2 7) (edge 4 6 12))
        (list (edge 6 2 4) (edge 6 3 7) (edge 5 5 12))))


;; given a list of edges, return a list of edges without
;; duplicates, without minding about order (i.e. (edge x y w)
;; is considered to be the same as (edge y x w)).
(define (unique-edges l-edges)
  (define (unique-aux left seen)
    (if (null? left) seen
        (let*
            ([e (car left)]
             [er (edge (edge-y e) (edge-x e) (edge-w e))])
          (if (or (member e seen)
                  (member er seen))
              (unique-aux (cdr left) seen)
              (unique-aux (cdr left) (cons e seen))))))
  (unique-aux l-edges '()))
      

(define G (graph vertices edges))


(test-case
 "Test on a weighted graph where we know the minimal weight is 23."
 (let-values
     ([(tree w) (minimum-tree-prim G)])
   (check-equal? w 23)
   (printf "Minimum weight tree has weight: ~a\n" w)
   (printf "With edges:\n")
   (let ([u-edges (unique-edges (foldl append '() (graph-edges tree)))])
     (for ([e (in-list u-edges)])
       (printf "~a\n" e)))))


(test-case
 "The minimal weight should not change if we start from a different vertex."
 (for ([v0 (in-list (graph-vs G))])
   (let-values
       ([(tree w) (minimum-tree-prim G #:starting-vertex v0)])
     (check-equal? w 23))))

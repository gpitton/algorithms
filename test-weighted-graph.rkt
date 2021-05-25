#lang racket


(require rackunit)
(require "weighted-graph.rkt")


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


(test-case
 "Kruskal algorithm on a known graph."
 (let-values
     ([(tree w) (minimum-tree-kruskal G)])
   (check-equal? w 23)))

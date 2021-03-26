; -*- Mode: Lisp -*-

; mst.lisp

; Hash Tables

(defparameter *vertices* (make-hash-table :test #'equal))
(defparameter *arcs* (make-hash-table :test #'equal))
(defparameter *graphs* (make-hash-table :test #'equal))
(defparameter *visited* (make-hash-table :test #'equal))
(defparameter *vertex-keys* (make-hash-table :test #'equal))
(defparameter *previous* (make-hash-table :test #'equal))
(defparameter *heaps* (make-hash-table :test #'equal))
(defparameter *inf* MOST-POSITIVE-DOUBLE-FLOAT)

; Graph

(defun is-graph (graph-id)
  (gethash graph-id *graphs*))

(defun is-arc (graph-id vertex-id1 vertex-id2)
  (or
    (gethash (list 'arc graph-id vertex-id1 vertex-id2) *arcs*)
    (gethash (list 'arc graph-id vertex-id2 vertex-id1) *arcs*)
 nil))

(defun new-graph (graph-id)
  (or (gethash graph-id *graphs*)
      (setf (gethash graph-id *graphs*) graph-id)))

(defun new-vertex (graph-id vertex-id)
  (setf (gethash (list 'vertex graph-id vertex-id)
                 *vertices*)
        (list 'vertex graph-id vertex-id)))

(defun new-arc (graph-id vertex-id1 vertex-id2 &optional (weight 1))  
  (cond ((not (gethash (list 'vertex graph-id vertex-id1) *vertices*))
         (new-vertex graph-id vertex-id1)))
  (cond ((not (gethash (list 'vertex graph-id vertex-id2) *vertices*))
         (new-vertex graph-id vertex-id2)))
  (if (is-arc graph-id vertex-id1 vertex-id2)
      (and
       (or
        (remhash (list 'arc graph-id vertex-id1 vertex-id2) *arcs*)
        (remhash (list 'arc graph-id vertex-id2 vertex-id1) *arcs*))
       (setf (gethash (list 'arc graph-id vertex-id1 vertex-id2) *arcs*)
             (list 'arc graph-id vertex-id1 vertex-id2 weight)))
    (setf (gethash (list 'arc graph-id vertex-id1 vertex-id2) *arcs*)
             (list 'arc graph-id vertex-id1 vertex-id2 weight))))
  

(defun delete-graph (graph-id)
  (if (is-graph graph-id)
      (or (maphash (lambda (key value)
                     (and (equal (second key) graph-id)
                     (remhash value *vertices*)))
          *vertices*)
          (maphash (lambda (key value)
                     (and (equal (second key) graph-id)
                     (remhash value *arcs*)))
          *arcs*)
          (remhash graph-id *graphs*)))
  NIL)
             

(defun graph-vertices (graph-id)
  (let ((vertex-rep-list '()))
    (maphash (lambda (key value)
               (cond ((equal (second key) graph-id)
                    (push value vertex-rep-list))))
             *vertices*)
    vertex-rep-list))

(defun graph-arcs (graph-id)
  (let ((arc-rep-list '()))
    (maphash (lambda (key value)
               (cond ((equal (second key) graph-id)
                      (push value arc-rep-list))))
             *arcs*)
    arc-rep-list))

(defun graph-vertex-neighbors (graph-id vertex-id)
  (let ((arc-rep-list '()))
    (maphash (lambda (key value)
               (cond
                ((and 
                  (equal (second key) graph-id)
                  (or (equal (third key) vertex-id)
                      (equal (fourth key) vertex-id))
                  (push value arc-rep-list)))))
             *arcs*)
    arc-rep-list))

(defun graph-vertex-adjacent (graph-id vertex-id)
  (let ((vertex-rep-list '()))
    (maphash (lambda (key value)
               (cond
                ((or
                  (and
                   (equal
                    (third key)
                    vertex-id)
                   (push (list 'vertex graph-id (fourth value)) 
                         vertex-rep-list))
                  (and
                   (equal
                    (fourth key)
                    vertex-id)
                   (push (list 'vertex graph-id (third value)) 
                         vertex-rep-list))))))
             *arcs*)
    vertex-rep-list))


(defun graph-print (graph-id)
  (if (is-graph graph-id)
      (or (maphash (lambda (key value)
                     (if (equal (second key) graph-id)
                         (print value)))
          *vertices*)
          (maphash (lambda (key value)
                     (if(equal (second key) graph-id)
                         (print value)))
          *arcs*))))
    

; Min Heap

(defun new-heap (heap-id &optional (capacity 42))
  (or (gethash heap-id *heaps*)
      (setf (gethash heap-id *heaps*)
            (list 'heap heap-id 0 (make-array capacity :adjustable t)))))

(defun heap-delete (heap-id)
  (remhash heap-id *heaps*))

(defun heap-id (heap-rep)
  (second heap-rep))

(defun heap-size (heap-rep)
  (third heap-rep))

(defun heap-actual-heap (heap-rep)
  (fourth heap-rep))

(defun heap-capacity (heap-rep)
  (length (fourth heap-rep)))

(defun heap-empty (heap-id)
  (= 0 (heap-size (gethash heap-id *heaps*))))

(defun heap-not-empty (heap-id)
  (/= 0 (heap-size (gethash heap-id *heaps*))))

(defun heap-head (heap-id)
  (aref (heap-actual-heap (gethash heap-id *heaps*)) 0))

(defun heap-print (heap-id)
  (print (gethash heap-id *heaps*))t)

(defun heap-insert (heap-id k v)
  (let ((capacity (heap-capacity (gethash heap-id *heaps*)))
        (size (heap-size (gethash heap-id *heaps*))))
    (cond
     ((= size capacity)
      (adjust-array (heap-actual-heap (gethash heap-id *heaps*))
                    (+ (heap-capacity (gethash heap-id *heaps*))
                       (floor (* (heap-capacity (gethash heap-id *heaps*))
                                 1/2))) :initial-element nil)
      (setf
       (aref (heap-actual-heap (gethash heap-id *heaps*)) size)
       (list k v))
      (insert-prop-maintenance heap-id size k v)
      (increase-size (gethash heap-id *heaps*))))                    
    (cond
     ((< size capacity)
      (setf
       (aref (heap-actual-heap (gethash heap-id *heaps*)) size)
       (list k v))
      (insert-prop-maintenance heap-id size k v)
      (increase-size (gethash heap-id *heaps*)))))t)

(defun heap-extract (heap-id)
  (if (heap-not-empty heap-id)
       (let ((head (heap-head heap-id)))
          (if (> (heap-size (gethash heap-id *heaps*)) 1)
              (and
               (decrease-size (gethash heap-id *heaps*))
               (set-node heap-id 0 
                         (get-node heap-id 
                                   (heap-size (gethash heap-id *heaps*))))
               (set-node heap-id 
                         (heap-size 
                          (gethash heap-id *heaps*)) nil))
            (and
             (decrease-size (gethash heap-id *heaps*))
             (set-node heap-id 0 nil)))
          (heapify heap-id) head)))

(defun increase-size (heap-rep)
  (setf (third heap-rep) (+ (third heap-rep) 1)))

(defun decrease-size (heap-rep)
  (setf (third heap-rep) (- (third heap-rep) 1)))

(defun insert-prop-maintenance (heap-id pos key value)
  (if (and
       (< 0 pos)
       (> (first (get-node heap-id (father pos))) key))
      (and (set-node 
            heap-id pos
            (aref (heap-actual-heap 
                   (gethash heap-id *heaps*)) 
                  (father pos)))
           (insert-prop-maintenance heap-id (father pos) key value))
    (set-node heap-id pos (list key value))))
        
(defun father (i)
  (floor (/ (- i 1) 2)))

(defun get-node (heap-id index)
  (aref (heap-actual-heap (gethash heap-id *heaps*)) index))

(defun set-node (heap-id index value)
  (setf
   (aref (heap-actual-heap (gethash heap-id *heaps*)) index) value))

(defun heapify (heap-id)
  (let ((size (heap-size (gethash heap-id *heaps*))))
    (cond
     ((= size 1) t)
     ((= size 2) (simple-swap heap-id 0 1))
     ((> size 2) (multiple-swap heap-id 0 size)))))

(defun simple-swap (heap-id index1 index2)
  (let ((node1 (get-node heap-id index1))
        (node2 (get-node heap-id index2)))
    (cond
     ((> (first node1) (first node2))
      (set-node heap-id index1 node2)
      (set-node heap-id index2 node1)))))

(defun simple-swap-aux (heap-id index1 index2 index3)
  (let ((node1 (get-node heap-id index1))
        (node2 (get-node heap-id index2))
        (node3 (get-node heap-id index3)))
    (cond
     ((> (first node1) (first (check-min node2 node3)))
      (if (eq (check-min node2 node3) node2)
          (simple-swap heap-id index1 index2)
        (simple-swap heap-id index1 index3))))))
          
(defun multiple-swap (heap-id index1 size)
  (if (or
       (< (+ 1 (* 2 index1)) size)
       (< (+ 1 (+ 1 (* 2 index1))) size))
      (cond
       ((eq (first (get-node heap-id (+ 1 (* 2 index1)))) nil)
        (simple-swap heap-id index1 (+ 1 (+ 1 (* 2 index1)))))
       ((eq (first (get-node heap-id (+ 1 (+ 1 (* 2 index1))))) nil)
        (simple-swap heap-id index1 (+ 1 (* 2 index1))))
      ((< (first (get-node heap-id (+ 1 (* 2 index1))))
          (first (get-node heap-id (+ 1 (+ 1 (* 2 index1))))))
       (and
        (simple-swap-aux heap-id index1 (+ 1 (* 2 index1)) 
                         (+ 1 (+ 1 (* 2 index1))))
        (multiple-swap heap-id (+ 1 (* 2 index1)) size)))
      ((> (first (get-node heap-id (+ 1 (* 2 index1))))
          (first (get-node heap-id (+ 1 (+ 1 (* 2 index1))))))
       (and
        (simple-swap-aux heap-id index1 (+ 1 (* 2 index1)) 
                         (+ 1 (+ 1 (* 2 index1))))
        (multiple-swap heap-id (+ 1 (+ 1 (* 2 index1))) size))))))

(defun check-min (node2 node3)
  (if (< (first node2) (first node3))
      node2
    node3))

(defun heap-modify-key (heap-id new-key old-key v)
  (if (heap-not-empty heap-id)
      (and
       (set-node heap-id (get-pos heap-id 0 old-key v) (list new-key v))
       (insert-prop-maintenance heap-id 
                                (get-pos heap-id 0 new-key v) 
                                new-key v)
       (heapify heap-id))))
 
(defun get-pos (heap-id index k v)
  (if (not (= index (heap-capacity (gethash heap-id *heaps*))))
      (if (and
           (= (first (get-node heap-id index)) k)
           (equal (second (get-node heap-id index)) v))
          index
        (get-pos heap-id (+ index 1) k v))))

(defun get-key (heap-id index v)
  (if (= index (heap-capacity (gethash heap-id *heaps*)))
      nil
    (if (equal (second (aref (heap-actual-heap 
                              (gethash heap-id *heaps*)) 
                             index)) v)
        (first (aref (heap-actual-heap 
                      (gethash heap-id *heaps*)) index))
      (get-key heap-id (+ index 1) v))))

(defun check-ex (graph-id index v)
  (if (not (= index (heap-capacity (gethash graph-id *heaps*))))
      (if (and
           (equal v 
                  (second 
                   (aref 
                    (heap-actual-heap 
                     (gethash graph-id *heaps*)) index))))
          v
        (check-ex graph-id (+ index 1) v))))

; Mst

(defun mst-vertex-key (graph-id vertex-id)
  (if (is-graph graph-id)
      (gethash (list 'vertex-key graph-id vertex-id) *vertex-keys*)))

(defun mst-previous (graph-id vertex-id)
  (if (is-graph graph-id)
      (gethash (list 'previous graph-id vertex-id) *previous*)))

(defun print-previous (graph-id)
  (maphash #'
           (lambda (k v)
             (and
              (equal (second k)
                     graph-id)
              (print
               (list k v))))
           *previous*))

(defun print-vk (graph-id)
  (maphash #'
           (lambda (k v)
             (and
              (equal (second k)
                     graph-id)
              (print
               (list k v))))
           *vertex-keys*))

(defun mst-prim (graph-id source)
  (if (is-graph graph-id)
      (and
       (clrhash *previous*)
       (clrhash *vertex-keys*)
       (new-heap graph-id (length (graph-vertices graph-id)))
       (initialize graph-id source (graph-vertices graph-id))
       (prim-cicle graph-id (graph-vertices graph-id))
       (heap-delete graph-id))) NIL)

(defun initialize (graph-id source vertices)
  (cond
   ((null vertices) t)
   ((eq source (third (first vertices)))
    (and
     (heap-insert graph-id 0 source)
     (set-vertex-key graph-id source 0)
     (initialize graph-id source (rest vertices))))
   (t
    (and
     (heap-insert graph-id *inf* (third (first vertices)))
     (set-vertex-key graph-id (third (first vertices)) *inf*)
     (set-previous graph-id (third (first vertices)) -1)
     (initialize graph-id source (rest vertices))))))

(defun set-vertex-key (graph-id vertex-id new-key)
  (if (is-graph graph-id)
      (setf
       (gethash 
        (list 'vertex-key graph-id vertex-id) *vertex-keys*) new-key)))

(defun set-previous (graph-id vertex-id new-prev)
  (if (is-graph graph-id)
      (setf
       (gethash 
        (list 'previous graph-id vertex-id) *previous*) new-prev)))

(defun prim-cicle (graph-id vertices)
  (if (null vertices)
      t
    (let* ((head (heap-head graph-id))
          (new-vertices (remove 
                         (list 'vertex graph-id 
                               (second head))
                         vertices :test #'equal))
          (ext (heap-extract graph-id))
          (adjs (graph-vertex-neighbors graph-id (second head))))
      (relax graph-id ext adjs)
      (prim-cicle graph-id new-vertices))))

(defun relax (graph-id ext adjs)
  (if (null adjs)
      t
    (or
     (if (equal (third (first adjs)) (second ext))         
         (if (and
              (check-ex graph-id 0 (fourth (first adjs)))
              (< (fifth (first adjs)) 
                 (mst-vertex-key graph-id (fourth (first adjs)))))
             (and
              (set-previous graph-id 
                            (fourth (first adjs)) 
                            (second ext))
              (set-vertex-key graph-id 
                              (fourth (first adjs)) 
                              (fifth (first adjs)))
              (heap-modify-key 
               graph-id
               (fifth (first adjs))
               (get-key 
                graph-id 
                0 
                (fourth (first adjs)))
               (fourth (first adjs)))
              (relax graph-id ext (rest adjs)))))
     (if (equal (fourth (first adjs)) (second ext))
         (if (and
              (check-ex graph-id 0 (third (first adjs)))
              (< (fifth (first adjs)) 
                 (mst-vertex-key graph-id (third (first adjs)))))
             (and
              (set-previous graph-id (third (first adjs)) (second ext))
              (set-vertex-key graph-id 
                              (third (first adjs)) 
                              (fifth (first adjs)))
              (heap-modify-key 
               graph-id 
               (fifth (first adjs))
               (get-key 
                graph-id 
                0 
                (third (first adjs)))
               (third (first adjs)))
              (relax graph-id ext (rest adjs)))))
     (relax graph-id ext (rest adjs)))))

                                
(defun graph-vk (graph-id)
  (let ((vk-rep-list '()))
    (maphash (lambda (key value)
               (cond ((equal (second key) graph-id)
                      (push (list key value) vk-rep-list))))
             *vertex-keys*)
    vk-rep-list))

(defun sumk (graph-id)
  (let ((sum '()))
    (maphash (lambda (key value)
               (cond ((equal (second key) graph-id )
                      (push value sum))))
             *vertex-keys*)
    sum))

; end of file -*- mst.lisp
    
                  
           
              
   
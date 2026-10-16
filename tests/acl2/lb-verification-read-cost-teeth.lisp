; Cold verification reads one entry; an already marked current key reads none.
(in-package "ACL2")
(include-book "lb-zero-read-cost-teeth")
(include-book "../../books/log-verified-map-properties")
(defun-nx fn-lbcwt-warm-map ()
 (fn-lb-vmap-mark 1 6 (fn-lbzc-log) '(nil nil)))
(defthm fn-lbcwt-selected-row-zero
 (equal (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))
        '(:row 0 1 t "fn.test"))
 :rule-classes nil
 :hints (("Goal" :use fn-lbzc-native-selection-facts
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-select fn-nntp-session-group fn-nntp-session-current posp natp)))))
(defthm fn-lbcwt-warm-bit-positive
 (fn-lb-verified-bit 1 6 (fn-lbcwt-warm-map))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lb-vmap-mark-bit-effect
  (seg 1) (entry 6) (oldseg 1) (oldentry 6) (log (fn-lbzc-log)) (fn-lb-vmap '(nil nil))))
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   (union-theories (executable-counterpart-theory :here) '(fn-lbcwt-warm-map)))
   '((:executable-counterpart fn-lbcwt-warm-map) (:executable-counterpart fn-lb-vmap-mark))))))

; BEGIN verification read-count teeth
(defthm fn-lbcwt-cold-whole-positive
 (<= (fn-lbc-retrieval-entry-reads '(t "fn.test" 1 nil) nil nil :head nil nil 1 (fn-lbzc-log) '(nil nil) nil (fn-lbcc-test-one-state)) 1) :rule-classes nil
 :hints (("Goal" :use fn-lbzc-native-selection-facts :in-theory (theory 'ground-zero))))
(defthm fn-lbcwt-cold-double-whole-positive
 (and (<= (fn-lbc-retrieval-entry-reads '(t "fn.test" 1 nil) nil nil :head nil nil 1 (fn-lbzc-log) '(nil nil) nil (fn-lbcc-test-one-state)) 1) (not (<= (fn-lbzc-prefetch-entry-reads '(t "fn.test" 1 nil) :head 1 (fn-lbzc-log) '(nil nil) nil (fn-lbcc-test-one-state)) 1))) :rule-classes nil
 :hints (("Goal" :use fn-lbzc-native-selection-facts
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbzc-prefetch-entry-reads)))))
(defteeth fn-lbc-retrieval-at-most-one-entry-read
 :claim (nil (<= (fn-lbc-retrieval-entry-reads session archive arts kind args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 1)) :subject fn-lbc-retrieval
 :witness ((session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head) (args nil) (server nil) (v 1) (log (fn-lbzc-log)) (fn-lb-vmap-v '(nil nil)) (fn-arena-v nil) (fn-lbc-v (fn-lbcc-test-one-state))) :witness-lemma fn-lbcwt-cold-whole-positive :breaks ()
 :mutations ((duplicate-verification (:conclusion (<= (fn-lbzc-prefetch-entry-reads session kind v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 1)) ((session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head) (args nil) (server nil) (v 1) (log (fn-lbzc-log)) (fn-lb-vmap-v '(nil nil)) (fn-arena-v nil) (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "Read the whole entry once before the reader cold-verifies it again" :lemma fn-lbcwt-cold-double-whole-positive)))
(defthm fn-lbcwt-warm-whole-positive
 (and (fn-lb-verified-bit
   (fn-loc-segment (fn-lbc-loc0 (cadr (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))) (fn-lbcc-test-one-state))
                   (fn-lbc-loc1 (cadr (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))) (fn-lbcc-test-one-state)))
   (fn-loc-offset (fn-lbc-loc0 (cadr (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))) (fn-lbcc-test-one-state))
                  (fn-lbc-loc1 (cadr (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))) (fn-lbcc-test-one-state))) (fn-lbcwt-warm-map)) (equal (fn-lbc-retrieval-entry-reads '(t "fn.test" 1 nil) nil nil :head nil nil 1 (fn-lbzc-log) (fn-lbcwt-warm-map) nil (fn-lbcc-test-one-state)) 0)) :rule-classes nil
 :hints (("Goal" :use (fn-lbcwt-selected-row-zero fn-lbcwt-warm-bit-positive fn-lbcc-test-head-positive
  (:instance fn-lbc-retrieval-warm-no-entry-read (session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head) (args nil) (server nil) (v 1) (log (fn-lbzc-log)) (fn-lb-vmap-v (fn-lbcwt-warm-map)) (fn-arena-v nil) (fn-lbc-v (fn-lbcc-test-one-state))))
  :in-theory (theory 'ground-zero))))
(defthm fn-lbcwt-warm-prefetch-whole-positive
 (and (fn-lb-verified-bit
   (fn-loc-segment (fn-lbc-loc0 (cadr (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))) (fn-lbcc-test-one-state))
                   (fn-lbc-loc1 (cadr (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))) (fn-lbcc-test-one-state)))
   (fn-loc-offset (fn-lbc-loc0 (cadr (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))) (fn-lbcc-test-one-state))
                  (fn-lbc-loc1 (cadr (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))) (fn-lbcc-test-one-state))) (fn-lbcwt-warm-map)) (equal (fn-lbc-retrieval-entry-reads '(t "fn.test" 1 nil) nil nil :head nil nil 1 (fn-lbzc-log) (fn-lbcwt-warm-map) nil (fn-lbcc-test-one-state)) 0) (not (equal (fn-lbzc-prefetch-entry-reads '(t "fn.test" 1 nil) :head 1 (fn-lbzc-log) (fn-lbcwt-warm-map) nil (fn-lbcc-test-one-state)) 0))) :rule-classes nil
 :hints (("Goal" :use fn-lbcwt-warm-whole-positive
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbzc-prefetch-entry-reads)))))
(defthm fn-lbcwt-warm-bit-removal
 (and (not (fn-lb-verified-bit
   (fn-loc-segment (fn-lbc-loc0 (cadr (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))) (fn-lbcc-test-one-state))
                   (fn-lbc-loc1 (cadr (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))) (fn-lbcc-test-one-state)))
   (fn-loc-offset (fn-lbc-loc0 (cadr (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))) (fn-lbcc-test-one-state))
                  (fn-lbc-loc1 (cadr (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))) (fn-lbcc-test-one-state))) '(nil nil))) (not (equal (fn-lbc-retrieval-entry-reads '(t "fn.test" 1 nil) nil nil :head nil nil 1 (fn-lbzc-log) '(nil nil) nil (fn-lbcc-test-one-state)) 0))) :rule-classes nil
 :hints (("Goal" :use (fn-lbcwt-selected-row-zero fn-lbcc-test-head-positive fn-lbzc-native-selection-facts)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-verified-bit fn-lb-vmap-bits-get nth hons-assoc-equal)))))
(defteeth fn-lbc-retrieval-warm-no-entry-read
 :claim (((marked (fn-lb-verified-bit
   (fn-loc-segment (fn-lbc-loc0 (cadr (fn-lbc-select session kind args v fn-lbc-v)) fn-lbc-v)
                   (fn-lbc-loc1 (cadr (fn-lbc-select session kind args v fn-lbc-v)) fn-lbc-v))
   (fn-loc-offset (fn-lbc-loc0 (cadr (fn-lbc-select session kind args v fn-lbc-v)) fn-lbc-v)
                  (fn-lbc-loc1 (cadr (fn-lbc-select session kind args v fn-lbc-v)) fn-lbc-v)) fn-lb-vmap-v))) (equal (fn-lbc-retrieval-entry-reads session archive arts kind args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)) :subject fn-lbc-retrieval
 :witness ((session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head) (args nil) (server nil) (v 1) (log (fn-lbzc-log)) (fn-lb-vmap-v (fn-lbcwt-warm-map)) (fn-arena-v nil) (fn-lbc-v (fn-lbcc-test-one-state))) :witness-lemma fn-lbcwt-warm-whole-positive
 :breaks ((marked ((session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head) (args nil) (server nil) (v 1) (log (fn-lbzc-log)) (fn-lb-vmap-v '(nil nil)) (fn-arena-v nil) (fn-lbc-v (fn-lbcc-test-one-state))) :lemma fn-lbcwt-warm-bit-removal))
 :mutations ((unnecessary-verification (:conclusion (equal (fn-lbzc-prefetch-entry-reads session kind v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)) ((session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head) (args nil) (server nil) (v 1) (log (fn-lbzc-log)) (fn-lb-vmap-v (fn-lbcwt-warm-map)) (fn-arena-v nil) (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "Read a whole entry even though its current key is already marked" :lemma fn-lbcwt-warm-prefetch-whole-positive)))

(defun fn-lbcwt-native-cold-warm-control ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (ok fn-lbc)
   (with-local-stobj fn-lb-vmap
    (mv-let (ok fn-lb-vmap fn-lbc)
     (with-local-stobj fn-arena
      (mv-let (ok fn-arena fn-lb-vmap fn-lbc)
       (let* ((row (fn-lbcc-test-decided-row)) (log (fn-lbzc-log))
              (fn-arena (fn-arena-seal-list *fn-lbr13-payload* fn-arena))
              (fn-lbc (fn-lbc-open-rebuild (list row) log fn-lbc))
              (cold (fn-lbc-retrieval '(t "fn.test" 1 nil) nil nil :head nil nil 1 log fn-lb-vmap fn-arena fn-lbc))
              (fn-lb-vmap (fn-lb-vmap-mark 1 6 log fn-lb-vmap))
              (warm (fn-lbc-retrieval '(t "fn.test" 1 nil) nil nil :head nil nil 1 log fn-lb-vmap fn-arena fn-lbc))
              (line (fn-ag-car (fn-ag-cdr (fn-ag-car (fn-nntp-result-effects warm))))))
        (mv (and (equal cold warm) (fn-lb-verified-bit 1 6 fn-lb-vmap)
                 (equal (take 3 line) '(50 50 49))) fn-arena fn-lb-vmap fn-lbc))
       (mv ok fn-lb-vmap fn-lbc)))
     (mv ok fn-lbc))) ok)))
(with-guard-checking-event t (assert-event (fn-lbcwt-native-cold-warm-control)))

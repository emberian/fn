; Actual one-byte arena continuation maintains the complete source prefix.
(in-package "ACL2")
(include-book "legacy-parser-catalog")

(defthm fn-lpr-feed-append
  (equal (fn-lpc-feed (append a b) s)
         (fn-lpc-feed b (fn-lpc-feed a s)))
  :hints (("Goal" :induct (fn-lpc-feed a s)
           :in-theory (e/d (fn-lpc-feed) (fn-lpc-byte)))))

(local
 (defthm fn-lpr-take-successor
  (implies (and (natp pos) (< pos (len bytes)))
           (equal (take (+ 1 pos) bytes)
                  (append (take pos bytes) (list (nth pos bytes)))))
  :hints (("Goal" :induct (take pos bytes) :in-theory (enable take nth)))))

(defun fn-lpr-prefix-p (s h pin bytes)
 (declare (xargs :guard t :verify-guards nil))
 (let ((pos (fn-lpc-at 3 s)))
  (and (natp pos) (<= pos (len bytes))
       (equal s (fn-lpc-feed (take pos bytes)
                            (fn-lpc-begin h (len bytes) pin))))))

(defthm fn-lpr-begin-establishes-prefix
 (fn-lpr-prefix-p (fn-lpc-begin h (len bytes) pin) h pin bytes)
 :hints (("Goal" :in-theory (enable fn-lpr-prefix-p fn-lpc-begin fn-lpc-at take fn-lpc-feed))))

(local
 (defthm fn-lpr-prefix-source-coordinates
  (implies (fn-lpr-prefix-p s h pin bytes)
           (and (equal (fn-lpc-at 0 s) h)
                (equal (fn-lpc-at 1 s) (len bytes))
                (equal (fn-lpc-at 2 s) pin)))
  :hints (("Goal" :use ((:instance fn-lpv-feed-keeps-source-and-position
                     (bytes (take (fn-lpc-at 3 s) bytes))
                     (s (fn-lpc-begin h (len bytes) pin))))
           :in-theory (e/d (fn-lpr-prefix-p fn-lpc-begin fn-lpc-at)
                           (fn-lpc-feed fn-lpc-header-begin fn-lpc-header-bad
                            fn-lpv-feed-keeps-source-and-position))))))

(local
 (defthm fn-lpr-one-tick-shape
  (equal (mv-nth 0 (fn-lpc-tick s 1 fn-arena))
         (if (<= (fn-lpc-at 1 s) (fn-lpc-at 3 s)) s
           (fn-lpc-byte s (fn-arena-get (fn-lpc-at 0 s) (fn-lpc-at 3 s) fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-lpc-tick mv-nth)
                                        (fn-lpc-byte fn-lpc-at fn-lpc-verdict))))))
(local
 (defthm fn-lpr-feed-singleton
  (equal (fn-lpc-feed (list byte) s) (fn-lpc-byte s byte))
  :hints (("Goal" :in-theory (e/d (fn-lpc-feed) (fn-lpc-byte))))))

(defthm fn-lpr-one-tick-preserves-prefix
 (implies (and (fn-lpr-prefix-p s h pin bytes)
               (equal bytes (nth h fn-arena)))
          (fn-lpr-prefix-p (mv-nth 0 (fn-lpc-tick s 1 fn-arena)) h pin bytes))
 :hints (("Goal"
          :use (fn-lpr-prefix-source-coordinates
                (:instance fn-lpr-take-successor (pos (fn-lpc-at 3 s)))
                (:instance fn-lpr-feed-append
                  (a (take (fn-lpc-at 3 s) bytes))
                  (b (list (nth (fn-lpc-at 3 s) bytes)))
                  (s (fn-lpc-begin h (len bytes) pin))))
          :in-theory (e/d (fn-lpr-prefix-p)
                          (fn-lpc-byte fn-lpc-at fn-lpc-begin fn-lpc-verdict
                           fn-lpr-feed-append fn-lpv-feed-keeps-source-and-position
                           fn-lpc-tick fn-lpc-feed nth take len
                           fn-lpr-prefix-source-coordinates fn-lpr-take-successor)))))

(local
 (defthm fn-lpr-feed-take-length-by-definition
  (equal (fn-lpc-feed (take (len bytes) bytes) s) (fn-lpc-feed bytes s))
  :hints (("Goal" :induct (fn-lpc-feed bytes s)
           :in-theory (e/d (fn-lpc-feed take) (fn-lpc-byte fn-lpr-take-successor fn-lpr-feed-append fn-lpr-feed-singleton))))))

(defthm fn-lpr-terminal-prefix-is-complete-feed
 (implies (and (fn-lpr-prefix-p s h pin bytes)
               (not (equal (fn-lpc-verdict s) :yield)))
          (equal s (fn-lpc-feed bytes (fn-lpc-begin h (len bytes) pin))))
 :rule-classes nil
 :hints (("Goal" :use fn-lpr-prefix-source-coordinates
          :in-theory (e/d (fn-lpr-prefix-p fn-lpc-verdict)
                          (fn-lpc-feed fn-lpc-at fn-lpc-begin fn-lpc-byte
                           fn-lpr-prefix-source-coordinates
                           fn-lpv-feed-keeps-source-and-position nth take len)))))

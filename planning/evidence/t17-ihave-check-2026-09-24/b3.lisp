(progn
(defun pixb-scan (k m node) (declare (xargs :mode :program)) (if (zp k) nil (prog2$ (fn-peer-history-hasp m node) (pixb-scan (1- k) m node))))
(defun pixb-trie (k m node trie arts) (declare (xargs :mode :program)) (if (zp k) nil (prog2$ (fn-pix-history-hasp m node trie arts) (pixb-trie (1- k) m node trie arts))))
(defconst *pixb-a120* (pixb-arts 120 nil)) (defconst *pixb-n120* (pixb-node *pixb-a120*)) (defconst *pixb-t120* (fn-midx-build *pixb-a120*))
(defconst *pixb-a1000* (pixb-arts 1000 nil)) (defconst *pixb-n1000* (pixb-node *pixb-a1000*)) (defconst *pixb-t1000* (fn-midx-build *pixb-a1000*))
(defconst *pixb-a10000* (pixb-arts 10000 nil)) (defconst *pixb-n10000* (pixb-node *pixb-a10000*)) (defconst *pixb-t10000* (fn-midx-build *pixb-a10000*)))

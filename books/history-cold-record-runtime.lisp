; Full borrowed-node byte controller. No whole source conversion or pool read.
(in-package "ACL2")
(include-book "history-decoded-octet-scan")
(include-book "history-normalized-span")

; phase, pending tasks, child, original node, capture, lease, prefix,
; active node, remaining opaque count. All node/source references are borrowed.
(defun fn-hrcur-cold-state (phase tasks child prefix node count c)
  (declare (xargs :guard t))
  (list phase tasks child (fn-hrcur-field 3 c)
        (fn-hrcur-field 4 c) (fn-hrcur-field 5 c) prefix node count))

(defun fn-hrcur-cold-begin (source capture lease)
  (declare (xargs :guard t))
  (if (and (fn-hrcur-widthp source 2) (eq (car source) :decoded))
      (list :work (list (list :node (cadr source))) nil (cadr source)
            capture lease nil nil 0)
    (list :refused nil nil nil capture lease nil nil 0)))

(defun fn-hrcur-cold-countp (x)
  (declare (xargs :guard t))
  (and (natp x) (< x *fn-hrcur-u64-bound*)))

(defun fn-hrcur-cold-symbol-childp (child)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-hdsn-statep)))))
  (and (fn-hdsn-statep child)
       (fn-hrcur-cold-countp (fn-hrcur-field 1 child))
       (fn-hrcur-cold-countp (fn-hrcur-field 2 child))
       (fn-hrcur-cold-countp (fn-hrcur-field 4 child))
       (natp (fn-hrcur-field 5 child))
       (<= (fn-hrcur-field 5 child) 12250)))

(defun fn-hrcur-cold-demand (position kind serial)
  (declare (xargs :guard t))
  (list :need-byte position kind serial))

(defun fn-hrcur-cold-tick (c)
  (declare (xargs :guard t))
  (let* ((phase (fn-hrcur-field 0 c)) (tasks (fn-hrcur-field 1 c))
         (child (fn-hrcur-field 2 c)) (capture (fn-hrcur-field 4 c))
         (lease (fn-hrcur-field 5 c)) (prefix (fn-hrcur-field 6 c))
         (node (fn-hrcur-field 7 c)) (count (fn-hrcur-field 8 c)))
    (cond
     ((not (fn-hrcur-widthp c 9)) (mv '(:refused :cold-cursor) nil c))
     ((eq phase :work)
      (cond
       ((null tasks) (mv :prepared nil
                         (fn-hrcur-cold-state :done nil nil nil nil 0 c)))
       ((not (consp tasks)) (mv '(:refused :cold-tasks) nil c))
       (t
        (let* ((task (car tasks)) (tag (fn-hrcur-field 0 task))
               (x (fn-hrcur-field 1 task)) (kind (fn-hrcur-field 0 x))
               (skip (fn-hrcur-field 2 task)) (rest (cdr tasks)))
          (cond
           ((and (eq tag :byte) (fn-scc-octetp x))
            (mv :emit x (fn-hrcur-cold-state :work rest nil nil nil 0 c)))
           ((not (member-eq tag '(:node :no-octets)))
            (mv '(:refused :cold-task) nil c))
           ((eq kind :atom)
            (mv :continue nil
                (fn-hrcur-cold-state :scalar rest
                  (fn-hrsc-begin (fn-hrcur-field 1 x) capture lease) nil x 0 c)))
           ((eq kind :pair)
            (if (eq tag :node)
                (mv :continue nil
                    (fn-hrcur-cold-state :classify rest
                      (fn-hrcur-dos-begin x capture lease) nil x 0 c))
              (if (fn-hrcur-cold-countp skip)
                  (mv :continue nil
                    (fn-hrcur-cold-state :work
                      (cons (list :node (fn-hrcur-field 1 x))
                        (cons (if (< 0 skip)
                                  (list :no-octets (fn-hrcur-field 2 x) (1- skip))
                                (list :node (fn-hrcur-field 2 x)))
                          (cons '(:byte 5) rest))) nil nil nil 0 c))
                (mv '(:refused :cold-skip) nil c))))
           ((eq kind :span)
            (let ((op (fn-hrcur-field 1 x)) (pkg (fn-hrcur-field 2 x))
                  (off (fn-hrcur-field 3 x)) (n (fn-hrcur-field 4 x)))
              (cond
               ((and (equal op 4) (member-equal pkg '(0 1 2))
                     (fn-hrcur-cold-countp off) (fn-hrcur-cold-countp n)
                     (< (+ off n) *fn-hrcur-u64-bound*))
                (mv :continue nil
                    (fn-hrcur-cold-state :symbol rest
                      (fn-hdsn-begin pkg off n) nil x 0 c)))
               ((member-equal op '(3 6))
                (mv :continue nil
                    (fn-hrcur-cold-state :span rest
                      (fn-hrcur-span-begin op pkg off n capture lease) nil x 0 c)))
               (t (mv '(:refused :cold-span) nil c)))))
           (t (mv '(:refused :cold-node) nil c)))))))
     ((eq phase :classify)
      (mv-let (v next) (fn-hrcur-dos-tick child)
        (cond
         ((eq v :continue)
          (mv :continue nil (fn-hrcur-cold-state phase tasks next nil node 0 c)))
         ((and (consp v) (eq (fn-hrcur-field 0 v) :need-byte))
          (mv (fn-hrcur-cold-demand (fn-hrcur-field 1 v) :octet-nil
                 (fn-hrcur-field 4 (fn-hrcur-field 4 child))) nil c))
         ((and (consp v) (eq (fn-hrcur-field 0 v) :done) (eq (fn-hrcur-field 1 v) :octets)
               (fn-hrcur-cold-countp (fn-hrcur-field 2 v)) (< 0 (fn-hrcur-field 2 v)))
          (mv :continue nil
              (fn-hrcur-cold-state :opaque-prefix tasks nil
                (cons 6 (fn-scc-nat-octets (fn-hrcur-field 2 v))) node (fn-hrcur-field 2 v) c)))
         ((and (consp v) (eq (fn-hrcur-field 0 v) :done) (eq (fn-hrcur-field 1 v) :not-octets))
          (mv :continue nil
              (fn-hrcur-cold-state :work
                (cons (list :no-octets node (fn-hrcur-field 3 child)) tasks)
                nil nil nil 0 c)))
         (t (mv v nil (fn-hrcur-cold-state :refused tasks next nil node 0 c))))))
     ((eq phase :opaque-prefix)
      (cond ((and (consp prefix) (fn-scc-octetp (car prefix)))
             (mv :emit (car prefix)
                 (fn-hrcur-cold-state phase tasks nil (cdr prefix) node count c)))
            ((null prefix)
             (mv :continue nil
                 (fn-hrcur-cold-state :opaque tasks nil nil node count c)))
            (t (mv '(:refused :cold-prefix) nil c))))
     ((eq phase :opaque)
      (cond
       ((not (fn-hrcur-cold-countp count)) (mv '(:refused :cold-count) nil c))
       ((equal count 0)
        (mv :continue nil (fn-hrcur-cold-state :work tasks nil nil nil 0 c)))
       ((and (eq (fn-hrcur-field 0 node) :pair)
             (eq (fn-hrcur-field 0 (fn-hrcur-field 1 node)) :atom)
             (fn-scc-octetp (fn-hrcur-field 1 (fn-hrcur-field 1 node))))
        (mv :emit (fn-hrcur-field 1 (fn-hrcur-field 1 node))
            (fn-hrcur-cold-state :opaque tasks nil nil
              (fn-hrcur-field 2 node) (1- count) c)))
       ((and (eq (fn-hrcur-field 0 node) :span)
             (equal (fn-hrcur-field 1 node) 6)
             (fn-hrcur-cold-countp (fn-hrcur-field 3 node))
             (equal count (fn-hrcur-field 4 node))
             (< (+ (fn-hrcur-field 3 node) count) *fn-hrcur-u64-bound*))
        (mv :continue nil
            (fn-hrcur-cold-state :opaque-span tasks (fn-hrcur-field 3 node)
              nil node count c)))
       (t (mv '(:refused :cold-opaque) nil c))))
     ((eq phase :opaque-span)
      (cond ((not (and (fn-hrcur-cold-countp count)
                       (fn-hrcur-cold-countp child)))
             (mv '(:refused :cold-opaque-span) nil c))
            ((equal count 0)
             (mv :continue nil (fn-hrcur-cold-state :work tasks nil nil nil 0 c)))
            (t (mv (fn-hrcur-cold-demand child :opaque-span child) nil c))))
     ((and (eq phase :symbol) (fn-hrcur-cold-symbol-childp child))
      (mv-let (v next) (fn-hdsn-tick child)
        (cond
         ((eq v :continue)
          (mv :continue nil (fn-hrcur-cold-state phase tasks next nil node 0 c)))
         ((and (consp v) (eq (fn-hrcur-field 0 v) :need-byte))
          (mv (fn-hrcur-cold-demand (fn-hrcur-field 1 v) :symbol-normalize (fn-hrcur-field 2 v)) nil c))
         ((and (consp v) (eq (fn-hrcur-field 0 v) :done))
          (mv :continue nil
              (fn-hrcur-cold-state :span tasks
                (fn-hrcur-ns-begin (fn-hrcur-field 1 v) (fn-hrcur-field 3 node)
                  (fn-hrcur-field 4 node) capture lease) nil node 0 c)))
         (t (mv v nil (fn-hrcur-cold-state :refused tasks next nil node 0 c))))))
     ((member-eq phase '(:scalar :span))
      (mv-let (v byte next)
        (if (eq phase :scalar) (fn-hrsc-tick child) (fn-hrcur-span-tick child))
        (cond
         ((eq v :prepared)
          (mv :continue nil (fn-hrcur-cold-state :work tasks nil nil nil 0 c)))
         ((member-eq v '(:continue :emit))
          (mv v byte (fn-hrcur-cold-state phase tasks next nil node 0 c)))
         ((and (eq phase :span) (consp v) (eq (fn-hrcur-field 0 v) :need-byte))
          (mv (fn-hrcur-cold-demand (fn-hrcur-field 1 v) :span-body (fn-hrcur-field 1 v)) nil c))
         (t (mv v nil (fn-hrcur-cold-state :refused tasks next nil node 0 c))))))
     ((eq phase :done) (mv :prepared nil c))
     (t (mv '(:refused :cold-cursor) nil c)))))

(defun fn-hrcur-cold-supply (c position byte)
  (declare (xargs :guard t))
  (let ((phase (fn-hrcur-field 0 c)) (tasks (fn-hrcur-field 1 c))
        (child (fn-hrcur-field 2 c)) (node (fn-hrcur-field 7 c))
        (count (fn-hrcur-field 8 c)))
    (cond
     ((not (fn-hrcur-widthp c 9)) (mv '(:refused :cold-response) nil c))
     ((eq phase :classify)
      (mv-let (v next) (fn-hrcur-dos-supply child position byte)
        (if (eq v :continue)
            (mv :continue nil (fn-hrcur-cold-state phase tasks next nil node 0 c))
          (mv v nil c))))
     ((and (eq phase :symbol) (fn-hrcur-cold-symbol-childp child)
           (fn-hrcur-cold-countp position) (fn-scc-octetp byte))
      (mv-let (v next) (fn-hdsn-supply position (fn-hrcur-field 5 child) byte child)
        (if (eq v :continue)
            (mv :continue nil (fn-hrcur-cold-state phase tasks next nil node 0 c))
          (mv v nil c))))
     ((eq phase :span)
      (mv-let (v b next) (fn-hrcur-span-supply child position byte)
        (if (eq v :emit)
            (mv v b (fn-hrcur-cold-state phase tasks next nil node 0 c))
          (mv v nil c))))
     ((and (eq phase :opaque-span) (fn-hrcur-cold-countp count) (< 0 count)
           (fn-hrcur-cold-countp child) (equal position child)
           (< (+ 1 child) *fn-hrcur-u64-bound*) (fn-scc-octetp byte))
      (mv :emit byte
          (fn-hrcur-cold-state phase tasks (+ 1 child) nil node (1- count) c)))
     (t (mv '(:refused :cold-response) nil c)))))

(in-theory (disable fn-hrcur-cold-state fn-hrcur-cold-begin fn-hrcur-cold-countp
                    fn-hrcur-cold-symbol-childp fn-hrcur-cold-demand
                    fn-hrcur-cold-tick fn-hrcur-cold-supply))

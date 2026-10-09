(in-package "ACL2")
(include-book "../../books/owner-readers-transitions")
(include-book "../../books/defkeystone")
(defteeth fn-ordr-capture-composition-by-definition
  :claim (() (equal (fn-ordr-capture r event current)
                    (list (fn-ocv-capture (fn-ordr-views r) event current) (fn-ordr-cache r))))
  :subject fn-ordr-capture
  :witness ((r '(nil access-cache)) (event :start) (current 'durable-view))
  :breaks ()
  :mutations ((stale-views (:conclusion (equal (fn-ordr-capture r event current) r))
              ((r '(nil access-cache)) (event :start) (current 'durable-view))
              :fault "capture must install the durable view before draining")))
(defteeth fn-ordr-cache-install-frames-views
  :claim (() (equal (fn-ordr-views (fn-ordr-cache-install r cache)) (fn-ordr-views r)))
  :subject fn-ordr-cache-install
  :witness ((r '((durable next) old-cache)) (cache 'new-cache))
  :breaks ()
  :mutations ((drops-capture (:conclusion
                (equal (fn-ordr-views (fn-ordr-cache-install r cache)) nil))
              ((r '((durable next) old-cache)) (cache 'new-cache))
              :fault "cache replacement must not release a held reader view")))
(defteeth fn-ordr-index-kind-composition-by-definition
  :claim (() (equal (fn-ordr-index-kind r) (if (consp (fn-ordr-views r)) :d :current)))
  :subject fn-ordr-index-kind
  :witness ((r '((durable next) cache)))
  :breaks ()
  :mutations ((always-current (:conclusion (equal (fn-ordr-index-kind r) :current))
              ((r '((durable next) cache)))
              :fault "a held D view must not select the working publication")))
(assert-event (equal (fn-ordr-index-kind (fn-ordr-initial)) :current))
(assert-event (equal (fn-ordr-capture '((durable next) cache) :complete 'working)
                     '((next) cache)))
(assert-event (equal (fn-ordr-capture '((durable next) cache) :unnext 'working)
                     '((durable) cache)))
(assert-event (equal (fn-ordr-capture '((durable) cache) :drop 'working) '(nil cache)))
(defteeth-check (fn-ordr-capture-composition-by-definition
                fn-ordr-cache-install-frames-views
                fn-ordr-index-kind-composition-by-definition))

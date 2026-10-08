(local
 (defthm fn-ocp-gc-seal-held-scheduler-fields
  (implies (and (fn-ocp-gc-linkedp x) (equal (nth 4 x) :drain)
                (not (fn-otm-held (nth 1 x))))
   (let* ((y (fn-ocp-gc-seal x nil frames))
          (e (case (nth 4 y) (:intents :started-held) (:idle :started-none-held)))
          (s (mv-nth 1 (fn-otm-held-event (nth 1 x) e))))
    (implies e
     (and (equal (fn-otm-phase-of s) (fn-otm-phase-of (nth 1 y)))
          (equal (fn-otm-next-of s) (fn-otm-next-of (nth 1 y)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-otm-held-event-is-the-held-step
                            (s (nth 1 x)) (event :started-held))
                 (:instance fn-otm-held-event-is-the-held-step
                            (s (nth 1 x)) (event :started-none-held)))
           :in-theory
           (e/d (fn-ocp-gc-seal fn-ocp-gc-linkedp fn-och-step)
                (fn-otm-held-event fn-otm-held-event-is-the-held-step
                 fn-otm-disk fn-otm-clock fn-ocp-gc-seal-extent fn-ocvm-make
                 fn-lgk-pipe-make fn-lgc-of fn-lg-append-admitsp))))))
(local
 (defthm fn-ocp-gc-seal-held-preserves-linkedp
  (implies (fn-ocp-gc-linkedp x) (fn-ocp-gc-linkedp (fn-ocp-gc-seal-held x frames)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ocp-gc-seal-held-scheduler-fields)
                 (:instance fn-ocp-gc-seal-preserves-linkedp (nextp nil)))
           :in-theory (e/d (fn-ocp-gc-seal-held)
                           (fn-ocp-gc-seal fn-ocp-gc-linkedp
                            fn-otm-held-event
                            fn-ocp-gc-seal-held-scheduler-fields))))))

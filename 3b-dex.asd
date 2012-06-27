(defsystem :3b-dex
  :description "Common Lisp .dex file manipulation library"
  :depends-on ("ieee-floats"
               "flexi-streams"
               "alexandria"
               ;"chipz" "salza2"
               )
  :components ((:file "package")
               (:file "dex")))

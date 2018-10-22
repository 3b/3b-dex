(defsystem :3b-dex
  :description "Common Lisp .dex file manipulation library"
  :depends-on ("ieee-floats"
               "flexi-streams"
               "alexandria"
               "babel"
               ;"chipz" "salza2"
               )
  :serial t
  :components ((:file "package")
               (:file "util")
               (:file "opcodes")
               (:file "dex")
               (:file "write-dex")
               (:file "abxml")))


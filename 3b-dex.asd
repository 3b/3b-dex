(defsystem :3b-dex
  :description "Common Lisp .dex file manipulation library"
  :depends-on ("ieee-floats"
               "flexi-streams"
               "alexandria"
               "babel"
               "3b-dex/build"
               "ironclad" ;; for adler32 checksum
               ;"chipz" "salza2"
               )
  :serial t
  :components ((:file "package")
               (:file "util")
               (:file "opcodes")
               (:file "dex")
               (:file "write-dex")
               (:file "abxml")))



(defsystem :3b-dex/build
  :description "utilities for running external android SDK tools"
  :depends-on ("uiop" "alexandria" "cl-ppcre")
  :serial t
  :components ((:file "build")
               (:file "build-asdf")))

(in-package #:3b-dex/build)
#++(ql:quickload "3bil2-sample")
(defclass resource-dir (asdf:module)
  ((apk-name :initform "apk" :initarg :apk :Reader apk)
   (manifest :initform "AndroidManifest.xml"
             :initarg :manifest :Reader manifest)
   (resource-package :initarg :resource-package :reader resource-package)))

(defmethod asdf:component-relative-pathname ((c resource-dir))
  "")

(defmethod unsigned-apk (r)
  (format nil "~a.unsigned.apk" (apk r)))
(defmethod signed-apk (r)
  (format nil "~a.apk" (apk r)))

(defmethod asdf:additional-input-files ((op asdf:compile-op) (r resource-dir))
  (print
   (list*
    (manifest r)
    (loop for i in (directory (format nil "~a/~a/**/*.*"
                                      (asdf:component-pathname r)
                                      (asdf:component-name r)))
          unless (or (uiop:directory-pathname-p i)
                     (alexandria:ends-with #\~ (pathname-type i))
                     (alexandria:ends-with #\~ (pathname-name i)))
            collect i))))

(defmethod asdf:output-files ((op asdf:compile-op) (r resource-dir))
  (format t "~&output-files ~s ->~%"
          (asdf:input-files op r))
  (print
   (append (list "ids.tmp.txt")
           (loop with base = (format nil "~a/~a/"
                                     (asdf:component-pathname r)
                                     (asdf:component-name r))
                 for .i in (cdr (asdf:input-files op r)) ;; skip manifest
                 for i = (enough-namestring .i base)
                 for flat = (format nil "~a.flat"
                                    (cl-ppcre:regex-replace-all "[\\/]" i "_"))
                 ;; values/*.xml get different output file name
                 when (or (alexandria:starts-with-subseq "values_" flat))
                   collect (cl-ppcre:regex-replace ".xml.flat$"
                                                   flat ".arsc.flat")
                 else
                   collect flat)
           (list (unsigned-apk r)))))

(defmethod asdf:perform ((op asdf:compile-op) (r resource-dir))
  (format t "~&perform compile op~%")
  (let* ((base (asdf:component-pathname r))
         (in (asdf:input-files op r))
         (manifest (pop in))
         (out (asdf:output-files op r))
         (id-file (pop out))
         (in2))
    (loop for i in in
          for o = (pop out)
          do (push (uiop:native-namestring o) in2)
             (compile-resource (uiop:native-namestring
                                i)
                               (uiop:native-namestring
                                (uiop:pathname-directory-pathname o))))
    (format t "compiling ~s~% -> ~s~%" in out)
    (format t "path=~s,~%find-path = ~s~%" base (asdf:component-find-path r))
    (link-resources* in2
                     (uiop:native-namestring (first out))
                     ;; manifest is in same dir as resource dir, not
                     ;; inside it... probably should rearrange things a
                     ;; bit to clean this up
                     (uiop:native-namestring
                      (merge-pathnames manifest
                                       (asdf:component-pathname
                                        (asdf:component-parent r))))
                     :id-file (uiop:native-namestring id-file))))

(defmethod asdf:perform ((op asdf:load-op) (r resource-dir))
  (format t "perform load op~%")
  (when (resource-package r)
    (let ((ids (first (asdf:input-files op r))))
      (with-open-file (f ids)
        (funcall
         (find-symbol "ENSURE-RESOURCE-CLASSES"
                      (find-package "3BIL2"))
         (resource-package r)
         (loop for l = (read-line f nil f)
               until (eql l f)
               collect (cl-ppcre:register-groups-bind (s v)
                           ("^[^:]+:([^ ]+) = 0x([a-f0-9]+)$" l)
                         (when (and s v)
                           (list (string-upcase s)
                                 (parse-integer v :radix 16))))))))))



;; make accessible as :3b-dex-resource-dir in defsystem
(setf (find-class 'asdf::3b-dex-resource-dir)
      (find-class 'resource-dir))

;; asdf component for building classes.dex

(defclass classes-dex (asdf:module)
  ((apk-name :initform nil :initarg :apk :Reader apk)
   (sign :initform nil :initarg :sign :Reader sign)))

(defmethod asdf:component-relative-pathname ((c classes-dex))
  "")

(defmethod asdf:output-files ((op asdf:compile-op) (r classes-dex))
  (list* "classes.dex"
         (when (apk r)
           (list* (unsigned-apk r)
                  (when (sign r)
                    (list (signed-apk r)))))))

(defun classes (c)
  ;; for now just using component name as name of package, and
  ;; treating all exported symbols as names of classes to dump...
  (let* ((n (asdf:component-name c))
         (p (find-package (string-upcase n)))
         (c nil))
    (do-external-symbols (s p)
      (push s c))
    c))

(defmethod asdf:perform ((op asdf:compile-op) (r classes-dex))
  (format t "Write dex file ~s~% ~s~%" (asdf:output-files op r) (classes r))
  (let* ((df (apply (find-symbol "LINK-DEX-FILE" :3bil2)
                    (classes r)))
         (out (asdf:output-files op r))
         (o (pop out))
         (apk (pop out))
         (signed-apk (pop out)))
    (with-open-file (f o :direction :io :element-type '(unsigned-byte 8)
                         :if-exists :supersede :if-does-not-exist :create)
      (funcall (find-symbol "WRITE-DEX-FILE" :3b-dex)
               df f))
    (when apk
      (add-to-apk (uiop:native-namestring
                   (uiop:pathname-directory-pathname apk))
                  (uiop:native-namestring apk)
                  "classes.dex")
      (when (sign r)
        (uiop:copy-file apk signed-apk)
        (sign-apk (uiop:native-namestring signed-apk))))))


;; make accessible as :3b-dex-classes in defsystem
(setf (find-class 'asdf::3b-dex-classes)
      (find-class 'classes-dex))

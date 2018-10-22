(defvar *sdk-dir* "d:/android/sdk/")
(defvar *sdk-build-tools-dir* (format nil "~abuild-tools/28.0.3/" *sdk-dir*))
(defvar *aapt2* (format nil "~aaapt2" *sdk-build-tools-dir*))
(defvar *apksigner* (merge-pathnames "lib/apksigner.jar"
                                     *sdk-build-tools-dir*))
(defvar *java* "d:/Android/Android Studio/jre/bin/java")
(defvar *android.jar* (format nil "~a/platforms/android-28/android.jar" *sdk-dir*))
(defvar *keystore*
  (loop for i in (list (uiop:getenv "USERPROFILE")
                       (uiop:getenv "HOME"))
        when (probe-file (format nil "~a/.android/debug.keystore" i))
          return it))
(defvar *keystore-pass* "android") ;; password for debug keystore is "android"

(defvar *zip* "c:/msys64/usr/bin/zip")

;; http://developer.android.com/tools/publishing/app-signing.html#debugmode
;; keytool -genkey -v -keystore debug.keystore -storepass android -alias androiddebugkey -keypass android -keyalg RSA -keysize 2048 -validity 10000

(defun compile-resource (filename out-dir)
  (print (multiple-value-list
          (uiop:run-program
           (print
            (list *aapt2* "compile" (uiop:native-namestring filename)
                  "-o" (uiop:native-namestring out-dir)))
           :force-shell nil :output :string
           :error-output :output))))

(defun compile-resources (res-dir out-dir)
  (ensure-directories-exist out-dir)
  (loop for i in (directory (merge-pathnames "**/*.*" res-dir))
        for o = (uiop:pathname-directory-pathname
                 (merge-pathnames (enough-namestring i res-dir) out-dir))
        unless (or (uiop:directory-pathname-p i)
                   (alexandria:ends-with #\~ (pathname-type i))
                   (alexandria:ends-with #\~ (pathname-name i)))
          do (compile-resource i out-dir)))

(defun link-resources (compiled-res-dir out-apk manifest
                       &key id-file)
  (let ((command (list* *aapt2* "link"
                        "-o" out-apk
                        "-I" *android.jar*
                        "--manifest" manifest
                        (append
                         (when id-file
                           (list "--emit-ids" id-file))
                         (map 'list 'uiop:native-namestring
                              (directory
                               (merge-pathnames "**/*.flat"
                                                compiled-res-dir)))))))
    (ensure-directories-exist out-apk)
    (print
     (uiop:run-program (print command) :force-shell nil :output :string
                                       :error-output :output
                                       :ignore-error-status t))))

(defun sign-apk (apk)
  (let ((command (list *jre*
                       "-jar"
                       (uiop:native-namestring *apksigner*)
                       "sign" "--ks" (uiop:native-namestring *keystore*)
                       "--ks-pass" (format nil "pass:~a" *keystore-pass*)
                       apk)))
    (print
     (uiop:run-program (print command) :force-shell nil :output :string
                                       :error-output :output
                                       :ignore-error-status t))))

(defun add-to-apk (base-dir apk &rest relative-paths)
  (uiop:with-current-directory (base-dir)
    (print
     (uiop:run-program (print
                        (list* *zip*
                               "-j"
                               apk
                               relative-paths))
                       :force-shell nil :output :string
                       :error-output :output
                       :ignore-error-status t))))

(defun build-apk (path apk-name dex
                  &key (res-dir "res/") (build-dir "build/")
                    (manifest "AndroidManifest.xml"))
  (let ((*default-pathname-defaults* (pathname path)))
    (uiop:with-current-directory (path)
      (compile-resources res-dir build-dir)
      (link-resources build-dir apk-name manifest)
      (with-open-file (s "classes.dex" :element-type '(unsigned-byte 8)
                                       :direction :io :if-exists :supersede
                                       :if-does-not-exist :create)
        (3b-dex::write-dex-file dex s))
      (add-to-apk path apk-name "classes.dex")
      (sign-apk apk-name))))

#++
(compile-resources "/tmp/tmp-app/res/" "c:/tmp/tmp-app/build/")
#++
(link-resources "c:/tmp/tmp-app/build/"  "c:/tmp/tmp-app/build.apk"
                "c:/tmp/tmp-app/AndroidManifest.xml"
                :id-file "/tmp/tmp-app/foo.ids")
#++
(add-to-apk "c:/tmp/tmp-app/" "build.apk" "classes.dex")
#++
(sign-apk "c:/tmp/tmp-app/build.apk")

#++
(time
 (build-apk "/tmp/tmp-app/" "hello.apk" 3b-dex::*f*))

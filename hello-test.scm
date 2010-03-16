(use-modules (ice-9 rdelim))
(for-each (lambda (i)
            (write (with-input-from-file "/home/neil/google-neil.csv"; "hello.txt"
                     (lambda ()
                       (set-port-encoding! (current-input-port) "UTF16LE")
                       (read-line))))
            (newline))
          (iota 5))


#lang racket

(require c
         consynth/lang/load
         consynth/lang/pprint)

(define mini-cprogram (parse-program (open-input-file "mini.c")))

(for-each (lambda (forstmt) (display (sprintc forstmt))) (loops mini-cprogram))


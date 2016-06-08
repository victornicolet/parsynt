#lang racket

(require c
         consynth/frontc/check
         consynth/frontc/loops
         consynth/frontc/pprint)

(define mini-cprogram (parse-program (open-input-file "exc1.c")))

(for-each (lambda (forstmt) (display (sprintc forstmt))) (loops mini-cprogram))


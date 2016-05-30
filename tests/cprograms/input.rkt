#lang racket

(require c
         consynth/lang/load)

(define mini-cprogram (parse-program (open-input-file "mini.c")))

(extract-for-loops '() mini-cprogram)

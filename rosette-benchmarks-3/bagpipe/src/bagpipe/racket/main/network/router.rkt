#lang racket

(require "../util/util.rkt")

(provide router-internal router-external injected 
         router-addr internal? external? injected?)

(define (router-internal ip) `(Router internal ,ip))
(define (router-external ip) `(Router external ,ip))
(define (injected) `(Injected))

(define (router-addr c) (third c))
(define (internal? c) (rosette-eq? 'internal (second c)))
(define (external? c) (rosette-eq? 'external (second c)))
(define (injected? c) (rosette-eq? c `(Injected)))

# GeoCoq
A formalization of geometry in Coq based on Tarski's axiom system

## About

This is a formalization of geometry using a simplified version of Tarski's axiom system. The development contains a formalization of the chapters 1-15 of the book "Metamathematische Methoden in der Geometrie" by W. Schwabhäuser, W. Szmielew and A. Tarski. The development focus on 2D geometry although results up to chapter 9  included are formalized in any dimension.
The first eleven chapters and a large part of Chapter 13 are developed without the parallel postulate and hence constitute a library for neutral geometry.

This includes:
 betweeness properties, 
 congruence properties, 
 the construction of the midpoint without any continuity axiom,
 perpendicular lines,
 point reflection,
 parallelism,
 Pappus theorem,
 Desargues theorem (Hessenberg's proof), ...

From this low-level results we derived some well-known theorems:
 Orthocenter's theorem,
 Gravity center's theorem,
 triangle midpoints theorem,
 Euler line,
 Varignon's theorem,
 properties of quadrilaterals...


This development can serve as a base for studying axiomatic foundations of geometry:
 We proved that Hilbert axioms can be derived from Tarski's axioms.  We also formalized the simplification of the axiom system proposed by Timothy Makarios: "A further simplification of Tarski's axioms of geometry" (http://arxiv.org/abs/1306.0066).
 We also proved that Tarski's axiom system is classically equivalent to a constructive version proposed by Michael Beeson (http://www.michaelbeeson.com/research/papers/AxiomatizingConstructiveGeometry.pdf).

We have removed classical logic from the developpement. 
We also have proven the equivalence between 10 versions of the parallel postulate.

## Members:

- Pierre Boutry
- Gabriel Braun
- Julien Narboux

## Related publications:
- Mechanical Theorem Proving in Tarski's geometry in the post-proceeding of ADG 2006, F. Botana and T. Recio (Eds.), LNAI 4869, pages 139-156, 2007.
http://hal.inria.fr/inria-00118812/PDF/adg06-narboux.pdf
- From Tarski to Hilbert, Sep 2012, Edinburgh, United Kingdom. Springer, Proceedings of ADG 2012, 7993, pp. 89-109, LNCS. 
http://hal.inria.fr/hal-00727117/PDF/adg2012_braun_narboux_final.pdf
- Using small scale automation to improve both accessibility and readability of formal proofs in geometry, in informal proceedgins of ADG 2014.
https://hal.inria.fr/hal-00989781v2/document
- A short note about case distinctions in Tarski’s geometry, in informal proceedings of ADG 2014.
https://hal.inria.fr/hal-00989785v2/document
- A synthetic proof of Pappus' theorem in Tarski's geometry, submitted 2015.
- Parallel postulates and decidability of intersection of lines: a mechanized study within Tarski's system of geometry, submitted 2015.

This direcotry contains the detailed AFP submission of the
"Featherweight OCL" semantics for OCL as well as our proposal
for Appendix A of the OCL standard.

Beyond the standard mechanism 

(* < *)
<<skipped isar text, not shown in doc >>
(* > *)

The two main targes of this Isabelle project are:
- check everything and generate all documents allowing "sorry"'s, i.e., 
  using Isabelles "quick-and-dirty"-mode:

  isabelle build -c -d . -v -b OCL-dirty

- check everything and generate all documents, ensurign that
   no "sorry"'s are used:

   isabelle build -c -d . -v -b OCL

In your LaTeX text, you can use the following two PlainTeX
environments for selectin in which version your text should
appear:

\isatagafp
  This text will only be visible in the AFP submission, i.e.,
  document.pdf and outline.pdf.
\endisatagafp

\isatagannexa
  This text will only be visible in the Annex A, i.e., annex-a.pdf.
\endisatagannexa


Note that these tags only work within regular Isabelle/Isar "text"
commands if they are complete, i.e.:

  text {* ... \isatagafp ... \endisatagafp ...*}

Only opening or closing such a tag in Isabelle/Isar "text" commands
will not work. For this, you need ot use the "text_raw" command:

  text_raw {* \isatagafp *}
  ...
  text_raw {* \endisatagafp *}


Warning:
=======
Please check twice that you are using \isatagX and \endisatagX
properly, i.e.,
- allways pairwise matching
- not separating other envirments.
Not using these PlainTeX environments (which are, generally,
obsolete and discouraged but used by the Isabelle LaTeX setup
anyhow. We only use them to avoid introducing a parallel setup to
the one that we cannot avoid due to design decisions by the
Isabelle maintainer) carefully, will result in LaTeX errors that
are close to not debug-able.

(******************************************************************************
 * Isabelle/C
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

chapter \<open>Appendices\<close>

(*<*)
theory C_Appendices_draft
  imports Isabelle_C_examples.C1
          "~~/src/Doc/Isar_Ref/Base"
begin

section \<open>A Guide to Implement Semantic Back-Ends for Isabelle/C\<close>

subsection \<open>General Principles\<close>

subsection \<open>Example: Citadelle\<close> (* HOL-OCL back-end *)

subsection \<open>Example: Clean\<close>

subsection \<open>Example: AutoCorres\<close>

section \<open>Known Limitation and Future Work\<close>
subsection \<open>The Document Model of the Isabelle/PIDE (applying for Isabelle 2019)\<close>
subsubsection \<open>The Document Model\<close>

text \<open> In this part, we explain why for the case of \<^theory_text>\<open>ML_file\<close>, it
is only the first level of reference which is triggered (e.g., files referred in formal comments in
the source included by \<^theory_text>\<open>ML_file\<close> behave as
\<^theory_text>\<open>ML\<close>). \<close>

text \<open> As remarkable feature of the document model, we can cite its capability to manage the
edition changes on an overall collection of theory documents in an implicit automatic way. Indeed,
any modifications occurring on one document node are all automatically scheduled to be at some point
propagated to other nodes depending on it. This is a task highly dynamic, particularly happening
during the edition activity.

In more detail, when the user is firstly about to start Isabelle/jEdit to load a specific theory
file, there is actually an initial step of resolving phase determining a first graph version of the
total documents to load (\<^file>\<open>~~/src/Pure/PIDE/document.ML\<close>). Later, this graph has
the potential to be further refined, depending on if new theory files are explicitly requested to be
added or removed. Consequently, we can already observe how this ML part of the system has been
fine-implemented to support such sort of dynamic influx.

In practice however, there is no way that user-programmed extensions can do to exploit implicit
dependencies between sub-documents. Indeed, we do not think false to affirm that the respective
implementation part of \<^file>\<open>~~/src/Pure/PIDE/document.ML\<close> has been enough
thoughtfully designed to handle sub-documents dependencies. On the other hand, it does not look
totally trivial to ultimately get a public ML API able to dynamically load and remove new document
nodes, through explicit on-demand requests, particularly at command execution time (like having a
dynamic version of \<^file>\<open>~~/src/Pure/PIDE/protocol.ML\<close>). \<^footnote>\<open>Also,
for optimal performance reasons, we would be better interested in a pure solution in ML whenever
this is ever feasible. Indeed, this is to be aligned with how the C-like commands
(\<^theory_text>\<open>C\<close> and \<^theory_text>\<open>C_file\<close>) are optimized in their
implementations. (Even if they are initially derived from Haskell, we are dealing in the end with
some raw translated ML code.)\<close> In comparison, the best situation currently handled by the
prover IDE is the possibility of tracking (arbitrary) files, but at the cost of mandatorily
involving first the user make any files of interests be loaded in the editor. (As remark, there are
multiple ways of making a file be loaded in the editor, this does not necessarily mean to open it
using one most accustomed way.) On the contrary, the limitation case pointed here at command
execution time is slightly more general:
  \<^item> The number of files wished to be opened or closed can not be solely determined from the
  sole information contained in the static theory file, where the C command is written.
  \<^item> The final list of files to be opened or closed might result from the execution of an
  arbitrary ML code, more specifically, when that code is executed when the system is internally
  joining in parallel other consecutive commands. As an example, conditional directives illustrate
  the case of dynamically generating a list of several files to include \<^C>\<open>#if _
    #include <file1>
  #else
    #include <file2>
    #include <file3>
  #endif\<close>.
\<close>

section \<open>Acknowledgments\<close>

(*<*)
end
(*>*)

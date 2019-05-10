(******************************************************************************
 * Generation of Language.C Grammar with ML Interface Binding
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

(*<*)
theory C_Intro
  imports C_DOF
begin

open_monitor*[this::article] 
declare[[strict_monitor_checking=false]]
(*>*)
(*
title*[tit::title]\<open>Deeply Integrating C11-Code Support into Isabelle/PIDE\<close> 
text*
[fred::author, email="''ftuong@lri.fr''", affiliation="\<open>LRI, Université Paris-Saclay\<close>", http_site="\<open>https://www.lri.fr/~ftuong/\<close>"]
\<open>Frédéric Tuong\<close>
text*
[bu::author, email= "''wolff@lri.fr''", affiliation = "\<open>LRI, Université Paris-Saclay\<close>", http_site="\<open>https://www.lri.fr/~wolff/\<close>"]
\<open>Burkhart Wolff\<close>

(**)

section*[intro::introduction]\<open> Introduction \<close> 
text*[introtext::introduction]
\<open>Recent successes like the Microsoft Hypervisor project @{cite "DBLP:conf/fm/LeinenbachS09"},
the verified CompCert compiler @{cite "DBLP:journals/cacm/Leroy09"}
and the seL4 microkernel @{cite "klein:sel4" and "DBLP:journals/tocs/KleinAEMSKH14"} 
show that the verification of low-level systems code has become feasible.
However, a closer look at the underlying verification engines  
VCC@{cite "DBLP:conf/tphol/CohenDHLMSST09"}, 
or Isabelle/AutoCorres@{cite "DBLP:conf/pldi/GreenawayLAK14"}
show that the road is still bumpy: in particular the  empirical cost evaluation  
of @{cite "DBLP:journals/tocs/KleinAEMSKH14"} reveals that a very substantial part 
of the overall effort of about one third of the 28 man years went into the development 
of libraries and the tool-chain itself. @{cite "DBLP:journals/tocs/KleinAEMSKH14"} expresses 
the hope that these were overall investments, that will, once done, not have to be repeated for 
``similar projects''.

However, none of these verifying compiler tool-chains capture all aspects of ``real life'' 
programming languages such as C. The variety of supported language fragments seem to contradict 
the assumption that we will all converge to one comprehensive tool-chain soon; There are so many 
different choices concerning memory models, non-standard control-flow, and execution models 
that a generic framework is desirable, in which verified compilers, deductive verification, 
static analysis and test-techniques (such as @{cite "DBLP:conf/tap/Keller18"}, 
@{cite "DBLP:conf/itp/AissatVW16"}) can be developed and used inside the Isabelle platform.

In this paper, we present such a generic framework in spirit similar to Frama-C 
@{cite "frama-c-home-page"}. In  contrast to the latter, however, it is deeply integrated into the 
Isabelle/PIDE @{cite "DBLP:conf/itp/Wenzel14"}  document model and offers, based on the C11 
standard (ISO/IEC 9899:2011), a parser, IDE-support using static scoping as well as the usual 
parallel evaluation techniques for SML-based, user-programmed extensions in Isabelle. 
The genericity allows for "plugged-in" concrete semantic representations available in 
Isabelle/HOL@{cite "nipkow.ea:isabelle:2002"}
such as AutoCorres@{cite "DBLP:conf/pldi/GreenawayLAK14"},  IMP2@{cite "IMP2-AFP"}, 
ORCA@{cite "bockenek:hal-02069705"}, and CLEAN@{footnote \<open>Part of the HOL-TestGen distribution 
\<^url>\<open>https://www.brucker.ch/projects/hol-testgen/\<close>.\<close>}. This also includes
generic support of semantic annotations controlled by specific semantic plug-ins.
Our framework is sufficiently reactive to be usable for C sources such as the seL4 project 
(we discuss their C-parsing tests in @{docitem \<open>c-tests\<close>}) 
--- although this depends, of course, of the computational load of the semantic back-ends being 
plugged in. Our framework supports annotations for multiple backends. \<close>

figure*
["C-sample"::figure,relative_width="60",src="''figures/A-C-Source''"]
\<open>A C11 Sample in Isabelle/jedit\<close>

text\<open> @{figure \<open>C-sample\<close>} shows our new \verb+C+-command, that analogously to the existing
\verb+ML+-command allows for editing C-sources. Inside the \inlineisar+\<Open> .. \<Close>+ brackets, 
C-code is parsed on the fly in a "continuous check, continuous build" manner. A parsed source 
is colorated according to the usual conventions for variables and keywords. A static scoping 
analysis makes the bindings inside the source explicit such that editing gestures like hovering 
and clicking may allow the user to reveal the applying or defining variable occurrences as well 
as C-level type information.\<close>

text\<open>Our framework allows for the deep integration of the C-source into a global document in which 
literate programming style documentation, modeling as well as static program analysis and verification 
co-exist.  In particular, information from the different tools realized as plugins in the Isabelle 
platform  can flow freely. This increases greatly the development agility of such type of sources 
and may be  attractive to  conventional developers, in particular when targeting a formal certification 
@{cite "DBLP:conf/mkm/BruckerACW18"}. \<close>
(*<*)
declare_reference*[background::text_section]
declare_reference*[annotations::text_section]
declare_reference*[backends::text_section]
declare_reference*[conclusion::text_section]
(*>*)
text\<open>This paper proceeds as follows: In the @{docitem (unchecked) \<open>background\<close>} section, we will briefly 
introduce Isabelle/PIDE and its document model, into which our framework is integrated. In the subsequent 
sections, we will discuss the build process (relevant for developers of similar front-ends, not 
end-users) and present some experimental results on the integrated parser. The handling of 
semantic annotations comments --- a vital part for back-end developers --- is discussed in 
@{docitem (unchecked) \<open>annotations\<close>}, while in @{docitem (unchecked) \<open>backends\<close>} we present some
techniques to integrate back-ends into our framework at hand of examples.
\<close>
*)
(*<*)
end
(*>*)
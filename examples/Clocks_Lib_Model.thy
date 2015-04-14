(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Clocks_Lib_Model.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Sud, France
 *               2013-2015 IRT SystemX, France
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
(* $Id:$ *)

header{* Part ... *}

theory   Clocks_Lib_Model
imports
  "../src/UML_OCL"
begin

Class Clock
  Attributes created_at : Real
  Operations after(c : Clock) : Boolean
  Operations equal(c : Clock) : Boolean

Class WorldClock < Clock
  Operations elapse() 
             Pre : "true"
  
Class DiscreteClock < Clock
  Operations create() 
             Post: "self .oclIsNew() and 
                    (self .created_at) \<doteq>
                    (((WorldClock .allInstances(WorldClock)) ->any()) .created_at)"
  Operations get_time() : Integer
             Post: "result \<doteq> (((WorldClock .allInstances(WorldClock)) ->any() .created_at)->asInt\<^sub>R\<^sub>e\<^sub>a\<^sub>l())
                               -\<^sub>i\<^sub>n\<^sub>t 
                               ((self .created_at) ->asInt\<^sub>R\<^sub>e\<^sub>a\<^sub>l())" 


Class PeriodicDiscreteClock < DiscreteClock
  Attributes period : Integer
  Operations create_period_clock(p : Integer)
             Pre : "\<zero> \<le>\<^sub>i\<^sub>n\<^sub>t p"
             Post: "self .period \<doteq> p"

Class ContClock < Clock
  Operations create() 
             Pre : "true"
             Post: "self .oclIsNew() and 
                    self .created_at \<doteq> ((WorldClock .allInstances(WorldClock)) 
                                                     ->any() .created_at).time"
  Operations get_time() : Real
             Post: "result \<doteq> (((WorldClock .allInstances(WorldClock)) ->any() .created_at)
                               -\<^sub>r\<^sub>e\<^sub>a\<^sub>l 
                               (self .created_at))" 

Class PeriodicContClock < Clock
  Attributes periode : Real
  Operations create_period_clock(p : Real)
             Pre : "\<zero> \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l p"
             Post: "self .periode \<doteq> p"

Context c: GlobalTime
  Inv "GlobalTime .allInstances(GlobalTime) ->size() \<doteq> \<one>"

lemmas [simp,code_unfold] = dot_accessor

end

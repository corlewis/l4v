(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)
chapter \<open>\label{h:dataportbase}Example -- Dataports\<close>
(*<*)
(* THIS FILE IS AUTOMATICALLY GENERATED. YOUR EDITS WILL BE OVERWRITTEN. *)
theory GenDataportBase
imports "../Types" "../Abbreviations" "../Connector"
begin
(*>*)

text \<open>
  This section provides an example of generated types and definitions derived
  from a \camkes dataport interface. The following example system is used
  throughout this section:

  \camkeslisting{dataport.camkes}

  Note that this system also, unlike the previous two examples, contains a
  component type that is instantiated twice.
\<close>

subsection \<open>\label{ssec:dataportbase}Generated Base Theory\<close>

subsubsection \<open>\label{sssec:dataportbasetypes}Types\<close>
text \<open>
  As with the previous examples, a type is generated for the connections in the
  system and the component instances in the system. The data type,
  @{term channel}, is as before, but @{term inst} also contains a member
  generated for each connection in the system involving a dataport.
\<close>

datatype channel
  = simple2
  | simple1

datatype inst
  = comp2
  | comp1
  | simple2\<^sub>d
  | simple1\<^sub>d

text \<open>
  The type for the interfaces of the single component in the system is
  generated as in the previous examples.
\<close>

datatype DataportTest_channel
  = DataportTest_d2
  | DataportTest_d1

subsubsection \<open>\label{sssec:dataportbaseprim}Interface Primitives\<close>
text \<open>
  For each dataport interface of each component type, definitions are generated
  for performing a read or write to the dataport. Like events, the details of
  these operations can be determined statically and are captured in the
  definitions, @{term MemoryRead} and @{term MemoryWrite}.

  Read and write are unconditionally generated for each dataport interface
  because all dataports are read/write memory regions. Should the \camkes model
  be extended to allow read-only or write-only dataports only the relevant
  single operation would be generated here.
\<close>

definition
  Read_DataportTest_d2 :: "(DataportTest_channel \<Rightarrow> channel) \<Rightarrow>
    ('cs local_state \<Rightarrow> nat) \<Rightarrow>
    ('cs local_state \<Rightarrow> variable \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
  "Read_DataportTest_d2 ch addr embed_data \<equiv>
    MemoryRead (ch DataportTest_d2) addr embed_data"

definition
  Write_DataportTest_d2 :: "(DataportTest_channel \<Rightarrow> channel) \<Rightarrow>
    ('cs local_state \<Rightarrow> nat) \<Rightarrow> ('cs local_state \<Rightarrow> variable) \<Rightarrow>
    (channel, 'cs) comp"
where
  "Write_DataportTest_d2 ch addr proj \<equiv>
    MemoryWrite (ch DataportTest_d2) addr proj"

definition
  Read_DataportTest_d1 :: "(DataportTest_channel \<Rightarrow> channel) \<Rightarrow>
    ('cs local_state \<Rightarrow> nat) \<Rightarrow>
    ('cs local_state \<Rightarrow> variable \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
 "Read_DataportTest_d1 ch addr embed_data \<equiv>
   MemoryRead (ch DataportTest_d1) addr embed_data"

definition
  Write_DataportTest_d1 :: "(DataportTest_channel \<Rightarrow> channel) \<Rightarrow>
    ('cs local_state \<Rightarrow> nat) \<Rightarrow> ('cs local_state \<Rightarrow> variable) \<Rightarrow>
    (channel, 'cs) comp"
where
  "Write_DataportTest_d1 ch addr proj \<equiv>
    MemoryWrite (ch DataportTest_d1) addr proj"

subsubsection \<open>\label{sssec:dataportbaseinst}Instantiations of Primitives\<close>
text \<open>
  The specialisation of the primitives from \autoref{sssec:dataportbaseprim} is
  similar to the previous examples, except that multiple instantiations for
  each are generated because the component type @{term DataportTest} is
  instantiated twice in this system.
\<close>

definition
  Read_comp2_d2 :: "('cs local_state \<Rightarrow> nat) \<Rightarrow>
    ('cs local_state \<Rightarrow> variable \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
  "Read_comp2_d2 \<equiv>
    Read_DataportTest_d2 (\<lambda>c. case c of DataportTest_d1 \<Rightarrow> simple2
                                      | DataportTest_d2 \<Rightarrow> simple1)"

definition
  Write_comp2_d2 :: "('cs local_state \<Rightarrow> nat) \<Rightarrow>
    ('cs local_state \<Rightarrow> variable) \<Rightarrow> (channel, 'cs) comp"
where
  "Write_comp2_d2 \<equiv>
    Write_DataportTest_d2 (\<lambda>c. case c of DataportTest_d1 \<Rightarrow> simple2
                                       | DataportTest_d2 \<Rightarrow> simple1)"

definition
  Read_comp2_d1 :: "('cs local_state \<Rightarrow> nat) \<Rightarrow>
    ('cs local_state \<Rightarrow> variable \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
  "Read_comp2_d1 \<equiv>
    Read_DataportTest_d1 (\<lambda>c. case c of DataportTest_d1 \<Rightarrow> simple2
                                      | DataportTest_d2 \<Rightarrow> simple1)"

definition
  Write_comp2_d1 :: "('cs local_state \<Rightarrow> nat) \<Rightarrow>
    ('cs local_state \<Rightarrow> variable) \<Rightarrow> (channel, 'cs) comp"
where
  "Write_comp2_d1 \<equiv>
    Write_DataportTest_d1 (\<lambda>c. case c of DataportTest_d1 \<Rightarrow> simple2
                                       | DataportTest_d2 \<Rightarrow> simple1)"

definition
  Read_comp1_d2 :: "('cs local_state \<Rightarrow> nat) \<Rightarrow>
    ('cs local_state \<Rightarrow> variable \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
  "Read_comp1_d2 \<equiv>
    Read_DataportTest_d2 (\<lambda>c. case c of DataportTest_d2 \<Rightarrow> simple2
                                      | DataportTest_d1 \<Rightarrow> simple1)"

definition
  Write_comp1_d2 :: "('cs local_state \<Rightarrow> nat) \<Rightarrow>
    ('cs local_state \<Rightarrow> variable) \<Rightarrow> (channel, 'cs) comp"
where
  "Write_comp1_d2 \<equiv>
    Write_DataportTest_d2 (\<lambda>c. case c of DataportTest_d2 \<Rightarrow> simple2
                                       | DataportTest_d1 \<Rightarrow> simple1)"

definition
  Read_comp1_d1 :: "('cs local_state \<Rightarrow> nat) \<Rightarrow>
    ('cs local_state \<Rightarrow> variable \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
  "Read_comp1_d1 \<equiv>
    Read_DataportTest_d1 (\<lambda>c. case c of DataportTest_d2 \<Rightarrow> simple2
                                      | DataportTest_d1 \<Rightarrow> simple1)"

definition
  Write_comp1_d1 :: "('cs local_state \<Rightarrow> nat) \<Rightarrow>
    ('cs local_state \<Rightarrow> variable) \<Rightarrow> (channel, 'cs) comp"
where
  "Write_comp1_d1 \<equiv>
    Write_DataportTest_d1 (\<lambda>c. case c of DataportTest_d2 \<Rightarrow> simple2
                                       | DataportTest_d1 \<Rightarrow> simple1)"

(*<*)
end
(*>*)

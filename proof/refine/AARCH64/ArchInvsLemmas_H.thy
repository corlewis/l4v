(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInvsLemmas_H
imports
  Invariants_H
begin

context Arch begin arch_global_naming

named_theorems Invariants_H_pspaceI_assms

(* FIXME arch-split: word_size is available outside of Arch due to Word_Setup, but to provide
   more guard rails during arch-split we are hiding the Haskell constant definition outside of
   Arch. To be evaluated as arch-split proceeds, since it can always be made generic again. *)
schematic_goal wordBits_def': "wordBits = numeral ?n" (* arch-specific consequence *)
  by (simp add: wordBits_def word_size)

lemmas wordRadix_def' = wordRadix_def[simplified]

lemma wordSizeCase_simp[simp]: "wordSizeCase a b = b"
  by (simp add: wordSizeCase_def wordBits_def word_size)

lemmas objBits_defs = tcbBlockSizeBits_def epSizeBits_def ntfnSizeBits_def cteSizeBits_def vcpuBits_def
lemmas untypedBits_defs = minUntypedSizeBits_def maxUntypedSizeBits_def
lemmas objBits_simps = objBits_def objBitsKO_def word_size_def archObjSize_def
lemmas objBits_simps' = objBits_simps objBits_defs

lemma frame_at'_pspaceI:
  "frame_at' p sz d s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> frame_at' p sz d s'"
  by (simp add: frame_at'_def typ_at'_def ko_wp_at'_def ps_clear_def)

lemma valid_cap'_pspaceI[Invariants_H_pspaceI_assms]:
  "s \<turnstile>' cap \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> s' \<turnstile>' cap"
  unfolding valid_cap'_def
  by (cases cap)
     (auto intro: obj_at'_pspaceI[rotated]
                  cte_wp_at'_pspaceI valid_untyped'_pspaceI
                  typ_at'_pspaceI[rotated] frame_at'_pspaceI[rotated]
            simp: vspace_table_at'_defs valid_arch_cap'_def valid_arch_cap_ref'_def
           split: arch_capability.split zombie_type.split option.splits)

(* FIXME arch-split: required since valid_arch_obj' takes state due to other arches *)
lemma valid_arch_obj'_pspaceI:
  "\<lbrakk>valid_arch_obj' obj s; ksPSpace s = ksPSpace s'\<rbrakk> \<Longrightarrow> valid_arch_obj' obj s'"
  unfolding valid_arch_obj'_def
  by simp

lemma valid_obj'_pspaceI[Invariants_H_pspaceI_assms]:
  "valid_obj' obj s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> valid_obj' obj s'"
  unfolding valid_obj'_def
  by (cases obj)
     (auto simp: valid_ep'_def valid_ntfn'_def valid_tcb'_def valid_cte'_def
                 valid_tcb_state'_def valid_bound_tcb'_def
                 valid_bound_ntfn'_def valid_arch_tcb'_def
           split: Structures_H.endpoint.splits Structures_H.notification.splits
                  Structures_H.thread_state.splits ntfn.splits option.splits
           intro: obj_at'_pspaceI valid_cap'_pspaceI typ_at'_pspaceI valid_arch_obj'_pspaceI)

lemma tcb_space_clear[Invariants_H_pspaceI_assms]:
  "\<lbrakk> tcb_cte_cases (y - x) = Some (getF, setF);
     is_aligned x tcbBlockSizeBits; ps_clear x tcbBlockSizeBits s;
     ksPSpace s x = Some (KOTCB tcb); ksPSpace s y = Some v;
     \<lbrakk> x = y; getF = tcbCTable; setF = tcbCTable_update \<rbrakk> \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P"
  apply (cases "x = y")
   apply simp
  apply (clarsimp simp: ps_clear_def mask_def add_diff_eq)
  apply (drule_tac a=y in equals0D)
  apply (simp add: domI)
  apply (subgoal_tac "\<exists>z. y = x + z \<and> z < 2 ^ tcbBlockSizeBits")
   apply (elim exE conjE)
   apply (frule(1) is_aligned_no_wrap'[rotated, rotated])
   apply (simp add: word_bits_conv objBits_defs)
   apply (erule notE, subst field_simps, rule word_plus_mono_right)
    apply (drule word_le_minus_one_leq,simp,erule is_aligned_no_wrap')
   apply (simp add: word_bits_conv)
  apply (simp add: objBits_defs)
  apply (rule_tac x="y - x" in exI)
  apply (simp add: tcb_cte_cases_def cteSizeBits_def split: if_split_asm)
  done

lemma pspace_in_kernel_mappings'_pspaceI[Invariants_H_pspaceI_assms]:
  "pspace_in_kernel_mappings' s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> pspace_in_kernel_mappings' s'"
  unfolding pspace_in_kernel_mappings'_def
  by simp

(* not interesting on this architecture *)
lemmas [simp] = pspace_in_kernel_mappings'_pspaceI

end

global_interpretation Invariants_H_pspaceI?: Invariants_H_pspaceI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Invariants_H_pspaceI_assms)?)?)
  qed

context Arch begin arch_global_naming

named_theorems Invariants_H_cte_ats_assms

(* FIXME arch-split: for proofs which require exact offsets lining up instead of cteSizeBits *)
lemma raw_tcb_cte_cases_simps:
  "tcb_cte_cases 32 = Some (tcbVTable, tcbVTable_update)"
  "tcb_cte_cases 64 = Some (tcbReply, tcbReply_update)"
  "tcb_cte_cases 96 = Some (tcbCaller, tcbCaller_update)"
  "tcb_cte_cases 128 = Some (tcbIPCBufferFrame, tcbIPCBufferFrame_update)"
  by (simp add: tcb_cte_cases_def cteSizeBits_def)+

lemma cte_wp_at_cases'[Invariants_H_cte_ats_assms]:
  shows "cte_wp_at' P p s =
  ((\<exists>cte. ksPSpace s p = Some (KOCTE cte) \<and> is_aligned p cte_level_bits
             \<and> P cte \<and> ps_clear p cteSizeBits s) \<or>
   (\<exists>n tcb getF setF. ksPSpace s (p - n) = Some (KOTCB tcb) \<and> is_aligned (p - n) tcbBlockSizeBits
             \<and> tcb_cte_cases n = Some (getF, setF) \<and> P (getF tcb) \<and> ps_clear (p - n) tcbBlockSizeBits s))"
  (is "?LHS = ?RHS")
  supply raw_tcb_cte_cases_simps[simp]
  apply (rule iffI)
   apply (clarsimp simp: cte_wp_at'_def split_def
                         getObject_def bind_def simpler_gets_def
                         assert_opt_def return_def fail_def
                  split: option.splits
                    del: disjCI)
   apply (clarsimp simp: loadObject_cte typeError_def alignError_def
                         fail_def return_def objBits_simps'
                         is_aligned_mask[symmetric] alignCheck_def
                         tcbVTableSlot_def field_simps tcbCTableSlot_def
                         tcbReplySlot_def tcbCallerSlot_def
                         tcbIPCBufferSlot_def
                         lookupAround2_char1
                         cte_level_bits_def Ball_def
                         unless_def when_def bind_def
                  split: kernel_object.splits if_split_asm option.splits
                    del: disjCI)
        apply (subst(asm) in_magnitude_check3, simp+,
               simp split: if_split_asm, (rule disjI2)?, intro exI, rule conjI,
               erule rsubst[where P="\<lambda>x. ksPSpace s x = v" for s v],
               fastforce simp add: field_simps, simp)+
   apply (subst(asm) in_magnitude_check3, simp+)
   apply (simp split: if_split_asm
                add: )
  apply (simp add: cte_wp_at'_def getObject_def split_def
                   bind_def simpler_gets_def return_def
                   assert_opt_def fail_def objBits_defs
            split: option.splits)
  apply (elim disjE conjE exE)
   apply (erule(1) ps_clear_lookupAround2)
     apply simp
    apply (simp add: field_simps)
    apply (erule is_aligned_no_wrap')
     apply (simp add: cte_level_bits_def word_bits_conv)
    apply (simp add: cte_level_bits_def)
   apply (simp add: loadObject_cte unless_def alignCheck_def
                    is_aligned_mask[symmetric] objBits_simps'
                    cte_level_bits_def magnitudeCheck_def
                    return_def fail_def)
   apply (clarsimp simp: bind_def return_def when_def fail_def
                  split: option.splits)
   apply simp
  apply (erule(1) ps_clear_lookupAround2)
    prefer 3
    apply (simp add: loadObject_cte unless_def alignCheck_def
                     is_aligned_mask[symmetric] objBits_simps'
                     cte_level_bits_def magnitudeCheck_def
                     return_def fail_def tcbCTableSlot_def tcbVTableSlot_def
                     tcbIPCBufferSlot_def tcbReplySlot_def tcbCallerSlot_def
              split: option.split_asm)
     apply (clarsimp simp: bind_def tcb_cte_cases_def cteSizeBits_def split: if_split_asm)
    apply (clarsimp simp: bind_def tcb_cte_cases_def iffD2[OF linorder_not_less]
                          return_def cteSizeBits_def
                   split: if_split_asm)
   apply (subgoal_tac "p - n \<le> (p - n) + n", simp)
   apply (erule is_aligned_no_wrap')
    apply (simp add: word_bits_conv)
   apply (simp add: tcb_cte_cases_def cteSizeBits_def split: if_split_asm)
  apply (subgoal_tac "(p - n) + n \<le> (p - n) + 0x7FF")
   apply (simp add: field_simps)
  apply (rule word_plus_mono_right)
   apply (simp add: tcb_cte_cases_def cteSizeBits_def split: if_split_asm)
  apply (erule is_aligned_no_wrap')
  apply simp
  done

lemma cte_wp_atE'[consumes 1, case_names CTE TCB]:
  assumes cte: "cte_wp_at' P ptr s"
  and   r1: "\<And>cte.
    \<lbrakk> ksPSpace s ptr = Some (KOCTE cte); ps_clear ptr cte_level_bits s;
      is_aligned ptr cte_level_bits; P cte \<rbrakk> \<Longrightarrow> R"
  and   r2: "\<And> tcb ptr' getF setF.
  \<lbrakk> ksPSpace s ptr' = Some (KOTCB tcb); ps_clear ptr' tcbBlockSizeBits s; is_aligned ptr' tcbBlockSizeBits;
     tcb_cte_cases (ptr - ptr') = Some (getF, setF); P (getF tcb) \<rbrakk> \<Longrightarrow> R"
  shows "R"
  by (rule disjE [OF iffD1 [OF cte_wp_at_cases' cte]]) (auto intro: r1 r2 simp: cte_level_bits_def objBits_defs)

lemma cte_wp_at_cteI':
  assumes "ksPSpace s ptr = Some (KOCTE cte)"
  assumes "is_aligned ptr cte_level_bits"
  assumes "ps_clear ptr cte_level_bits s"
  assumes "P cte"
  shows "cte_wp_at' P ptr s"
  using assms by (simp add: cte_wp_at_cases' cte_level_bits_def objBits_defs)

lemma cte_at_typ'[Invariants_H_cte_ats_assms]:
  "cte_at' c = (\<lambda>s. typ_at' CTET c s \<or> (\<exists>n. typ_at' TCBT (c - n) s \<and> n \<in> dom tcb_cte_cases))"
proof -
  have P: "\<And>ko. (koTypeOf ko = CTET) = (\<exists>cte. ko = KOCTE cte)"
          "\<And>ko. (koTypeOf ko = TCBT) = (\<exists>tcb. ko = KOTCB tcb)"
    by (case_tac ko, simp_all)+
  have Q: "\<And>P f. (\<exists>x. (\<exists>y. x = f y) \<and> P x) = (\<exists>y. P (f y))"
    by fastforce
  show ?thesis
    by (fastforce simp: cte_wp_at_cases' obj_at'_real_def typ_at'_def
                        ko_wp_at'_def objBits_simps' P Q conj_comms cte_level_bits_def)
qed

(* interface lemma *)
lemma tcb_at_cte_at':
  "tcb_at' t s \<Longrightarrow> cte_at' t s"
  apply (clarsimp simp add: cte_wp_at_cases' obj_at'_def projectKO_def
                       del: disjCI)
  apply (case_tac ko)
   apply (simp_all add: projectKO_opt_tcb fail_def)
  apply (rule exI[where x=0])
  apply (clarsimp simp add: return_def objBits_simps)
  done

end

global_interpretation Invariants_H_cte_ats?: Invariants_H_cte_ats
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Invariants_H_cte_ats_assms)?)
  qed


(* arch-specific consequences of kernel_state field update identities *)

context Arch_pspace_update_eq'
begin

lemma page_table_at_update' [iff]:
  "page_table_at' pt_t p (f s) = page_table_at' pt_t p s"
  by (simp add: page_table_at'_def)

lemma frame_at_update' [iff]:
  "frame_at' p sz d (f s) = frame_at' p sz d s"
  by (simp add: frame_at'_def)

lemma pspace_in_kernel_mappings_update' [iff]:
  "pspace_in_kernel_mappings' (f s) = pspace_in_kernel_mappings' s"
  by (simp add: pspace_in_kernel_mappings'_def)

end

context Arch_p_arch_idle_update_eq'
begin

lemma valid_arch_state_update'[iff]:
  "valid_arch_state' (f s) = valid_arch_state' s"
  by (simp add: valid_arch_state'_def arch cong: option.case_cong)

end

context Arch begin arch_global_naming

lemma mask_wordRadix_less_wordBits:
  assumes sz: "wordRadix \<le> size w"
  shows "unat ((w::'a::len word) && mask wordRadix) < wordBits"
  using word_unat_mask_lt[where m=wordRadix and w=w] assms
  by (simp add: wordRadix_def wordBits_def')

lemma priority_mask_wordRadix_size:
  "unat ((w::priority) && mask wordRadix) < wordBits"
  by (rule mask_wordRadix_less_wordBits, simp add: wordRadix_def word_size)

lemma canonical_address_mask_eq:
  "canonical_address p = (p && mask (Suc canonical_bit) = p)"
  by (simp add: canonical_address_def canonical_address_of_def ucast_ucast_mask canonical_bit_def)

lemma canonical_address_and:
  "canonical_address p \<Longrightarrow> canonical_address (p && b)"
  by (simp add: canonical_address_range word_and_le)

lemma canonical_address_add:
  assumes "is_aligned p n"
  assumes "f < 2 ^ n"
  assumes "n \<le> canonical_bit"
  assumes "canonical_address p"
  shows "canonical_address (p + f)"
proof -
  from `f < 2 ^ n`
  have "f \<le> mask n"
    by (simp add: mask_plus_1 plus_one_helper)

  from `canonical_address p`
  have "p && mask (Suc canonical_bit) = p"
    by (simp add: canonical_address_mask_eq)
  moreover
  from `f \<le> mask n` `is_aligned p n`
  have "p + f = p || f"
    by (simp add: word_and_or_mask_aligned)
  moreover
  from `f \<le> mask n` `n \<le> canonical_bit`
  have "f \<le> mask (Suc canonical_bit)"
    using le_smaller_mask by fastforce
  hence "f && mask (Suc canonical_bit) = f"
    by (simp add: le_mask_imp_and_mask)
  ultimately
  have "(p + f) && mask (Suc canonical_bit) = p + f"
    by (simp add: word_ao_dist)
  thus ?thesis
    by (simp add: canonical_address_mask_eq)
qed

lemma range_cover_canonical_address:
  "\<lbrakk> range_cover ptr sz us n ; p < n ;
     canonical_address (ptr && ~~ mask sz) ; sz \<le> maxUntypedSizeBits \<rbrakk>
   \<Longrightarrow> canonical_address (ptr + of_nat p * 2 ^ us)"
  apply (subst word_plus_and_or_coroll2[symmetric, where w = "mask sz"])
  apply (subst add.commute)
  apply (subst add.assoc)
  apply (rule canonical_address_add[where n=sz] ; simp add: untypedBits_defs is_aligned_neg_mask)
   apply (drule (1) range_cover.range_cover_compare)
   apply (clarsimp simp: word_less_nat_alt)
   apply unat_arith
  apply (simp add: canonical_bit_def)
  done

lemma tcb_hyp_refs_of'_simps[simp]:
  "tcb_hyp_refs' atcb = tcb_vcpu_refs' (atcbVCPUPtr atcb)"
  by (auto simp: tcb_hyp_refs'_def)

lemma tcb_vcpu_refs_of'_simps[simp]:
  "tcb_vcpu_refs' (Some vc) = {(vc, TCBHypRef)}"
  "tcb_vcpu_refs' None = {}"
  by (auto simp: tcb_vcpu_refs'_def)

lemma vcpu_tcb_refs_of'_simps[simp]:
  "vcpu_tcb_refs' (Some tcb) = {(tcb, HypTCBRef)}"
  "vcpu_tcb_refs' None = {}"
  by (auto simp: vcpu_tcb_refs'_def)

lemma refs_of_a'_simps[simp]:
  "refs_of_a' (KOASIDPool p) = {}"
  "refs_of_a' (KOPTE pt) = {}"
  "refs_of_a' (KOVCPU v) = vcpu_tcb_refs' (vcpuTCBPtr v)"
 by (auto simp: refs_of_a'_def)

lemma vcpu_at_is_vcpu':
  "vcpu_at' v = ko_wp_at' is_vcpu' v"
  apply (rule ext)
  apply (clarsimp simp: typ_at'_def is_vcpu'_def ko_wp_at'_def)
  apply (rule iffI; clarsimp?)
  apply (case_tac ko; simp; rename_tac ako; case_tac ako; simp)
  done

lemma hyp_refs_of_rev':
 "(x, TCBHypRef) \<in> hyp_refs_of' ko =
    (\<exists>tcb. ko = KOTCB tcb \<and> (atcbVCPUPtr (tcbArch tcb) = Some x))"
 "(x, HypTCBRef) \<in> hyp_refs_of' ko =
    (\<exists>v. ko = KOArch (KOVCPU v) \<and> (vcpuTCBPtr v = Some x))"
  by (auto simp: hyp_refs_of'_def tcb_hyp_refs'_def tcb_vcpu_refs'_def
                    vcpu_tcb_refs'_def refs_of_a'_def
              split: kernel_object.splits arch_kernel_object.splits option.split)

lemma hyp_refs_of_hyp_live':
  "hyp_refs_of' ko \<noteq> {} \<Longrightarrow> hyp_live' ko"
  apply (cases ko, simp_all)
   apply (rename_tac tcb_ext)
   apply (simp add: tcb_hyp_refs'_def hyp_live'_def)
   apply (case_tac "atcbVCPUPtr (tcbArch tcb_ext)"; clarsimp)
  apply (clarsimp simp: hyp_live'_def arch_live'_def refs_of_a'_def vcpu_tcb_refs'_def
                  split: arch_kernel_object.splits option.splits)
  done

lemma hyp_refs_of_live':
  "hyp_refs_of' ko \<noteq> {} \<Longrightarrow> live' ko"
  by (cases ko, simp_all add: live'_def hyp_refs_of_hyp_live')

lemmas valid_cap_simps' =
  valid_cap'_def[split_simps capability.split arch_capability.split]

lemma is_physical_cases:
 "(capClass cap = PhysicalClass) =
  (case cap of NullCap                         \<Rightarrow> False
             | DomainCap                       \<Rightarrow> False
             | IRQControlCap                   \<Rightarrow> False
             | IRQHandlerCap irq               \<Rightarrow> False
             | ReplyCap r m cr                 \<Rightarrow> False
             | ArchObjectCap ASIDControlCap    \<Rightarrow> False
             | _                               \<Rightarrow> True)"
  by (simp split: capability.splits arch_capability.splits zombie_type.splits)

lemma typ_at_lift_page_table_at':
  assumes x: "\<And>T p. f \<lbrace>typ_at' T p\<rbrace>"
  shows "f \<lbrace>page_table_at' pt_t p\<rbrace>"
  unfolding page_table_at'_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' x)

lemma typ_at_lift_asid_at':
  "(\<And>T p. \<lbrace>typ_at' T p\<rbrace> f \<lbrace>\<lambda>_. typ_at' T p\<rbrace>) \<Longrightarrow> \<lbrace>asid_pool_at' p\<rbrace> f \<lbrace>\<lambda>_. asid_pool_at' p\<rbrace>"
  by assumption

lemma typ_at_lift_vcpu_at':
  "(\<And>T p. \<lbrace>typ_at' T p\<rbrace> f \<lbrace>\<lambda>_. typ_at' T p\<rbrace>) \<Longrightarrow> \<lbrace>vcpu_at' p\<rbrace> f \<lbrace>\<lambda>_. vcpu_at' p\<rbrace>"
  by assumption

lemma typ_at_lift_frame_at':
  assumes "\<And>T p. f \<lbrace>typ_at' T p\<rbrace>"
  shows "f \<lbrace>frame_at' p sz d\<rbrace>"
  unfolding frame_at'_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_const_imp_lift assms split_del: if_split)

lemma typ_at_lift_valid_cap':
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_cap' cap s\<rbrace> f \<lbrace>\<lambda>rv s. valid_cap' cap s\<rbrace>"
  including no_pre
  apply (simp add: valid_cap'_def)
  apply wp
  apply (case_tac cap;
         simp add: valid_cap'_def P[of id, simplified] typ_at_lift_tcb'
                   hoare_vcg_prop typ_at_lift_ep'
                   typ_at_lift_ntfn' typ_at_lift_cte_at'
                   hoare_vcg_conj_lift [OF typ_at_lift_cte_at'])
     apply (rename_tac zombie_type nat)
     apply (case_tac zombie_type; simp)
      apply (wp typ_at_lift_tcb' P hoare_vcg_all_lift typ_at_lift_cte')+
    apply (rename_tac arch_capability)
    apply (case_tac arch_capability,
           simp_all add: P[of id, simplified] vspace_table_at'_defs
                         hoare_vcg_prop All_less_Ball
                    split del: if_split)
       apply (wp hoare_vcg_const_Ball_lift P typ_at_lift_valid_untyped'
                 hoare_vcg_all_lift typ_at_lift_cte' typ_at_lift_frame_at')+
  done

(* interface lemma *)
lemma valid_arch_tcb_lift':
  assumes x: "\<And>T p. \<lbrace>typ_at' T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at' T p\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_arch_tcb' tcb s\<rbrace> f \<lbrace>\<lambda>rv s. valid_arch_tcb' tcb s\<rbrace>"
  apply (clarsimp simp add: valid_arch_tcb'_def)
  apply (cases "atcbVCPUPtr tcb"; simp)
   apply (wp x)+
  done

lemmas typ_at_lifts =
           typ_at_lift_tcb' typ_at_lift_ep' typ_at_lift_ntfn' typ_at_lift_cte' typ_at_lift_cte_at'
           typ_at_lift_valid_untyped' typ_at_lift_valid_cap' valid_bound_tcb_lift
           typ_at_lift_page_table_at' typ_at_lift_asid_at' typ_at_lift_vcpu_at'

lemma valid_arch_state_armKSGlobalUserVSpace:
  "valid_arch_state' s \<Longrightarrow> canonical_address (addrFromKPPtr (armKSGlobalUserVSpace (ksArchState s)))"
  by (simp add: valid_arch_state'_def)

lemma page_table_pte_atI':
  "\<lbrakk> page_table_at' pt_t p s; i \<le> mask (ptTranslationBits pt_t) \<rbrakk> \<Longrightarrow>
   pte_at' (p + (i << pte_bits)) s"
  by (simp add: page_table_at'_def)

lemmas bit_simps' = pteBits_def asidHighBits_def asidPoolBits_def asid_low_bits_def
                    asid_high_bits_def bit_simps

lemma objBitsT_simps:
  "objBitsT EndpointT = epSizeBits"
  "objBitsT NotificationT = ntfnSizeBits"
  "objBitsT CTET = cteSizeBits"
  "objBitsT TCBT = tcbBlockSizeBits"
  "objBitsT UserDataT = pageBits"
  "objBitsT UserDataDeviceT = pageBits"
  "objBitsT KernelDataT = pageBits"
  "objBitsT (ArchT PTET) = word_size_bits"
  "objBitsT (ArchT ASIDPoolT) = pageBits"
  "objBitsT (ArchT VCPUT) = vcpuBits"
  unfolding objBitsT_def makeObjectT_def archMakeObjectT_def
  by (simp add: makeObject_simps objBits_simps bit_simps')+

(* interface lemma - exports only generic equations from objBitsT_simps *)
lemmas gen_objBitsT_simps = objBitsT_simps(1-7)

(* interface lemma *)
lemma objBitsT_koTypeOf:
  "(objBitsT (koTypeOf ko)) = objBitsKO ko"
  apply (cases ko; simp add: objBits_simps objBitsT_simps)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object; simp add: archObjSize_def objBitsT_simps bit_simps')
  done

end

qualify AARCH64_H (in Arch)

(*
  Then idea with this class is to be able to generically constrain
  predicates over pspace_storable values to are not of type VCPU,
  this is useful for invariants such as obj_at' that are trivially
  true (sort of) if the predicate and the function (in the Hoare triple)
  manipulate different types of objects
*)

class no_vcpu = pspace_storable +
  assumes not_vcpu: "koType TYPE('a) \<noteq> ArchT AARCH64_H.VCPUT"

instance tcb              :: no_vcpu by intro_classes auto
instance endpoint         :: no_vcpu by intro_classes auto
instance notification     :: no_vcpu by intro_classes auto
instance cte              :: no_vcpu by intro_classes auto
instance user_data        :: no_vcpu by intro_classes auto
instance user_data_device :: no_vcpu by intro_classes auto

end_qualify

instantiation AARCH64_H.asidpool :: no_vcpu
begin
interpretation Arch .
instance by intro_classes auto
end

instantiation AARCH64_H.pte :: no_vcpu
begin
interpretation Arch .
instance by intro_classes auto
end

context Arch begin

lemma objBits_less_word_bits:
  "objBits v < word_bits"
  unfolding objBits_simps'
  apply (case_tac "injectKO v"; simp)
  by (simp add: pageBits_def pteBits_def objBits_simps word_bits_def
         split: arch_kernel_object.split)+

lemma objBits_pos_power2[simp]:
  assumes "objBits v < word_bits"
  shows "(1::machine_word) < (2::machine_word) ^ objBits v"
  unfolding objBits_simps'
  apply (insert assms)
  apply (case_tac "injectKO v"; simp)
  by (simp add: pageBits_def pteBits_def objBits_simps
         split: arch_kernel_object.split)+

end

end
